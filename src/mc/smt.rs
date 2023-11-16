// Copyright 2023 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

use crate::ir;
use crate::ir::{Context, Expr, ExprRef, GetNode, SignalKind, Type, TypeCheck};
use std::borrow::Cow;

use crate::ir::SignalKind::Input;
use crate::mc::{State, Value, Witness};
use easy_smt as smt;

#[derive(Debug, Clone, Copy)]
pub struct SmtSolverCmd {
    pub name: &'static str,
    pub args: &'static [&'static str],
    pub supports_uf: bool,
}

pub const BITWUZLA_CMD: SmtSolverCmd = SmtSolverCmd {
    name: "bitwuzla",
    args: &["--smt2", "--incremental"],
    supports_uf: false,
};

#[derive(Debug, Clone, Copy)]
pub struct SmtModelCheckerOptions {
    /// Perform additional checking to ensure that the assumptions are satisfiable.
    pub check_constraints: bool,
    /// Perform one SMT solver check per assertion instead of combining them into a single check.
    pub check_bad_states_individually: bool,
}

pub struct SmtModelChecker {
    solver: SmtSolverCmd,
    opts: SmtModelCheckerOptions,
}

type Result<T> = std::io::Result<T>;

impl SmtModelChecker {
    pub fn new(solver: SmtSolverCmd, opts: SmtModelCheckerOptions) -> Self {
        Self { solver, opts }
    }

    pub fn check(
        &self,
        ctx: &ir::Context,
        sys: &ir::TransitionSystem,
        k_max: u64,
    ) -> Result<ModelCheckResult> {
        assert!(k_max > 0 && k_max <= 2000, "unreasonable k_max={}", k_max);
        let mut smt_ctx = easy_smt::ContextBuilder::new()
            .solver(self.solver.name, self.solver.args)
            .replay_file(Some(std::fs::File::create("replay.smt")?))
            .build()?;

        // z3 only supports the non-standard as-const array syntax when the logic is set to ALL
        let logic = if self.solver.name == "z3" {
            "ALL"
        } else if self.solver.supports_uf {
            "QF_AUFBV"
        } else {
            "QF_ABV"
        };
        smt_ctx.set_logic(logic)?;

        // TODO: maybe add support for the more compact SMT encoding
        let mut enc = UnrollSmtEncoding::new(ctx, sys);
        enc.define_header(&mut smt_ctx)?;
        enc.init(&mut smt_ctx)?;

        let constraints = sys.constraints();
        let bad_states = sys.bad_states();

        for k in 0..=k_max {
            // assume all constraints hold in this step
            for (expr_ref, _) in constraints.iter() {
                smt_ctx.assert(enc.get_constraint(*expr_ref))?;
            }

            // make sure the constraints are not contradictory
            if self.opts.check_constraints {
                let res = smt_ctx.check()?;
                assert_eq!(
                    res,
                    smt::Response::Sat,
                    "Found unsatisfiable constraints in cycle {}",
                    k
                );
            }

            if self.opts.check_bad_states_individually {
                for (_bs_id, (expr_ref, _)) in bad_states.iter().enumerate() {
                    let res = smt_ctx.check_assuming([enc.get_bad_state(*expr_ref)])?;

                    if res == smt::Response::Sat {
                        let wit = self.get_witness(sys, &mut smt_ctx, &enc, k)?;
                        return Ok(ModelCheckResult::Fail(wit));
                    }
                }
            } else {
                let any_bad = smt_ctx.or_many(
                    bad_states
                        .iter()
                        .map(|(expr_ref, _)| enc.get_bad_state(*expr_ref)),
                );
                let res = smt_ctx.check_assuming([any_bad])?;

                if res == smt::Response::Sat {
                    let wit = self.get_witness(sys, &mut smt_ctx, &enc, k)?;
                    return Ok(ModelCheckResult::Fail(wit));
                }
            }

            // advance
            enc.unroll(&mut smt_ctx)?;
        }

        // we have not found any assertion violations
        Ok(ModelCheckResult::Success)
    }

    fn get_witness(
        &self,
        sys: &ir::TransitionSystem,
        smt_ctx: &mut smt::Context,
        enc: &UnrollSmtEncoding,
        k_max: u64,
    ) -> Result<Witness> {
        let mut wit = Witness::default();
        // collect initial values
        for (state_idx, state) in sys.states().enumerate() {
            let sym_at = enc.get_signal_at(state.symbol, 0);
            let value = get_smt_value(smt_ctx, sym_at)?;
            wit.init.insert(state_idx, value);
        }

        // collect all inputs
        let inputs = sys.get_signals(|s| s.kind == SignalKind::Input);
        for k in 0..=k_max {
            let mut input_values = State::default();
            for (input_idx, (input, _)) in inputs.iter().enumerate() {
                let sym_at = enc.get_signal_at(*input, k);
                let value = get_smt_value(smt_ctx, sym_at)?;
                input_values.insert(input_idx, value);
            }
            wit.inputs.push(input_values);
        }

        Ok(wit)
    }
}

fn get_smt_value(smt_ctx: &mut smt::Context, expr: smt::SExpr) -> Result<Value> {
    let smt_value = smt_ctx.get_value(vec![expr])?[0].1;
    todo!("Convert: {:?}", smt_value)
}

pub enum ModelCheckResult {
    Success,
    Fail(Witness),
}

pub trait TransitionSystemEncoding {
    fn define_header(&self, smt_ctx: &mut smt::Context) -> Result<()>;
    fn init(&mut self, smt_ctx: &mut smt::Context) -> Result<()>;
    fn unroll(&self, smt_ctx: &mut smt::Context) -> Result<()>;
    fn get_constraint(&self, e: ExprRef) -> smt::SExpr;
    fn get_bad_state(&self, e: ExprRef) -> smt::SExpr;
    fn get_signal_at(&self, sym: ExprRef, k: u64) -> smt::SExpr;
}

pub struct UnrollSmtEncoding<'a> {
    ctx: &'a ir::Context,
    sys: &'a ir::TransitionSystem,
    current_step: Option<u64>,
    inputs: Vec<(ExprRef, ir::SignalInfo)>,
}

impl<'a> UnrollSmtEncoding<'a> {
    pub fn new(ctx: &'a ir::Context, sys: &'a ir::TransitionSystem) -> Self {
        // remember inputs instead of constantly re-filtering them
        let inputs = sys.get_signals(|s| s.kind == Input);
        Self {
            ctx,
            sys,
            current_step: None,
            inputs,
        }
    }

    fn define_inputs_and_signals(&self, smt_ctx: &mut smt::Context, step: u64) -> Result<()> {
        // declare inputs
        for (input_sym, _) in self.inputs.iter() {
            let name = self.name_at(*input_sym, step);
            let tpe = convert_tpe(smt_ctx, input_sym.get_type(self.ctx));
            smt_ctx.declare_const(escape_smt_identifier(&name), tpe)?;
        }

        // define signals
        todo!();
    }

    fn expr_in_step(
        &self,
        smt_ctx: &mut smt::Context,
        ctx: &Context,
        expr: ExprRef,
        step: u64,
    ) -> smt::SExpr {
        let rename = |name: &str| -> Cow<'_, str> { Cow::Owned(format!("{}@{}", name, step)) };
        convert_expr(smt_ctx, ctx, expr, rename)
    }

    fn name_at(&self, sym: ExprRef, step: u64) -> String {
        format!("{}@{}", sym.get_symbol_name(self.ctx).unwrap(), step)
    }
}

fn convert_tpe(smt_ctx: &mut smt::Context, tpe: Type) -> smt::SExpr {
    match tpe {
        Type::BV(1) => smt_ctx.bool_sort(),
        Type::BV(width) => smt_ctx.bit_vec_sort(smt_ctx.numeral(width)),
        Type::Array(a) => {
            let from = convert_tpe(smt_ctx, a.index_type());
            let to = convert_tpe(smt_ctx, a.data_type());
            smt_ctx.array_sort(from, to)
        }
    }
}

fn convert_expr<'a, 'f>(
    smt_ctx: &'a mut smt::Context,
    ctx: &'a ir::Context,
    expr: ExprRef,
    rename_sym: impl Fn(&'f str) -> Cow<'f, str>,
) -> smt::SExpr
where
    'a: 'f,
{
    match ctx.get(expr) {
        Expr::BVSymbol { name, .. } => {
            let renamed = (rename_sym)(ctx.get(name));
            smt_ctx.atom(escape_smt_identifier(&renamed))
        }
        Expr::BVLiteral { value, width } if *width == 1 => {
            if *value == 1 {
                smt_ctx.true_()
            } else {
                smt_ctx.false_()
            }
        }
        Expr::BVLiteral { value, width } => smt_ctx.binary(*width as usize, *value),
        Expr::BVZeroExt { .. } => todo!(),
        Expr::BVSignExt { .. } => todo!(),
        Expr::BVSlice { .. } => todo!(),
        Expr::BVNot(_, _) => todo!(),
        Expr::BVNegate(_, _) => todo!(),
        Expr::BVReduceOr(_) => todo!(),
        Expr::BVReduceAnd(_) => todo!(),
        Expr::BVReduceXor(_) => todo!(),
        Expr::BVEqual(_, _) => todo!(),
        Expr::BVImplies(_, _) => todo!(),
        Expr::BVGreater(_, _) => todo!(),
        Expr::BVGreaterSigned(_, _) => todo!(),
        Expr::BVGreaterEqual(_, _) => todo!(),
        Expr::BVGreaterEqualSigned(_, _) => todo!(),
        Expr::BVConcat(_, _, _) => todo!(),
        Expr::BVAnd(_, _, _) => todo!(),
        Expr::BVOr(_, _, _) => todo!(),
        Expr::BVXor(_, _, _) => todo!(),
        Expr::BVShiftLeft(_, _, _) => todo!(),
        Expr::BVArithmeticShiftRight(_, _, _) => todo!(),
        Expr::BVShiftRight(_, _, _) => todo!(),
        Expr::BVAdd(_, _, _) => todo!(),
        Expr::BVMul(_, _, _) => todo!(),
        Expr::BVSignedDiv(_, _, _) => todo!(),
        Expr::BVUnsignedDiv(_, _, _) => todo!(),
        Expr::BVSignedMod(_, _, _) => todo!(),
        Expr::BVSignedRem(_, _, _) => todo!(),
        Expr::BVUnsignedRem(_, _, _) => todo!(),
        Expr::BVSub(_, _, _) => todo!(),
        Expr::BVArrayRead { .. } => todo!(),
        Expr::BVIte { .. } => todo!(),
        Expr::ArraySymbol { name, .. } => {
            let renamed = (rename_sym)(ctx.get(name));
            smt_ctx.atom(escape_smt_identifier(&renamed))
        }
        Expr::ArrayConstant { .. } => todo!(),
        Expr::ArrayEqual(_, _) => todo!(),
        Expr::ArrayStore { .. } => todo!(),
        Expr::ArrayIte { .. } => todo!(),
    }
}

impl<'a> TransitionSystemEncoding for UnrollSmtEncoding<'a> {
    fn define_header(&self, _smt_ctx: &mut smt::Context) -> Result<()> {
        // nothing to do in this encoding
        Ok(())
    }

    fn init(&mut self, smt_ctx: &mut smt::Context) -> Result<()> {
        assert!(self.current_step.is_none(), "init must be called only once");
        self.current_step = Some(0);
        // declare initial states
        for state in self.sys.states() {
            let name = self.name_at(state.symbol, 0);
            let out = convert_tpe(smt_ctx, state.symbol.get_type(self.ctx));
            match state.init {
                Some(value) => {
                    let body = self.expr_in_step(smt_ctx, self.ctx, value, 0);
                    smt_ctx.define_const(escape_smt_identifier(&name), out, body)?;
                }
                None => {
                    smt_ctx.declare_const(escape_smt_identifier(&name), out)?;
                }
            }
        }
        // define the inputs for the initial state and all signals derived from it
        self.define_inputs_and_signals(smt_ctx, 0)?;
        Ok(())
    }

    fn unroll(&self, smt_ctx: &mut smt::Context) -> Result<()> {
        todo!()
    }

    fn get_constraint(&self, e: ExprRef) -> smt::SExpr {
        todo!()
    }

    fn get_bad_state(&self, e: ExprRef) -> smt::SExpr {
        todo!()
    }

    fn get_signal_at(&self, sym: ExprRef, k: u64) -> smt::SExpr {
        todo!()
    }
}

/// See <simple_symbol> definition in the Concrete Syntax Appendix of the SMTLib Spec
fn is_simple_smt_identifier(id: &str) -> bool {
    if id.is_empty() {
        return false; // needs to be non-empty
    }
    let mut is_first = true;
    for cc in id.chars() {
        if !cc.is_ascii() {
            return false; // all allowed characters are ASCII characters
        }
        let ac = cc as u8;
        let is_alpha = (ac >= b'A' && ac <= b'Z') || (ac >= b'a' && ac <= b'z');
        let is_num = ac >= b'0' && ac <= b'9';
        let is_other_allowed_char = matches!(
            ac,
            b'+' | b'-'
                | b'/'
                | b'*'
                | b'='
                | b'%'
                | b'?'
                | b'!'
                | b'.'
                | b'$'
                | b'_'
                | b'~'
                | b'&'
                | b'^'
                | b'<'
                | b'>'
                | b'@'
        );
        if !(is_alpha | is_num | is_other_allowed_char) {
            return false;
        }
        if is_num && is_first {
            return false; // the first character is not allowed ot be a digit
        }
        is_first = false;
    }
    true // passed all checks
}

fn escape_smt_identifier(id: &str) -> std::borrow::Cow<'_, str> {
    if is_simple_smt_identifier(id) {
        std::borrow::Cow::Borrowed(id)
    } else {
        let escaped = format!("|{}|", id);
        std::borrow::Cow::Owned(escaped)
    }
}

fn unescape_smt_identifier(id: &str) -> &str {
    if id.starts_with("|") {
        assert!(id.ends_with("|"));
        &id[1..id.len() - 1]
    } else {
        id
    }
}

#[cfg(test)]
mod tests {
    use easy_smt::*;

    #[test]
    fn easy_smt_symbol_escaping() {
        let mut ctx = ContextBuilder::new().build().unwrap();
        let test = ctx.atom("test");
        assert_eq!(ctx.display(test).to_string(), "test");
        let needs_to_be_escaped_1 = ctx.atom("a b");
        assert_eq!(ctx.display(needs_to_be_escaped_1).to_string(), "a b");
    }
}
