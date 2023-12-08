// Copyright 2023 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

use crate::ir;
use crate::ir::{
    count_expr_uses, ArrayType, Expr, ExprRef, GetNode, SignalInfo, SignalKind, Type, TypeCheck,
    WidthInt,
};
use crate::mc::{parse_big_uint_from_bit_string, Witness, WitnessArray, WitnessValue};
use easy_smt as smt;
use num_bigint::BigUint;
use num_traits::{One, Zero};
use std::borrow::Cow;

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
    /// If true, the communication with the SMT solver will be logged into a `replay.smt` file.
    pub save_smt_replay: bool,
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
        let replay_file = if self.opts.save_smt_replay {
            Some(std::fs::File::create("replay.smt")?)
        } else {
            None
        };
        let mut smt_ctx = easy_smt::ContextBuilder::new()
            .solver(self.solver.name, self.solver.args)
            .replay_file(replay_file)
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

        // count expression uses
        let use_counts = count_expr_uses(ctx, sys);
        // TODO: use this data in order to optimize the way we print smt expressions!

        // TODO: maybe add support for the more compact SMT encoding
        let mut enc = UnrollSmtEncoding::new(ctx, sys, false);
        enc.define_header(&mut smt_ctx)?;
        enc.init(&mut smt_ctx)?;

        let constraints = sys.constraints();
        let bad_states = sys.bad_states();

        for k in 0..=k_max {
            // assume all constraints hold in this step
            for (expr_ref, _) in constraints.iter() {
                let expr = enc.get_at(&mut smt_ctx, *expr_ref, k);
                smt_ctx.assert(expr)?;
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
                    let expr = enc.get_at(&mut smt_ctx, *expr_ref, k);
                    let res = smt_ctx.check_assuming([expr])?;

                    if res == smt::Response::Sat {
                        let wit = self.get_witness(
                            sys,
                            ctx,
                            &use_counts,
                            &mut smt_ctx,
                            &enc,
                            k,
                            &bad_states,
                        )?;
                        return Ok(ModelCheckResult::Fail(wit));
                    }
                }
            } else {
                let all_bads = bad_states
                    .iter()
                    .map(|(expr_ref, _)| enc.get_at(&mut smt_ctx, *expr_ref, k))
                    .collect::<Vec<_>>();
                let any_bad = smt_ctx.or_many(all_bads);
                let res = smt_ctx.check_assuming([any_bad])?;

                if res == smt::Response::Sat {
                    let wit = self.get_witness(
                        sys,
                        ctx,
                        &use_counts,
                        &mut smt_ctx,
                        &enc,
                        k,
                        &bad_states,
                    )?;
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
        ctx: &ir::Context,
        _use_counts: &[u32], // TODO: analyze array expressions in order to record which indices are accessed
        smt_ctx: &mut smt::Context,
        enc: &UnrollSmtEncoding,
        k_max: u64,
        bad_states: &[(ExprRef, SignalInfo)],
    ) -> Result<Witness> {
        let mut wit = Witness::default();

        // which bad states did we hit?
        for (bad_idx, (expr, _)) in bad_states.iter().enumerate() {
            let sym_at = enc.get_at(smt_ctx, *expr, k_max);
            let value = get_smt_value(smt_ctx, sym_at)?;
            if !value.is_zero() {
                // was the bad state condition fulfilled?
                wit.failed_safety.push(bad_idx as u32);
            }
        }

        // collect initial values
        for (state_idx, state) in sys.states().enumerate() {
            let sym_at = enc.get_at(smt_ctx, state.symbol, 0);
            let value = get_smt_value(smt_ctx, sym_at)?;
            // we assume that state ids are monotonically increasing with +1
            assert_eq!(wit.init.len(), state_idx);
            wit.init.push(Some(value));
            // also save state name
            wit.init_names
                .push(Some(state.symbol.get_symbol_name(ctx).unwrap().to_string()))
        }

        // collect all inputs
        let inputs = sys.get_signals(|s| s.kind == ir::SignalKind::Input);

        // save input names
        for (input, _) in inputs.iter() {
            wit.input_names
                .push(Some(input.get_symbol_name(ctx).unwrap().to_string()));
        }

        for k in 0..=k_max {
            let mut input_values = Vec::default();
            for (input, _) in inputs.iter() {
                let sym_at = enc.get_at(smt_ctx, *input, k);
                let value = get_smt_value(smt_ctx, sym_at)?;
                input_values.push(Some(value));
            }
            wit.inputs.push(input_values);
        }

        // TODO: get rid of default values in a more intelligent fashion,
        //       e.g., by recording which indices are accessed
        for init in wit.init.iter_mut() {
            match init.as_mut() {
                Some(WitnessValue::Array(a)) => {
                    a.default = None;
                }
                _ => {}
            }
        }

        Ok(wit)
    }
}

pub fn get_smt_value(smt_ctx: &mut smt::Context, expr: smt::SExpr) -> Result<WitnessValue> {
    let smt_value = smt_ctx.get_value(vec![expr])?[0].1;
    let res = match parse_smt_bit_vec(smt_ctx, smt_value) {
        Some((value, width)) => WitnessValue::Scalar(value, width),
        None => WitnessValue::Array(parse_smt_array(smt_ctx, smt_value).unwrap()),
    };
    Ok(res)
}

fn parse_smt_bit_vec(smt_ctx: &smt::Context, expr: smt::SExpr) -> Option<(BigUint, WidthInt)> {
    let data = smt_ctx.get(expr);
    match data {
        smt::SExprData::Atom(value) => Some(smt_bit_vec_str_to_value(value)),
        _ => None,
    }
}

fn parse_smt_array(smt_ctx: &smt::Context, expr: smt::SExpr) -> Option<WitnessArray> {
    let data = smt_ctx.get(expr);
    match data {
        smt::SExprData::List([p0, p1]) => parse_smt_as_const(smt_ctx, *p0, *p1),
        smt::SExprData::List([id, array, index, value]) => {
            parse_smt_store(smt_ctx, *id, *array, *index, *value)
        }
        _ => todo!("Unexpected array expression: {}", smt_ctx.display(expr)),
    }
}

fn parse_smt_as_const(
    smt_ctx: &smt::Context,
    p0: smt::SExpr,
    p1: smt::SExpr,
) -> Option<WitnessArray> {
    match smt_ctx.get(p0) {
        smt::SExprData::List([as_str, const_str, array_tpe]) => {
            parse_smt_id(smt_ctx, *as_str, "as")?;
            parse_smt_id(smt_ctx, *const_str, "const")?;
            let tpe = parse_smt_array_tpe(smt_ctx, *array_tpe)?;
            let (default_value, _width) = parse_smt_bit_vec(smt_ctx, p1)?;
            Some(WitnessArray {
                tpe,
                default: Some(default_value),
                updates: Vec::new(),
            })
        }
        _ => None,
    }
}

fn parse_smt_store(
    smt_ctx: &smt::Context,
    id: smt::SExpr,
    array: smt::SExpr,
    index: smt::SExpr,
    value: smt::SExpr,
) -> Option<WitnessArray> {
    parse_smt_id(smt_ctx, id, "store")?;
    let mut inner = parse_smt_array(smt_ctx, array)?;
    let (index_val, _) = parse_smt_bit_vec(smt_ctx, index)?;
    let (data_val, _) = parse_smt_bit_vec(smt_ctx, value)?;
    inner.add_update(index_val, data_val);
    Some(inner)
}

fn parse_smt_array_tpe(smt_ctx: &smt::Context, expr: smt::SExpr) -> Option<ArrayType> {
    match smt_ctx.get(expr) {
        smt::SExprData::List([array, index, data]) => {
            parse_smt_id(smt_ctx, *array, "Array")?;
            let index_width = parse_smt_bit_vec_tpe(smt_ctx, *index)?;
            let data_width = parse_smt_bit_vec_tpe(smt_ctx, *data)?;
            Some(ArrayType {
                index_width,
                data_width,
            })
        }
        _ => None,
    }
}

fn parse_smt_bit_vec_tpe(smt_ctx: &smt::Context, expr: smt::SExpr) -> Option<WidthInt> {
    match smt_ctx.get(expr) {
        smt::SExprData::List([under_score, bit_vec, width]) => {
            parse_smt_id(smt_ctx, *under_score, "_")?;
            parse_smt_id(smt_ctx, *bit_vec, "BitVec")?;
            match smt_ctx.get(*width) {
                smt::SExprData::Atom(val) => Some(WidthInt::from_str_radix(val, 10).unwrap()),
                _ => None,
            }
        }
        _ => None,
    }
}

fn parse_smt_id(smt_ctx: &smt::Context, expr: smt::SExpr, expected: &str) -> Option<()> {
    match smt_ctx.get(expr) {
        smt::SExprData::Atom(val) if val == expected => Some(()),
        _ => None,
    }
}

fn smt_bit_vec_str_to_value(a: &str) -> (BigUint, WidthInt) {
    if let Some(suffix) = a.strip_prefix("#b") {
        parse_big_uint_from_bit_string(suffix)
    } else if let Some(_suffix) = a.strip_prefix("#x") {
        todo!("hex string: {a}")
    } else if a == "true" {
        (BigUint::one(), 1)
    } else if a == "false" {
        (BigUint::zero(), 1)
    } else {
        todo!("decimal string: {a}")
    }
}

pub enum ModelCheckResult {
    Success,
    Fail(Witness),
}

pub trait TransitionSystemEncoding {
    fn define_header(&self, smt_ctx: &mut smt::Context) -> Result<()>;
    fn init(&mut self, smt_ctx: &mut smt::Context) -> Result<()>;
    fn unroll(&mut self, smt_ctx: &mut smt::Context) -> Result<()>;
    /// Allows access to inputs, states, constraints and bad_state expressions.
    fn get_at(&self, smt_ctx: &mut smt::Context, expr: ExprRef, k: u64) -> smt::SExpr;
}

pub struct UnrollSmtEncoding<'a> {
    ctx: &'a ir::Context,
    sys: &'a ir::TransitionSystem,
    current_step: Option<u64>,
    inputs: Vec<(ExprRef, ir::SignalInfo)>,
    /// outputs (depending on option), constraint and bad state signals (for now)
    signals: Vec<(ExprRef, String)>,
}

impl<'a> UnrollSmtEncoding<'a> {
    pub fn new(ctx: &'a ir::Context, sys: &'a ir::TransitionSystem, include_outputs: bool) -> Self {
        // remember inputs instead of constantly re-filtering them
        let inputs = sys.get_signals(|s| s.kind == ir::SignalKind::Input);
        // name all constraints and bad states
        let mut signals = Vec::new();
        for (ii, (expr, _)) in sys.constraints().iter().enumerate() {
            signals.push((*expr, format!("__constraint_{ii}")));
        }
        for (ii, (expr, _)) in sys.bad_states().iter().enumerate() {
            signals.push((*expr, format!("__bad_{ii}")));
        }
        // remember all outputs as well
        if include_outputs {
            for (expr, info) in sys.get_signals(|s| s.kind == SignalKind::Output) {
                signals.push((expr, ctx.get(info.name.unwrap()).to_string()))
            }
        }

        Self {
            ctx,
            sys,
            current_step: None,
            inputs,
            signals,
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
        for (expr, name) in self.signals.iter() {
            let name = format!("{}@{}", name, step);
            let tpe = convert_tpe(smt_ctx, expr.get_type(self.ctx));
            let value = self.expr_in_step(smt_ctx, *expr, step);
            smt_ctx.define_const(escape_smt_identifier(&name), tpe, value)?;
        }

        Ok(())
    }

    fn get_local_expr_symbol_at(
        &self,
        smt_ctx: &mut smt::Context,
        e: ExprRef,
        k: u64,
    ) -> smt::SExpr {
        // is it already a symbol?
        if e.is_symbol(self.ctx) {
            let name = self.name_at(e, k);
            smt_ctx.atom(escape_smt_identifier(&name))
        } else {
            // find our local name
            let base_name: &str = self
                .signals
                .iter()
                .find(|(id, _)| *id == e)
                .map(|(_, n)| n)
                .unwrap();
            let name = format!("{}@{}", base_name, k);
            smt_ctx.atom(escape_smt_identifier(&name))
        }
    }

    fn expr_in_step(&self, smt_ctx: &mut smt::Context, expr: ExprRef, step: u64) -> smt::SExpr {
        let rename = |name: &str| -> Cow<'_, str> { Cow::Owned(format!("{}@{}", name, step)) };
        convert_expr(smt_ctx, self.ctx, expr, &rename)
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

fn convert_expr<'a, 'f, F>(
    smt_ctx: &smt::Context,
    ctx: &'a ir::Context,
    expr: ExprRef,
    rename_sym: &F,
) -> smt::SExpr
where
    F: Fn(&'f str) -> Cow<'f, str>,
    'a: 'f,
{
    match ctx.get(expr) {
        Expr::BVSymbol { name, .. } => {
            let name_str = ctx.get(name);
            let renamed = (rename_sym)(name_str);
            smt_ctx.atom(escape_smt_identifier(&renamed))
        }
        Expr::BVLiteral { value, width } if *width == 1 => {
            if *value == 1 {
                smt_ctx.true_()
            } else {
                smt_ctx.false_()
            }
        }
        Expr::BVLiteral { value, width } => {
            if *width == 1 {
                if *value == 1 {
                    smt_ctx.true_()
                } else {
                    smt_ctx.false_()
                }
            } else {
                smt_ctx.binary(*width as usize, *value)
            }
        }
        Expr::BVZeroExt { e, by, .. } => {
            let e_expr = convert_expr(smt_ctx, ctx, *e, rename_sym);
            match e.get_type(ctx) {
                Type::BV(width) => {
                    if width == 1 {
                        let res_size = (by + 1) as usize;
                        // in the one bit case, the underlying expression is represented as a Bool in SMT
                        smt_ctx.ite(
                            e_expr,
                            smt_ctx.binary(res_size, 1),
                            smt_ctx.binary(res_size, 0),
                        )
                    } else {
                        smt_ctx.zext(e_expr, *by as usize)
                    }
                }
                Type::Array(_) => {
                    panic!("Mall-formed expression: zext should never be applied to an array!")
                }
            }
        }
        Expr::BVSignExt { .. } => todo!(),
        Expr::BVSlice { e, hi, lo } => {
            let e_expr = convert_expr(smt_ctx, ctx, *e, rename_sym);
            // skip no-op bit extracts (this helps us avoid slices on boolean values)
            if *lo == 0 && e.get_type(ctx).get_bit_vector_width().unwrap() - 1 == *hi {
                e_expr
            } else {
                smt_ctx.extract(*hi as i32, *lo as i32, e_expr)
            }
        }
        Expr::BVNot(e_ref, _) => {
            let e = convert_expr(smt_ctx, ctx, *e_ref, rename_sym);
            if e_ref.get_type(ctx).is_bool() {
                smt_ctx.not(e)
            } else {
                smt_ctx.bvnot(e)
            }
        }
        Expr::BVNegate(_, _) => todo!(),
        Expr::BVEqual(a_ref, b_ref) => {
            let a = convert_expr(smt_ctx, ctx, *a_ref, rename_sym);
            let b = convert_expr(smt_ctx, ctx, *b_ref, rename_sym);
            smt_ctx.eq(a, b)
        }
        Expr::BVImplies(a_ref, b_ref) => {
            assert!(a_ref.get_type(ctx).is_bool());
            let a = convert_expr(smt_ctx, ctx, *a_ref, rename_sym);
            let b = convert_expr(smt_ctx, ctx, *b_ref, rename_sym);
            smt_ctx.imp(a, b)
        }
        Expr::BVGreater(a_ref, b_ref) => {
            convert_simple_binop(smt_ctx, ctx, "bvugt", a_ref, b_ref, rename_sym)
        }
        Expr::BVGreaterSigned(_, _) => todo!(),
        Expr::BVGreaterEqual(a_ref, b_ref) => {
            convert_simple_binop(smt_ctx, ctx, "bvuge", a_ref, b_ref, rename_sym)
        }
        Expr::BVGreaterEqualSigned(_, _) => todo!(),
        Expr::BVConcat(_, _, _) => todo!(),
        Expr::BVAnd(a_ref, b_ref, _) => {
            let a = convert_expr(smt_ctx, ctx, *a_ref, rename_sym);
            let b = convert_expr(smt_ctx, ctx, *b_ref, rename_sym);
            if let Some(1) = a_ref.get_type(ctx).get_bit_vector_width() {
                smt_ctx.and(a, b)
            } else {
                smt_ctx.bvand(a, b)
            }
        }
        Expr::BVOr(a_ref, b_ref, _) => {
            let a = convert_expr(smt_ctx, ctx, *a_ref, rename_sym);
            let b = convert_expr(smt_ctx, ctx, *b_ref, rename_sym);
            if let Some(1) = a_ref.get_type(ctx).get_bit_vector_width() {
                smt_ctx.or(a, b)
            } else {
                smt_ctx.bvor(a, b)
            }
        }
        Expr::BVXor(a_ref, b_ref, _) => {
            let a = convert_expr(smt_ctx, ctx, *a_ref, rename_sym);
            let b = convert_expr(smt_ctx, ctx, *b_ref, rename_sym);
            if let Some(1) = a_ref.get_type(ctx).get_bit_vector_width() {
                smt_ctx.xor(a, b)
            } else {
                smt_ctx.bvxor(a, b)
            }
        }
        Expr::BVShiftLeft(_, _, _) => todo!(),
        Expr::BVArithmeticShiftRight(_, _, _) => todo!(),
        Expr::BVShiftRight(_, _, _) => todo!(),
        Expr::BVAdd(a_ref, b_ref, _) => {
            convert_simple_binop(smt_ctx, ctx, "bvadd", a_ref, b_ref, rename_sym)
        }
        Expr::BVMul(a_ref, b_ref, _) => {
            convert_simple_binop(smt_ctx, ctx, "bvmul", a_ref, b_ref, rename_sym)
        }
        Expr::BVSignedDiv(_, _, _) => todo!(),
        Expr::BVUnsignedDiv(_, _, _) => todo!(),
        Expr::BVSignedMod(_, _, _) => todo!(),
        Expr::BVSignedRem(_, _, _) => todo!(),
        Expr::BVUnsignedRem(_, _, _) => todo!(),
        Expr::BVSub(a_ref, b_ref, _) => {
            convert_simple_binop(smt_ctx, ctx, "bvsub", a_ref, b_ref, rename_sym)
        }
        Expr::BVArrayRead { array, index, .. } => {
            let a = convert_expr(smt_ctx, ctx, *array, rename_sym);
            let i = convert_expr(smt_ctx, ctx, *index, rename_sym);
            smt_ctx.select(a, i)
        }
        Expr::BVIte { cond, tru, fals } => {
            let c = convert_expr(smt_ctx, ctx, *cond, rename_sym);
            let t = convert_expr(smt_ctx, ctx, *tru, rename_sym);
            let f = convert_expr(smt_ctx, ctx, *fals, rename_sym);
            smt_ctx.ite(c, t, f)
        }
        Expr::ArraySymbol { name, .. } => {
            let renamed = (rename_sym)(ctx.get(name));
            smt_ctx.atom(escape_smt_identifier(&renamed))
        }
        Expr::ArrayConstant { .. } => todo!(),
        Expr::ArrayEqual(_, _) => todo!(),
        Expr::ArrayStore { array, index, data } => {
            let a = convert_expr(smt_ctx, ctx, *array, rename_sym);
            let i = convert_expr(smt_ctx, ctx, *index, rename_sym);
            let d = convert_expr(smt_ctx, ctx, *data, rename_sym);
            smt_ctx.store(a, i, d)
        }
        Expr::ArrayIte { .. } => todo!(),
    }
}

fn convert_simple_binop<'a, 'f, F>(
    smt_ctx: &smt::Context,
    ctx: &'a ir::Context,
    op: &str,
    a_ref: &ExprRef,
    b_ref: &ExprRef,
    rename_sym: &F,
) -> smt::SExpr
where
    F: Fn(&'f str) -> Cow<'f, str>,
    'a: 'f,
{
    let a = ensure_bit_vec(
        smt_ctx,
        ctx,
        *a_ref,
        convert_expr(smt_ctx, ctx, *a_ref, rename_sym),
    );
    let b = ensure_bit_vec(
        smt_ctx,
        ctx,
        *b_ref,
        convert_expr(smt_ctx, ctx, *b_ref, rename_sym),
    );
    smt_ctx.list(vec![smt_ctx.atom(op), a, b])
}

// adds a cast if the underlying value is 1-bit and thus represented as a Bool in SMT
fn ensure_bit_vec(
    smt_ctx: &smt::Context,
    ctx: &ir::Context,
    e_ref: ExprRef,
    e: smt::SExpr,
) -> smt::SExpr {
    match e_ref.get_type(ctx) {
        Type::BV(width) => {
            if width == 1 {
                smt_ctx.ite(e, smt_ctx.binary(1, 1), smt_ctx.binary(1, 0))
            } else {
                e
            }
        }
        Type::Array(_) => panic!("This function should never be called on an array!"),
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
                    let body = self.expr_in_step(smt_ctx, value, 0);
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

    fn unroll(&mut self, smt_ctx: &mut smt::Context) -> Result<()> {
        let prev_step = self.current_step.unwrap();
        let next_step = prev_step + 1;

        // define next state
        for state in self.sys.states() {
            let name = self.name_at(state.symbol, next_step);
            let out = convert_tpe(smt_ctx, state.symbol.get_type(self.ctx));
            match state.next {
                Some(value) => {
                    let body = self.expr_in_step(smt_ctx, value, prev_step);
                    smt_ctx.define_const(escape_smt_identifier(&name), out, body)?;
                }
                None => {
                    smt_ctx.declare_const(escape_smt_identifier(&name), out)?;
                }
            }
        }

        // declare the inputs and all signals derived from the new state and inputs
        self.define_inputs_and_signals(smt_ctx, next_step)?;

        // update step count
        self.current_step = Some(next_step);
        Ok(())
    }
    fn get_at(&self, smt_ctx: &mut smt::Context, expr: ExprRef, k: u64) -> smt::SExpr {
        assert!(k <= self.current_step.unwrap_or(0));
        self.get_local_expr_symbol_at(smt_ctx, expr, k)
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
        let is_alpha = ac.is_ascii_uppercase() || ac.is_ascii_lowercase();
        let is_num = ac.is_ascii_digit();
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
        Cow::Borrowed(id)
    } else {
        let escaped = format!("|{}|", id);
        Cow::Owned(escaped)
    }
}

#[cfg(test)]
fn unescape_smt_identifier(id: &str) -> &str {
    if id.starts_with("|") {
        assert!(id.ends_with("|"));
        &id[1..id.len() - 1]
    } else {
        id
    }
}

trait PatronSmtHelpers {
    /// Zero extend a bit-vector.
    fn zext(&self, e: smt::SExpr, by: usize) -> smt::SExpr;

    /// Declare a constant array (non-standard but supported by many solvers)
    fn const_array(&self, tpe: smt::SExpr, default: smt::SExpr) -> smt::SExpr;
}

impl PatronSmtHelpers for smt::Context {
    fn zext(&self, e: smt::SExpr, by: usize) -> smt::SExpr {
        self.list(vec![
            self.list(vec![
                self.atoms().und,
                self.atom("zero_extend"),
                self.numeral(by),
            ]),
            e,
        ])
    }

    fn const_array(&self, tpe: smt::SExpr, default: smt::SExpr) -> smt::SExpr {
        self.list(vec![
            self.list(vec![self.atom("as"), self.atom("const"), tpe]),
            default,
        ])
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use easy_smt::*;

    #[test]
    fn easy_smt_symbol_escaping() {
        let ctx = ContextBuilder::new().build().unwrap();
        let test = ctx.atom("test");
        assert_eq!(ctx.display(test).to_string(), "test");
        // turns out easy_smt does not do any escaping!
        let needs_to_be_escaped_1 = ctx.atom("a b");
        assert_eq!(ctx.display(needs_to_be_escaped_1).to_string(), "a b");
    }

    #[test]
    fn test_our_escaping() {
        assert_eq!(
            unescape_smt_identifier(&escape_smt_identifier("a b")),
            "a b"
        );
    }

    #[test]
    fn test_parse_smt_array_const_and_store() {
        let ctx = ContextBuilder::new().build().unwrap();
        let data_width = 32usize;
        let index_width = 5usize;
        let default_value = 0b110011u64;
        let tpe = ctx.array_sort(
            ctx.bit_vec_sort(ctx.numeral(index_width)),
            ctx.bit_vec_sort(ctx.numeral(data_width)),
        );
        let default = ctx.binary(data_width, default_value);

        // check the base expression
        // ((as const (Array (_ BitVec 5) (_ BitVec 32))) #b00000000000000000000000000110011)
        let base = ctx.const_array(tpe, default);
        let base_val = parse_smt_array(&ctx, base).unwrap();
        assert_eq!(base_val.default, Some(BigUint::from(default_value)));

        // store
        // (store <base> #b01110 #x00000000)
        let store_index: usize = 14;
        let store_data: usize = 0;
        let store = ctx.store(
            base,
            ctx.binary(index_width, store_index),
            ctx.binary(data_width, store_data),
        );
        let store_val = parse_smt_array(&ctx, store).unwrap();
        assert_eq!(store_val.default, Some(BigUint::from(default_value)));
        assert_eq!(
            store_val.updates,
            vec![(BigUint::from(store_index), BigUint::from(store_data))]
        );

        // two stores
        // (store <store> #b01110 #x00000011)
        let store2_index: usize = 14;
        let store2_data: usize = 3;
        let store2 = ctx.store(
            store,
            ctx.binary(index_width, store2_index),
            ctx.binary(data_width, store2_data),
        );
        let store2_val = parse_smt_array(&ctx, store2).unwrap();
        assert_eq!(store2_val.default, Some(BigUint::from(default_value)));
        assert_eq!(
            store2_val.updates,
            vec![
                // should be overwritten
                (BigUint::from(store2_index), BigUint::from(store2_data))
            ]
        );
    }
}
