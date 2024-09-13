// Copyright 2023 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

use crate::ir::*;
use crate::mc::{parse_big_uint_from_bit_string, Witness, WitnessArray, WitnessValue};
use baa::WidthInt;
use easy_smt as smt;
use num_bigint::BigUint;
use num_traits::{One, Zero};
use std::borrow::Cow;
use std::collections::HashSet;

#[derive(Debug, Clone, Copy)]
pub struct SmtSolverCmd {
    pub name: &'static str,
    pub args: &'static [&'static str],
    pub supports_uf: bool,
    pub supports_check_assuming: bool,
}

pub const BITWUZLA_CMD: SmtSolverCmd = SmtSolverCmd {
    name: "bitwuzla",
    args: &["--smt2", "--incremental"],
    supports_uf: false,
    supports_check_assuming: true,
};

pub const YICES2_CMD: SmtSolverCmd = SmtSolverCmd {
    name: "yices-smt2",
    args: &["--incremental"],
    supports_uf: false, // actually true, but ignoring for now
    supports_check_assuming: false,
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
        ctx: &mut Context,
        sys: &TransitionSystem,
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

        // TODO: maybe add support for the more compact SMT encoding
        let mut enc = UnrollSmtEncoding::new(ctx, sys, false);
        enc.define_header(&mut smt_ctx)?;
        enc.init_at(ctx, &mut smt_ctx, 0)?;

        let constraints = sys.constraints();
        let bad_states = sys.bad_states();

        for k in 0..=k_max {
            // assume all constraints hold in this step
            for (expr_ref, _) in constraints.iter() {
                let expr = enc.get_at(ctx, &mut smt_ctx, *expr_ref, k);
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
                    let expr = enc.get_at(ctx, &mut smt_ctx, *expr_ref, k);
                    let res = check_assuming(&mut smt_ctx, expr, &self.solver)?;

                    // count expression uses
                    let use_counts = count_expr_uses(ctx, sys);
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
                    check_assuming_end(&mut smt_ctx, &self.solver)?;
                }
            } else {
                let all_bads = bad_states
                    .iter()
                    .map(|(expr_ref, _)| enc.get_at(ctx, &mut smt_ctx, *expr_ref, k))
                    .collect::<Vec<_>>();
                let any_bad = smt_ctx.or_many(all_bads);
                let res = check_assuming(&mut smt_ctx, any_bad, &self.solver)?;

                // count expression uses
                let use_counts = count_expr_uses(ctx, sys);
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
                check_assuming_end(&mut smt_ctx, &self.solver)?;
            }

            // advance
            enc.unroll(ctx, &mut smt_ctx)?;
        }

        // we have not found any assertion violations
        Ok(ModelCheckResult::Success)
    }

    #[allow(clippy::too_many_arguments)]
    fn get_witness(
        &self,
        sys: &TransitionSystem,
        ctx: &Context,
        _use_counts: &[UseCountInt], // TODO: analyze array expressions in order to record which indices are accessed
        smt_ctx: &mut smt::Context,
        enc: &UnrollSmtEncoding,
        k_max: u64,
        bad_states: &[(ExprRef, SignalInfo)],
    ) -> Result<Witness> {
        let mut wit = Witness::default();

        // which bad states did we hit?
        for (bad_idx, (expr, _)) in bad_states.iter().enumerate() {
            let sym_at = enc.get_at(ctx, smt_ctx, *expr, k_max);
            let value = get_smt_value(smt_ctx, sym_at, expr.get_type(ctx))?;
            if !value.is_zero() {
                // was the bad state condition fulfilled?
                wit.failed_safety.push(bad_idx as u32);
            }
        }

        // collect initial values
        for (state_cnt, (_, state)) in sys.states().enumerate() {
            let sym_at = enc.get_at(ctx, smt_ctx, state.symbol, 0);
            let value = get_smt_value(smt_ctx, sym_at, state.symbol.get_type(ctx))?;
            // we assume that state ids are monotonically increasing with +1
            assert_eq!(wit.init.len(), state_cnt);
            wit.init.push(Some(value));
            // also save state name
            wit.init_names
                .push(Some(state.symbol.get_symbol_name(ctx).unwrap().to_string()))
        }

        // collect all inputs
        let inputs = sys.get_signals(|s| s.kind == SignalKind::Input);

        // save input names
        for (input, _) in inputs.iter() {
            wit.input_names
                .push(Some(input.get_symbol_name(ctx).unwrap().to_string()));
        }

        for k in 0..=k_max {
            let mut input_values = Vec::default();
            for (input, _) in inputs.iter() {
                let sym_at = enc.get_at(ctx, smt_ctx, *input, k);
                let value = get_smt_value(smt_ctx, sym_at, input.get_type(ctx))?;
                input_values.push(Some(value));
            }
            wit.inputs.push(input_values);
        }

        // TODO: get rid of default values in a more intelligent fashion,
        //       e.g., by recording which indices are accessed
        for init in wit.init.iter_mut() {
            if let Some(WitnessValue::Array(a)) = init.as_mut() {
                a.default = None;
            }
        }

        Ok(wit)
    }
}

#[inline]
pub fn check_assuming(
    smt_ctx: &mut smt::Context,
    assumption: smt::SExpr,
    solver: &SmtSolverCmd,
) -> std::io::Result<smt::Response> {
    if solver.supports_check_assuming {
        smt_ctx.check_assuming([assumption])
    } else {
        smt_ctx.push_many(1)?; // add new assertion
        smt_ctx.assert(assumption)?;
        let res = smt_ctx.check()?;
        Ok(res)
    }
}

// pops context for solver that do not not support check assuming
#[inline]
pub fn check_assuming_end(
    smt_ctx: &mut smt::Context,
    solver: &SmtSolverCmd,
) -> std::io::Result<()> {
    if !solver.supports_check_assuming {
        smt_ctx.pop_many(1)
    } else {
        Ok(())
    }
}

pub fn get_smt_value(
    smt_ctx: &mut smt::Context,
    expr: smt::SExpr,
    tpe: Type,
) -> Result<WitnessValue> {
    let smt_value = smt_ctx.get_value(vec![expr])?[0].1;
    let res = if tpe.is_array() {
        WitnessValue::Array(parse_smt_array(smt_ctx, smt_value).unwrap())
    } else {
        let (value, width) = parse_smt_bit_vec(smt_ctx, smt_value).unwrap();
        WitnessValue::Scalar(value, width)
    };
    Ok(res)
}

fn parse_smt_bit_vec(smt_ctx: &smt::Context, expr: smt::SExpr) -> Option<(BigUint, WidthInt)> {
    let data = smt_ctx.get(expr);
    match data {
        smt::SExprData::Atom(value) => Some(smt_bit_vec_str_to_value(value)),
        // unwraps expressions like: ((a true))
        smt::SExprData::List([inner]) => parse_smt_bit_vec(smt_ctx, *inner),
        // unwraps expressions like: (a true)
        smt::SExprData::List([_, value]) => parse_smt_bit_vec(smt_ctx, *value),
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
    fn init_at(&mut self, ctx: &mut Context, smt_ctx: &mut smt::Context, step: u64) -> Result<()>;
    fn unroll(&mut self, ctx: &mut Context, smt_ctx: &mut smt::Context) -> Result<()>;
    /// Allows access to inputs, states, constraints and bad_state expressions.
    fn get_at(
        &self,
        ctx: &Context,
        smt_ctx: &mut smt::Context,
        expr: ExprRef,
        k: u64,
    ) -> smt::SExpr;
}

pub struct UnrollSmtEncoding {
    /// the offset at which our encoding was initialized
    offset: Option<u64>,
    current_step: Option<u64>,
    /// all signals that need to be serialized separately, in the correct order
    signal_order: Vec<ExprRef>,
    /// look up table to see if an expression is a reference
    signals: Vec<Option<SmtSignalInfo>>,
    /// system states
    states: Vec<State>,
    /// symbols of signals at every step
    symbols_at: Vec<Vec<ExprRef>>,
}

#[derive(Clone)]
struct SmtSignalInfo {
    /// monotonically increasing unique id
    id: u16,
    name: StringRef,
    uses: Uses,
    is_state: bool,
    is_input: bool,
    /// denotes states that do not change and thus can be represented by a single symbol
    is_const: bool,
}

impl UnrollSmtEncoding {
    pub fn new(ctx: &mut Context, sys: &TransitionSystem, include_outputs: bool) -> Self {
        let ser_info = analyze_for_serialization(ctx, sys, include_outputs);
        let max_ser_index = ser_info
            .signal_order
            .iter()
            .map(|s| s.expr.index())
            .max()
            .unwrap_or_default();
        let max_state_index = sys
            .states()
            .map(|(_, s)| s.symbol.index())
            .max()
            .unwrap_or_default();
        let signals_map_len = std::cmp::max(max_ser_index, max_state_index) + 1;
        let mut signals = vec![None; signals_map_len];
        let mut signal_order = Vec::with_capacity(ser_info.signal_order.len());

        let is_state: HashSet<ExprRef> = HashSet::from_iter(sys.states().map(|(_, s)| s.symbol));

        // we skip states in our signal order since they are not calculated directly in the update function
        for (id, root) in ser_info
            .signal_order
            .into_iter()
            .filter(|r| !is_state.contains(&r.expr))
            .enumerate()
        {
            signal_order.push(root.expr);
            let name = sys.get_signal(root.expr).and_then(|i| i.name).unwrap_or({
                let default_name = format!("__n{}", root.expr.index());
                ctx.string(default_name.into())
            });
            let is_input = sys
                .get_signal(root.expr)
                .map(|i| i.kind == SignalKind::Input)
                .unwrap_or(false);
            let info = SmtSignalInfo {
                id: id as u16,
                name,
                uses: root.uses,
                is_state: false,
                is_input,
                is_const: false,
            };
            signals[root.expr.index()] = Some(info);
        }
        for (id, state) in sys.states() {
            let id = (id.to_index() + signal_order.len()) as u16;
            let info = SmtSignalInfo {
                id,
                name: state.symbol.get_symbol_name_ref(ctx).unwrap(),
                uses: Uses::default(), // irrelevant
                is_state: true,
                is_input: false,
                is_const: state.is_const(),
            };
            signals[state.symbol.index()] = Some(info);
        }
        let current_step = None;
        let offset = None;
        let states = sys.states.clone();

        Self {
            offset,
            current_step,
            signals,
            signal_order,
            states,
            symbols_at: Vec::new(),
        }
    }

    fn define_signals(
        &self,
        ctx: &mut Context,
        smt_ctx: &mut smt::Context,
        step: u64,
        filter: &impl Fn(&SmtSignalInfo) -> bool,
    ) -> Result<()> {
        for expr in self.signal_order.iter() {
            let info = self.signals[expr.index()].as_ref().unwrap();
            if info.is_state {
                continue;
            }
            let skip = !(filter)(info);
            if !skip {
                let tpe = convert_tpe(smt_ctx, expr.get_type(ctx));
                let name = name_at(ctx.get_str(info.name), step);
                if expr.is_symbol(ctx) {
                    smt_ctx.declare_const(escape_smt_identifier(&name), tpe)?;
                } else {
                    let value = self.expr_in_step(ctx, smt_ctx, *expr, step);
                    smt_ctx.define_const(escape_smt_identifier(&name), tpe, value)?;
                }
            }
        }
        Ok(())
    }

    fn create_signal_symbols_in_step(&mut self, ctx: &mut Context, step: u64) {
        let offset = self.offset.expect("Need to call init_at first!");
        let index = (step - offset) as usize;
        assert_eq!(self.symbols_at.len(), index, "Missing or duplicate step!");
        let mut syms = Vec::with_capacity(self.signal_order.len());
        for signal in self
            .signal_order
            .iter()
            .chain(self.states.iter().map(|s| &s.symbol))
        {
            let info = self.signals[signal.index()].as_ref().unwrap();
            let name_ref = if info.is_const {
                info.name
            } else {
                let name = name_at(ctx.get_str(info.name), step);
                ctx.string(name.into())
            };
            let tpe = signal.get_type(ctx);
            debug_assert_eq!(info.id as usize, syms.len());
            syms.push(ctx.symbol(name_ref, tpe));
        }
        self.symbols_at.push(syms);
    }

    fn signal_sym_in_step(&self, expr: ExprRef, step: u64) -> Option<ExprRef> {
        if let Some(Some(info)) = self.signals.get(expr.index()) {
            let offset = self.offset.expect("Need to call init_at first!");
            let index = (step - offset) as usize;
            Some(self.symbols_at[index][info.id as usize])
        } else {
            None
        }
    }

    fn expr_in_step(
        &self,
        ctx: &Context,
        smt_ctx: &mut smt::Context,
        expr: ExprRef,
        step: u64,
    ) -> smt::SExpr {
        let expr_is_symbol = ctx.get(expr).is_symbol();
        let patch = |e: &ExprRef| -> Option<ExprRef> {
            // If the expression we are trying to serialize is not a symbol, then wo
            // do not just want to replace it with one, as that would lead us to a tautology!
            if !expr_is_symbol && *e == expr {
                None
            } else {
                self.signal_sym_in_step(*e, step)
            }
        };
        convert_expr(smt_ctx, ctx, expr, &patch)
    }
}

impl TransitionSystemEncoding for UnrollSmtEncoding {
    fn define_header(&self, _smt_ctx: &mut smt::Context) -> Result<()> {
        // nothing to do in this encoding
        Ok(())
    }

    fn init_at(&mut self, ctx: &mut Context, smt_ctx: &mut smt::Context, step: u64) -> Result<()> {
        // delete old mutable state
        self.symbols_at.clear();
        // remember current step and starting offset
        self.current_step = Some(step);
        self.offset = Some(step);
        self.create_signal_symbols_in_step(ctx, step);

        if step == 0 {
            // define signals that are used to calculate init expressions
            self.define_signals(ctx, smt_ctx, 0, &|info: &SmtSignalInfo| info.uses.init)?;
        }

        // declare/define initial states
        for state in self.states.iter() {
            let base_name = state.symbol.get_symbol_name(ctx).unwrap();
            let name = if state.is_const() {
                base_name.to_string()
            } else {
                name_at(base_name, step)
            };
            let out = convert_tpe(smt_ctx, state.symbol.get_type(ctx));
            match (step, state.init) {
                (0, Some(value)) => {
                    let body = self.expr_in_step(ctx, smt_ctx, value, step);
                    smt_ctx.define_const(escape_smt_identifier(&name), out, body)?;
                }
                _ => {
                    smt_ctx.declare_const(escape_smt_identifier(&name), out)?;
                }
            }
        }

        // define other signals including inputs
        if step == 0 {
            self.define_signals(ctx, smt_ctx, step, &|info: &SmtSignalInfo| {
                (info.uses.other || info.is_input) && !info.uses.init
            })?;
        } else {
            self.define_signals(ctx, smt_ctx, step, &|info: &SmtSignalInfo| {
                info.uses.other || info.is_input
            })?;
        }

        Ok(())
    }

    fn unroll(&mut self, ctx: &mut Context, smt_ctx: &mut smt::Context) -> Result<()> {
        let prev_step = self.current_step.unwrap();
        let next_step = prev_step + 1;
        self.create_signal_symbols_in_step(ctx, next_step);

        // define next state signals for previous state
        self.define_signals(ctx, smt_ctx, prev_step, &|info: &SmtSignalInfo| {
            info.uses.next && !info.uses.other && !info.is_input
        })?;

        // define next state
        for state in self.states.iter() {
            let name = name_at(state.symbol.get_symbol_name(ctx).unwrap(), next_step);
            let out = convert_tpe(smt_ctx, state.symbol.get_type(ctx));
            match state.next {
                Some(value) => {
                    let is_const = value == state.symbol;
                    // constant states never change from their initial value
                    if !is_const {
                        let body = self.expr_in_step(ctx, smt_ctx, value, prev_step);
                        smt_ctx.define_const(escape_smt_identifier(&name), out, body)?;
                    }
                }
                None => {
                    smt_ctx.declare_const(escape_smt_identifier(&name), out)?;
                }
            }
        }

        // define other signals and inputs
        // we always define all inputs, even if they are only used in the "next" expression
        // since our witness extraction relies on them being available
        self.define_signals(ctx, smt_ctx, next_step, &|info: &SmtSignalInfo| {
            info.uses.other || info.is_input
        })?;

        // update step count
        self.current_step = Some(next_step);
        Ok(())
    }

    fn get_at(
        &self,
        ctx: &Context,
        smt_ctx: &mut smt::Context,
        expr: ExprRef,
        step: u64,
    ) -> smt::SExpr {
        assert!(step <= self.current_step.unwrap_or(0));
        let sym = self.signal_sym_in_step(expr, step).unwrap();
        convert_expr(smt_ctx, ctx, sym, &|_| None)
    }
}

fn name_at(name: &str, step: u64) -> String {
    format!("{}@{}", name, step)
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

fn convert_expr(
    smt_ctx: &smt::Context,
    ctx: &Context,
    expr_ref_in: ExprRef,
    patch_expr: &impl Fn(&ExprRef) -> Option<ExprRef>,
) -> smt::SExpr {
    // replace expressions on the flow (generally in order to inject a symbol or change a symbol name)
    let expr_ref = match (patch_expr)(&expr_ref_in) {
        Some(patched) => patched,
        None => expr_ref_in,
    };

    match ctx.get(expr_ref) {
        Expr::BVSymbol { name, .. } => {
            let name_str = ctx.get_str(*name);
            smt_ctx.atom(escape_smt_identifier(name_str))
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
            let e_expr = convert_expr(smt_ctx, ctx, *e, patch_expr);
            match e.get_type(ctx) {
                Type::BV(width) => {
                    let inner_ite_encoding = false;
                    if width == 1 {
                        if inner_ite_encoding {
                            // this encoding sticks an ite into the zext
                            let inner =
                                smt_ctx.ite(e_expr, smt_ctx.binary(1, 1), smt_ctx.binary(0, 0));
                            smt_ctx.zext(inner, *by as usize)
                        } else {
                            // this encoding avoids the zext by using an ite on the expanded true/false case
                            let res_size = (by + 1) as usize;
                            // in the one bit case, the underlying expression is represented as a Bool in SMT
                            smt_ctx.ite(
                                e_expr,
                                smt_ctx.binary(res_size, 1),
                                smt_ctx.binary(res_size, 0),
                            )
                        }
                    } else {
                        smt_ctx.zext(e_expr, *by as usize)
                    }
                }
                Type::Array(_) => {
                    panic!("Mall-formed expression: zext should never be applied to an array!")
                }
            }
        }
        Expr::BVSignExt { e, by, .. } => {
            let e_expr = convert_expr(smt_ctx, ctx, *e, patch_expr);
            match e.get_type(ctx) {
                Type::BV(width) => {
                    if width == 1 {
                        let inner = smt_ctx.ite(e_expr, smt_ctx.binary(1, 1), smt_ctx.binary(0, 0));
                        smt_ctx.sext(inner, *by as usize)
                    } else {
                        smt_ctx.sext(e_expr, *by as usize)
                    }
                }
                Type::Array(_) => {
                    panic!("Mall-formed expression: sext should never be applied to an array!")
                }
            }
        }
        Expr::BVSlice { e, hi, lo } => {
            let e_expr = convert_expr(smt_ctx, ctx, *e, patch_expr);
            // skip no-op bit extracts (this helps us avoid slices on boolean values)
            if *lo == 0 && e.get_type(ctx).get_bit_vector_width().unwrap() - 1 == *hi {
                e_expr
            } else {
                let extracted = smt_ctx.extract(*hi as i32, *lo as i32, e_expr);
                if hi > lo {
                    // result width is at least two
                    extracted
                } else {
                    // result width is one => we need to convert to bool
                    to_bool(smt_ctx, extracted)
                }
            }
        }
        Expr::BVNot(e_ref, _) => {
            let e = convert_expr(smt_ctx, ctx, *e_ref, patch_expr);
            if e_ref.get_type(ctx).is_bool() {
                smt_ctx.not(e)
            } else {
                smt_ctx.bvnot(e)
            }
        }
        Expr::BVNegate(e_ref, _) => {
            let e = ensure_bit_vec(
                smt_ctx,
                ctx,
                *e_ref,
                convert_expr(smt_ctx, ctx, *e_ref, patch_expr),
            );
            smt_ctx.bvneg(e)
        }
        Expr::BVEqual(a_ref, b_ref) => {
            let a = convert_expr(smt_ctx, ctx, *a_ref, patch_expr);
            let b = convert_expr(smt_ctx, ctx, *b_ref, patch_expr);
            smt_ctx.eq(a, b)
        }
        Expr::BVImplies(a_ref, b_ref) => {
            assert!(a_ref.get_type(ctx).is_bool());
            let a = convert_expr(smt_ctx, ctx, *a_ref, patch_expr);
            let b = convert_expr(smt_ctx, ctx, *b_ref, patch_expr);
            smt_ctx.imp(a, b)
        }
        Expr::BVGreater(a_ref, b_ref) => {
            convert_simple_binop(true, smt_ctx, ctx, "bvugt", a_ref, b_ref, patch_expr)
        }
        Expr::BVGreaterSigned(a_ref, b_ref, _) => {
            convert_simple_binop(true, smt_ctx, ctx, "bvsgt", a_ref, b_ref, patch_expr)
        }
        Expr::BVGreaterEqual(a_ref, b_ref) => {
            convert_simple_binop(true, smt_ctx, ctx, "bvuge", a_ref, b_ref, patch_expr)
        }
        Expr::BVGreaterEqualSigned(a_ref, b_ref, _) => {
            convert_simple_binop(true, smt_ctx, ctx, "bvsge", a_ref, b_ref, patch_expr)
        }
        Expr::BVConcat(a_ref, b_ref, _) => {
            convert_simple_binop(true, smt_ctx, ctx, "concat", a_ref, b_ref, patch_expr)
        }
        Expr::BVAnd(a_ref, b_ref, _) => {
            let a = convert_expr(smt_ctx, ctx, *a_ref, patch_expr);
            let b = convert_expr(smt_ctx, ctx, *b_ref, patch_expr);
            if let Some(1) = a_ref.get_type(ctx).get_bit_vector_width() {
                smt_ctx.and(a, b)
            } else {
                smt_ctx.bvand(a, b)
            }
        }
        Expr::BVOr(a_ref, b_ref, _) => {
            let a = convert_expr(smt_ctx, ctx, *a_ref, patch_expr);
            let b = convert_expr(smt_ctx, ctx, *b_ref, patch_expr);
            if let Some(1) = a_ref.get_type(ctx).get_bit_vector_width() {
                smt_ctx.or(a, b)
            } else {
                smt_ctx.bvor(a, b)
            }
        }
        Expr::BVXor(a_ref, b_ref, _) => {
            let a = convert_expr(smt_ctx, ctx, *a_ref, patch_expr);
            let b = convert_expr(smt_ctx, ctx, *b_ref, patch_expr);
            if let Some(1) = a_ref.get_type(ctx).get_bit_vector_width() {
                smt_ctx.xor(a, b)
            } else {
                smt_ctx.bvxor(a, b)
            }
        }
        Expr::BVShiftLeft(a_ref, b_ref, _) => {
            convert_simple_binop(false, smt_ctx, ctx, "bvshl", a_ref, b_ref, patch_expr)
        }
        Expr::BVArithmeticShiftRight(a_ref, b_ref, _) => {
            convert_simple_binop(false, smt_ctx, ctx, "bvashr", a_ref, b_ref, patch_expr)
        }
        Expr::BVShiftRight(a_ref, b_ref, _) => {
            convert_simple_binop(false, smt_ctx, ctx, "bvlshr", a_ref, b_ref, patch_expr)
        }
        Expr::BVAdd(a_ref, b_ref, _) => {
            convert_simple_binop(false, smt_ctx, ctx, "bvadd", a_ref, b_ref, patch_expr)
        }
        Expr::BVMul(a_ref, b_ref, _) => {
            convert_simple_binop(false, smt_ctx, ctx, "bvmul", a_ref, b_ref, patch_expr)
        }
        Expr::BVSignedDiv(a_ref, b_ref, _) => {
            convert_simple_binop(false, smt_ctx, ctx, "bvsdiv", a_ref, b_ref, patch_expr)
        }
        Expr::BVUnsignedDiv(a_ref, b_ref, _) => {
            convert_simple_binop(false, smt_ctx, ctx, "bvudiv", a_ref, b_ref, patch_expr)
        }
        Expr::BVSignedMod(a_ref, b_ref, _) => {
            convert_simple_binop(false, smt_ctx, ctx, "bvsmod", a_ref, b_ref, patch_expr)
        }
        Expr::BVSignedRem(a_ref, b_ref, _) => {
            convert_simple_binop(false, smt_ctx, ctx, "bvsrem", a_ref, b_ref, patch_expr)
        }
        Expr::BVUnsignedRem(a_ref, b_ref, _) => {
            convert_simple_binop(false, smt_ctx, ctx, "bvurem", a_ref, b_ref, patch_expr)
        }
        Expr::BVSub(a_ref, b_ref, _) => {
            convert_simple_binop(false, smt_ctx, ctx, "bvsub", a_ref, b_ref, patch_expr)
        }
        Expr::BVArrayRead { array, index, .. } => {
            let a = convert_expr(smt_ctx, ctx, *array, patch_expr);
            let i = convert_expr(smt_ctx, ctx, *index, patch_expr);
            smt_ctx.select(a, i)
        }
        Expr::BVIte { cond, tru, fals } => {
            let c = convert_expr(smt_ctx, ctx, *cond, patch_expr);
            let t = convert_expr(smt_ctx, ctx, *tru, patch_expr);
            let f = convert_expr(smt_ctx, ctx, *fals, patch_expr);
            smt_ctx.ite(c, t, f)
        }
        Expr::ArraySymbol { name, .. } => smt_ctx.atom(escape_smt_identifier(ctx.get_str(*name))),
        Expr::ArrayConstant {
            e,
            index_width,
            data_width,
        } => {
            let e_expr = convert_expr(smt_ctx, ctx, *e, patch_expr);
            let tpe = smt_ctx.array_sort(
                smt_ctx.bit_vec_sort(smt_ctx.numeral(*index_width)),
                smt_ctx.bit_vec_sort(smt_ctx.numeral(*data_width)),
            );
            smt_ctx.const_array(tpe, e_expr)
        }
        Expr::ArrayEqual(a_ref, b_ref) => {
            let a = convert_expr(smt_ctx, ctx, *a_ref, patch_expr);
            let b = convert_expr(smt_ctx, ctx, *b_ref, patch_expr);
            smt_ctx.eq(a, b)
        }
        Expr::ArrayStore { array, index, data } => {
            let a = convert_expr(smt_ctx, ctx, *array, patch_expr);
            let i = convert_expr(smt_ctx, ctx, *index, patch_expr);
            let d = convert_expr(smt_ctx, ctx, *data, patch_expr);
            smt_ctx.store(a, i, d)
        }
        Expr::ArrayIte { cond, tru, fals } => {
            let c = convert_expr(smt_ctx, ctx, *cond, patch_expr);
            let t = convert_expr(smt_ctx, ctx, *tru, patch_expr);
            let f = convert_expr(smt_ctx, ctx, *fals, patch_expr);
            smt_ctx.ite(c, t, f)
        }
    }
}

/// for all bin ops that require a conversion to bit-vec from bool
fn convert_simple_binop(
    do_not_convert_to_bool: bool,
    smt_ctx: &smt::Context,
    ctx: &Context,
    op: &str,
    a_ref: &ExprRef,
    b_ref: &ExprRef,
    patch_expr: &impl Fn(&ExprRef) -> Option<ExprRef>,
) -> smt::SExpr {
    let a = ensure_bit_vec(
        smt_ctx,
        ctx,
        *a_ref,
        convert_expr(smt_ctx, ctx, *a_ref, patch_expr),
    );
    let b = ensure_bit_vec(
        smt_ctx,
        ctx,
        *b_ref,
        convert_expr(smt_ctx, ctx, *b_ref, patch_expr),
    );
    let res = smt_ctx.list(vec![smt_ctx.atom(op), a, b]);
    if !do_not_convert_to_bool && a_ref.get_bv_type(ctx).unwrap() == 1 {
        to_bool(smt_ctx, res)
    } else {
        res
    }
}

// adds a cast if the underlying value is 1-bit and thus represented as a Bool in SMT
fn ensure_bit_vec(
    smt_ctx: &smt::Context,
    ctx: &Context,
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

fn to_bool(smt_ctx: &smt::Context, e: smt::SExpr) -> smt::SExpr {
    smt_ctx.eq(e, smt_ctx.binary(1, 1))
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

    /// Sign extend a bit-vector.
    fn sext(&self, e: smt::SExpr, by: usize) -> smt::SExpr;

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

    fn sext(&self, e: smt::SExpr, by: usize) -> smt::SExpr {
        self.list(vec![
            self.list(vec![
                self.atoms().und,
                self.atom("sign_extend"),
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

    #[test]
    fn test_yices2_result_parsing() {
        // yices will produce responses like this for a `get-value` call:
        // ((n9@0 true))
        let ctx = ContextBuilder::new().build().unwrap();
        let r0 = ctx.list(vec![ctx.list(vec![ctx.atom("n9@0"), ctx.true_()])]);
        let (val0, width0) = parse_smt_bit_vec(&ctx, r0).unwrap();
        assert_eq!(val0, BigUint::from(1u8));
        assert_eq!(width0, 1);
    }
}
