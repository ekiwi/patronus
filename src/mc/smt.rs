// Copyright 2023 The Regents of the University of California
// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::ir::*;
use crate::mc::types::InitValue;
use crate::mc::Witness;
use crate::smt::*;
use baa::*;
use easy_smt as smt;
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
            let value = match value {
                Value::Array(_) => unreachable!("should always be a bitvector!"),
                Value::BitVec(v) => v,
            };
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
            // convert to a witness value
            let wit_value = match value {
                Value::Array(v) => {
                    // TODO: narrow down the relevant indices
                    let indices = (0..v.num_elements())
                        .map(|ii| BitVecValue::from_u64(ii as u64, v.index_width()))
                        .collect::<Vec<_>>();
                    InitValue::Array(v, indices)
                }
                Value::BitVec(v) => InitValue::BitVec(v),
            };
            wit.init.push(wit_value);
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

// pops context for solver that do not support check assuming
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

pub fn get_smt_value(smt_ctx: &mut smt::Context, expr: smt::SExpr, tpe: Type) -> Result<Value> {
    let smt_value = smt_ctx.get_value(vec![expr])?[0].1;
    let res = if tpe.is_array() {
        Value::Array(parse_smt_array(smt_ctx, smt_value).unwrap())
    } else {
        Value::BitVec(parse_smt_bit_vec(smt_ctx, smt_value).unwrap())
    };
    Ok(res)
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
