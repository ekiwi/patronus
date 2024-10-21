// Copyright 2023 The Regents of the University of California
// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::ir::*;
use baa::*;

pub trait Simulator {
    type SnapshotId;

    /// Initializes all states and inputs to zero.
    fn init(&mut self);

    /// Recalculate signals.
    fn update(&mut self);

    /// Advance the state.
    fn step(&mut self);

    /// Change the value or an expression in the simulator.
    fn set<'a>(&mut self, expr: ExprRef, value: impl Into<BitVecValueRef<'a>>);

    /// Inspect the value of any bit vector expression in the circuit
    fn get(&self, expr: ExprRef) -> Option<BitVecValue>;

    /// Retrieve the value of an array element
    fn get_element<'a>(
        &self,
        expr: ExprRef,
        index: impl Into<BitVecValueRef<'a>>,
    ) -> Option<BitVecValue>;

    fn step_count(&self) -> u64;

    /// Takes a snapshot of the state (excluding inputs) and saves it internally.
    fn take_snapshot(&mut self) -> Self::SnapshotId;
    /// Restores a snapshot that was previously taken with the same simulator.
    fn restore_snapshot(&mut self, id: Self::SnapshotId);
}

/// Interpreter based simulator for a transition system.
pub struct Interpreter<'a> {
    ctx: &'a Context,
    sys: &'a TransitionSystem,
    step_count: u64,
    data: SymbolValueStore,
    snapshots: Vec<SymbolValueStore>,
    do_trace: bool,
}

impl<'a> Interpreter<'a> {
    pub fn new(ctx: &'a Context, sys: &'a TransitionSystem) -> Self {
        Self::internal_new(ctx, sys, false)
    }

    pub fn new_with_trace(ctx: &'a Context, sys: &'a TransitionSystem) -> Self {
        Self::internal_new(ctx, sys, true)
    }

    fn internal_new(ctx: &'a Context, sys: &'a TransitionSystem, do_trace: bool) -> Self {
        Self {
            ctx,
            sys,
            step_count: 0,
            data: Default::default(),
            snapshots: vec![],
            do_trace,
        }
    }
}

fn set_signal_to_zero(ctx: &Context, state: &mut SymbolValueStore, symbol: ExprRef) {
    let tpe = ctx.get(symbol).get_type(ctx);
    match tpe {
        Type::BV(bits) => {
            state.define_bv(symbol, &BitVecValue::zero(bits));
        }
        Type::Array(ArrayType {
            index_width,
            data_width,
        }) => {
            let value = ArrayValue::new_sparse(index_width, &BitVecValue::zero(data_width));
            state.define_array(symbol, value);
        }
    }
}

impl<'a> Simulator for Interpreter<'a> {
    type SnapshotId = u32;

    fn init(&mut self) {
        self.data.clear();

        // allocate space for inputs, and states
        for state in self.sys.states.iter() {
            set_signal_to_zero(self.ctx, &mut self.data, state.symbol);
        }
        for (symbol, _) in self.sys.get_signals(|s| s.is_input()) {
            set_signal_to_zero(self.ctx, &mut self.data, symbol);
        }

        // evaluate init expressions
        for state in self.sys.states.iter() {
            if let Some(init) = state.init {
                let value = eval_expr(self.ctx, &self.data, init);
                self.data.update(state.symbol, value);
            }
        }
    }

    fn update(&mut self) {
        // in this implementation, we calculate expressions on the fly, so there is nothing to update
    }

    fn step(&mut self) {
        // calculate all next states
        let next_states = self
            .sys
            .states
            .iter()
            .map(|s| s.next.map(|n| eval_expr(self.ctx, &self.data, n)))
            .collect::<Vec<_>>();

        // assign next value to store
        for (state, next_value) in self.sys.states.iter().zip(next_states.into_iter()) {
            if let Some(value) = next_value {
                self.data.update(state.symbol, value);
            }
        }

        // increment step cout
        self.step_count += 1;
    }

    fn set<'b>(&mut self, expr: ExprRef, value: impl Into<BitVecValueRef<'b>>) {
        self.data.update_bv(expr, value);
    }

    fn get(&self, expr: ExprRef) -> Option<BitVecValue> {
        if !self.ctx.get(expr).is_bv_type() {
            return None;
        }
        Some(eval_bv_expr(self.ctx, &self.data, expr))
    }

    fn get_element<'b>(
        &self,
        _expr: ExprRef,
        _index: impl Into<BitVecValueRef<'b>>,
    ) -> Option<BitVecValue> {
        todo!()
    }

    fn step_count(&self) -> u64 {
        self.step_count
    }

    fn take_snapshot(&mut self) -> Self::SnapshotId {
        let id = self.snapshots.len() as u32;
        self.snapshots.push(self.data.clone());
        id
    }

    fn restore_snapshot(&mut self, id: Self::SnapshotId) {
        self.data = self.snapshots[id as usize].clone();
    }
}
