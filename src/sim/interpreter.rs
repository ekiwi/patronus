// Copyright 2023 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

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

    /// Change the value or an expression in the simulator. Be careful!
    fn set<'a>(&mut self, expr: ExprRef, value: impl Into<BitVecValueRef<'a>>);

    fn get(&self, expr: ExprRef) -> Option<BitVecValueRef<'_>>;

    /// Retrieve the value of an array element
    fn get_element<'a>(
        &self,
        expr: ExprRef,
        index: impl Into<BitVecValueRef<'a>>,
    ) -> Option<BitVecValueRef<'_>>;

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
    state: SymbolValueStore,
    snapshots: Vec<Vec<Word>>,
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
            state: Default::default(),
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
        self.state.clear();

        // allocate space for inputs, and states
        for (_, state) in self.sys.states() {
            set_signal_to_zero(self.ctx, &mut self.state, state.symbol);
            if state.init.is_some() {
                todo!("deal with init expressions!");
            }
        }
        for (symbol, _) in self.sys.get_signals(|s| s.is_input()) {
            set_signal_to_zero(self.ctx, &mut self.state, symbol);
        }
    }

    fn update(&mut self) {
        // in this implementation, we calculate expressions on the fly, so there is nothing to update
    }

    fn step(&mut self) {
        // calculate all next states and then

        // assign next state to current state
        todo!()
    }

    fn set<'b>(&mut self, expr: ExprRef, value: impl Into<BitVecValueRef<'b>>) {}

    fn get(&self, _expr: ExprRef) -> Option<BitVecValueRef<'_>> {
        todo!()
    }

    fn get_element<'b>(
        &self,
        _expr: ExprRef,
        _index: impl Into<BitVecValueRef<'b>>,
    ) -> Option<BitVecValueRef<'_>> {
        todo!()
    }

    fn step_count(&self) -> u64 {
        self.step_count
    }

    fn take_snapshot(&mut self) -> Self::SnapshotId {
        todo!()
    }

    fn restore_snapshot(&mut self, _id: Self::SnapshotId) {
        todo!()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn type_size() {}
}
