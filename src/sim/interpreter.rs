// Copyright 2023 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

use crate::ir::*;
use baa::*;
use rand::SeedableRng;
use std::fmt::Debug;

/// Specifies how to initialize states that do not have
#[derive(Debug, PartialEq, Copy, Clone)]
pub enum InitKind {
    Zero,
    Random(u64), // with seed
}

pub trait Simulator {
    type SnapshotId;

    /// Load the initial state values.
    fn init(&mut self, kind: InitKind);

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

impl<'a> Simulator for Interpreter<'a> {
    type SnapshotId = u32;

    fn init(&mut self, kind: InitKind) {
        assert!(matches!(kind, InitKind::Zero));
        self.state.clear();

        // allocate input state
    }

    fn update(&mut self) {
        todo!()
    }

    fn step(&mut self) {
        todo!()
    }

    fn set<'b>(&mut self, expr: ExprRef, value: impl Into<BitVecValueRef<'b>>) {
        todo!()
    }

    fn get(&self, expr: ExprRef) -> Option<BitVecValueRef<'_>> {
        todo!()
    }

    fn get_element<'b>(
        &self,
        expr: ExprRef,
        index: impl Into<BitVecValueRef<'b>>,
    ) -> Option<BitVecValueRef<'_>> {
        todo!()
    }

    fn step_count(&self) -> u64 {
        self.step_count
    }

    fn take_snapshot(&mut self) -> Self::SnapshotId {
        todo!()
    }

    fn restore_snapshot(&mut self, id: Self::SnapshotId) {
        todo!()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn type_size() {}
}
