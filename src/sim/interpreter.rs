// Copyright 2023 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

use crate::ir::*;
use crate::sim::ValueStore;

pub trait Simulator {
    /// Advance the state.
    fn step(&mut self);
}

/// Interpreter based simulator for a transition system.
pub struct Interpreter<'a> {
    ctx: &'a Context,
    sys: &'a TransitionSystem,
    state: ValueStore,
}

impl<'a> Interpreter<'a> {
    pub fn new(ctx: &'a Context, sys: &'a TransitionSystem) -> Self {
        let types = sys.states().map(|s| s.symbol.get_type(ctx));
        let state = ValueStore::new(types);
        Self { ctx, sys, state }
    }
}

impl<'a> Simulator for Interpreter<'a> {
    fn step(&mut self) {
        todo!()
    }
}
