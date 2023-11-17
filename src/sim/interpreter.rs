// Copyright 2023 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

use crate::ir::*;
use crate::sim::{Value, ValueStore};

/// Specifies how to initialize states that do not have
#[derive(Debug, PartialEq, Copy, Clone)]
pub enum InitKind {
    Zero,
    Random,
}

pub trait Simulator {
    /// Load the initial state values.
    fn init(&mut self, kind: InitKind);

    /// Advance the state.
    fn step(&mut self);

    /// Change the value of an input
    fn set_input(&mut self, input_id: usize, value: Value);
}

/// Interpreter based simulator for a transition system.
pub struct Interpreter<'a> {
    ctx: &'a Context,
    sys: &'a TransitionSystem,
    state: ValueStore,
    meta: Vec<InterpreterMetaData>,
}

/// Meta data for each expression.
#[derive(Debug, Clone, Copy)]
struct InterpreterMetaData {}

impl Default for InterpreterMetaData {
    fn default() -> Self {
        Self {}
    }
}

impl<'a> Interpreter<'a> {
    pub fn new(ctx: &'a Context, sys: &'a TransitionSystem) -> Self {
        let use_counts = count_expr_uses(ctx, sys);
        let types = sys.states().map(|s| s.symbol.get_type(ctx));
        let state = ValueStore::new(types);
        let mut meta = Vec::with_capacity(use_counts.len());
        meta.resize(use_counts.len(), InterpreterMetaData::default());
        Self {
            ctx,
            sys,
            state,
            meta,
        }
    }
}

impl<'a> Simulator for Interpreter<'a> {
    fn init(&mut self, kind: InitKind) {
        todo!()
    }

    fn step(&mut self) {
        todo!()
    }

    fn set_input(&mut self, input_id: usize, value: Value) {
        todo!()
    }
}
