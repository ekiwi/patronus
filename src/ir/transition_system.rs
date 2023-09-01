// Copyright 2023 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

use super::{Expr, ExprIntrospection, ExprRef, GetNode};

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub enum SignalKind {
    Node,
    Output,
    Bad,
    Constraint,
    Fair,
}

impl std::str::FromStr for SignalKind {
    type Err = ();

    fn from_str(kind: &str) -> Result<Self, Self::Err> {
        match kind {
            "node" => Ok(SignalKind::Node),
            "output" => Ok(SignalKind::Output),
            "bad" => Ok(SignalKind::Bad),
            "constraint" => Ok(SignalKind::Constraint),
            "fair" => Ok(SignalKind::Fair),
            _ => Err(()),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct Signal {
    pub name: Option<String>,
    pub expr: ExprRef,
    pub kind: SignalKind,
}
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub struct SignalRef(usize);

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct State {
    pub symbol: ExprRef,
    pub init: Option<ExprRef>,
    pub next: Option<ExprRef>,
}
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub struct StateRef(usize);

#[derive(Debug, PartialEq, Eq)]
pub struct TransitionSystem {
    pub name: String,
    pub(crate) states: Vec<State>,
    pub(crate) inputs: Vec<ExprRef>,
    pub(crate) signals: Vec<Signal>,
}

impl TransitionSystem {
    pub fn new(name: String) -> Self {
        TransitionSystem {
            name,
            states: Vec::default(),
            inputs: Vec::default(),
            signals: Vec::default(),
        }
    }

    pub fn add_signal(&mut self, expr: ExprRef, kind: SignalKind) -> SignalRef {
        let id = self.signals.len();
        self.signals.push(Signal {
            name: None,
            expr,
            kind,
        });
        SignalRef(id)
    }

    pub fn add_state(&mut self, ctx: &impl GetNode<Expr, ExprRef>, symbol: ExprRef) -> StateRef {
        assert!(symbol.is_symbol(ctx));
        let id = self.states.len();
        self.states.push(State {
            symbol,
            init: None,
            next: None,
        });
        StateRef(id)
    }

    pub fn modify_state<F>(&mut self, reference: StateRef, modify: F)
    where
        F: FnOnce(&mut State),
    {
        modify(self.states.get_mut(reference.0).unwrap())
    }
}

impl GetNode<Signal, SignalRef> for TransitionSystem {
    fn get(&self, reference: SignalRef) -> &Signal {
        &self.signals[reference.0]
    }
}

impl GetNode<State, StateRef> for TransitionSystem {
    fn get(&self, reference: StateRef) -> &State {
        &self.states[reference.0]
    }
}
