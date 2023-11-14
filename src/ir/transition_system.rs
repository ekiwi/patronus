// Copyright 2023 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

use super::{Expr, ExprIntrospection, ExprRef, GetNode};
use crate::ir::StringRef;

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub enum SignalKind {
    Node,
    Output,
    Bad,
    Constraint,
    Fair,
    Input,
    State,
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
pub struct SignalInfo {
    pub name: Option<StringRef>,
    pub kind: SignalKind,
}

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct State {
    pub symbol: ExprRef,
    pub init: Option<ExprRef>,
    pub next: Option<ExprRef>,
}
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub struct StateRef(usize);

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub struct InputRef(usize);

#[derive(Debug, PartialEq, Eq)]
pub struct TransitionSystem {
    pub name: String,
    pub(crate) states: Vec<State>,
    /// signal meta-data stored in a dense hash map, matching the index of the corresponding expression
    pub(crate) signals: Vec<Option<SignalInfo>>,
}

impl TransitionSystem {
    pub fn new(name: String) -> Self {
        TransitionSystem {
            name,
            states: Vec::default(),
            signals: Vec::default(),
        }
    }

    pub fn add_signal(&mut self, expr: ExprRef, kind: SignalKind, name: Option<StringRef>) {
        let id = expr.index();
        if self.signals.len() <= id {
            self.signals.resize(id + 1, None);
        }
        self.signals[id] = Some(SignalInfo { name, kind });
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

impl GetNode<SignalInfo, ExprRef> for TransitionSystem {
    fn get(&self, reference: ExprRef) -> &SignalInfo {
        self.signals[reference.index()].as_ref().unwrap()
    }
}

impl GetNode<State, StateRef> for TransitionSystem {
    fn get(&self, reference: StateRef) -> &State {
        &self.states[reference.0]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ir_type_size() {
        // Simple C-like enum
        assert_eq!(std::mem::size_of::<SignalKind>(), 1);
        // Optional name (saved as a string ref) + SignalKind
        assert_eq!(std::mem::size_of::<SignalInfo>(), 4);
        // the option type can use unused byt
        assert_eq!(std::mem::size_of::<Option<SignalInfo>>(), 4);
    }
}
