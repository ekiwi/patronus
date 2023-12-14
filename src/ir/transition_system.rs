// Copyright 2023 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

use super::{Context, Expr, ExprRef, GetNode, StringRef};
use std::collections::HashMap;
use std::fmt::{Display, Formatter};

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub enum SignalKind {
    Node,
    Output,
    Bad,
    Constraint,
    Fair,
    Input,
    State,
}

impl SignalKind {
    #[inline]
    pub fn to_string(&self) -> &'static str {
        match &self {
            SignalKind::Node => "node",
            SignalKind::Output => "output",
            SignalKind::Bad => "bad",
            SignalKind::Constraint => "constraint",
            SignalKind::Fair => "fair",
            SignalKind::Input => "input",
            SignalKind::State => "state",
        }
    }
}

impl Display for SignalKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.to_string())
    }
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

impl State {
    pub fn is_const(&self) -> bool {
        self.next.map(|n| n == self.symbol).unwrap_or(false)
    }
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
    signals: Vec<Option<SignalInfo>>,
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

    pub fn get_signal(&self, expr: ExprRef) -> Option<&SignalInfo> {
        let entry = self.signals.get(expr.index())?;
        entry.as_ref()
    }

    pub fn remove_signal(&mut self, expr: ExprRef) {
        *self
            .signals
            .get_mut(expr.index())
            .expect("trying to remove non-existing signal") = None;
    }

    pub fn update_signal_expr(&mut self, old: ExprRef, new: ExprRef) {
        if old != new {
            if let Some(old_info) = &self.signals[old.index()] {
                let cloned = old_info.clone();
                let new_id = new.index();
                if self.signals.len() <= new_id {
                    self.signals.resize(new_id + 1, None);
                }
                let merged = if let Some(new_info) = &self.signals[new_id] {
                    merge_signal_info(&cloned, new_info)
                } else {
                    cloned
                };
                self.signals[new_id] = Some(merged);
                self.signals[old.index()] = None;
            }
        }
    }

    pub fn add_input(&mut self, ctx: &impl GetNode<Expr, ExprRef>, symbol: ExprRef) {
        assert!(symbol.is_symbol(ctx));
        let name = symbol.get_symbol_name_ref(ctx);
        self.add_signal(symbol, SignalKind::Input, name);
    }

    pub fn add_state(&mut self, ctx: &impl GetNode<Expr, ExprRef>, symbol: ExprRef) -> StateRef {
        assert!(symbol.is_symbol(ctx));
        // also add as a signal
        let name = symbol.get_symbol_name_ref(ctx);
        self.add_signal(symbol, SignalKind::State, name);
        let id = self.states.len();
        self.states.push(State {
            symbol,
            init: None,
            next: None,
        });
        StateRef(id)
    }

    pub fn get_state_by_name(&self, ctx: &Context, name: &str) -> Option<&State> {
        self.states
            .iter()
            .find(|s| s.symbol.get_symbol_name(ctx).unwrap() == name)
    }

    pub fn modify_state<F>(&mut self, reference: StateRef, modify: F)
    where
        F: FnOnce(&mut State),
    {
        modify(self.states.get_mut(reference.0).unwrap())
    }

    pub fn states(&self) -> core::slice::Iter<'_, State> {
        self.states.iter()
    }

    pub fn remove_state(&mut self, index: usize) -> State {
        self.states.remove(index)
    }

    pub fn get_signals(&self, filter: fn(&SignalInfo) -> bool) -> Vec<(ExprRef, SignalInfo)> {
        self.signals
            .iter()
            .enumerate()
            .filter(|(_, opt)| opt.as_ref().map(filter).unwrap_or(false))
            .map(|(index, opt_info)| {
                (
                    ExprRef::from_index(index),
                    opt_info.as_ref().unwrap().clone(),
                )
            })
            .collect::<Vec<_>>()
    }

    pub fn constraints(&self) -> Vec<(ExprRef, SignalInfo)> {
        self.get_signals(|info| info.kind == SignalKind::Constraint)
    }

    pub fn bad_states(&self) -> Vec<(ExprRef, SignalInfo)> {
        self.get_signals(|info| info.kind == SignalKind::Bad)
    }

    /// Uses signal names to generate a lookup map from name to the expression that represents it.
    /// Currently ignores any internal nodes.
    pub fn generate_name_to_ref(&self, ctx: &Context) -> HashMap<String, ExprRef> {
        let mut out = HashMap::new();
        for (idx, maybe_signal) in self.signals.iter().enumerate() {
            if let Some(signal) = maybe_signal {
                if signal.kind != SignalKind::Node {
                    // ignore nodes
                    if let Some(name) = signal.name {
                        let name_str = ctx.get(name).to_string();
                        out.insert(name_str, ExprRef::from_index(idx));
                    }
                }
            }
        }

        out
    }
}

pub fn merge_signal_info(original: &SignalInfo, alias: &SignalInfo) -> SignalInfo {
    let name = match (original.name, alias.name) {
        (Some(name), None) => Some(name),
        (None, Some(name)) => Some(name),
        (None, None) => None,
        (Some(old_name), Some(new_name)) => {
            // we decide whether to overwrite depending on the old signal kind
            match original.kind {
                SignalKind::Input | SignalKind::Output => {
                    // inputs and outputs must retain their old names in order to be identifiable
                    Some(old_name)
                }
                SignalKind::State => {
                    // yosys often adds state labels that contain the actual name used in the verilog
                    Some(new_name)
                }
                _ => {
                    // for other signals, the new name might be better
                    Some(new_name)
                }
            }
        }
    };
    // TODO: it might be interesting to retain alias names

    // only overwrite the kind if it was a node, since other labels add more info
    let kind = match (original.kind, alias.kind) {
        // nodes can always be renamed
        (SignalKind::Node, alias) => alias,
        // outputs always overwrite
        (_, SignalKind::Output) => SignalKind::Output,
        // otherwise we want to keep the original kind
        (original, _) => original,
    };
    // TODO: it might be interesting to retain alias kinds
    //       e.g., a single signal could be a state and an output

    SignalInfo { name, kind }
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
        // the option type can use unused values and thus takes no extra space
        assert_eq!(std::mem::size_of::<Option<SignalInfo>>(), 4);
    }
}
