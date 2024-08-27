// Copyright 2023 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

use super::{Context, Expr, ExprRef, GetNode, StringRef};
use std::collections::HashMap;
use std::fmt::{Display, Formatter};
use std::iter::Enumerate;

/// Represents three fundamental signal kinds that are mutually exclusive:
/// - inputs
/// - states
/// - everything else (a node!)
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub enum SignalKind {
    Node,
    Input,
    State,
}

impl SignalKind {
    #[inline]
    pub fn to_string(&self) -> &'static str {
        match &self {
            SignalKind::Node => "node",
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

#[derive(Copy, Clone, Default, Eq, PartialEq, Hash)]
pub struct SignalLabels(u8);

impl SignalLabels {
    pub fn output() -> Self {
        Self::set(0)
    }
    pub fn is_output(&self) -> bool {
        self.get(0)
    }
    pub fn bad() -> Self {
        Self::set(1)
    }
    pub fn is_bad(&self) -> bool {
        self.get(1)
    }
    pub fn constraint() -> Self {
        Self::set(2)
    }
    pub fn is_constraint(&self) -> bool {
        self.get(2)
    }
    pub fn fair() -> Self {
        Self::set(3)
    }
    pub fn is_fair(&self) -> bool {
        self.get(3)
    }
    #[inline]
    fn get(&self, pos: usize) -> bool {
        (self.0 >> pos) & 1 == 1
    }
    #[inline]
    fn set(pos: usize) -> Self {
        Self(1 << pos)
    }

    pub fn is_none(&self) -> bool {
        self.0 == 0
    }

    pub fn union(&self, other: &Self) -> Self {
        Self(self.0 | other.0)
    }

    pub fn clear(&self, other: &Self) -> Self {
        Self(self.0 & !other.0)
    }
}

impl std::str::FromStr for SignalLabels {
    type Err = ();

    fn from_str(label: &str) -> Result<Self, Self::Err> {
        match label {
            "output" => Ok(SignalLabels::output()),
            "bad" => Ok(SignalLabels::bad()),
            "constraint" => Ok(SignalLabels::constraint()),
            "fair" => Ok(SignalLabels::fair()),
            _ => Err(()),
        }
    }
}

impl std::fmt::Debug for SignalLabels {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "SignalLabels(")?;
        if self.is_output() {
            write!(f, "output ")?;
        }
        if self.is_bad() {
            write!(f, "bad ")?;
        }
        if self.is_constraint() {
            write!(f, "constraint ")?;
        }
        if self.is_fair() {
            write!(f, "fair ")?;
        }
        write!(f, ")")
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct SignalInfo {
    pub name: Option<StringRef>,
    pub kind: SignalKind,
    pub labels: SignalLabels,
}

impl SignalInfo {
    pub fn is_input(&self) -> bool {
        self.kind == SignalKind::Input
    }
    pub fn is_state(&self) -> bool {
        self.kind == SignalKind::State
    }
    pub fn is_output(&self) -> bool {
        self.labels.is_output()
    }
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

impl StateRef {
    pub fn to_index(&self) -> usize {
        self.0
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub struct InputRef(usize);

#[derive(Debug, PartialEq, Eq, Clone)]
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

    pub fn add_signal(
        &mut self,
        expr: ExprRef,
        kind: SignalKind,
        labels: SignalLabels,
        name: Option<StringRef>,
    ) {
        let id = expr.index();
        if self.signals.len() <= id {
            self.signals.resize(id + 1, None);
        }
        self.signals[id] = Some(SignalInfo { name, kind, labels });
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
        self.add_signal(symbol, SignalKind::Input, SignalLabels::default(), name);
    }

    pub fn add_state(&mut self, ctx: &impl GetNode<Expr, ExprRef>, symbol: ExprRef) -> StateRef {
        assert!(symbol.is_symbol(ctx));
        // also add as a signal
        let name = symbol.get_symbol_name_ref(ctx);
        self.add_signal(symbol, SignalKind::State, SignalLabels::default(), name);
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

    pub fn states(&self) -> StateIter<'_> {
        StateIter {
            underlying: self.states.iter().enumerate(),
        }
    }

    pub fn state_map(&self) -> HashMap<ExprRef, &State> {
        HashMap::from_iter(self.states.iter().map(|s| (s.symbol, s)))
    }

    pub fn remove_state(&mut self, state: StateRef) -> State {
        self.states.remove(state.0)
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
        self.get_signals(|info| info.labels.is_constraint())
    }

    pub fn bad_states(&self) -> Vec<(ExprRef, SignalInfo)> {
        self.get_signals(|info| info.labels.is_bad())
    }

    /// Uses signal names to generate a lookup map from name to the expression that represents it.
    /// Currently ignores any internal nodes.
    pub fn generate_name_to_ref(&self, ctx: &Context) -> HashMap<String, ExprRef> {
        let mut out = HashMap::new();
        for (idx, maybe_signal) in self.signals.iter().enumerate() {
            if let Some(signal) = maybe_signal {
                // ignore nodes
                let skip = signal.kind == SignalKind::Node && signal.labels.is_none();
                if !skip {
                    let expr_ref = ExprRef::from_index(idx);
                    if let Some(name) = signal.name {
                        let name_str = ctx.get(name).to_string();
                        out.insert(name_str, expr_ref);
                    }
                    // sometimes symbols might have a different name than the signal, because of aliasing
                    if let Some(name) = expr_ref.get_symbol_name(ctx) {
                        out.insert(name.to_string(), expr_ref);
                    }
                }
            }
        }

        out
    }
}

pub struct StateIter<'a> {
    underlying: Enumerate<std::slice::Iter<'a, State>>,
}

impl<'a> Iterator for StateIter<'a> {
    type Item = (StateRef, &'a State);

    fn next(&mut self) -> Option<Self::Item> {
        self.underlying.next().map(|(i, s)| (StateRef(i), s))
    }
}

impl<'a> DoubleEndedIterator for StateIter<'a> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.underlying.next_back().map(|(i, s)| (StateRef(i), s))
    }
}

pub fn merge_signal_info(original: &SignalInfo, alias: &SignalInfo) -> SignalInfo {
    let name = match (original.name, alias.name) {
        (Some(name), None) => Some(name),
        (None, Some(name)) => Some(name),
        (None, None) => None,
        (Some(old_name), Some(new_name)) => {
            // we decide whether to overwrite depending on the old signal kind
            if original.labels.is_output() {
                // outputs must retain their old names in order to be identifiable
                Some(old_name)
            } else {
                Some(new_name)
            }
        }
    };
    // TODO: it might be interesting to retain alias names

    // only overwrite the kind if it was a node
    let kind = match (original.kind, alias.kind) {
        // nodes can always be renamed
        (SignalKind::Node, alias) => alias,
        // otherwise we want to keep the original kind
        (original, _) => original,
    };

    let labels = original.labels.union(&alias.labels);

    SignalInfo { name, kind, labels }
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
        // simple bit flags
        assert_eq!(std::mem::size_of::<SignalLabels>(), 1);
        // Optional name (saved as a string ref) + SignalKind
        assert_eq!(std::mem::size_of::<SignalInfo>(), 8);
        // the option type can use unused values and thus takes no extra space
        assert_eq!(std::mem::size_of::<Option<SignalInfo>>(), 8);
    }
}
