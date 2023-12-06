// Copyright 2023 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

use crate::ir::{Context, Expr, ExprRef, GetNode, SignalInfo, SignalKind, State, TransitionSystem};
use std::collections::HashMap;
use std::ops::Index;

pub fn find_expr_with_multiple_uses(ctx: &Context, sys: &TransitionSystem) -> Vec<ExprRef> {
    let counts = count_expr_uses(ctx, sys);
    let mut out = Vec::new();
    for (idx, count) in counts.iter().enumerate() {
        if *count > 1 {
            out.push(ExprRef::from_index(idx));
        }
    }
    out
}

pub fn count_expr_uses(ctx: &Context, sys: &TransitionSystem) -> Vec<u32> {
    internal_count_expr_uses(ctx, sys, false)
}

pub fn count_expr_uses_without_init(ctx: &Context, sys: &TransitionSystem) -> Vec<u32> {
    internal_count_expr_uses(ctx, sys, true)
}

fn internal_count_expr_uses(ctx: &Context, sys: &TransitionSystem, ignore_init: bool) -> Vec<u32> {
    let mut use_count = ExprMetaData::default();
    let states: HashMap<ExprRef, &State> = HashMap::from_iter(sys.states().map(|s| (s.symbol, s)));
    let mut todo = Vec::from_iter(
        sys.get_signals(is_usage_root_signal)
            .iter()
            .map(|(e, _)| *e),
    );
    // ensure that all roots start with count 1
    for expr in todo.iter() {
        *use_count.get_mut(*expr) = 1;
    }

    while let Some(expr) = todo.pop() {
        if let Some(state) = states.get(&expr) {
            // for states, we also want to mark the initial and the next expression as used
            if let Some(init) = state.init {
                if !ignore_init {
                    let count = use_count.get_mut(init);
                    if *count == 0 {
                        *count = 1;
                        todo.push(init);
                    }
                }
            }
            if let Some(next) = state.next {
                let count = use_count.get_mut(next);
                if *count == 0 {
                    *count = 1;
                    todo.push(next);
                }
            }
        }

        ctx.get(expr).for_each_child(|child| {
            let count = use_count.get_mut(*child);
            let is_first_use = *count == 0;
            *count += 1;
            if is_first_use {
                todo.push(*child);
            }
        });
    }

    use_count.into_vec()
}

/// Returns whether a signal is always "used", i.e. visible to the outside world or not.
pub fn is_usage_root_signal(info: &SignalInfo) -> bool {
    matches!(
        info.kind,
        SignalKind::Bad | SignalKind::Constraint | SignalKind::Output | SignalKind::Fair
    )
}

/// A dense hash map to store meta-data related to each expression
#[derive(Debug, Default)]
pub struct ExprMetaData<T: Default + Clone> {
    inner: Vec<T>,
    default: T,
}

impl<T: Default + Clone> ExprMetaData<T> {
    #[allow(dead_code)]
    pub fn get(&self, e: ExprRef) -> &T {
        self.inner.get(e.index()).unwrap_or(&self.default)
    }

    pub fn get_mut(&mut self, e: ExprRef) -> &mut T {
        if self.inner.len() <= e.index() {
            self.inner.resize(e.index() + 1, T::default());
        }
        &mut self.inner[e.index()]
    }

    pub fn into_vec(self) -> Vec<T> {
        self.inner
    }

    pub fn iter(&self) -> ExprMetaDataIter<T> {
        ExprMetaDataIter {
            inner: self.inner.iter(),
            index: 0,
        }
    }
}

impl<T: Default + Clone> Index<ExprRef> for ExprMetaData<T> {
    type Output = T;

    fn index(&self, index: ExprRef) -> &Self::Output {
        self.get(index)
    }
}

impl<T: Default + Clone> Index<&ExprRef> for ExprMetaData<T> {
    type Output = T;

    fn index(&self, index: &ExprRef) -> &Self::Output {
        self.get(*index)
    }
}

pub struct ExprMetaDataIter<'a, T> {
    inner: std::slice::Iter<'a, T>,
    index: usize,
}

impl<'a, T> Iterator for ExprMetaDataIter<'a, T> {
    type Item = (ExprRef, &'a T);

    fn next(&mut self) -> Option<Self::Item> {
        match self.inner.next() {
            None => None,
            Some(value) => {
                let index_ref = ExprRef::from_index(self.index);
                self.index += 1;
                Some((index_ref, value))
            }
        }
    }
}

pub trait ForEachChild<T> {
    fn for_each_child(&self, visitor: impl FnMut(&T));
}

impl ForEachChild<ExprRef> for Expr {
    fn for_each_child(&self, mut visitor: impl FnMut(&ExprRef)) {
        match self {
            Expr::BVSymbol { .. } => {}  // no children
            Expr::BVLiteral { .. } => {} // no children
            Expr::BVZeroExt { e, .. } => {
                (visitor)(e);
            }
            Expr::BVSignExt { e, .. } => {
                (visitor)(e);
            }
            Expr::BVSlice { e, .. } => {
                (visitor)(e);
            }
            Expr::BVNot(e, _) => {
                (visitor)(e);
            }
            Expr::BVNegate(e, _) => {
                (visitor)(e);
            }
            Expr::BVEqual(a, b) => {
                (visitor)(a);
                (visitor)(b);
            }
            Expr::BVImplies(a, b) => {
                (visitor)(a);
                (visitor)(b);
            }
            Expr::BVGreater(a, b) => {
                (visitor)(a);
                (visitor)(b);
            }
            Expr::BVGreaterSigned(a, b) => {
                (visitor)(a);
                (visitor)(b);
            }
            Expr::BVGreaterEqual(a, b) => {
                (visitor)(a);
                (visitor)(b);
            }
            Expr::BVGreaterEqualSigned(a, b) => {
                (visitor)(a);
                (visitor)(b);
            }
            Expr::BVConcat(a, b, _) => {
                (visitor)(a);
                (visitor)(b);
            }
            Expr::BVAnd(a, b, _) => {
                (visitor)(a);
                (visitor)(b);
            }
            Expr::BVOr(a, b, _) => {
                (visitor)(a);
                (visitor)(b);
            }
            Expr::BVXor(a, b, _) => {
                (visitor)(a);
                (visitor)(b);
            }
            Expr::BVShiftLeft(a, b, _) => {
                (visitor)(a);
                (visitor)(b);
            }
            Expr::BVArithmeticShiftRight(a, b, _) => {
                (visitor)(a);
                (visitor)(b);
            }
            Expr::BVShiftRight(a, b, _) => {
                (visitor)(a);
                (visitor)(b);
            }
            Expr::BVAdd(a, b, _) => {
                (visitor)(a);
                (visitor)(b);
            }
            Expr::BVMul(a, b, _) => {
                (visitor)(a);
                (visitor)(b);
            }
            Expr::BVSignedDiv(a, b, _) => {
                (visitor)(a);
                (visitor)(b);
            }
            Expr::BVUnsignedDiv(a, b, _) => {
                (visitor)(a);
                (visitor)(b);
            }
            Expr::BVSignedMod(a, b, _) => {
                (visitor)(a);
                (visitor)(b);
            }
            Expr::BVSignedRem(a, b, _) => {
                (visitor)(a);
                (visitor)(b);
            }
            Expr::BVUnsignedRem(a, b, _) => {
                (visitor)(a);
                (visitor)(b);
            }
            Expr::BVSub(a, b, _) => {
                (visitor)(a);
                (visitor)(b);
            }
            Expr::BVArrayRead { array, index, .. } => {
                (visitor)(array);
                (visitor)(index);
            }
            Expr::BVIte { cond, tru, fals } => {
                (visitor)(cond);
                (visitor)(tru);
                (visitor)(fals);
            }
            Expr::ArraySymbol { .. } => {} // no children
            Expr::ArrayConstant { e, .. } => {
                (visitor)(e);
            }
            Expr::ArrayEqual(a, b) => {
                (visitor)(a);
                (visitor)(b);
            }
            Expr::ArrayStore { array, index, data } => {
                (visitor)(array);
                (visitor)(index);
                (visitor)(data)
            }
            Expr::ArrayIte { cond, tru, fals } => {
                (visitor)(cond);
                (visitor)(tru);
                (visitor)(fals);
            }
        }
    }
}
