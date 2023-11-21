// Copyright 2023 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

use crate::ir::{Context, Expr, ExprRef, GetNode, SignalInfo, SignalKind, State, TransitionSystem};
use std::collections::HashMap;

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
    let mut use_count = ExprMetaData::default();
    let states: HashMap<ExprRef, &State> = HashMap::from_iter(sys.states().map(|s| (s.symbol, s)));
    let mut todo = Vec::from_iter(
        sys.get_signals(is_usage_root_signal)
            .iter()
            .map(|(e, _)| *e),
    );

    // make sure that all root nodes are marked as used at least once
    for initial in todo.iter() {
        *use_count.get_mut(*initial) = 1;
    }
    while let Some(expr) = todo.pop() {
        ctx.get(expr).for_each_child(|child| {
            let is_first_use = {
                let count = use_count.get_mut(*child);
                *count += 1;
                *count == 1
            };
            if is_first_use {
                todo.push(*child);
                if let Some(state) = states.get(child) {
                    // for states, we also want to mark the initial and the next expression as used
                    if let Some(init) = state.init {
                        *use_count.get_mut(init) = 1;
                        todo.push(init);
                    }
                    if let Some(next) = state.next {
                        *use_count.get_mut(next) = 1;
                        todo.push(next);
                    }
                }
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
struct ExprMetaData<T: Default + Clone> {
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
