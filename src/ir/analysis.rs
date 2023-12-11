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

pub type UseCountInt = u16;

pub fn count_expr_uses(ctx: &Context, sys: &TransitionSystem) -> Vec<UseCountInt> {
    internal_count_expr_uses(ctx, sys, false)
}

pub fn count_expr_uses_without_init(ctx: &Context, sys: &TransitionSystem) -> Vec<UseCountInt> {
    internal_count_expr_uses(ctx, sys, true)
}

fn internal_count_expr_uses(
    ctx: &Context,
    sys: &TransitionSystem,
    ignore_init: bool,
) -> Vec<UseCountInt> {
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

        count_uses(ctx, expr, &mut use_count, &mut todo);
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

pub fn is_non_output_root_signal(info: &SignalInfo) -> bool {
    matches!(
        info.kind,
        SignalKind::Bad | SignalKind::Constraint | SignalKind::Fair
    )
}

/// Counts how often expressions are used. This version _does not_ follow any state symbols.
fn simple_count_expr_uses(ctx: &Context, roots: Vec<ExprRef>) -> Vec<UseCountInt> {
    let mut use_count = ExprMetaData::default();
    let mut todo = roots;

    // ensure that all roots start with count 1
    for expr in todo.iter() {
        *use_count.get_mut(*expr) = 1;
    }

    while let Some(expr) = todo.pop() {
        count_uses(ctx, expr, &mut use_count, &mut todo);
    }

    use_count.into_vec()
}

#[inline]
fn count_uses(
    ctx: &Context,
    expr: ExprRef,
    use_count: &mut ExprMetaData<UseCountInt>,
    todo: &mut Vec<ExprRef>,
) {
    ctx.get(expr).for_each_child(|child| {
        let count = use_count.get_mut(*child);
        let is_first_use = *count == 0;
        *count += 1;
        if is_first_use {
            todo.push(*child);
        }
    });
}

#[derive(Debug, Clone)]
pub struct RootInfo {
    pub expr: ExprRef,
    pub uses: Uses,
}

/// Indicates which context an expression is used in.
#[derive(Debug, Clone, Default)]
pub struct Uses {
    pub next: bool,
    pub init: bool,
    pub other: bool,
}

/// Meta-data that helps with serialization, no matter if serializing to btor, our custom
/// "human-readable" format or SMTLib.
#[derive(Debug, Default, Clone)]
pub struct SerializeMeta {
    pub signal_order: Vec<RootInfo>,
}

pub fn analyze_for_serialization(
    ctx: &Context,
    sys: &TransitionSystem,
    include_outputs: bool,
) -> SerializeMeta {
    // first we identify which expressions are used for init and which are used for next
    let (mut init_count, mut next_count, mut other_count) = init_counts(ctx, sys, include_outputs);

    let mut visited = ExprMetaData::default();
    let mut signal_order = Vec::new();

    // add all inputs
    for (input, _) in sys.get_signals(|s| s.kind == SignalKind::Input) {
        *visited.get_mut(input) = true;
        let (uses, _) = analyze_use(input, &init_count, &next_count, &other_count);
        signal_order.push(RootInfo { expr: input, uses });
    }

    // add all roots to todo list
    let mut todo = Vec::new();
    let filter = if include_outputs {
        is_usage_root_signal
    } else {
        is_non_output_root_signal
    };
    for (expr, _) in sys.get_signals(filter) {
        todo.push(expr);
        other_count[expr.index()] = 100; // ensure that this expression will always be serialized
    }
    for state in sys.states() {
        if let Some(expr) = state.next {
            todo.push(expr);
            next_count[expr.index()] = 100; // ensure that this expression will always be serialized
        }
        if let Some(expr) = state.init {
            todo.push(expr);
            init_count[expr.index()] = 100; // ensure that this expression will always be serialized
        }
    }

    // visit roots in the order in which they were declared
    todo.reverse();

    // visit expressions
    while let Some(expr_ref) = todo.pop() {
        let expr = ctx.get(expr_ref);

        // check to see if all children are done
        let mut all_done = true;
        let mut num_children = 0;
        expr.for_each_child(|c| {
            if !*visited.get(*c) {
                if all_done {
                    todo.push(expr_ref); // return expression to the todo list
                }
                all_done = false;
                // we need to visit the child first
                todo.push(*c);
            }
            num_children += 1;
        });

        if !all_done {
            continue;
        }

        // add to signal order if applicable
        if num_children > 0 {
            let (uses, total_use) = analyze_use(expr_ref, &init_count, &next_count, &other_count);
            if total_use > 1 {
                signal_order.push(RootInfo {
                    expr: expr_ref,
                    uses,
                });
            }
        }
        *visited.get_mut(expr_ref) = true;
    }

    SerializeMeta { signal_order }
}

fn analyze_use(
    expr_ref: ExprRef,
    init_count: &[UseCountInt],
    next_count: &[UseCountInt],
    other_count: &[UseCountInt],
) -> (Uses, UseCountInt) {
    let ii = expr_ref.index();
    let init = *init_count.get(ii).unwrap_or(&0);
    let next = *next_count.get(ii).unwrap_or(&0);
    let other = *other_count.get(ii).unwrap_or(&0);
    let total = init + next + other;
    (
        Uses {
            init: init > 0,
            next: next > 0,
            other: other > 0,
        },
        total,
    )
}

fn init_counts(
    ctx: &Context,
    sys: &TransitionSystem,
    include_outputs: bool,
) -> (Vec<UseCountInt>, Vec<UseCountInt>, Vec<UseCountInt>) {
    let mut init_roots = Vec::new();
    let mut next_roots = Vec::new();
    for state in sys.states() {
        if let Some(next) = state.next {
            next_roots.push(next);
        }
        if let Some(init) = state.init {
            init_roots.push(init);
        }
    }

    let filter = if include_outputs {
        is_usage_root_signal
    } else {
        is_non_output_root_signal
    };
    let other_roots = Vec::from_iter(sys.get_signals(filter).iter().map(|(e, _)| *e));

    let init_count = simple_count_expr_uses(ctx, init_roots);
    let next_count = simple_count_expr_uses(ctx, next_roots);
    let other_count = simple_count_expr_uses(ctx, other_roots);

    (init_count, next_count, other_count)
}

/// A dense hash map to store meta-data related to each expression
#[derive(Debug, Default, Clone)]
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

pub trait ForEachChild<T: Clone> {
    fn for_each_child(&self, visitor: impl FnMut(&T));
    fn collect_children(&self, children: &mut Vec<T>) {
        self.for_each_child(|c: &T| {
            children.push(c.clone());
        });
    }
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

impl ForEachChild<ExprRef> for State {
    fn for_each_child(&self, mut visitor: impl FnMut(&ExprRef)) {
        if let Some(next) = &self.next {
            (visitor)(next);
        }
        if let Some(init) = &self.init {
            (visitor)(init);
        }
    }
}
