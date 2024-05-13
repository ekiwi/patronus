// Copyright 2023 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

use crate::btor2::{DEFAULT_INPUT_PREFIX, DEFAULT_STATE_PREFIX};
use crate::ir::*;
use std::collections::HashMap;

/** Remove any inputs named `_input_[...]` and replace their use with a literal zero.
 * This essentially gets rid of all undefined value modelling by yosys.
 */
pub fn replace_anonymous_inputs_with_zero(ctx: &mut Context, sys: &mut TransitionSystem) {
    // find and remove inputs
    let mut replace_map = HashMap::new();
    for (expr, signal_info) in sys.get_signals(|s| s.is_input()) {
        let name = expr.get_symbol_name(ctx).unwrap();
        if name.starts_with(DEFAULT_INPUT_PREFIX) || name.starts_with(DEFAULT_STATE_PREFIX) {
            let replacement = match expr.get_type(ctx) {
                Type::BV(width) => ctx.zero(width),
                Type::Array(tpe) => ctx.zero_array(tpe),
            };
            replace_map.insert(expr, replacement);
            sys.remove_signal(expr);
            // re-insert signal info if the input has labels
            if !signal_info.labels.is_none() {
                sys.add_signal(
                    replacement,
                    SignalKind::Node,
                    signal_info.labels,
                    signal_info.name,
                );
            }
        }
    }

    // replace any use of the input with zero
    do_transform(ctx, sys, |_ctx, expr, _children| {
        replace_map.get(&expr).cloned()
    });
}

/// Applies simplifications to the expressions used in the system.
pub fn simplify_expressions(ctx: &mut Context, sys: &mut TransitionSystem) {
    do_transform(ctx, sys, simplify);
}

fn simplify(ctx: &mut Context, expr: ExprRef, children: &[ExprRef]) -> Option<ExprRef> {
    match (ctx.get(expr).clone(), children) {
        (Expr::BVIte { .. }, [cond, tru, fals]) => {
            if tru == fals {
                // condition does not matter
                Some(*tru)
            } else if let Expr::BVLiteral { value, .. } = ctx.get(*cond) {
                if *value == 0 {
                    Some(*fals)
                } else {
                    Some(*tru)
                }
            } else {
                None
            }
        }
        (Expr::BVAnd(_, _, width), [a, b]) => {
            if let (Expr::BVLiteral { value: va, .. }, Expr::BVLiteral { value: vb, .. }) =
                (ctx.get(*a), ctx.get(*b))
            {
                Some(ctx.bv_lit(*va & *vb, width))
            } else {
                None
            }
        }
        (Expr::BVOr(_, _, width), [a, b]) => {
            if let (Expr::BVLiteral { value: va, .. }, Expr::BVLiteral { value: vb, .. }) =
                (ctx.get(*a), ctx.get(*b))
            {
                Some(ctx.bv_lit(*va | *vb, width))
            } else {
                None
            }
        }
        (Expr::BVNot(_, width), [e]) => {
            match ctx.get(*e) {
                Expr::BVNot(inner, _) => Some(*inner), // double negation
                Expr::BVLiteral { value, .. } => {
                    Some(ctx.bv_lit((!*value) & value::mask(width), width))
                }
                _ => None,
            }
        }
        (Expr::BVZeroExt { width, .. }, [e]) => match ctx.get(*e) {
            Expr::BVLiteral { value, .. } => Some(ctx.bv_lit(*value, width)),
            _ => None,
        },
        // combine slices
        (Expr::BVSlice { lo, hi, .. }, [e]) => match ctx.get(*e) {
            Expr::BVSlice {
                lo: inner_lo,
                e: inner_e,
                ..
            } => Some(ctx.slice(*inner_e, hi + inner_lo, lo + inner_lo)),
            _ => None,
        },
        _ => None, // no matching simplification
    }
}

pub fn do_transform(
    ctx: &mut Context,
    sys: &mut TransitionSystem,
    tran: impl FnMut(&mut Context, ExprRef, &[ExprRef]) -> Option<ExprRef>,
) {
    let todo = get_root_expressions(sys);
    let transformed = do_transform_expr(ctx, todo, tran);

    // update transition system signals
    for (old_expr, maybe_new_expr) in transformed.iter() {
        if let Some(new_expr) = maybe_new_expr {
            if *new_expr != old_expr {
                sys.update_signal_expr(old_expr, *new_expr);
            }
        }
    }
    // update states
    for state in sys.states.iter_mut() {
        if let Some(new_symbol) = changed(&transformed, state.symbol) {
            state.symbol = new_symbol;
        }
        if let Some(old_next) = state.next {
            if let Some(new_next) = changed(&transformed, old_next) {
                state.next = Some(new_next);
            }
        }
        if let Some(old_init) = state.init {
            if let Some(new_init) = changed(&transformed, old_init) {
                state.init = Some(new_init);
            }
        }
    }
}

fn changed(transformed: &ExprMetaData<Option<ExprRef>>, old_expr: ExprRef) -> Option<ExprRef> {
    if let Some(new_expr) = transformed.get(old_expr) {
        if *new_expr != old_expr {
            Some(*new_expr)
        } else {
            None
        }
    } else {
        None
    }
}

fn do_transform_expr(
    ctx: &mut Context,
    mut todo: Vec<ExprRef>,
    mut tran: impl FnMut(&mut Context, ExprRef, &[ExprRef]) -> Option<ExprRef>,
) -> ExprMetaData<Option<ExprRef>> {
    let mut transformed = ExprMetaData::default();
    let mut children = Vec::with_capacity(4);

    while let Some(expr_ref) = todo.pop() {
        // check to see if we translated all the children
        children.clear();
        let mut children_changed = false; // track whether any of the children changed
        let mut all_transformed = true; // tracks whether all children have been transformed or if there is more work to do
        ctx.get(expr_ref).for_each_child(|c| {
            match transformed.get(*c) {
                Some(new_child_expr) => {
                    if *new_child_expr != *c {
                        children_changed = true; // child changed
                    }
                    children.push(*new_child_expr);
                }
                None => {
                    if all_transformed {
                        todo.push(expr_ref);
                    }
                    all_transformed = false;
                    todo.push(*c);
                }
            }
        });
        if !all_transformed {
            continue;
        }

        // call out to the transform
        let tran_res = (tran)(ctx, expr_ref, &children);
        let new_expr_ref = match tran_res {
            Some(e) => e,
            None => {
                if children_changed {
                    update_expr_children(ctx, expr_ref, &children)
                } else {
                    // if no children changed and the transform does not want to do changes,
                    // we can just keep the old expression
                    expr_ref
                }
            }
        };
        // remember the transformed version
        *transformed.get_mut(expr_ref) = Some(new_expr_ref);
    }
    transformed
}

fn get_root_expressions(sys: &TransitionSystem) -> Vec<ExprRef> {
    // include all input, output, assertion and assumptions expressions
    let mut out = Vec::from_iter(
        sys.get_signals(is_usage_root_signal)
            .iter()
            .map(|(e, _)| *e),
    );

    // include all states
    for (_, state) in sys.states() {
        out.push(state.symbol);
        if let Some(init) = state.init {
            out.push(init);
        }
        if let Some(next) = state.next {
            out.push(next);
        }
    }

    out
}

fn update_expr_children(ctx: &mut Context, expr_ref: ExprRef, children: &[ExprRef]) -> ExprRef {
    let new_expr = match (ctx.get(expr_ref), children) {
        (Expr::BVSymbol { .. }, _) => panic!("No children, should never get here."),
        (Expr::BVLiteral { .. }, _) => panic!("No children, should never get here."),
        (Expr::BVZeroExt { by, width, .. }, [e]) => Expr::BVZeroExt {
            e: *e,
            by: *by,
            width: *width,
        },
        (Expr::BVSignExt { by, width, .. }, [e]) => Expr::BVSignExt {
            e: *e,
            by: *by,
            width: *width,
        },
        (Expr::BVSlice { hi, lo, .. }, [e]) => Expr::BVSlice {
            e: *e,
            hi: *hi,
            lo: *lo,
        },
        (Expr::BVNot(_, width), [e]) => Expr::BVNot(*e, *width),
        (Expr::BVNegate(_, width), [e]) => Expr::BVNegate(*e, *width),
        (Expr::BVEqual(_, _), [a, b]) => Expr::BVEqual(*a, *b),
        (Expr::BVImplies(_, _), [a, b]) => Expr::BVImplies(*a, *b),
        (Expr::BVGreater(_, _), [a, b]) => Expr::BVGreater(*a, *b),
        (Expr::BVGreaterSigned(_, _, w), [a, b]) => Expr::BVGreaterSigned(*a, *b, *w),
        (Expr::BVGreaterEqual(_, _), [a, b]) => Expr::BVGreaterEqual(*a, *b),
        (Expr::BVGreaterEqualSigned(_, _, w), [a, b]) => Expr::BVGreaterEqualSigned(*a, *b, *w),
        (Expr::BVConcat(_, _, w), [a, b]) => Expr::BVConcat(*a, *b, *w),
        (Expr::BVAnd(_, _, w), [a, b]) => Expr::BVAnd(*a, *b, *w),
        (Expr::BVOr(_, _, w), [a, b]) => Expr::BVOr(*a, *b, *w),
        (Expr::BVXor(_, _, w), [a, b]) => Expr::BVXor(*a, *b, *w),
        (Expr::BVShiftLeft(_, _, w), [a, b]) => Expr::BVShiftLeft(*a, *b, *w),
        (Expr::BVArithmeticShiftRight(_, _, w), [a, b]) => Expr::BVArithmeticShiftRight(*a, *b, *w),
        (Expr::BVShiftRight(_, _, w), [a, b]) => Expr::BVShiftRight(*a, *b, *w),
        (Expr::BVAdd(_, _, w), [a, b]) => Expr::BVAdd(*a, *b, *w),
        (Expr::BVMul(_, _, w), [a, b]) => Expr::BVMul(*a, *b, *w),
        (Expr::BVSignedDiv(_, _, w), [a, b]) => Expr::BVSignedDiv(*a, *b, *w),
        (Expr::BVUnsignedDiv(_, _, w), [a, b]) => Expr::BVUnsignedDiv(*a, *b, *w),
        (Expr::BVSignedMod(_, _, w), [a, b]) => Expr::BVSignedMod(*a, *b, *w),
        (Expr::BVSignedRem(_, _, w), [a, b]) => Expr::BVSignedRem(*a, *b, *w),
        (Expr::BVUnsignedRem(_, _, w), [a, b]) => Expr::BVUnsignedRem(*a, *b, *w),
        (Expr::BVSub(_, _, w), [a, b]) => Expr::BVSub(*a, *b, *w),
        (Expr::BVArrayRead { width, .. }, [array, index]) => Expr::BVArrayRead {
            array: *array,
            index: *index,
            width: *width,
        },
        (Expr::BVIte { .. }, [cond, tru, fals]) => Expr::BVIte {
            cond: *cond,
            tru: *tru,
            fals: *fals,
        },
        (Expr::ArraySymbol { .. }, _) => panic!("No children, should never get here."),
        (
            Expr::ArrayConstant {
                index_width,
                data_width,
                ..
            },
            [e],
        ) => Expr::ArrayConstant {
            e: *e,
            index_width: *index_width,
            data_width: *data_width,
        },
        (Expr::ArrayEqual(_, _), [a, b]) => Expr::ArrayEqual(*a, *b),
        (Expr::ArrayStore { .. }, [array, index, data]) => Expr::ArrayStore {
            array: *array,
            index: *index,
            data: *data,
        },
        (Expr::ArrayIte { .. }, [cond, tru, fals]) => Expr::ArrayIte {
            cond: *cond,
            tru: *tru,
            fals: *fals,
        },
        (other, _) => {
            todo!("implement code to re-create expression `{other:?}` with updated children")
        }
    };
    ctx.add_node(new_expr)
}

/// Slightly different definition from use counts, as we want to retain all inputs in transformation passes.
fn is_usage_root_signal(info: &SignalInfo) -> bool {
    info.is_input()
        || info.labels.is_output()
        || info.labels.is_constraint()
        || info.labels.is_bad()
        || info.labels.is_fair()
}
