// Copyright 2023 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

use crate::ir::*;

pub fn do_transform(
    ctx: &mut Context,
    sys: &mut TransitionSystem,
    mut foo: impl FnMut(&mut Context, ExprRef, &[ExprRef]) -> Option<ExprRef>,
) {
    let todo = get_root_expressions(sys);
    let transformed = do_transform_expr(ctx, todo, foo);

    // update transition system signals
    for (old_expr, maybe_new_expr) in transformed.iter() {
        if let Some(new_expr) = maybe_new_expr {
            if *new_expr != old_expr {
                sys.update_signal_expr(old_expr, *new_expr);
            }
        }
    }
    // update states
    for state in sys.states() {}

    todo!()
}

fn do_transform_expr(
    ctx: &mut Context,
    mut todo: Vec<ExprRef>,
    mut foo: impl FnMut(&mut Context, ExprRef, &[ExprRef]) -> Option<ExprRef>,
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
        let foo_res = (foo)(ctx, expr_ref, &children);
        let new_expr_ref = match foo_res {
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
    for state in sys.states() {
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
    todo!("implement code to re-create expression with updated children")
}

/// Slightly different definition from use counts, as we want to retain all inputs in transformation passes.
fn is_usage_root_signal(info: &SignalInfo) -> bool {
    matches!(
        info.kind,
        SignalKind::Bad
            | SignalKind::Constraint
            | SignalKind::Output
            | SignalKind::Fair
            | SignalKind::Input
    )
}
