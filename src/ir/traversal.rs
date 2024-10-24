// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::ir::{Context, Expr, ExprRef, ForEachChild};

/// Visits expression nodes bottom up while propagating values
pub fn bottom_up<R>(
    ctx: &Context,
    expr: ExprRef,
    mut f: impl FnMut(&Context, &Expr, &[R]) -> R,
) -> R {
    let mut todo = vec![(expr, false)];
    let mut stack = Vec::with_capacity(4);

    while let Some((e, bottom_up)) = todo.pop() {
        let expr = ctx.get(e);

        // Check if there are children that we need to compute first.
        if !bottom_up {
            // check if there are child expressions to evaluate
            let mut has_child = false;
            expr.for_each_child(|c| {
                if !has_child {
                    has_child = true;
                    todo.push((e, true));
                }
                todo.push((*c, false));
            });
            // we need to process the children first
            if has_child {
                continue;
            }
        }

        // Otherwise, all arguments are available on the stack for us to use.
        let num_children = expr.num_children();
        let values = &stack[stack.len() - num_children..];
        let result = f(ctx, expr, values);
        stack.truncate(stack.len() - num_children);
        stack.push(result);
    }

    debug_assert_eq!(stack.len(), 1);
    stack.pop().unwrap()
}
