// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

// web sources on expression tree evaluation:
// https://www.geeksforgeeks.org/evaluation-of-expression-tree/ (recursive, C++)
// https://medium.com/javarevisited/evaluation-of-binary-expression-tree-6768db3be82f (recursive, Java)
//

use crate::ir::{Context, Expr, ExprRef, ForEachChild};
use baa::{BitVecValue, BitVecValueRef};
use smallvec::SmallVec;
use std::collections::HashMap;

pub trait SymbolValues {
    fn get(&self, symbol: &ExprRef) -> Option<BitVecValueRef<'_>>;
}

impl SymbolValues for HashMap<ExprRef, BitVecValue> {
    fn get(&self, symbol: &ExprRef) -> Option<BitVecValueRef<'_>> {
        self.get(symbol).map(|v| v.into())
    }
}

impl SymbolValues for [(ExprRef, BitVecValue)] {
    fn get(&self, symbol: &ExprRef) -> Option<BitVecValueRef<'_>> {
        self.iter()
            .find(|(e, v)| e == symbol)
            .map(|(e, v)| v.into())
    }
}

pub fn eval_bv_expr(
    ctx: &Context,
    symbols: &(impl SymbolValues + ?Sized),
    expr: ExprRef,
) -> BitVecValue {
    let mut stack: SmallVec<[BitVecValue; 4]> = SmallVec::with_capacity(4);
    let mut todo: SmallVec<[(ExprRef, bool); 4]> = SmallVec::with_capacity(4);

    todo.push((expr, false));
    while let Some((e, args_available)) = todo.pop() {
        let expr = ctx.get(e);

        // Check if there are children that we need to compute first.
        if !args_available {
            let mut count = 0;
            expr.for_each_child(|c| {
                todo.push((*c, false));
                count += 1;
            });
            if count > 0 {
                todo.push((e, true));
                continue;
            }
        }

        // Otherwise, all arguments are available on the stack for us to use.
        match ctx.get(e) {
            // leaves
            Expr::BVLiteral(value) => stack.push(value.get(ctx).into()),
            Expr::BVSymbol { .. } => stack.push(symbols.get(&e).unwrap().into()),
            other => todo!("deal with {other:?}"),
        }
    }

    debug_assert_eq!(stack.len(), 1);
    stack.pop().unwrap()
}

#[cfg(test)]
mod tests {
    use super::eval_bv_expr;
    use crate::ir::*;
    use baa::*;

    #[test]
    fn test_eval_bv_expr() {
        let mut c = Context::default();
        let a = c.bv_symbol("a", 1);
        let a_and_1 = c.build(|c| c.and(a, c.one(1)));
        assert!(eval_bv_expr(&c, [(a, BitVecValue::tru())].as_slice(), a_and_1).is_tru());
        assert!(eval_bv_expr(&c, [(a, BitVecValue::fals())].as_slice(), a_and_1).is_fals());
    }
}
