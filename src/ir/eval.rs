// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

// web sources on expression tree evaluation:
// https://www.geeksforgeeks.org/evaluation-of-expression-tree/ (recursive, C++)
// https://medium.com/javarevisited/evaluation-of-binary-expression-tree-6768db3be82f (recursive, Java)
//

use crate::ir::{Context, Expr, ExprRef, ForEachChild};
use baa::{BitVecOps, BitVecValue, BitVecValueRef};
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

type Stack = SmallVec<[BitVecValue; 4]>;

#[inline]
fn un_op(stack: &mut Stack, op: impl Fn(BitVecValue) -> BitVecValue) {
    let e = stack.pop().unwrap_or_else(|| panic!("Stack is empty!"));
    let res = op(e);
    stack.push(res);
}

#[inline]
fn bin_op(stack: &mut Stack, op: impl Fn(BitVecValue, BitVecValue) -> BitVecValue) {
    let a = stack.pop().unwrap_or_else(|| panic!("Stack is empty!"));
    let b = stack.pop().unwrap_or_else(|| panic!("Stack is empty!"));
    let res = op(a, b);
    stack.push(res);
}

pub fn eval_bv_expr(
    ctx: &Context,
    symbols: &(impl SymbolValues + ?Sized),
    expr: ExprRef,
) -> BitVecValue {
    let mut stack: Stack = SmallVec::with_capacity(4);
    let mut todo: SmallVec<[(ExprRef, bool); 4]> = SmallVec::with_capacity(4);

    todo.push((expr, false));
    while let Some((e, args_available)) = todo.pop() {
        let expr = ctx.get(e);

        // Check if there are children that we need to compute first.
        if !args_available {
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
        match ctx.get(e) {
            // nullary
            Expr::BVSymbol { .. } => stack.push(symbols.get(&e).unwrap().into()),
            Expr::BVLiteral(value) => stack.push(value.get(ctx).into()),
            // unary
            Expr::BVZeroExt { by, .. } => un_op(&mut stack, |e| e.zero_extend(*by)),
            Expr::BVSignExt { by, .. } => un_op(&mut stack, |e| e.sign_extend(*by)),
            Expr::BVSlice { hi, lo, .. } => un_op(&mut stack, |e| e.slice(*hi, *lo)),
            Expr::BVNot(_, _) => un_op(&mut stack, |e| e.not()),
            Expr::BVNegate(_, _) => un_op(&mut stack, |e| e.negate()),
            // binary
            Expr::BVEqual(_, _) => bin_op(&mut stack, |a, b| a.is_equal(&b).into()),
            Expr::BVImplies(_, _) => bin_op(&mut stack, |a, b| a.not().or(&b)),
            Expr::BVGreater(_, _) => bin_op(&mut stack, |a, b| a.is_greater(&b).into()),
            Expr::BVGreaterSigned(_, _, _) => {
                bin_op(&mut stack, |a, b| a.is_greater_signed(&b).into())
            }
            Expr::BVGreaterEqual(_, _) => {
                bin_op(&mut stack, |a, b| a.is_greater_or_equal(&b).into())
            }
            Expr::BVGreaterEqualSigned(_, _, _) => {
                bin_op(&mut stack, |a, b| a.is_greater_or_equal_signed(&b).into())
            }
            Expr::BVConcat(_, _, _) => bin_op(&mut stack, |a, b| a.concat(&b)),
            // binary arithmetic
            Expr::BVAnd(_, _, _) => bin_op(&mut stack, |a, b| a.and(&b)),
            Expr::BVOr(_, _, _) => bin_op(&mut stack, |a, b| a.or(&b)),
            Expr::BVXor(_, _, _) => bin_op(&mut stack, |a, b| a.xor(&b)),
            Expr::BVShiftLeft(_, _, _) => bin_op(&mut stack, |a, b| a.shift_left(&b)),
            Expr::BVArithmeticShiftRight(_, _, _) => {
                bin_op(&mut stack, |a, b| a.arithmetic_shift_right(&b))
            }
            Expr::BVShiftRight(_, _, _) => bin_op(&mut stack, |a, b| a.shift_right(&b)),
            Expr::BVAdd(_, _, _) => bin_op(&mut stack, |a, b| a.add(&b)),
            Expr::BVMul(_, _, _) => bin_op(&mut stack, |a, b| a.mul(&b)),
            // div, rem and mod are still TODO
            Expr::BVSub(_, _, _) => bin_op(&mut stack, |a, b| a.sub(&b)),
            // BVArrayRead needs array support!
            Expr::BVIte { .. } => {
                let cond = stack.pop().unwrap().to_bool().unwrap();
                let tru = stack.pop().unwrap();
                let fals = stack.pop().unwrap();
                stack.push(if cond { tru } else { fals });
            }
            // array ops are not supported yet
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

        // boolean
        let a = c.bv_symbol("a", 1);
        let a_and_1 = c.build(|c| c.and(a, c.one(1)));
        assert!(eval_bv_expr(&c, [(a, BitVecValue::tru())].as_slice(), a_and_1).is_tru());
        assert!(eval_bv_expr(&c, [(a, BitVecValue::fals())].as_slice(), a_and_1).is_fals());
        let b = c.bv_symbol("b", 1);
        let expr = c.build(|c| c.or(c.and(a, c.not(b)), c.and(a, b)));
        assert!(eval_bv_expr(
            &c,
            [(a, BitVecValue::fals()), (b, BitVecValue::fals())].as_slice(),
            expr
        )
        .is_fals());

        // arithmetic and ite
        let a = c.bv_symbol("a", 128);
        let b = c.bv_symbol("b", 128);
        let expr = c.build(|c| {
            c.bv_ite(
                c.greater_signed(a, c.bv_lit(&BitVecValue::from_u64(0, 128))),
                c.sub(b, a),
                c.add(b, a),
            )
        });
        {
            let eval = |a_v: i64, b_v: i64| -> i64 {
                let symbols = [
                    (a, BitVecValue::from_i64(a_v, 128)),
                    (b, BitVecValue::from_i64(b_v, 128)),
                ];
                let res = eval_bv_expr(&c, symbols.as_slice(), expr);
                res.to_i64().unwrap()
            };
            assert_eq!(eval(1, 0), -1);
            assert_eq!(eval(-1, 0), -1);
            assert_eq!(eval(-1, -2), -3);
            assert_eq!(eval(-1, 2000), 2000 - 1);
            assert_eq!(eval(1000, 2000), 2000 - 1000);
        }
    }
}
