// Copyright 2023 The Regents of the University of California
// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::ir::*;
use baa::BitVecOps;
use easy_smt as smt;
use std::borrow::Cow;

pub fn convert_tpe(smt_ctx: &mut smt::Context, tpe: Type) -> smt::SExpr {
    match tpe {
        Type::BV(1) => smt_ctx.bool_sort(),
        Type::BV(width) => smt_ctx.bit_vec_sort(smt_ctx.numeral(width)),
        Type::Array(a) => {
            let from = convert_tpe(smt_ctx, a.index_type());
            let to = convert_tpe(smt_ctx, a.data_type());
            smt_ctx.array_sort(from, to)
        }
    }
}

pub fn convert_expr(
    smt_ctx: &smt::Context,
    ctx: &Context,
    expr_ref_in: ExprRef,
    patch_expr: &impl Fn(&ExprRef) -> Option<ExprRef>,
) -> smt::SExpr {
    // replace expressions on the flow (generally in order to inject a symbol or change a symbol name)
    let expr_ref = (patch_expr)(&expr_ref_in).unwrap_or_else(|| expr_ref_in);

    match ctx.get(expr_ref) {
        Expr::BVSymbol { name, .. } => {
            let name_str = ctx.get_str(*name);
            smt_ctx.atom(escape_smt_identifier(name_str))
        }
        Expr::BVLiteral(value) => {
            let value = value.get(ctx);
            if value.is_tru() {
                smt_ctx.true_()
            } else if value.is_fals() {
                smt_ctx.false_()
            } else {
                smt_ctx.atom(format!("#b{}", value.to_bit_str()))
            }
        }
        Expr::BVZeroExt { e, by, .. } => {
            let e_expr = convert_expr(smt_ctx, ctx, *e, patch_expr);
            match e.get_type(ctx) {
                Type::BV(width) => {
                    let inner_ite_encoding = false;
                    if width == 1 {
                        if inner_ite_encoding {
                            // this encoding sticks an ite into the zext
                            let inner =
                                smt_ctx.ite(e_expr, smt_ctx.binary(1, 1), smt_ctx.binary(0, 0));
                            smt_ctx.zext(inner, *by as usize)
                        } else {
                            // this encoding avoids the zext by using an ite on the expanded true/false case
                            let res_size = (by + 1) as usize;
                            // in the one bit case, the underlying expression is represented as a Bool in SMT
                            smt_ctx.ite(
                                e_expr,
                                smt_ctx.binary(res_size, 1),
                                smt_ctx.binary(res_size, 0),
                            )
                        }
                    } else {
                        smt_ctx.zext(e_expr, *by as usize)
                    }
                }
                Type::Array(_) => {
                    panic!("Mall-formed expression: zext should never be applied to an array!")
                }
            }
        }
        Expr::BVSignExt { e, by, .. } => {
            let e_expr = convert_expr(smt_ctx, ctx, *e, patch_expr);
            match e.get_type(ctx) {
                Type::BV(width) => {
                    if width == 1 {
                        let inner = smt_ctx.ite(e_expr, smt_ctx.binary(1, 1), smt_ctx.binary(0, 0));
                        smt_ctx.sext(inner, *by as usize)
                    } else {
                        smt_ctx.sext(e_expr, *by as usize)
                    }
                }
                Type::Array(_) => {
                    panic!("Mall-formed expression: sext should never be applied to an array!")
                }
            }
        }
        Expr::BVSlice { e, hi, lo } => {
            let e_expr = convert_expr(smt_ctx, ctx, *e, patch_expr);
            // skip no-op bit extracts (this helps us avoid slices on boolean values)
            if *lo == 0 && e.get_type(ctx).get_bit_vector_width().unwrap() - 1 == *hi {
                e_expr
            } else {
                let extracted = smt_ctx.extract(*hi as i32, *lo as i32, e_expr);
                if hi > lo {
                    // result width is at least two
                    extracted
                } else {
                    // result width is one => we need to convert to bool
                    to_bool(smt_ctx, extracted)
                }
            }
        }
        Expr::BVNot(e_ref, _) => {
            let e = convert_expr(smt_ctx, ctx, *e_ref, patch_expr);
            if e_ref.get_type(ctx).is_bool() {
                smt_ctx.not(e)
            } else {
                smt_ctx.bvnot(e)
            }
        }
        Expr::BVNegate(e_ref, _) => {
            let e = ensure_bit_vec(
                smt_ctx,
                ctx,
                *e_ref,
                convert_expr(smt_ctx, ctx, *e_ref, patch_expr),
            );
            smt_ctx.bvneg(e)
        }
        Expr::BVEqual(a_ref, b_ref) => {
            let a = convert_expr(smt_ctx, ctx, *a_ref, patch_expr);
            let b = convert_expr(smt_ctx, ctx, *b_ref, patch_expr);
            smt_ctx.eq(a, b)
        }
        Expr::BVImplies(a_ref, b_ref) => {
            assert!(a_ref.get_type(ctx).is_bool());
            let a = convert_expr(smt_ctx, ctx, *a_ref, patch_expr);
            let b = convert_expr(smt_ctx, ctx, *b_ref, patch_expr);
            smt_ctx.imp(a, b)
        }
        Expr::BVGreater(a_ref, b_ref) => {
            convert_simple_binop(true, smt_ctx, ctx, "bvugt", a_ref, b_ref, patch_expr)
        }
        Expr::BVGreaterSigned(a_ref, b_ref, _) => {
            convert_simple_binop(true, smt_ctx, ctx, "bvsgt", a_ref, b_ref, patch_expr)
        }
        Expr::BVGreaterEqual(a_ref, b_ref) => {
            convert_simple_binop(true, smt_ctx, ctx, "bvuge", a_ref, b_ref, patch_expr)
        }
        Expr::BVGreaterEqualSigned(a_ref, b_ref, _) => {
            convert_simple_binop(true, smt_ctx, ctx, "bvsge", a_ref, b_ref, patch_expr)
        }
        Expr::BVConcat(a_ref, b_ref, _) => {
            convert_simple_binop(true, smt_ctx, ctx, "concat", a_ref, b_ref, patch_expr)
        }
        Expr::BVAnd(a_ref, b_ref, _) => {
            let a = convert_expr(smt_ctx, ctx, *a_ref, patch_expr);
            let b = convert_expr(smt_ctx, ctx, *b_ref, patch_expr);
            if let Some(1) = a_ref.get_type(ctx).get_bit_vector_width() {
                smt_ctx.and(a, b)
            } else {
                smt_ctx.bvand(a, b)
            }
        }
        Expr::BVOr(a_ref, b_ref, _) => {
            let a = convert_expr(smt_ctx, ctx, *a_ref, patch_expr);
            let b = convert_expr(smt_ctx, ctx, *b_ref, patch_expr);
            if let Some(1) = a_ref.get_type(ctx).get_bit_vector_width() {
                smt_ctx.or(a, b)
            } else {
                smt_ctx.bvor(a, b)
            }
        }
        Expr::BVXor(a_ref, b_ref, _) => {
            let a = convert_expr(smt_ctx, ctx, *a_ref, patch_expr);
            let b = convert_expr(smt_ctx, ctx, *b_ref, patch_expr);
            if let Some(1) = a_ref.get_type(ctx).get_bit_vector_width() {
                smt_ctx.xor(a, b)
            } else {
                smt_ctx.bvxor(a, b)
            }
        }
        Expr::BVShiftLeft(a_ref, b_ref, _) => {
            convert_simple_binop(false, smt_ctx, ctx, "bvshl", a_ref, b_ref, patch_expr)
        }
        Expr::BVArithmeticShiftRight(a_ref, b_ref, _) => {
            convert_simple_binop(false, smt_ctx, ctx, "bvashr", a_ref, b_ref, patch_expr)
        }
        Expr::BVShiftRight(a_ref, b_ref, _) => {
            convert_simple_binop(false, smt_ctx, ctx, "bvlshr", a_ref, b_ref, patch_expr)
        }
        Expr::BVAdd(a_ref, b_ref, _) => {
            convert_simple_binop(false, smt_ctx, ctx, "bvadd", a_ref, b_ref, patch_expr)
        }
        Expr::BVMul(a_ref, b_ref, _) => {
            convert_simple_binop(false, smt_ctx, ctx, "bvmul", a_ref, b_ref, patch_expr)
        }
        Expr::BVSignedDiv(a_ref, b_ref, _) => {
            convert_simple_binop(false, smt_ctx, ctx, "bvsdiv", a_ref, b_ref, patch_expr)
        }
        Expr::BVUnsignedDiv(a_ref, b_ref, _) => {
            convert_simple_binop(false, smt_ctx, ctx, "bvudiv", a_ref, b_ref, patch_expr)
        }
        Expr::BVSignedMod(a_ref, b_ref, _) => {
            convert_simple_binop(false, smt_ctx, ctx, "bvsmod", a_ref, b_ref, patch_expr)
        }
        Expr::BVSignedRem(a_ref, b_ref, _) => {
            convert_simple_binop(false, smt_ctx, ctx, "bvsrem", a_ref, b_ref, patch_expr)
        }
        Expr::BVUnsignedRem(a_ref, b_ref, _) => {
            convert_simple_binop(false, smt_ctx, ctx, "bvurem", a_ref, b_ref, patch_expr)
        }
        Expr::BVSub(a_ref, b_ref, _) => {
            convert_simple_binop(false, smt_ctx, ctx, "bvsub", a_ref, b_ref, patch_expr)
        }
        Expr::BVArrayRead { array, index, .. } => {
            let a = convert_expr(smt_ctx, ctx, *array, patch_expr);
            let i = convert_expr(smt_ctx, ctx, *index, patch_expr);
            smt_ctx.select(a, i)
        }
        Expr::BVIte { cond, tru, fals } => {
            let c = convert_expr(smt_ctx, ctx, *cond, patch_expr);
            let t = convert_expr(smt_ctx, ctx, *tru, patch_expr);
            let f = convert_expr(smt_ctx, ctx, *fals, patch_expr);
            smt_ctx.ite(c, t, f)
        }
        Expr::ArraySymbol { name, .. } => smt_ctx.atom(escape_smt_identifier(ctx.get_str(*name))),
        Expr::ArrayConstant {
            e,
            index_width,
            data_width,
        } => {
            let e_expr = convert_expr(smt_ctx, ctx, *e, patch_expr);
            let tpe = smt_ctx.array_sort(
                smt_ctx.bit_vec_sort(smt_ctx.numeral(*index_width)),
                smt_ctx.bit_vec_sort(smt_ctx.numeral(*data_width)),
            );
            smt_ctx.const_array(tpe, e_expr)
        }
        Expr::ArrayEqual(a_ref, b_ref) => {
            let a = convert_expr(smt_ctx, ctx, *a_ref, patch_expr);
            let b = convert_expr(smt_ctx, ctx, *b_ref, patch_expr);
            smt_ctx.eq(a, b)
        }
        Expr::ArrayStore { array, index, data } => {
            let a = convert_expr(smt_ctx, ctx, *array, patch_expr);
            let i = convert_expr(smt_ctx, ctx, *index, patch_expr);
            let d = convert_expr(smt_ctx, ctx, *data, patch_expr);
            smt_ctx.store(a, i, d)
        }
        Expr::ArrayIte { cond, tru, fals } => {
            let c = convert_expr(smt_ctx, ctx, *cond, patch_expr);
            let t = convert_expr(smt_ctx, ctx, *tru, patch_expr);
            let f = convert_expr(smt_ctx, ctx, *fals, patch_expr);
            smt_ctx.ite(c, t, f)
        }
    }
}

/// for all bin ops that require a conversion to bit-vec from bool
fn convert_simple_binop(
    do_not_convert_to_bool: bool,
    smt_ctx: &smt::Context,
    ctx: &Context,
    op: &str,
    a_ref: &ExprRef,
    b_ref: &ExprRef,
    patch_expr: &impl Fn(&ExprRef) -> Option<ExprRef>,
) -> smt::SExpr {
    let a = ensure_bit_vec(
        smt_ctx,
        ctx,
        *a_ref,
        convert_expr(smt_ctx, ctx, *a_ref, patch_expr),
    );
    let b = ensure_bit_vec(
        smt_ctx,
        ctx,
        *b_ref,
        convert_expr(smt_ctx, ctx, *b_ref, patch_expr),
    );
    let res = smt_ctx.list(vec![smt_ctx.atom(op), a, b]);
    if !do_not_convert_to_bool && a_ref.get_bv_type(ctx).unwrap() == 1 {
        to_bool(smt_ctx, res)
    } else {
        res
    }
}

// adds a cast if the underlying value is 1-bit and thus represented as a Bool in SMT
fn ensure_bit_vec(
    smt_ctx: &smt::Context,
    ctx: &Context,
    e_ref: ExprRef,
    e: smt::SExpr,
) -> smt::SExpr {
    match e_ref.get_type(ctx) {
        Type::BV(width) => {
            if width == 1 {
                smt_ctx.ite(e, smt_ctx.binary(1, 1), smt_ctx.binary(1, 0))
            } else {
                e
            }
        }
        Type::Array(_) => panic!("This function should never be called on an array!"),
    }
}

fn to_bool(smt_ctx: &smt::Context, e: smt::SExpr) -> smt::SExpr {
    smt_ctx.eq(e, smt_ctx.binary(1, 1))
}

/// See <simple_symbol> definition in the Concrete Syntax Appendix of the SMTLib Spec
fn is_simple_smt_identifier(id: &str) -> bool {
    if id.is_empty() {
        return false; // needs to be non-empty
    }
    let mut is_first = true;
    for cc in id.chars() {
        if !cc.is_ascii() {
            return false; // all allowed characters are ASCII characters
        }
        let ac = cc as u8;
        let is_alpha = ac.is_ascii_uppercase() || ac.is_ascii_lowercase();
        let is_num = ac.is_ascii_digit();
        let is_other_allowed_char = matches!(
            ac,
            b'+' | b'-'
                | b'/'
                | b'*'
                | b'='
                | b'%'
                | b'?'
                | b'!'
                | b'.'
                | b'$'
                | b'_'
                | b'~'
                | b'&'
                | b'^'
                | b'<'
                | b'>'
                | b'@'
        );
        if !(is_alpha | is_num | is_other_allowed_char) {
            return false;
        }
        if is_num && is_first {
            return false; // the first character is not allowed ot be a digit
        }
        is_first = false;
    }
    true // passed all checks
}

pub fn escape_smt_identifier(id: &str) -> std::borrow::Cow<'_, str> {
    if is_simple_smt_identifier(id) {
        Cow::Borrowed(id)
    } else {
        let escaped = format!("|{}|", id);
        Cow::Owned(escaped)
    }
}

#[cfg(test)]
fn unescape_smt_identifier(id: &str) -> &str {
    if id.starts_with("|") {
        assert!(id.ends_with("|"));
        &id[1..id.len() - 1]
    } else {
        id
    }
}

pub trait PatronSmtHelpers {
    /// Zero extend a bit-vector.
    fn zext(&self, e: smt::SExpr, by: usize) -> smt::SExpr;

    /// Sign extend a bit-vector.
    fn sext(&self, e: smt::SExpr, by: usize) -> smt::SExpr;

    /// Declare a constant array (non-standard but supported by many solvers)
    fn const_array(&self, tpe: smt::SExpr, default: smt::SExpr) -> smt::SExpr;
}

impl PatronSmtHelpers for smt::Context {
    fn zext(&self, e: smt::SExpr, by: usize) -> smt::SExpr {
        self.list(vec![
            self.list(vec![
                self.atoms().und,
                self.atom("zero_extend"),
                self.numeral(by),
            ]),
            e,
        ])
    }

    fn sext(&self, e: smt::SExpr, by: usize) -> smt::SExpr {
        self.list(vec![
            self.list(vec![
                self.atoms().und,
                self.atom("sign_extend"),
                self.numeral(by),
            ]),
            e,
        ])
    }

    fn const_array(&self, tpe: smt::SExpr, default: smt::SExpr) -> smt::SExpr {
        self.list(vec![
            self.list(vec![self.atom("as"), self.atom("const"), tpe]),
            default,
        ])
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use easy_smt::*;

    #[test]
    fn easy_smt_symbol_escaping() {
        let ctx = ContextBuilder::new().build().unwrap();
        let test = ctx.atom("test");
        assert_eq!(ctx.display(test).to_string(), "test");
        // turns out easy_smt does not do any escaping!
        let needs_to_be_escaped_1 = ctx.atom("a b");
        assert_eq!(ctx.display(needs_to_be_escaped_1).to_string(), "a b");
    }

    #[test]
    fn test_our_escaping() {
        assert_eq!(
            unescape_smt_identifier(&escape_smt_identifier("a b")),
            "a b"
        );
    }
}
