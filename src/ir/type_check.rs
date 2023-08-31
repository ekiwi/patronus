// Copyright 2023 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

use super::{ArrayType, Expr, ExprRef, GetNode, Type, WidthInt};

#[derive(Debug, Clone)]
pub struct TypeCheckError {
    msg: String,
}

impl TypeCheckError {
    pub fn get_msg(&self) -> &str {
        &self.msg
    }
}

impl Type {
    fn expect_bv(&self, op: &str) -> std::result::Result<WidthInt, TypeCheckError> {
        match self {
            Type::BV(width) => Ok(*width),
            Type::Array(_) => Err(TypeCheckError {
                msg: format!("{op} only works on bit-vectors, not arrays."),
            }),
        }
    }
    fn expect_bv_of(
        &self,
        expected_width: WidthInt,
        op: &str,
    ) -> std::result::Result<(), TypeCheckError> {
        match self {
            Type::BV(width) if *width == expected_width => Ok(()),
            other => Err(TypeCheckError {
                msg: format!(
                    "{op} only works on bit-vectors of size {expected_width}, not {other:?}."
                ),
            }),
        }
    }
    fn expect_array(&self, op: &str) -> std::result::Result<ArrayType, TypeCheckError> {
        match self {
            Type::BV(_) => Err(TypeCheckError {
                msg: format!("{op} only works on arrays, not bit-vectors."),
            }),
            Type::Array(tpe) => Ok(*tpe),
        }
    }
}

fn expect_same_width_bvs(
    ctx: &impl GetNode<Expr, ExprRef>,
    op: &str,
    a: ExprRef,
    b: ExprRef,
) -> std::result::Result<Type, TypeCheckError> {
    let a_width = a.type_check(ctx)?.expect_bv(op)?;
    let b_width = b.type_check(ctx)?.expect_bv(op)?;
    if a_width == b_width {
        Ok(Type::BV(a_width))
    } else {
        Err(TypeCheckError {
            msg: format!(
                "{op} requires two bit-vectors of the same width, not {a_width} and {b_width}"
            ),
        })
    }
}

fn expect_same_size_arrays(
    ctx: &impl GetNode<Expr, ExprRef>,
    op: &str,
    a: ExprRef,
    b: ExprRef,
) -> std::result::Result<Type, TypeCheckError> {
    let a_tpe = a.type_check(ctx)?.expect_array(op)?;
    let b_tpe = b.type_check(ctx)?.expect_array(op)?;
    if a_tpe == b_tpe {
        Ok(Type::Array(a_tpe))
    } else {
        Err(TypeCheckError {
            msg: format!("{op} requires two arrays of the same type, not {a_tpe:?} and {b_tpe:?}"),
        })
    }
}

pub trait TypeCheck {
    fn type_check(
        &self,
        ctx: &impl GetNode<Expr, ExprRef>,
    ) -> std::result::Result<Type, TypeCheckError>;
}

impl TypeCheck for Expr {
    fn type_check(
        &self,
        ctx: &impl GetNode<Expr, ExprRef>,
    ) -> std::result::Result<Type, TypeCheckError> {
        match *self {
            Expr::BVSymbol { name: _, width } => Ok(Type::BV(width)),
            Expr::BVLiteral { value: _, width } => Ok(Type::BV(width)),
            Expr::BVZeroExt { e, by } => {
                Ok(Type::BV(e.type_check(ctx)?.expect_bv("zero extend")? + by))
            }
            Expr::BVSignExt { e, by } => {
                Ok(Type::BV(e.type_check(ctx)?.expect_bv("sign extend")? + by))
            }
            Expr::BVSlice { e, hi, lo } => {
                let e_width = e.type_check(ctx)?.expect_bv("slicing")?;
                if hi >= e_width {
                    Err(TypeCheckError{msg: format!("Bit-slice upper index must be smaller than the width {e_width}. Not: {hi}")})
                } else if hi < lo {
                    Err(TypeCheckError{msg: format!("Bit-slice upper index must be larger or the same as the lower index. But {hi} < {lo}")})
                } else {
                    Ok(Type::BV(hi - lo + 1))
                }
            }
            Expr::BVNot(e) => {
                e.type_check(ctx)?.expect_bv_of(1, "not")?;
                Ok(Type::BV(1))
            }
            Expr::BVNegate(e) => Ok(Type::BV(e.type_check(ctx)?.expect_bv("negation")?)),
            Expr::BVReduceOr(e) => {
                e.type_check(ctx)?.expect_bv("or reduction")?;
                Ok(Type::BV(1))
            }
            Expr::BVReduceAnd(e) => {
                e.type_check(ctx)?.expect_bv("and reduction")?;
                Ok(Type::BV(1))
            }
            Expr::BVReduceXor(e) => {
                e.type_check(ctx)?.expect_bv("xor reduction")?;
                Ok(Type::BV(1))
            }
            Expr::BVEqual(a, b) => {
                expect_same_width_bvs(ctx, "bit-vector equality", a, b)?;
                Ok(Type::BV(1))
            }
            Expr::BVImplies(a, b) => {
                a.type_check(ctx)?.expect_bv("implies")?;
                b.type_check(ctx)?.expect_bv("implies")?;
                Ok(Type::BV(1))
            }
            Expr::BVGreater(a, b) => {
                expect_same_width_bvs(ctx, "greater", a, b)?;
                Ok(Type::BV(1))
            }
            Expr::BVGreaterSigned(a, b) => {
                expect_same_width_bvs(ctx, "greater signed", a, b)?;
                Ok(Type::BV(1))
            }
            Expr::BVGreaterEqual(a, b) => {
                expect_same_width_bvs(ctx, "greater or equals", a, b)?;
                Ok(Type::BV(1))
            }
            Expr::BVGreaterEqualSigned(a, b) => {
                expect_same_width_bvs(ctx, "greater or equals signed", a, b)?;
                Ok(Type::BV(1))
            }
            Expr::BVConcat(a, b) => {
                let a_width = a.type_check(ctx)?.expect_bv("concat")?;
                let b_width = b.type_check(ctx)?.expect_bv("concat")?;
                Ok(Type::BV(a_width + b_width))
            }
            Expr::BVAnd(a, b) => expect_same_width_bvs(ctx, "and", a, b),
            Expr::BVOr(a, b) => expect_same_width_bvs(ctx, "or", a, b),
            Expr::BVXor(a, b) => expect_same_width_bvs(ctx, "xor", a, b),
            Expr::BVShiftLeft(a, b) => expect_same_width_bvs(ctx, "shift left", a, b),
            Expr::BVArithmeticShiftRight(a, b) => {
                expect_same_width_bvs(ctx, "arithmetic shift right", a, b)
            }
            Expr::BVShiftRight(a, b) => expect_same_width_bvs(ctx, "shift right", a, b),
            Expr::BVAdd(a, b) => expect_same_width_bvs(ctx, "add", a, b),
            Expr::BVMul(a, b) => expect_same_width_bvs(ctx, "mul", a, b),
            Expr::BVSignedDiv(a, b) => expect_same_width_bvs(ctx, "signed div", a, b),
            Expr::BVUnsignedDiv(a, b) => expect_same_width_bvs(ctx, "unsigned div", a, b),
            Expr::BVSignedMod(a, b) => expect_same_width_bvs(ctx, "signed mod", a, b),
            Expr::BVSignedRem(a, b) => expect_same_width_bvs(ctx, "signed rem", a, b),
            Expr::BVUnsignedRem(a, b) => expect_same_width_bvs(ctx, "unsigned rem", a, b),
            Expr::BVSub(a, b) => expect_same_width_bvs(ctx, "subtraction", a, b),
            Expr::BVArrayRead { array, index } => {
                let array_tpe = array.type_check(ctx)?.expect_array("array read")?;
                let index_width = index.type_check(ctx)?.expect_bv("array read index")?;
                if array_tpe.index_width != index_width {
                    Err(TypeCheckError {
                        msg: format!(
                            "Underlying array requires index width {0} not {index_width}",
                            array_tpe.index_width
                        ),
                    })
                } else {
                    Ok(Type::BV(array_tpe.data_width))
                }
            }
            Expr::BVIte { cond, tru, fals } => {
                cond.type_check(ctx)?.expect_bv_of(1, "ite condition")?;
                expect_same_width_bvs(ctx, "ite branches", tru, fals)
            }
            Expr::ArraySymbol {
                name: _,
                index_width,
                data_width,
            } => Ok(Type::Array(ArrayType {
                index_width,
                data_width,
            })),
            Expr::ArrayConstant { e, index_width } => {
                let data_width = e.type_check(ctx)?.expect_bv("array constant")?;
                Ok(Type::Array(ArrayType {
                    index_width,
                    data_width,
                }))
            }
            Expr::ArrayEqual(a, b) => {
                expect_same_size_arrays(ctx, "array equals", a, b)?;
                Ok(Type::BV(1))
            }
            Expr::ArrayStore { array, index, data } => {
                let tpe = array.type_check(ctx)?.expect_array("array store")?;
                index
                    .type_check(ctx)?
                    .expect_bv_of(tpe.index_width, "array store index")?;
                data.type_check(ctx)?
                    .expect_bv_of(tpe.data_width, "array store data")?;
                Ok(Type::Array(tpe))
            }
            Expr::ArrayIte { cond, tru, fals } => {
                cond.type_check(ctx)?.expect_bv_of(1, "ite condition")?;
                expect_same_size_arrays(ctx, "ite branches", tru, fals)
            }
        }
    }
}
impl TypeCheck for ExprRef {
    fn type_check(
        &self,
        ctx: &impl GetNode<Expr, ExprRef>,
    ) -> std::result::Result<Type, TypeCheckError> {
        ctx.get(*self).type_check(ctx)
    }
}
