// Copyright 2023 The Regents of the University of California
// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

//! # IR Context
//!
//! The [`Context`] is used to create and access bit-vector and array expressions.
//! It ensures that the same expression always maps to the same expression reference.
//! Thus, if two references are equal, we can be certain that the expressions they point to are
//! equivalent.
//!
//! Users are expected to generally use a single Context for all their expressions. There
//! are no checks to ensure that a [`ExprRef`] or [`StringRef`] from different contexts are
//! not matched. Thus working with more than one [`Context`] object can be dangerous.

use crate::ir::expr::*;
use crate::ir::TypeCheck;
use baa::{BitVecValue, BitVecValueIndex, BitVecValueRef, IndexToRef};
use std::borrow::Borrow;
use std::cell::RefCell;
use std::fmt::{Debug, Formatter};
use std::num::{NonZeroU16, NonZeroU32};

/// Uniquely identifies a [`String`] stored in a [`Context`].
#[derive(PartialEq, Eq, Clone, Copy, Hash)]
pub struct StringRef(NonZeroU16);

impl Debug for StringRef {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "StringRef({})", self.index())
    }
}

impl StringRef {
    fn from_index(index: usize) -> Self {
        Self(NonZeroU16::new((index + 1) as u16).unwrap())
    }

    fn index(&self) -> usize {
        (self.0.get() - 1) as usize
    }
}

/// Uniquely identifies an [`Expr`] stored in a [`Context`].
#[derive(PartialEq, Eq, Clone, Copy, Hash, Ord, PartialOrd)]
pub struct ExprRef(NonZeroU32);

impl Debug for ExprRef {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        // we need a custom implementation in order to show the zero based index
        write!(f, "ExprRef({})", self.index())
    }
}

impl ExprRef {
    // TODO: reduce visibility to pub(crate)
    pub fn from_index(index: usize) -> Self {
        ExprRef(NonZeroU32::new((index + 1) as u32).unwrap())
    }

    pub(crate) fn index(&self) -> usize {
        (self.0.get() - 1) as usize
    }
}

/// Context which is used to create all SMT expressions. Expressions are interned such that
/// reference equivalence implies structural equivalence.
#[derive(Clone, Default)]
pub struct Context {
    strings: indexmap::IndexSet<String>,
    exprs: indexmap::IndexSet<Expr>,
    values: baa::ValueInterner,
}

impl Context {
    /// ensures that the value is unique (by appending a number if necessary) and then adds it to the store
    /// TODO: move this functionality to the parser, since it is only really good to use when we
    ///       have a fresh context. Otherwise, we might encounter "false" conflicts, leading to
    ///       unstable names.
    pub(crate) fn add_unique_str(&mut self, value: &str) -> StringRef {
        let mut name: String = value.to_string();
        let mut count: usize = 0;
        while self.is_interned(&name) {
            name = format!("{value}_{count}");
            count += 1;
        }
        self.string(name.into())
    }

    fn is_interned(&self, value: &str) -> bool {
        self.strings.get(value).is_some()
    }
}

/// Adding and removing nodes.
impl Context {
    pub fn get(&self, reference: ExprRef) -> &Expr {
        self.exprs
            .get_index((reference.0.get() as usize) - 1)
            .expect("Invalid ExprRef!")
    }

    pub(crate) fn add_expr(&mut self, value: Expr) -> ExprRef {
        let (index, _) = self.exprs.insert_full(value);
        ExprRef::from_index(index)
    }

    pub(crate) fn get_str(&self, reference: StringRef) -> &str {
        self.strings
            .get_index((reference.0.get() as usize) - 1)
            .expect("Invalid StringRef!")
    }

    pub(crate) fn string(&mut self, value: std::borrow::Cow<str>) -> StringRef {
        if let Some(index) = self.strings.get_index_of(value.as_ref()) {
            StringRef::from_index(index)
        } else {
            let (index, _) = self.strings.insert_full(value.into_owned());
            StringRef::from_index(index)
        }
    }

    pub(crate) fn get_bv_value(&self, index: impl Borrow<BitVecValueIndex>) -> BitVecValueRef<'_> {
        self.values.words().get_ref(index)
    }
}

/// Convenience methods to construct IR nodes.
impl Context {
    // helper functions to construct expressions
    pub fn bv_symbol(&mut self, name: &str, width: WidthInt) -> ExprRef {
        assert!(width > 0, "0-bit bitvectors are not allowed");
        let name_ref = self.string(name.into());
        self.add_expr(Expr::BVSymbol {
            name: name_ref,
            width,
        })
    }

    pub fn array_symbol(
        &mut self,
        name: &str,
        index_width: WidthInt,
        data_width: WidthInt,
    ) -> ExprRef {
        assert!(index_width > 0, "0-bit bitvectors are not allowed");
        assert!(data_width > 0, "0-bit bitvectors are not allowed");
        let name_ref = self.string(name.into());
        self.add_expr(Expr::ArraySymbol {
            name: name_ref,
            index_width,
            data_width,
        })
    }
    pub fn symbol(&mut self, name: StringRef, tpe: Type) -> ExprRef {
        assert_ne!(tpe, Type::BV(0), "0-bit bitvectors are not allowed");
        self.add_expr(Expr::symbol(name, tpe))
    }
    pub fn bv_lit<'a>(&mut self, value: impl Into<BitVecValueRef<'a>>) -> ExprRef {
        let index = self.values.get_index(value);
        self.add_expr(Expr::BVLiteral(BVLitValue::new(index)))
    }
    pub fn zero(&mut self, width: WidthInt) -> ExprRef {
        self.bv_lit(&BitVecValue::zero(width))
    }

    pub fn zero_array(&mut self, tpe: ArrayType) -> ExprRef {
        let data = self.zero(tpe.data_width);
        self.array_const(data, tpe.index_width)
    }

    pub fn mask(&mut self, width: WidthInt) -> ExprRef {
        self.bv_lit(&BitVecValue::ones(width))
    }
    pub fn one(&mut self, width: WidthInt) -> ExprRef {
        self.bv_lit(&BitVecValue::from_u64(1, width))
    }
    pub fn bv_equal(&mut self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.add_expr(Expr::BVEqual(a, b))
    }
    pub fn bv_ite(&mut self, cond: ExprRef, tru: ExprRef, fals: ExprRef) -> ExprRef {
        self.add_expr(Expr::BVIte { cond, tru, fals })
    }
    pub fn array_ite(&mut self, cond: ExprRef, tru: ExprRef, fals: ExprRef) -> ExprRef {
        self.add_expr(Expr::ArrayIte { cond, tru, fals })
    }
    pub fn implies(&mut self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.add_expr(Expr::BVImplies(a, b))
    }
    pub fn greater_signed(&mut self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.add_expr(Expr::BVGreaterSigned(a, b, b.get_bv_type(self).unwrap()))
    }

    pub fn greater(&mut self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.add_expr(Expr::BVGreater(a, b))
    }
    pub fn greater_or_equal_signed(&mut self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.add_expr(Expr::BVGreaterEqualSigned(
            a,
            b,
            b.get_bv_type(self).unwrap(),
        ))
    }

    pub fn greater_or_equal(&mut self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.add_expr(Expr::BVGreaterEqual(a, b))
    }
    pub fn not(&mut self, e: ExprRef) -> ExprRef {
        self.add_expr(Expr::BVNot(e, e.get_bv_type(self).unwrap()))
    }
    pub fn negate(&mut self, e: ExprRef) -> ExprRef {
        self.add_expr(Expr::BVNegate(e, e.get_bv_type(self).unwrap()))
    }
    pub fn and(&mut self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.add_expr(Expr::BVAnd(a, b, b.get_bv_type(self).unwrap()))
    }
    pub fn or(&mut self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.add_expr(Expr::BVOr(a, b, b.get_bv_type(self).unwrap()))
    }
    pub fn xor(&mut self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.add_expr(Expr::BVXor(a, b, b.get_bv_type(self).unwrap()))
    }
    pub fn shift_left(&mut self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.add_expr(Expr::BVShiftLeft(a, b, b.get_bv_type(self).unwrap()))
    }
    pub fn arithmetic_shift_right(&mut self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.add_expr(Expr::BVArithmeticShiftRight(
            a,
            b,
            b.get_bv_type(self).unwrap(),
        ))
    }
    pub fn shift_right(&mut self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.add_expr(Expr::BVShiftRight(a, b, b.get_bv_type(self).unwrap()))
    }
    pub fn add(&mut self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.add_expr(Expr::BVAdd(a, b, b.get_bv_type(self).unwrap()))
    }
    pub fn sub(&mut self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.add_expr(Expr::BVSub(a, b, b.get_bv_type(self).unwrap()))
    }
    pub fn mul(&mut self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.add_expr(Expr::BVMul(a, b, b.get_bv_type(self).unwrap()))
    }
    pub fn div(&mut self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.add_expr(Expr::BVUnsignedDiv(a, b, b.get_bv_type(self).unwrap()))
    }
    pub fn signed_div(&mut self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.add_expr(Expr::BVSignedDiv(a, b, b.get_bv_type(self).unwrap()))
    }
    pub fn signed_mod(&mut self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.add_expr(Expr::BVSignedMod(a, b, b.get_bv_type(self).unwrap()))
    }
    pub fn signed_remainder(&mut self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.add_expr(Expr::BVSignedRem(a, b, b.get_bv_type(self).unwrap()))
    }
    pub fn remainder(&mut self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.add_expr(Expr::BVUnsignedRem(a, b, b.get_bv_type(self).unwrap()))
    }
    pub fn concat(&mut self, a: ExprRef, b: ExprRef) -> ExprRef {
        let width = a.get_bv_type(self).unwrap() + b.get_bv_type(self).unwrap();
        self.add_expr(Expr::BVConcat(a, b, width))
    }
    pub fn slice(&mut self, e: ExprRef, hi: WidthInt, lo: WidthInt) -> ExprRef {
        if lo == 0 && hi + 1 == e.get_bv_type(self).unwrap() {
            e
        } else {
            assert!(hi >= lo, "{hi} < {lo} ... not allowed!");
            self.add_expr(Expr::BVSlice { e, hi, lo })
        }
    }
    pub fn zero_extend(&mut self, e: ExprRef, by: WidthInt) -> ExprRef {
        if by == 0 {
            e
        } else {
            let width = e.get_bv_type(self).unwrap() + by;
            self.add_expr(Expr::BVZeroExt { e, by, width })
        }
    }
    pub fn sign_extend(&mut self, e: ExprRef, by: WidthInt) -> ExprRef {
        if by == 0 {
            e
        } else {
            let width = e.get_bv_type(self).unwrap() + by;
            self.add_expr(Expr::BVSignExt { e, by, width })
        }
    }

    pub fn array_store(&mut self, array: ExprRef, index: ExprRef, data: ExprRef) -> ExprRef {
        self.add_expr(Expr::ArrayStore { array, index, data })
    }

    pub fn array_const(&mut self, e: ExprRef, index_width: WidthInt) -> ExprRef {
        let data_width = e.get_bv_type(self).unwrap();
        self.add_expr(Expr::ArrayConstant {
            e,
            index_width,
            data_width,
        })
    }

    pub fn array_read(&mut self, array: ExprRef, index: ExprRef) -> ExprRef {
        let width = array.get_type(self).get_array_data_width().unwrap();
        self.add_expr(Expr::BVArrayRead {
            array,
            index,
            width,
        })
    }

    pub fn build(&mut self, foo: impl FnOnce(Builder) -> ExprRef) -> ExprRef {
        let builder = Builder::new(self);
        foo(builder)
    }
}

/// Makes it possible to build up expressions while using dynamically checked borrowing rules
/// to work around a shortcoming of the Rust borrow checker.
/// Thus, with a builder you will be able to build up nested expressions easily!
pub struct Builder<'a> {
    ctx: RefCell<&'a mut Context>,
}

impl<'a> Builder<'a> {
    fn new(ctx: &'a mut Context) -> Self {
        Self {
            ctx: RefCell::new(ctx),
        }
    }
}

impl<'a> Builder<'a> {
    pub fn bv_symbol(&self, name: &str, width: WidthInt) -> ExprRef {
        self.ctx.borrow_mut().bv_symbol(name, width)
    }
    pub fn symbol(&self, name: StringRef, tpe: Type) -> ExprRef {
        self.ctx.borrow_mut().symbol(name, tpe)
    }
    pub fn bv_lit<'b>(&self, value: impl Into<BitVecValueRef<'b>>) -> ExprRef {
        self.ctx.borrow_mut().bv_lit(value)
    }
    pub fn zero(&mut self, width: WidthInt) -> ExprRef {
        self.ctx.borrow_mut().zero(width)
    }

    pub fn zero_array(&mut self, tpe: ArrayType) -> ExprRef {
        self.ctx.borrow_mut().zero_array(tpe)
    }

    pub fn mask(&self, width: WidthInt) -> ExprRef {
        self.ctx.borrow_mut().mask(width)
    }
    pub fn one(&self, width: WidthInt) -> ExprRef {
        self.ctx.borrow_mut().one(width)
    }
    pub fn bv_equal(&self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.ctx.borrow_mut().bv_equal(a, b)
    }
    pub fn bv_ite(&self, cond: ExprRef, tru: ExprRef, fals: ExprRef) -> ExprRef {
        self.ctx.borrow_mut().bv_ite(cond, tru, fals)
    }
    pub fn array_ite(&self, cond: ExprRef, tru: ExprRef, fals: ExprRef) -> ExprRef {
        self.ctx.borrow_mut().array_ite(cond, tru, fals)
    }
    pub fn implies(&self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.ctx.borrow_mut().implies(a, b)
    }
    pub fn greater_signed(&self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.ctx.borrow_mut().greater_signed(a, b)
    }

    pub fn greater(&self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.ctx.borrow_mut().greater(a, b)
    }
    pub fn greater_or_equal_signed(&self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.ctx.borrow_mut().greater_or_equal_signed(a, b)
    }

    pub fn greater_or_equal(&self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.ctx.borrow_mut().greater_or_equal(a, b)
    }
    pub fn not(&self, e: ExprRef) -> ExprRef {
        self.ctx.borrow_mut().not(e)
    }
    pub fn negate(&self, e: ExprRef) -> ExprRef {
        self.ctx.borrow_mut().negate(e)
    }
    pub fn and(&self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.ctx.borrow_mut().and(a, b)
    }
    pub fn or(&self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.ctx.borrow_mut().or(a, b)
    }
    pub fn xor(&self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.ctx.borrow_mut().xor(a, b)
    }
    pub fn shift_left(&self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.ctx.borrow_mut().shift_left(a, b)
    }
    pub fn arithmetic_shift_right(&self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.ctx.borrow_mut().arithmetic_shift_right(a, b)
    }
    pub fn shift_right(&self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.ctx.borrow_mut().shift_right(a, b)
    }
    pub fn add(&self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.ctx.borrow_mut().add(a, b)
    }
    pub fn sub(&self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.ctx.borrow_mut().sub(a, b)
    }
    pub fn mul(&self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.ctx.borrow_mut().mul(a, b)
    }
    pub fn div(&self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.ctx.borrow_mut().div(a, b)
    }
    pub fn signed_div(&self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.ctx.borrow_mut().signed_div(a, b)
    }
    pub fn signed_mod(&self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.ctx.borrow_mut().signed_mod(a, b)
    }
    pub fn signed_remainder(&self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.ctx.borrow_mut().signed_remainder(a, b)
    }
    pub fn remainder(&self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.ctx.borrow_mut().remainder(a, b)
    }
    pub fn concat(&self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.ctx.borrow_mut().concat(a, b)
    }
    pub fn slice(&self, e: ExprRef, hi: WidthInt, lo: WidthInt) -> ExprRef {
        self.ctx.borrow_mut().slice(e, hi, lo)
    }
    pub fn zero_extend(&self, e: ExprRef, by: WidthInt) -> ExprRef {
        self.ctx.borrow_mut().zero_extend(e, by)
    }
    pub fn sign_extend(&self, e: ExprRef, by: WidthInt) -> ExprRef {
        self.ctx.borrow_mut().sign_extend(e, by)
    }

    pub fn array_store(&self, array: ExprRef, index: ExprRef, data: ExprRef) -> ExprRef {
        self.ctx.borrow_mut().array_store(array, index, data)
    }

    pub fn array_const(&self, e: ExprRef, index_width: WidthInt) -> ExprRef {
        self.ctx.borrow_mut().array_const(e, index_width)
    }

    pub fn array_read(&self, array: ExprRef, index: ExprRef) -> ExprRef {
        self.ctx.borrow_mut().array_read(array, index)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::SerializableIrNode;

    #[test]
    fn ir_type_size() {
        assert_eq!(std::mem::size_of::<StringRef>(), 2);
        assert_eq!(std::mem::size_of::<ExprRef>(), 4);
    }

    #[test]
    fn reference_ids() {
        let mut ctx = Context::default();
        let str_id0 = ctx.string("a".into());
        let id0 = ctx.add_expr(Expr::BVSymbol {
            name: str_id0,
            width: 1,
        });
        assert_eq!(id0.0.get(), 1, "ids start at one (for now)");
        let id0_b = ctx.add_expr(Expr::BVSymbol {
            name: str_id0,
            width: 1,
        });
        assert_eq!(id0.0, id0_b.0, "ids should be interned!");
        let id1 = ctx.add_expr(Expr::BVSymbol {
            name: str_id0,
            width: 2,
        });
        assert_eq!(id0.0.get() + 1, id1.0.get(), "ids should increment!");
    }

    /// make sure that we can intern a lot of strings before running out of IDs
    #[test]
    fn intern_lots_of_strings() {
        let mut ctx = Context::default();
        // we loose 1 ID since 0 is not a valid ID value
        let max_strings = (1u64 << 16) - 1;
        for ii in 0..max_strings {
            let value = format!("{ii}AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA");
            let _id = ctx.string(value.into());
        }
        // now that we have used up all the IDs, we should still be able to "add" strings that
        // are already part of the context
        let first = "0AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA";
        assert_eq!(ctx.string(first.into()).index(), 0);
    }

    #[test]
    fn test_builder() {
        let mut ctx = Context::default();
        let expr = ctx.build(|b| b.and(b.bv_symbol("a", 1), b.bv_symbol("b", 1)));
        assert_eq!(expr.serialize_to_str(&ctx), "and(a, b)");
    }
}
