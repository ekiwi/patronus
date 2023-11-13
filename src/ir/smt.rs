// Copyright 2023 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

use crate::ir::TypeCheck;
use std::num::NonZeroU32;

/// This type restricts the maximum width that a bit-vector type is allowed to have in our IR.
pub type WidthInt = u32;

/// This restricts the maximum value that a bit-vector literal can carry.
pub type BVLiteralInt = u64;

/// Add an IR node to the context.
pub trait AddNode<D, I: Clone + Copy> {
    /// Add a new value to the context obtaining a reference
    fn add_node(&mut self, val: D) -> I;
}

/// Lookup an IR node from the context
pub trait GetNode<D: ?Sized, I: Clone + Copy> {
    /// Lookup the value by the reference obtained from a call to add
    fn get(&self, reference: I) -> &D;
}

/// Convenience methods to construct IR nodes.
pub trait ExprNodeConstruction:
    AddNode<String, StringRef> + AddNode<Expr, ExprRef> + GetNode<Expr, ExprRef> + Sized
{
    // helper functions to construct expressions
    fn bv_symbol(&mut self, name: &str, width: WidthInt) -> ExprRef {
        let name_ref = self.add_node(name.to_string());
        self.add_node(Expr::BVSymbol {
            name: name_ref,
            width,
        })
    }
    fn symbol(&mut self, name: StringRef, tpe: Type) -> ExprRef {
        self.add_node(Expr::symbol(name, tpe))
    }
    fn bv_lit(&mut self, value: BVLiteralInt, width: WidthInt) -> ExprRef {
        assert!(bv_value_fits_width(value, width));
        self.add_node(Expr::BVLiteral { value, width })
    }
    fn zero(&mut self, width: WidthInt) -> ExprRef {
        self.bv_lit(0, width)
    }
    fn one(&mut self, width: WidthInt) -> ExprRef {
        self.bv_lit(1, width)
    }
    fn bv_equal(&mut self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.add_node(Expr::BVEqual(a, b))
    }
    fn bv_ite(&mut self, cond: ExprRef, tru: ExprRef, fals: ExprRef) -> ExprRef {
        self.add_node(Expr::BVIte { cond, tru, fals })
    }
    fn implies(&mut self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.add_node(Expr::BVImplies(a, b))
    }
    fn greater_signed(&mut self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.add_node(Expr::BVGreaterSigned(a, b))
    }

    fn greater(&mut self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.add_node(Expr::BVGreaterSigned(a, b))
    }
    fn greater_or_equal_signed(&mut self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.add_node(Expr::BVGreaterEqualSigned(a, b))
    }

    fn greater_or_equal(&mut self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.add_node(Expr::BVGreaterEqual(a, b))
    }
    fn not(&mut self, e: ExprRef) -> ExprRef {
        self.add_node(Expr::BVNot(e, e.get_bv_type(self).unwrap()))
    }
    fn and(&mut self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.add_node(Expr::BVAnd(a, b, b.get_bv_type(self).unwrap()))
    }
    fn or(&mut self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.add_node(Expr::BVOr(a, b, b.get_bv_type(self).unwrap()))
    }
    fn xor(&mut self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.add_node(Expr::BVXor(a, b, b.get_bv_type(self).unwrap()))
    }
    fn shift_left(&mut self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.add_node(Expr::BVShiftLeft(a, b, b.get_bv_type(self).unwrap()))
    }
    fn arithmetic_shift_right(&mut self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.add_node(Expr::BVArithmeticShiftRight(
            a,
            b,
            b.get_bv_type(self).unwrap(),
        ))
    }
    fn shift_right(&mut self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.add_node(Expr::BVShiftRight(a, b, b.get_bv_type(self).unwrap()))
    }
    fn add(&mut self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.add_node(Expr::BVAdd(a, b, b.get_bv_type(self).unwrap()))
    }
    fn sub(&mut self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.add_node(Expr::BVSub(a, b, b.get_bv_type(self).unwrap()))
    }
    fn mul(&mut self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.add_node(Expr::BVMul(a, b, b.get_bv_type(self).unwrap()))
    }
    fn div(&mut self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.add_node(Expr::BVUnsignedDiv(a, b, b.get_bv_type(self).unwrap()))
    }
    fn signed_div(&mut self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.add_node(Expr::BVSignedDiv(a, b, b.get_bv_type(self).unwrap()))
    }
    fn signed_mod(&mut self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.add_node(Expr::BVSignedMod(a, b, b.get_bv_type(self).unwrap()))
    }
    fn signed_remainder(&mut self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.add_node(Expr::BVSignedRem(a, b, b.get_bv_type(self).unwrap()))
    }
    fn remainder(&mut self, a: ExprRef, b: ExprRef) -> ExprRef {
        self.add_node(Expr::BVUnsignedRem(a, b, b.get_bv_type(self).unwrap()))
    }
    fn concat(&mut self, a: ExprRef, b: ExprRef) -> ExprRef {
        let width = a.get_bv_type(self).unwrap() + b.get_bv_type(self).unwrap();
        self.add_node(Expr::BVConcat(a, b, width))
    }
    fn slice(&mut self, e: ExprRef, hi: WidthInt, lo: WidthInt) -> ExprRef {
        self.add_node(Expr::BVSlice { e, hi, lo })
    }
    fn zero_extend(&mut self, e: ExprRef, by: WidthInt) -> ExprRef {
        let width = e.get_bv_type(self).unwrap() + by;
        self.add_node(Expr::BVZeroExt { e, by, width })
    }
    fn sign_extend(&mut self, e: ExprRef, by: WidthInt) -> ExprRef {
        let width = e.get_bv_type(self).unwrap() + by;
        self.add_node(Expr::BVSignExt { e, by, width })
    }
}

pub fn bv_value_fits_width(value: BVLiteralInt, width: WidthInt) -> bool {
    let bits_required = BVLiteralInt::BITS - value.leading_zeros();
    width >= bits_required
}

type StringInternerU16 = string_interner::StringInterner<
    string_interner::DefaultBackend<string_interner::symbol::SymbolU16>,
>;

/// The actual context implementation.
pub struct Context {
    strings: StringInternerU16,
    exprs: indexmap::IndexSet<Expr>,
}

impl Default for Context {
    fn default() -> Self {
        Context {
            strings: StringInternerU16::new(),
            exprs: indexmap::IndexSet::default(),
        }
    }
}

impl Context {
    /// ensures that the value is unique (by appending a number if necessary) and then adds it to the store
    pub fn add_unique_str(&mut self, value: &str) -> StringRef {
        let mut name: String = value.to_string();
        let mut count: usize = 0;
        while self.is_interned(value) {
            name = format!("{value}_{count}");
            count += 1;
        }
        self.add_node(name)
    }

    fn is_interned(&self, value: &str) -> bool {
        self.strings.get(value).is_some()
    }
}

impl AddNode<String, StringRef> for Context {
    fn add_node(&mut self, value: String) -> StringRef {
        StringRef(self.strings.get_or_intern(value))
    }
}

impl AddNode<&str, StringRef> for Context {
    fn add_node(&mut self, value: &str) -> StringRef {
        self.add_node(value.to_owned())
    }
}

impl GetNode<str, StringRef> for Context {
    fn get(&self, reference: StringRef) -> &str {
        self.strings
            .resolve(reference.0)
            .expect("Invalid StringRef!")
    }
}

impl AddNode<Expr, ExprRef> for Context {
    fn add_node(&mut self, value: Expr) -> ExprRef {
        let (index, _) = self.exprs.insert_full(value);
        ExprRef(NonZeroU32::new((index + 1) as u32).unwrap())
    }
}

impl GetNode<Expr, ExprRef> for Context {
    fn get(&self, reference: ExprRef) -> &Expr {
        self.exprs
            .get_index((reference.0.get() as usize) - 1)
            .expect("Invalid ExprRef!")
    }
}

impl ExprNodeConstruction for Context {}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub struct StringRef(string_interner::symbol::SymbolU16);
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub struct ExprRef(NonZeroU32);

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
/// Represents a SMT bit-vector or array expression.
pub enum Expr {
    // Bit-Vector Expressions
    // nullary
    BVSymbol {
        name: StringRef,
        width: WidthInt,
    },
    // TODO: support literals that do not fit into 64-bit
    BVLiteral {
        value: BVLiteralInt,
        width: WidthInt,
    },
    // unary operations
    BVZeroExt {
        e: ExprRef,
        by: WidthInt,
        width: WidthInt,
    },
    BVSignExt {
        e: ExprRef,
        by: WidthInt,
        width: WidthInt,
    },
    BVSlice {
        e: ExprRef,
        hi: WidthInt,
        lo: WidthInt,
        // no `width` since it is easy to calculate from `hi` and `lo` without looking at `e`
    },
    BVNot(ExprRef, WidthInt),
    BVNegate(ExprRef, WidthInt),
    BVReduceOr(ExprRef),
    BVReduceAnd(ExprRef),
    BVReduceXor(ExprRef),
    // binary operations
    BVEqual(ExprRef, ExprRef),
    BVImplies(ExprRef, ExprRef),
    BVGreater(ExprRef, ExprRef),
    BVGreaterSigned(ExprRef, ExprRef),
    BVGreaterEqual(ExprRef, ExprRef),
    BVGreaterEqualSigned(ExprRef, ExprRef),
    BVConcat(ExprRef, ExprRef, WidthInt),
    // binary arithmetic
    BVAnd(ExprRef, ExprRef, WidthInt),
    BVOr(ExprRef, ExprRef, WidthInt),
    BVXor(ExprRef, ExprRef, WidthInt),
    BVShiftLeft(ExprRef, ExprRef, WidthInt),
    BVArithmeticShiftRight(ExprRef, ExprRef, WidthInt),
    BVShiftRight(ExprRef, ExprRef, WidthInt),
    BVAdd(ExprRef, ExprRef, WidthInt),
    BVMul(ExprRef, ExprRef, WidthInt),
    BVSignedDiv(ExprRef, ExprRef, WidthInt),
    BVUnsignedDiv(ExprRef, ExprRef, WidthInt),
    BVSignedMod(ExprRef, ExprRef, WidthInt),
    BVSignedRem(ExprRef, ExprRef, WidthInt),
    BVUnsignedRem(ExprRef, ExprRef, WidthInt),
    BVSub(ExprRef, ExprRef, WidthInt),
    //
    BVArrayRead {
        array: ExprRef,
        index: ExprRef,
        width: WidthInt,
    },
    // ternary op
    BVIte {
        cond: ExprRef,
        tru: ExprRef,
        fals: ExprRef,
        // no width since that would increase the Expr size by 8 bytes (b/c of alignment)
        // width: WidthInt
    },
    // Array Expressions
    // nullary
    ArraySymbol {
        name: StringRef,
        index_width: WidthInt,
        data_width: WidthInt,
    },
    // unary
    ArrayConstant {
        e: ExprRef,
        index_width: WidthInt,
        data_width: WidthInt, // extra info since we have space
    },
    // binary
    ArrayEqual(ExprRef, ExprRef),
    // ternary
    ArrayStore {
        array: ExprRef,
        index: ExprRef,
        data: ExprRef,
    },
    ArrayIte {
        cond: ExprRef,
        tru: ExprRef,
        fals: ExprRef,
    },
}

impl Expr {
    pub fn symbol(name: StringRef, tpe: Type) -> Expr {
        match tpe {
            Type::BV(width) => Expr::BVSymbol { name, width },
            Type::Array(ArrayType {
                data_width,
                index_width,
            }) => Expr::ArraySymbol {
                name,
                data_width,
                index_width,
            },
        }
    }
}

pub trait ExprIntrospection {
    fn is_symbol(&self, ctx: &impl GetNode<Expr, ExprRef>) -> bool;
    fn get_symbol_name<'a>(
        &self,
        ctx: &'a (impl GetNode<Expr, ExprRef> + GetNode<str, StringRef>),
    ) -> Option<&'a str>;
}

impl ExprIntrospection for Expr {
    fn is_symbol(&self, _ctx: &impl GetNode<Expr, ExprRef>) -> bool {
        matches!(self, Expr::BVSymbol { .. } | Expr::ArraySymbol { .. })
    }

    fn get_symbol_name<'a>(
        &self,
        ctx: &'a (impl GetNode<Expr, ExprRef> + GetNode<str, StringRef>),
    ) -> Option<&'a str> {
        match self {
            Expr::BVSymbol { name, .. } => Some(ctx.get(*name)),
            Expr::ArraySymbol { name, .. } => Some(ctx.get(*name)),
            _ => None,
        }
    }
}

impl ExprIntrospection for ExprRef {
    fn is_symbol(&self, ctx: &impl GetNode<Expr, ExprRef>) -> bool {
        ctx.get(*self).is_symbol(ctx)
    }

    fn get_symbol_name<'a>(
        &self,
        ctx: &'a (impl GetNode<Expr, ExprRef> + GetNode<str, StringRef>),
    ) -> Option<&'a str> {
        ctx.get(*self).get_symbol_name(ctx)
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Hash, Copy)]
pub struct BVType(WidthInt);
#[derive(Debug, PartialEq, Eq, Clone, Hash, Copy)]
pub struct ArrayType {
    pub index_width: WidthInt,
    pub data_width: WidthInt,
}
#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub enum Type {
    BV(WidthInt),
    Array(ArrayType),
}

impl Type {
    pub const BOOL: Type = Type::BV(1);
    pub fn is_bit_vector(&self) -> bool {
        match &self {
            Type::BV(_) => true,
            Type::Array(_) => false,
        }
    }
}

impl std::fmt::Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match *self {
            Type::BV(width) => write!(f, "bv<{width}>"),
            Type::Array(ArrayType {
                index_width,
                data_width,
            }) => write!(f, "bv<{index_width}> -> bv<{data_width}>"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ir_type_size() {
        assert_eq!(std::mem::size_of::<StringRef>(), 2);
        assert_eq!(std::mem::size_of::<ExprRef>(), 4);

        // 8 bytes for the tag, 4 * 4 bytes for the largest field
        assert_eq!(std::mem::size_of::<Expr>(), 16);
        // we only represents widths up to (2^32 - 1)
        assert_eq!(std::mem::size_of::<WidthInt>(), 4);
        // an array has a index and a data width
        assert_eq!(std::mem::size_of::<ArrayType>(), 2 * 4);
        // Type could be a bit-vector or an array type (4 bytes for the tag!)
        assert_eq!(std::mem::size_of::<Type>(), 2 * 4 + 4);
    }

    #[test]
    fn reference_ids() {
        let mut ctx = Context::default();
        let str_id0 = ctx.add_node("a");
        let id0 = ctx.add_node(Expr::BVSymbol {
            name: str_id0,
            width: 1,
        });
        assert_eq!(id0.0.get(), 1, "ids start at one (for now)");
        let id0_b = ctx.add_node(Expr::BVSymbol {
            name: str_id0,
            width: 1,
        });
        assert_eq!(id0.0, id0_b.0, "ids should be interned!");
        let id1 = ctx.add_node(Expr::BVSymbol {
            name: str_id0,
            width: 2,
        });
        assert_eq!(id0.0.get() + 1, id1.0.get(), "ids should increment!");
    }
}
