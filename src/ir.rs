// Copyright 2023 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

/// This type restricts the maximum width that a bit-vector type is allowed to have in our IR.
pub type WidthInt = u32;

/// IR Nodes are only valid with their context
pub trait Context {
    fn add();
    fn get_string(reference: StringRef) -> String;
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct StringRef(u16);
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct BVExprRef(u32);
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct ArrayExprRef(u32);


#[derive(Debug, PartialEq, Eq, Clone)]
pub enum STMExpr {
    BitVec(BVExpr)
}


#[derive(Debug, PartialEq, Eq, Clone)]
/// Represents a SMT bit-vector expression.
pub enum BVExpr {
    // nullary
    Symbol{ name : StringRef, width: WidthInt},
    // TODO: support literals that do not fit into 64-bit
    Literal { value: u64, width: WidthInt},
    // unary operations
    ZeroExt { e: BVExprRef, by: WidthInt },
    SignExt { e: BVExprRef, by: WidthInt },
    Slice { e: BVExprRef, hi: WidthInt, lo: WidthInt },
    Not(BVExprRef),
    Negate(BVExprRef),
    ReduceOr(BVExprRef),
    ReduceAnd(BVExprRef),
    ReduceXor(BVExprRef),
    // binary operations
    Equal(BVExprRef, BVExprRef),
    Implies(BVExprRef, BVExprRef),
    Greater(BVExprRef, BVExprRef),
    GreaterEqual(BVExprRef, BVExprRef),
    Concat(BVExprRef, BVExprRef),
    // binary arithmetic
    And(BVExprRef, BVExprRef),
    Or(BVExprRef, BVExprRef),
    Xor(BVExprRef, BVExprRef),
    ShiftLeft(BVExprRef, BVExprRef),
    ArithmeticShiftRight(BVExprRef, BVExprRef),
    ShiftRight(BVExprRef, BVExprRef),
    Add(BVExprRef, BVExprRef),
    Mul(BVExprRef, BVExprRef),
    SignedDiv(BVExprRef, BVExprRef),
    UnsignedDiv(BVExprRef, BVExprRef),
    SignedMod(BVExprRef, BVExprRef),
    SignedRem(BVExprRef, BVExprRef),
    UnsignedRem(BVExprRef, BVExprRef),
    Sub(BVExprRef, BVExprRef),
    //
    ArrayRead { array: ArrayExprRef, index: BVExprRef },
    // ternary op
    Ite { cond: BVExprRef, tru: BVExprRef, fals: BVExprRef},
}

#[derive(Debug, PartialEq, Eq, Clone)]
/// Represents a SMT array expression.
pub enum ArrayExpr {
    // nullary
    Symbol{ name : StringRef, index_width: WidthInt, data_width: WidthInt },
    // unary
    Constant { e: BVExprRef, index_width: WidthInt },
    // binary
    Equal(ArrayExprRef, ArrayExprRef),
    // ternary
    Store{ array: ArrayExprRef, index: BVExprRef, data: BVExprRef },
    Ite { cond: BVExprRef, tru: ArrayExprRef, fals: ArrayExprRef },
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ir_type_size() {
        assert_eq!(std::mem::size_of::<StringRef>(), 2);
        assert_eq!(std::mem::size_of::<BVExprRef>(), 4);
        assert_eq!(std::mem::size_of::<WidthInt>(), 4);
        // 4 bytes for the tag, 4 * 3 bytes for the largest field
        assert_eq!(std::mem::size_of::<BVExpr>(), 16);
        // 4 bytes for the tag, 4 * 3 bytes for the largest field
        assert_eq!(std::mem::size_of::<ArrayExpr>(), 16);
    }
}