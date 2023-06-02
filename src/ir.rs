// Copyright 2023 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

/// This type restricts the maximum width that a bit-vector type is allowed to have in our IR.
pub type WidthInt = u32;

/// This restricts the maximum value that a bit-vector literal can carry.
pub type BVLiteralInt = u64;

/// IR Nodes are only valid with their context
pub trait Context {
    // helper functions to construct expressions
    fn bv_literal(&mut self, value: BVLiteralInt, width: WidthInt) -> BVExprRef {
        self.add_bv_expr(BVExpr::Literal {value, width})
    }
    fn bv_symbol(&mut self, name: &str, width: WidthInt) -> BVExprRef {
        let name_ref = self.add_string(name.to_string());
        self.add_bv_expr(BVExpr::Symbol {name: name_ref, width })
    }

    // basic functions that need to be implemented by every context
    fn add_string(&mut self, value: String) -> StringRef;
    fn get_string(&self, reference: StringRef) -> String;
    fn add_bv_expr(&mut self, value: BVExpr) -> BVExprRef;
    fn get_bv_expr(&self, reference: BVExprRef) -> BVExpr;

}

#[derive(Default)]
/// simple implementation of a context
struct BasicContext {
    strings: Vec<String>,
    bv_exprs: Vec<BVExpr>,
}

impl Context for BasicContext {
    fn add_string(&mut self, value: String) -> StringRef {
        let index = self.strings.len();
        self.strings.push(value);
        StringRef(index as u16)
    }

    fn get_string(&self, reference: StringRef) -> String {
        self.strings[reference.0 as usize].clone()
    }

    fn add_bv_expr(&mut self, value: BVExpr) -> BVExprRef {
        let index = self.bv_exprs.len();
        self.bv_exprs.push(value);
        BVExprRef(index as u32)
    }

    fn get_bv_expr(&self, reference: BVExprRef) -> BVExpr {
        self.bv_exprs[reference.0 as usize].clone()
    }
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
    Literal { value: BVLiteralInt, width: WidthInt},
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

/// Serialize Expression to custom format
fn serialize_bv_expr<C: Context>(ctx: &C, expr: BVExpr) -> String {
    match expr {
        BVExpr::Symbol { name, .. } => ctx.get_string(name),
        BVExpr::Literal { value, width } =>
            if width <= 8 { format!("{width}'b{value:b}") } else { format!("{width}'x{value:x}") },
        BVExpr::ZeroExt { .. } => format!(""),
        BVExpr::SignExt { .. } => format!(""),
        BVExpr::Slice { .. } => format!(""),
        BVExpr::Not(_) => format!(""),
        BVExpr::Negate(_) => format!(""),
        BVExpr::ReduceOr(_) => format!(""),
        BVExpr::ReduceAnd(_) => format!(""),
        BVExpr::ReduceXor(_) => format!(""),
        BVExpr::Equal(_, _) => format!(""),
        BVExpr::Implies(_, _) => format!(""),
        BVExpr::Greater(_, _) => format!(""),
        BVExpr::GreaterEqual(_, _) => format!(""),
        BVExpr::Concat(_, _) => format!(""),
        BVExpr::And(_, _) => format!(""),
        BVExpr::Or(_, _) => format!(""),
        BVExpr::Xor(_, _) => format!(""),
        BVExpr::ShiftLeft(_, _) => format!(""),
        BVExpr::ArithmeticShiftRight(_, _) => format!(""),
        BVExpr::ShiftRight(_, _) => format!(""),
        BVExpr::Add(_, _) => format!(""),
        BVExpr::Mul(_, _) => format!(""),
        BVExpr::SignedDiv(_, _) => format!(""),
        BVExpr::UnsignedDiv(_, _) => format!(""),
        BVExpr::SignedMod(_, _) => format!(""),
        BVExpr::SignedRem(_, _) => format!(""),
        BVExpr::UnsignedRem(_, _) => format!(""),
        BVExpr::Sub(_, _) => format!(""),
        BVExpr::ArrayRead { .. } => format!(""),
        BVExpr::Ite { .. } => format!(""),
    }
}

fn serialize_bv_expr_ref<C: Context>(ctx: &C, reference: BVExprRef) -> String {
    serialize_bv_expr(ctx, ctx.get_bv_expr(reference))
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

    #[test]
    fn simple_serialization() {
        let mut ctx = BasicContext::default();
        let test_expr = ctx.bv_symbol("test", 3);
        assert_eq!("test", serialize_bv_expr_ref(&ctx, test_expr));
    }
}