// Copyright 2023 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

/// This type restricts the maximum width that a bit-vector type is allowed to have in our IR.
pub type WidthInt = u32;

/// This restricts the maximum value that a bit-vector literal can carry.
pub type BVLiteralInt = u64;

/// Add an IR node to the context.
pub trait AddNode<D, I: Clone + Copy> {
    /// Add a new value to the context obtaining a reference
    fn add(&mut self, val: D) -> I;
}

/// Lookup an IR node from the context
pub trait GetNode<D: ?Sized, I: Clone + Copy> {
    /// Lookup the value by the reference obtained from a call to add
    fn get(&self, reference: I) -> &D;
}

/// Convenience methods to construct IR nodes.
pub trait NodeConstruction: AddNode<String, StringRef> + AddNode<Expr, ExprRef> {
    // helper functions to construct expressions
    fn bv_literal(&mut self, value: BVLiteralInt, width: WidthInt) -> ExprRef {
        self.add(Expr::BVLiteral { value, width })
    }
    fn bv_symbol(&mut self, name: &str, width: WidthInt) -> ExprRef {
        let name_ref = self.add(name.to_string());
        self.add(Expr::BVSymbol {
            name: name_ref,
            width,
        })
    }
}

type StringInternerU16 = string_interner::StringInterner<
    string_interner::DefaultBackend<string_interner::symbol::SymbolU16>,
>;

/// The actual context implementation.
struct Context {
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

impl AddNode<String, StringRef> for Context {
    fn add(&mut self, value: String) -> StringRef {
        StringRef(self.strings.get_or_intern(value))
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
    fn add(&mut self, value: Expr) -> ExprRef {
        let (index, _) = self.exprs.insert_full(value);
        ExprRef(index as u32)
    }
}

impl GetNode<Expr, ExprRef> for Context {
    fn get(&self, reference: ExprRef) -> &Expr {
        self.exprs
            .get_index(reference.0 as usize)
            .expect("Invalid ExprRef!")
    }
}

impl NodeConstruction for Context {}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub struct StringRef(string_interner::symbol::SymbolU16);
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub struct ExprRef(u32);

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
    },
    BVSignExt {
        e: ExprRef,
        by: WidthInt,
    },
    BVSlice {
        e: ExprRef,
        hi: WidthInt,
        lo: WidthInt,
    },
    BVNot(ExprRef),
    BVNegate(ExprRef),
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
    BVConcat(ExprRef, ExprRef),
    // binary arithmetic
    BVAnd(ExprRef, ExprRef),
    BVOr(ExprRef, ExprRef),
    BVXor(ExprRef, ExprRef),
    BVShiftLeft(ExprRef, ExprRef),
    BVArithmeticShiftRight(ExprRef, ExprRef),
    BVShiftRight(ExprRef, ExprRef),
    BVAdd(ExprRef, ExprRef),
    BVMul(ExprRef, ExprRef),
    BVSignedDiv(ExprRef, ExprRef),
    BVUnsignedDiv(ExprRef, ExprRef),
    BVSignedMod(ExprRef, ExprRef),
    BVSignedRem(ExprRef, ExprRef),
    BVUnsignedRem(ExprRef, ExprRef),
    BVSub(ExprRef, ExprRef),
    //
    BVArrayRead {
        array: ExprRef,
        index: ExprRef,
    },
    // ternary op
    BVIte {
        cond: ExprRef,
        tru: ExprRef,
        fals: ExprRef,
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

pub enum SignalKind {
    Node,
    Output,
}

pub struct Signal {
    name: StringRef,
    kind: SignalKind,
    expr: ExprRef,
}

pub struct State {
    symbol: ExprRef,
    init: Option<ExprRef>,
    next: Option<ExprRef>,
}

pub struct TransitionSystem {
    name: StringRef,
    states: Vec<State>,
    inputs: Vec<ExprRef>,
    signals: Vec<Signal>,
}

trait SerializableIrNode {
    fn serialize(&self, ctx: &Context, writer: &mut impl (std::io::Write)) -> std::io::Result<()>;
    fn serialize_to_str(&self, ctx: &Context) -> String {
        let mut buf = Vec::new();
        self.serialize(ctx, &mut buf)
            .expect("Failed to write to string!");
        String::from_utf8(buf).expect("Failed to read string we wrote!")
    }
}

impl SerializableIrNode for Expr {
    fn serialize(&self, ctx: &Context, writer: &mut impl (std::io::Write)) -> std::io::Result<()> {
        match *self {
            Expr::BVSymbol { name, .. } => write!(writer, "{}", ctx.get(name)),
            Expr::BVLiteral { value, width } => {
                if width <= 8 {
                    write!(writer, "{width}'b{value:b}")
                } else {
                    write!(writer, "{width}'x{value:x}")
                }
            }
            Expr::BVZeroExt { e, by } => {
                write!(writer, "zext(")?;
                e.serialize(ctx, writer)?;
                write!(writer, ", {by})")
            }
            Expr::BVSignExt { e, by } => {
                write!(writer, "sext(")?;
                e.serialize(ctx, writer)?;
                write!(writer, ", {by})")
            }
            Expr::BVSlice { e, hi, lo } => {
                e.serialize(ctx, writer)?;
                if hi == lo {
                    write!(writer, "[{hi}]")
                } else {
                    write!(writer, "[{hi}:{lo}]")
                }
            }
            Expr::BVNot(e) => {
                write!(writer, "not(")?;
                e.serialize(ctx, writer)?;
                write!(writer, ")")
            }
            Expr::BVNegate(e) => {
                write!(writer, "neg(")?;
                e.serialize(ctx, writer)?;
                write!(writer, ")")
            }
            Expr::BVReduceOr(e) => {
                write!(writer, "redor(")?;
                e.serialize(ctx, writer)?;
                write!(writer, ")")
            }
            Expr::BVReduceAnd(e) => {
                write!(writer, "redand(")?;
                e.serialize(ctx, writer)?;
                write!(writer, ")")
            }
            Expr::BVReduceXor(e) => {
                write!(writer, "redxor(")?;
                e.serialize(ctx, writer)?;
                write!(writer, ")")
            }
            Expr::BVEqual(a, b) => {
                write!(writer, "eq(")?;
                a.serialize(ctx, writer)?;
                write!(writer, ", ")?;
                b.serialize(ctx, writer)?;
                write!(writer, ")")
            }
            Expr::BVImplies(a, b) => {
                write!(writer, "implies(")?;
                a.serialize(ctx, writer)?;
                write!(writer, ", ")?;
                b.serialize(ctx, writer)?;
                write!(writer, ")")
            }
            Expr::BVGreater(a, b) => {
                write!(writer, "ugt(")?;
                a.serialize(ctx, writer)?;
                write!(writer, ", ")?;
                b.serialize(ctx, writer)?;
                write!(writer, ")")
            }
            Expr::BVGreaterSigned(a, b) => {
                write!(writer, "sgt(")?;
                a.serialize(ctx, writer)?;
                write!(writer, ", ")?;
                b.serialize(ctx, writer)?;
                write!(writer, ")")
            }
            Expr::BVGreaterEqual(a, b) => {
                write!(writer, "ugte(")?;
                a.serialize(ctx, writer)?;
                write!(writer, ", ")?;
                b.serialize(ctx, writer)?;
                write!(writer, ")")
            }
            Expr::BVGreaterEqualSigned(a, b) => {
                write!(writer, "sgte(")?;
                a.serialize(ctx, writer)?;
                write!(writer, ", ")?;
                b.serialize(ctx, writer)?;
                write!(writer, ")")
            }
            Expr::BVConcat(a, b) => {
                write!(writer, "concat(")?;
                a.serialize(ctx, writer)?;
                write!(writer, ", ")?;
                b.serialize(ctx, writer)?;
                write!(writer, ")")
            }
            Expr::BVAnd(a, b) => {
                write!(writer, "and(")?;
                a.serialize(ctx, writer)?;
                write!(writer, ", ")?;
                b.serialize(ctx, writer)?;
                write!(writer, ")")
            }
            Expr::BVOr(a, b) => {
                write!(writer, "or(")?;
                a.serialize(ctx, writer)?;
                write!(writer, ", ")?;
                b.serialize(ctx, writer)?;
                write!(writer, ")")
            }
            Expr::BVXor(a, b) => {
                write!(writer, "xor(")?;
                a.serialize(ctx, writer)?;
                write!(writer, ", ")?;
                b.serialize(ctx, writer)?;
                write!(writer, ")")
            }
            Expr::BVShiftLeft(a, b) => {
                write!(writer, "logical_shift_left(")?;
                a.serialize(ctx, writer)?;
                write!(writer, ", ")?;
                b.serialize(ctx, writer)?;
                write!(writer, ")")
            }
            Expr::BVArithmeticShiftRight(a, b) => {
                write!(writer, "arithmetic_shift_right(")?;
                a.serialize(ctx, writer)?;
                write!(writer, ", ")?;
                b.serialize(ctx, writer)?;
                write!(writer, ")")
            }
            Expr::BVShiftRight(a, b) => {
                write!(writer, "logical_shift_right(")?;
                a.serialize(ctx, writer)?;
                write!(writer, ", ")?;
                b.serialize(ctx, writer)?;
                write!(writer, ")")
            }
            Expr::BVAdd(a, b) => {
                write!(writer, "add(")?;
                a.serialize(ctx, writer)?;
                write!(writer, ", ")?;
                b.serialize(ctx, writer)?;
                write!(writer, ")")
            }
            Expr::BVMul(a, b) => {
                write!(writer, "mul(")?;
                a.serialize(ctx, writer)?;
                write!(writer, ", ")?;
                b.serialize(ctx, writer)?;
                write!(writer, ")")
            }
            Expr::BVSignedDiv(a, b) => {
                write!(writer, "sdiv(")?;
                a.serialize(ctx, writer)?;
                write!(writer, ", ")?;
                b.serialize(ctx, writer)?;
                write!(writer, ")")
            }
            Expr::BVUnsignedDiv(a, b) => {
                write!(writer, "udiv(")?;
                a.serialize(ctx, writer)?;
                write!(writer, ", ")?;
                b.serialize(ctx, writer)?;
                write!(writer, ")")
            }
            Expr::BVSignedMod(a, b) => {
                write!(writer, "smod(")?;
                a.serialize(ctx, writer)?;
                write!(writer, ", ")?;
                b.serialize(ctx, writer)?;
                write!(writer, ")")
            }
            Expr::BVSignedRem(a, b) => {
                write!(writer, "srem(")?;
                a.serialize(ctx, writer)?;
                write!(writer, ", ")?;
                b.serialize(ctx, writer)?;
                write!(writer, ")")
            }
            Expr::BVUnsignedRem(a, b) => {
                write!(writer, "urem(")?;
                a.serialize(ctx, writer)?;
                write!(writer, ", ")?;
                b.serialize(ctx, writer)?;
                write!(writer, ")")
            }
            Expr::BVSub(a, b) => {
                write!(writer, "sub(")?;
                a.serialize(ctx, writer)?;
                write!(writer, ", ")?;
                b.serialize(ctx, writer)?;
                write!(writer, ")")
            }
            Expr::BVArrayRead { array, index } => {
                array.serialize(ctx, writer)?;
                write!(writer, "[")?;
                index.serialize(ctx, writer)?;
                write!(writer, "]")
            }
            Expr::BVIte { cond, tru, fals } => {
                write!(writer, "ite(")?;
                cond.serialize(ctx, writer)?;
                write!(writer, ", ")?;
                tru.serialize(ctx, writer)?;
                write!(writer, ", ")?;
                fals.serialize(ctx, writer)?;
                write!(writer, ")")
            }
            Expr::ArraySymbol { name, .. } => write!(writer, "{}", ctx.get(name)),
            Expr::ArrayConstant { e, index_width } => {
                write!(writer, "([")?;
                e.serialize(ctx, writer)?;
                write!(writer, "] x 2^{index_width})")
            }
            Expr::ArrayEqual(a, b) => {
                write!(writer, "eq(")?;
                a.serialize(ctx, writer)?;
                write!(writer, ", ")?;
                b.serialize(ctx, writer)?;
                write!(writer, ")")
            }
            Expr::ArrayStore { array, index, data } => {
                array.serialize(ctx, writer)?;
                write!(writer, "[")?;
                index.serialize(ctx, writer)?;
                write!(writer, " := ")?;
                data.serialize(ctx, writer)?;
                write!(writer, "]")
            }
            Expr::ArrayIte { cond, tru, fals } => {
                write!(writer, "ite(")?;
                cond.serialize(ctx, writer)?;
                write!(writer, ", ")?;
                tru.serialize(ctx, writer)?;
                write!(writer, ", ")?;
                fals.serialize(ctx, writer)?;
                write!(writer, ")")
            }
        }
    }
}

impl SerializableIrNode for ExprRef {
    fn serialize(&self, ctx: &Context, writer: &mut impl (std::io::Write)) -> std::io::Result<()> {
        ctx.get(*self).serialize(ctx, writer)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ir_type_size() {
        assert_eq!(std::mem::size_of::<StringRef>(), 2);
        assert_eq!(std::mem::size_of::<ExprRef>(), 4);
        assert_eq!(std::mem::size_of::<WidthInt>(), 4);
        // 4 bytes for the tag, 4 * 3 bytes for the largest field
        assert_eq!(std::mem::size_of::<Expr>(), 16);
    }

    #[test]
    fn simple_serialization() {
        let mut ctx = Context::default();
        let test_expr = ctx.bv_symbol("test", 3);
        assert_eq!("test", test_expr.serialize_to_str(&ctx));
    }
}
