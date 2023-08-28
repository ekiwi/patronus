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

#[derive(Debug, PartialEq, Eq, Clone, Hash, Copy)]
pub struct BVType(WidthInt);
#[derive(Debug, PartialEq, Eq, Clone, Hash, Copy)]
pub struct ArrayType {
    index_width: WidthInt,
    data_width: WidthInt,
}
#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub enum Type {
    BV(WidthInt),
    Array(ArrayType),
}

#[derive(Debug, Clone)]
pub struct TypeCheckError {
    msg: String,
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
            Expr::BVSymbol { name, width } => Ok(Type::BV(width)),
            Expr::BVLiteral { value, width } => Ok(Type::BV(width)),
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
            Expr::BVEqual(a, b) => expect_same_width_bvs(ctx, "bit-vector equality", a, b),
            Expr::BVImplies(a, b) => {
                a.type_check(ctx)?.expect_bv("implies")?;
                b.type_check(ctx)?.expect_bv("implies")?;
                Ok(Type::BV(1))
            }
            Expr::BVGreater(a, b) => expect_same_width_bvs(ctx, "greater", a, b),
            Expr::BVGreaterSigned(a, b) => expect_same_width_bvs(ctx, "greater signed", a, b),
            Expr::BVGreaterEqual(a, b) => expect_same_width_bvs(ctx, "greater or equals", a, b),
            Expr::BVGreaterEqualSigned(a, b) => {
                expect_same_width_bvs(ctx, "greater or equals signed", a, b)
            }
            Expr::BVConcat(a, b) => expect_same_width_bvs(ctx, "concatenation", a, b),
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
                tru.type_check(ctx)?.expect_bv_of(1, "ite condition")?;
                expect_same_width_bvs(ctx, "ite branches", tru, fals)
            }
            Expr::ArraySymbol {
                name,
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
            Expr::ArrayEqual(a, b) => Err(TypeCheckError {
                msg: format!("TODO"),
            }),
            Expr::ArrayStore { .. } => Err(TypeCheckError {
                msg: format!("TODO"),
            }),
            Expr::ArrayIte { .. } => Err(TypeCheckError {
                msg: format!("TODO"),
            }),
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

        // 4 bytes for the tag, 4 * 3 bytes for the largest field
        assert_eq!(std::mem::size_of::<Expr>(), 16);
        // we only represents widths up to (2^32 - 1)
        assert_eq!(std::mem::size_of::<WidthInt>(), 4);
        // an array has a index and a data width
        assert_eq!(std::mem::size_of::<ArrayType>(), 2 * 4);
        // Type could be a bit-vector or an array type (4 bytes for the tag!)
        assert_eq!(std::mem::size_of::<Type>(), 2 * 4 + 4);
    }

    #[test]
    fn simple_serialization() {
        let mut ctx = Context::default();
        let test_expr = ctx.bv_symbol("test", 3);
        assert_eq!("test", test_expr.serialize_to_str(&ctx));
    }
}
