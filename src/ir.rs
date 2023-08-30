// Copyright 2023 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

use std::fmt::{Display, Formatter};

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
pub trait ExprNodeConstruction: AddNode<String, StringRef> + AddNode<Expr, ExprRef> {
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
    fn bv_lit(&mut self, value: BVLiteralInt, width: WidthInt) -> ExprRef {
        assert!(bv_value_fits_width(value, width));
        self.add(Expr::BVLiteral { value, width })
    }
    fn zero(&mut self, width: WidthInt) -> ExprRef {
        self.bv_lit(0, width)
    }
    fn one(&mut self, width: WidthInt) -> ExprRef {
        self.bv_lit(1, width)
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
        self.add(name)
    }

    fn is_interned(&self, value: &str) -> bool {
        self.strings.get(value).is_some()
    }
}

impl AddNode<String, StringRef> for Context {
    fn add(&mut self, value: String) -> StringRef {
        StringRef(self.strings.get_or_intern(value))
    }
}

impl AddNode<&str, StringRef> for Context {
    fn add(&mut self, value: &str) -> StringRef {
        self.add(value.to_owned())
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

impl ExprNodeConstruction for Context {}

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

impl Display for Type {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match *self {
            Type::BV(width) => write!(f, "bv<{width}>"),
            Type::Array(ArrayType {
                index_width,
                data_width,
            }) => write!(f, "bv<{index_width}> -> bv<{data_width}>"),
        }
    }
}

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

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub enum SignalKind {
    Node,
    Output,
}

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct Signal {
    pub name: Option<String>,
    pub expr: ExprRef,
    pub kind: SignalKind,
}
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub struct SignalRef(usize);

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct State {
    pub symbol: ExprRef,
    pub init: Option<ExprRef>,
    pub next: Option<ExprRef>,
}
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub struct StateRef(usize);

#[derive(Debug, PartialEq, Eq)]
pub struct TransitionSystem {
    name: StringRef,
    states: Vec<State>,
    inputs: Vec<ExprRef>,
    signals: Vec<Signal>,
}

impl TransitionSystem {
    pub fn new(name: StringRef) -> Self {
        TransitionSystem {
            name,
            states: Vec::default(),
            inputs: Vec::default(),
            signals: Vec::default(),
        }
    }

    pub fn add_signal(&mut self, expr: ExprRef, kind: SignalKind) -> SignalRef {
        let id = self.signals.len();
        self.signals.push(Signal {
            name: None,
            expr,
            kind,
        });
        SignalRef(id)
    }

    pub fn add_state(&mut self, ctx: &impl GetNode<Expr, ExprRef>, symbol: ExprRef) -> StateRef {
        assert!(symbol.is_symbol(ctx));
        let id = self.states.len();
        self.states.push(State {
            symbol,
            init: None,
            next: None,
        });
        StateRef(id)
    }

    pub fn modify_state<F>(&mut self, reference: StateRef, modify: F)
    where
        F: FnOnce(&mut State) -> (),
    {
        modify(self.states.get_mut(reference.0).unwrap())
    }
}

impl GetNode<Signal, SignalRef> for TransitionSystem {
    fn get(&self, reference: SignalRef) -> &Signal {
        &self.signals[reference.0]
    }
}

impl GetNode<State, StateRef> for TransitionSystem {
    fn get(&self, reference: StateRef) -> &State {
        &self.states[reference.0]
    }
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
    fn reference_ids() {
        let mut ctx = Context::default();
        let str_id0 = ctx.add("a");
        let id0 = ctx.add(Expr::BVSymbol {
            name: str_id0,
            width: 1,
        });
        assert_eq!(id0.0, 0, "ids start at zero (for now)");
        let id0_b = ctx.add(Expr::BVSymbol {
            name: str_id0,
            width: 1,
        });
        assert_eq!(id0.0, id0_b.0, "ids should be interned!");
        let id1 = ctx.add(Expr::BVSymbol {
            name: str_id0,
            width: 2,
        });
        assert_eq!(id0.0 + 1, id1.0, "ids should increment!");
    }

    #[test]
    fn simple_serialization() {
        let mut ctx = Context::default();
        let test_expr = ctx.bv_symbol("test", 3);
        assert_eq!("test", test_expr.serialize_to_str(&ctx));
    }
}
