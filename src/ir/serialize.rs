// Copyright 2023 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

use super::{Context, Expr, ExprRef, GetNode};
use crate::ir::{SignalKind, TransitionSystem, Type, TypeCheck};
use std::io::Write;

pub trait SerializableIrNode {
    fn serialize(&self, ctx: &Context, writer: &mut impl Write) -> std::io::Result<()>;
    fn serialize_to_str(&self, ctx: &Context) -> String {
        let mut buf = Vec::new();
        self.serialize(ctx, &mut buf)
            .expect("Failed to write to string!");
        String::from_utf8(buf).expect("Failed to read string we wrote!")
    }
}

impl SerializableIrNode for Expr {
    fn serialize(&self, ctx: &Context, writer: &mut impl Write) -> std::io::Result<()> {
        serialize_expr(&self, ctx, writer)
    }
}

/// Internal serialize function for expressions that can be specialized depending on how we want
/// to treat sub-expressions.
fn serialize_expr(expr: &Expr, ctx: &Context, writer: &mut impl Write) -> std::io::Result<()> {
    match expr {
        Expr::BVSymbol { name, .. } => write!(writer, "{}", ctx.get(*name)),
        Expr::BVLiteral { value, width } => {
            if *width <= 8 {
                write!(writer, "{width}'b{value:b}")
            } else {
                write!(writer, "{width}'x{value:x}")
            }
        }
        Expr::BVZeroExt { e, by, .. } => {
            write!(writer, "zext(")?;
            serialize_expr_ref(e, ctx, writer)?;
            write!(writer, ", {by})")
        }
        Expr::BVSignExt { e, by, .. } => {
            write!(writer, "sext(")?;
            serialize_expr_ref(e, ctx, writer)?;
            write!(writer, ", {by})")
        }
        Expr::BVSlice { e, hi, lo, .. } => {
            serialize_expr_ref(e, ctx, writer)?;
            if hi == lo {
                write!(writer, "[{hi}]")
            } else {
                write!(writer, "[{hi}:{lo}]")
            }
        }
        Expr::BVNot(e, _) => {
            write!(writer, "not(")?;
            serialize_expr_ref(e, ctx, writer)?;
            write!(writer, ")")
        }
        Expr::BVNegate(e, _) => {
            write!(writer, "neg(")?;
            serialize_expr_ref(e, ctx, writer)?;
            write!(writer, ")")
        }
        Expr::BVReduceOr(e) => {
            write!(writer, "redor(")?;
            serialize_expr_ref(e, ctx, writer)?;
            write!(writer, ")")
        }
        Expr::BVReduceAnd(e) => {
            write!(writer, "redand(")?;
            serialize_expr_ref(e, ctx, writer)?;
            write!(writer, ")")
        }
        Expr::BVReduceXor(e) => {
            write!(writer, "redxor(")?;
            serialize_expr_ref(e, ctx, writer)?;
            write!(writer, ")")
        }
        Expr::BVEqual(a, b) => {
            write!(writer, "eq(")?;
            serialize_expr_ref(a, ctx, writer)?;
            write!(writer, ", ")?;
            serialize_expr_ref(b, ctx, writer)?;
            write!(writer, ")")
        }
        Expr::BVImplies(a, b) => {
            write!(writer, "implies(")?;
            serialize_expr_ref(a, ctx, writer)?;
            write!(writer, ", ")?;
            serialize_expr_ref(b, ctx, writer)?;
            write!(writer, ")")
        }
        Expr::BVGreater(a, b) => {
            write!(writer, "ugt(")?;
            serialize_expr_ref(a, ctx, writer)?;
            write!(writer, ", ")?;
            serialize_expr_ref(b, ctx, writer)?;
            write!(writer, ")")
        }
        Expr::BVGreaterSigned(a, b) => {
            write!(writer, "sgt(")?;
            serialize_expr_ref(a, ctx, writer)?;
            write!(writer, ", ")?;
            serialize_expr_ref(b, ctx, writer)?;
            write!(writer, ")")
        }
        Expr::BVGreaterEqual(a, b) => {
            write!(writer, "ugte(")?;
            serialize_expr_ref(a, ctx, writer)?;
            write!(writer, ", ")?;
            serialize_expr_ref(b, ctx, writer)?;
            write!(writer, ")")
        }
        Expr::BVGreaterEqualSigned(a, b) => {
            write!(writer, "sgte(")?;
            serialize_expr_ref(a, ctx, writer)?;
            write!(writer, ", ")?;
            serialize_expr_ref(b, ctx, writer)?;
            write!(writer, ")")
        }
        Expr::BVConcat(a, b, _) => {
            write!(writer, "concat(")?;
            serialize_expr_ref(a, ctx, writer)?;
            write!(writer, ", ")?;
            serialize_expr_ref(b, ctx, writer)?;
            write!(writer, ")")
        }
        Expr::BVAnd(a, b, _) => {
            write!(writer, "and(")?;
            serialize_expr_ref(a, ctx, writer)?;
            write!(writer, ", ")?;
            serialize_expr_ref(b, ctx, writer)?;
            write!(writer, ")")
        }
        Expr::BVOr(a, b, _) => {
            write!(writer, "or(")?;
            serialize_expr_ref(a, ctx, writer)?;
            write!(writer, ", ")?;
            serialize_expr_ref(b, ctx, writer)?;
            write!(writer, ")")
        }
        Expr::BVXor(a, b, _) => {
            write!(writer, "xor(")?;
            serialize_expr_ref(a, ctx, writer)?;
            write!(writer, ", ")?;
            serialize_expr_ref(b, ctx, writer)?;
            write!(writer, ")")
        }
        Expr::BVShiftLeft(a, b, _) => {
            write!(writer, "logical_shift_left(")?;
            serialize_expr_ref(a, ctx, writer)?;
            write!(writer, ", ")?;
            serialize_expr_ref(b, ctx, writer)?;
            write!(writer, ")")
        }
        Expr::BVArithmeticShiftRight(a, b, _) => {
            write!(writer, "arithmetic_shift_right(")?;
            serialize_expr_ref(a, ctx, writer)?;
            write!(writer, ", ")?;
            serialize_expr_ref(b, ctx, writer)?;
            write!(writer, ")")
        }
        Expr::BVShiftRight(a, b, _) => {
            write!(writer, "logical_shift_right(")?;
            serialize_expr_ref(a, ctx, writer)?;
            write!(writer, ", ")?;
            serialize_expr_ref(b, ctx, writer)?;
            write!(writer, ")")
        }
        Expr::BVAdd(a, b, _) => {
            write!(writer, "add(")?;
            serialize_expr_ref(a, ctx, writer)?;
            write!(writer, ", ")?;
            serialize_expr_ref(b, ctx, writer)?;
            write!(writer, ")")
        }
        Expr::BVMul(a, b, _) => {
            write!(writer, "mul(")?;
            serialize_expr_ref(a, ctx, writer)?;
            write!(writer, ", ")?;
            serialize_expr_ref(b, ctx, writer)?;
            write!(writer, ")")
        }
        Expr::BVSignedDiv(a, b, _) => {
            write!(writer, "sdiv(")?;
            serialize_expr_ref(a, ctx, writer)?;
            write!(writer, ", ")?;
            serialize_expr_ref(b, ctx, writer)?;
            write!(writer, ")")
        }
        Expr::BVUnsignedDiv(a, b, _) => {
            write!(writer, "udiv(")?;
            serialize_expr_ref(a, ctx, writer)?;
            write!(writer, ", ")?;
            serialize_expr_ref(b, ctx, writer)?;
            write!(writer, ")")
        }
        Expr::BVSignedMod(a, b, _) => {
            write!(writer, "smod(")?;
            serialize_expr_ref(a, ctx, writer)?;
            write!(writer, ", ")?;
            serialize_expr_ref(b, ctx, writer)?;
            write!(writer, ")")
        }
        Expr::BVSignedRem(a, b, _) => {
            write!(writer, "srem(")?;
            serialize_expr_ref(a, ctx, writer)?;
            write!(writer, ", ")?;
            serialize_expr_ref(b, ctx, writer)?;
            write!(writer, ")")
        }
        Expr::BVUnsignedRem(a, b, _) => {
            write!(writer, "urem(")?;
            serialize_expr_ref(a, ctx, writer)?;
            write!(writer, ", ")?;
            serialize_expr_ref(b, ctx, writer)?;
            write!(writer, ")")
        }
        Expr::BVSub(a, b, _) => {
            write!(writer, "sub(")?;
            serialize_expr_ref(a, ctx, writer)?;
            write!(writer, ", ")?;
            serialize_expr_ref(b, ctx, writer)?;
            write!(writer, ")")
        }
        Expr::BVArrayRead { array, index, .. } => {
            serialize_expr_ref(array, ctx, writer)?;
            write!(writer, "[")?;
            serialize_expr_ref(index, ctx, writer)?;
            write!(writer, "]")
        }
        Expr::BVIte {
            cond, tru, fals, ..
        } => {
            write!(writer, "ite(")?;
            serialize_expr_ref(cond, ctx, writer)?;
            write!(writer, ", ")?;
            serialize_expr_ref(tru, ctx, writer)?;
            write!(writer, ", ")?;
            serialize_expr_ref(fals, ctx, writer)?;
            write!(writer, ")")
        }
        Expr::ArraySymbol { name, .. } => write!(writer, "{}", ctx.get(*name)),
        Expr::ArrayConstant { e, index_width, .. } => {
            write!(writer, "([")?;
            serialize_expr_ref(e, ctx, writer)?;
            write!(writer, "] x 2^{index_width})")
        }
        Expr::ArrayEqual(a, b) => {
            write!(writer, "eq(")?;
            serialize_expr_ref(a, ctx, writer)?;
            write!(writer, ", ")?;
            serialize_expr_ref(b, ctx, writer)?;
            write!(writer, ")")
        }
        Expr::ArrayStore { array, index, data } => {
            serialize_expr_ref(array, ctx, writer)?;
            write!(writer, "[")?;
            serialize_expr_ref(index, ctx, writer)?;
            write!(writer, " := ")?;
            serialize_expr_ref(data, ctx, writer)?;
            write!(writer, "]")
        }
        Expr::ArrayIte { cond, tru, fals } => {
            write!(writer, "ite(")?;
            serialize_expr_ref(cond, ctx, writer)?;
            write!(writer, ", ")?;
            serialize_expr_ref(tru, ctx, writer)?;
            write!(writer, ", ")?;
            serialize_expr_ref(fals, ctx, writer)?;
            write!(writer, ")")
        }
    }
}

/// De-reference and serialize.
#[inline]
fn serialize_expr_ref(
    expr: &ExprRef,
    ctx: &Context,
    writer: &mut impl Write,
) -> std::io::Result<()> {
    serialize_expr(ctx.get(*expr), ctx, writer)
}

impl SerializableIrNode for ExprRef {
    fn serialize(&self, ctx: &Context, writer: &mut impl Write) -> std::io::Result<()> {
        ctx.get(*self).serialize(ctx, writer)
    }
}

impl SerializableIrNode for Type {
    fn serialize(&self, _ctx: &Context, writer: &mut impl Write) -> std::io::Result<()> {
        write!(writer, "{}", self)
    }
}

impl SerializableIrNode for TransitionSystem {
    fn serialize(&self, ctx: &Context, writer: &mut impl Write) -> std::io::Result<()> {
        if !self.name.is_empty() {
            writeln!(writer, "{}", self.name)?;
        }

        // signals
        for (ii, signal) in self
            .signals
            .iter()
            .enumerate()
            .flat_map(|(ii, maybe_signal)| maybe_signal.as_ref().and_then(|s| Some((ii, s))))
            // do not explicitly print states
            .filter(|(_, s)| !matches!(s.kind, SignalKind::State))
        {
            // we deduce the expression id from the index
            let expr = ctx.get(ExprRef::from_index(ii));

            // skip symbols and literals
            if expr.is_symbol() || expr.is_bv_lit() {
                continue;
            }

            // print the kind
            write!(writer, "{} ", signal.kind)?;

            // we use the position as name if no name is available
            if let Some(name_ref) = signal.name {
                write!(writer, "{}", ctx.get(name_ref))?;
            } else {
                write!(writer, "%{}", ii)?;
            }

            // print the type
            let tpe = expr.get_type(ctx);
            write!(writer, " : {tpe}",)?;

            // do not print simple symbols
            if expr.is_symbol() {
                writeln!(writer, "")?;
            } else {
                write!(writer, " = ")?;
                expr.serialize(ctx, writer)?;
                writeln!(writer, "",)?;
            }
        }

        // states
        for state in self.states.iter() {
            let name = state
                .symbol
                .get_symbol_name(ctx)
                .expect("all states are required to have a name!");
            let tpe = state.symbol.get_type(ctx);
            writeln!(writer, "state {name} : {tpe}")?;

            if let Some(expr) = state.init {
                write!(writer, "  [init] ")?;
                expr.serialize(ctx, writer)?;
                writeln!(writer, "",)?;
            }
            if let Some(expr) = state.next {
                write!(writer, "  [next] ")?;
                expr.serialize(ctx, writer)?;
                writeln!(writer, "",)?;
            }
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::super::ExprNodeConstruction;
    use super::*;

    #[test]
    fn simple_serialization() {
        let mut ctx = Context::default();
        let test_expr = ctx.bv_symbol("test", 3);
        assert_eq!("test", test_expr.serialize_to_str(&ctx));
    }
}
