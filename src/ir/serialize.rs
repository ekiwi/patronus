// Copyright 2023 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

use super::{Context, Expr, ExprRef, GetNode};
use crate::ir::{
    count_expr_uses, is_usage_root_signal, SignalKind, TransitionSystem, Type, TypeCheck,
};
use std::io::Write;

pub trait SerializableIrNode {
    fn serialize<W: Write>(&self, ctx: &Context, writer: &mut W) -> std::io::Result<()>;
    fn serialize_to_str(&self, ctx: &Context) -> String {
        let mut buf = Vec::new();
        self.serialize(ctx, &mut buf)
            .expect("Failed to write to string!");
        String::from_utf8(buf).expect("Failed to read string we wrote!")
    }
}

impl SerializableIrNode for Expr {
    fn serialize<W: Write>(&self, ctx: &Context, writer: &mut W) -> std::io::Result<()> {
        serialize_expr(&self, ctx, writer, &|_, _, _| Ok(false))
    }
}

/// Internal serialize function for expressions that can be specialized depending on how we want
/// to treat sub-expressions.
fn serialize_expr<F, W>(
    expr: &Expr,
    ctx: &Context,
    writer: &mut W,
    serialize_child: &F,
) -> std::io::Result<()>
where
    F: Fn(&ExprRef, &Context, &mut W) -> std::io::Result<bool>,
    W: Write,
{
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
            if (serialize_child)(e, ctx, writer)? {
                serialize_expr_ref(e, ctx, writer, serialize_child)?;
            }
            write!(writer, ", {by})")
        }
        Expr::BVSignExt { e, by, .. } => {
            write!(writer, "sext(")?;
            if (serialize_child)(e, ctx, writer)? {
                serialize_expr_ref(e, ctx, writer, serialize_child)?;
            }
            write!(writer, ", {by})")
        }
        Expr::BVSlice { e, hi, lo, .. } => {
            if (serialize_child)(e, ctx, writer)? {
                serialize_expr_ref(e, ctx, writer, serialize_child)?;
            }
            if hi == lo {
                write!(writer, "[{hi}]")
            } else {
                write!(writer, "[{hi}:{lo}]")
            }
        }
        Expr::BVNot(e, _) => {
            write!(writer, "not(")?;
            if (serialize_child)(e, ctx, writer)? {
                serialize_expr_ref(e, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
        Expr::BVNegate(e, _) => {
            write!(writer, "neg(")?;
            if (serialize_child)(e, ctx, writer)? {
                serialize_expr_ref(e, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
        Expr::BVReduceOr(e) => {
            write!(writer, "redor(")?;
            if (serialize_child)(e, ctx, writer)? {
                serialize_expr_ref(e, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
        Expr::BVReduceAnd(e) => {
            write!(writer, "redand(")?;
            if (serialize_child)(e, ctx, writer)? {
                serialize_expr_ref(e, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
        Expr::BVReduceXor(e) => {
            write!(writer, "redxor(")?;
            if (serialize_child)(e, ctx, writer)? {
                serialize_expr_ref(e, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
        Expr::BVEqual(a, b) => {
            write!(writer, "eq(")?;
            if (serialize_child)(a, ctx, writer)? {
                serialize_expr_ref(a, ctx, writer, serialize_child)?;
            }
            write!(writer, ", ")?;
            if (serialize_child)(b, ctx, writer)? {
                serialize_expr_ref(b, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
        Expr::BVImplies(a, b) => {
            write!(writer, "implies(")?;
            if (serialize_child)(a, ctx, writer)? {
                serialize_expr_ref(a, ctx, writer, serialize_child)?;
            }
            write!(writer, ", ")?;
            if (serialize_child)(b, ctx, writer)? {
                serialize_expr_ref(b, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
        Expr::BVGreater(a, b) => {
            write!(writer, "ugt(")?;
            if (serialize_child)(a, ctx, writer)? {
                serialize_expr_ref(a, ctx, writer, serialize_child)?;
            }
            write!(writer, ", ")?;
            if (serialize_child)(b, ctx, writer)? {
                serialize_expr_ref(b, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
        Expr::BVGreaterSigned(a, b) => {
            write!(writer, "sgt(")?;
            if (serialize_child)(a, ctx, writer)? {
                serialize_expr_ref(a, ctx, writer, serialize_child)?;
            }
            write!(writer, ", ")?;
            if (serialize_child)(b, ctx, writer)? {
                serialize_expr_ref(b, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
        Expr::BVGreaterEqual(a, b) => {
            write!(writer, "ugte(")?;
            if (serialize_child)(a, ctx, writer)? {
                serialize_expr_ref(a, ctx, writer, serialize_child)?;
            }
            write!(writer, ", ")?;
            if (serialize_child)(b, ctx, writer)? {
                serialize_expr_ref(b, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
        Expr::BVGreaterEqualSigned(a, b) => {
            write!(writer, "sgte(")?;
            if (serialize_child)(a, ctx, writer)? {
                serialize_expr_ref(a, ctx, writer, serialize_child)?;
            }
            write!(writer, ", ")?;
            if (serialize_child)(b, ctx, writer)? {
                serialize_expr_ref(b, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
        Expr::BVConcat(a, b, _) => {
            write!(writer, "concat(")?;
            if (serialize_child)(a, ctx, writer)? {
                serialize_expr_ref(a, ctx, writer, serialize_child)?;
            }
            write!(writer, ", ")?;
            if (serialize_child)(b, ctx, writer)? {
                serialize_expr_ref(b, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
        Expr::BVAnd(a, b, _) => {
            write!(writer, "and(")?;
            if (serialize_child)(a, ctx, writer)? {
                serialize_expr_ref(a, ctx, writer, serialize_child)?;
            }
            write!(writer, ", ")?;
            if (serialize_child)(b, ctx, writer)? {
                serialize_expr_ref(b, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
        Expr::BVOr(a, b, _) => {
            write!(writer, "or(")?;
            if (serialize_child)(a, ctx, writer)? {
                serialize_expr_ref(a, ctx, writer, serialize_child)?;
            }
            write!(writer, ", ")?;
            if (serialize_child)(b, ctx, writer)? {
                serialize_expr_ref(b, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
        Expr::BVXor(a, b, _) => {
            write!(writer, "xor(")?;
            if (serialize_child)(a, ctx, writer)? {
                serialize_expr_ref(a, ctx, writer, serialize_child)?;
            }
            write!(writer, ", ")?;
            if (serialize_child)(b, ctx, writer)? {
                serialize_expr_ref(b, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
        Expr::BVShiftLeft(a, b, _) => {
            write!(writer, "logical_shift_left(")?;
            if (serialize_child)(a, ctx, writer)? {
                serialize_expr_ref(a, ctx, writer, serialize_child)?;
            }
            write!(writer, ", ")?;
            if (serialize_child)(b, ctx, writer)? {
                serialize_expr_ref(b, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
        Expr::BVArithmeticShiftRight(a, b, _) => {
            write!(writer, "arithmetic_shift_right(")?;
            if (serialize_child)(a, ctx, writer)? {
                serialize_expr_ref(a, ctx, writer, serialize_child)?;
            }
            write!(writer, ", ")?;
            if (serialize_child)(b, ctx, writer)? {
                serialize_expr_ref(b, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
        Expr::BVShiftRight(a, b, _) => {
            write!(writer, "logical_shift_right(")?;
            if (serialize_child)(a, ctx, writer)? {
                serialize_expr_ref(a, ctx, writer, serialize_child)?;
            }
            write!(writer, ", ")?;
            if (serialize_child)(b, ctx, writer)? {
                serialize_expr_ref(b, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
        Expr::BVAdd(a, b, _) => {
            write!(writer, "add(")?;
            if (serialize_child)(a, ctx, writer)? {
                serialize_expr_ref(a, ctx, writer, serialize_child)?;
            }
            write!(writer, ", ")?;
            if (serialize_child)(b, ctx, writer)? {
                serialize_expr_ref(b, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
        Expr::BVMul(a, b, _) => {
            write!(writer, "mul(")?;
            if (serialize_child)(a, ctx, writer)? {
                serialize_expr_ref(a, ctx, writer, serialize_child)?;
            }
            write!(writer, ", ")?;
            if (serialize_child)(b, ctx, writer)? {
                serialize_expr_ref(b, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
        Expr::BVSignedDiv(a, b, _) => {
            write!(writer, "sdiv(")?;
            if (serialize_child)(a, ctx, writer)? {
                serialize_expr_ref(a, ctx, writer, serialize_child)?;
            }
            write!(writer, ", ")?;
            if (serialize_child)(b, ctx, writer)? {
                serialize_expr_ref(b, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
        Expr::BVUnsignedDiv(a, b, _) => {
            write!(writer, "udiv(")?;
            if (serialize_child)(a, ctx, writer)? {
                serialize_expr_ref(a, ctx, writer, serialize_child)?;
            }
            write!(writer, ", ")?;
            if (serialize_child)(b, ctx, writer)? {
                serialize_expr_ref(b, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
        Expr::BVSignedMod(a, b, _) => {
            write!(writer, "smod(")?;
            if (serialize_child)(a, ctx, writer)? {
                serialize_expr_ref(a, ctx, writer, serialize_child)?;
            }
            write!(writer, ", ")?;
            if (serialize_child)(b, ctx, writer)? {
                serialize_expr_ref(b, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
        Expr::BVSignedRem(a, b, _) => {
            write!(writer, "srem(")?;
            if (serialize_child)(a, ctx, writer)? {
                serialize_expr_ref(a, ctx, writer, serialize_child)?;
            }
            write!(writer, ", ")?;
            if (serialize_child)(b, ctx, writer)? {
                serialize_expr_ref(b, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
        Expr::BVUnsignedRem(a, b, _) => {
            write!(writer, "urem(")?;
            if (serialize_child)(a, ctx, writer)? {
                serialize_expr_ref(a, ctx, writer, serialize_child)?;
            }
            write!(writer, ", ")?;
            if (serialize_child)(b, ctx, writer)? {
                serialize_expr_ref(b, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
        Expr::BVSub(a, b, _) => {
            write!(writer, "sub(")?;
            if (serialize_child)(a, ctx, writer)? {
                serialize_expr_ref(a, ctx, writer, serialize_child)?;
            }
            write!(writer, ", ")?;
            if (serialize_child)(b, ctx, writer)? {
                serialize_expr_ref(b, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
        Expr::BVArrayRead { array, index, .. } => {
            if (serialize_child)(array, ctx, writer)? {
                serialize_expr_ref(array, ctx, writer, serialize_child)?;
            }
            write!(writer, "[")?;
            if (serialize_child)(index, ctx, writer)? {
                serialize_expr_ref(index, ctx, writer, serialize_child)?;
            }
            write!(writer, "]")
        }
        Expr::BVIte {
            cond, tru, fals, ..
        } => {
            write!(writer, "ite(")?;
            if (serialize_child)(cond, ctx, writer)? {
                serialize_expr_ref(cond, ctx, writer, serialize_child)?;
            }
            write!(writer, ", ")?;
            if (serialize_child)(tru, ctx, writer)? {
                serialize_expr_ref(tru, ctx, writer, serialize_child)?;
            }
            write!(writer, ", ")?;
            if (serialize_child)(fals, ctx, writer)? {
                serialize_expr_ref(fals, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
        Expr::ArraySymbol { name, .. } => write!(writer, "{}", ctx.get(*name)),
        Expr::ArrayConstant { e, index_width, .. } => {
            write!(writer, "([")?;
            if (serialize_child)(e, ctx, writer)? {
                serialize_expr_ref(e, ctx, writer, serialize_child)?;
            }
            write!(writer, "] x 2^{index_width})")
        }
        Expr::ArrayEqual(a, b) => {
            write!(writer, "eq(")?;
            if (serialize_child)(a, ctx, writer)? {
                serialize_expr_ref(a, ctx, writer, serialize_child)?;
            }
            write!(writer, ", ")?;
            if (serialize_child)(b, ctx, writer)? {
                serialize_expr_ref(b, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
        Expr::ArrayStore { array, index, data } => {
            if (serialize_child)(array, ctx, writer)? {
                serialize_expr_ref(array, ctx, writer, serialize_child)?;
            }
            write!(writer, "[")?;
            if (serialize_child)(index, ctx, writer)? {
                serialize_expr_ref(index, ctx, writer, serialize_child)?;
            }
            write!(writer, " := ")?;
            if (serialize_child)(data, ctx, writer)? {
                serialize_expr_ref(data, ctx, writer, serialize_child)?;
            }
            write!(writer, "]")
        }
        Expr::ArrayIte { cond, tru, fals } => {
            write!(writer, "ite(")?;
            if (serialize_child)(cond, ctx, writer)? {
                serialize_expr_ref(cond, ctx, writer, serialize_child)?;
            }
            write!(writer, ", ")?;
            if (serialize_child)(tru, ctx, writer)? {
                serialize_expr_ref(tru, ctx, writer, serialize_child)?;
            }
            write!(writer, ", ")?;
            if (serialize_child)(fals, ctx, writer)? {
                serialize_expr_ref(fals, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
    }
}

/// De-reference and serialize.
#[inline]
fn serialize_expr_ref<F, W>(
    expr: &ExprRef,
    ctx: &Context,
    writer: &mut W,
    serialize_child: &F,
) -> std::io::Result<()>
where
    F: Fn(&ExprRef, &Context, &mut W) -> std::io::Result<bool>,
    W: Write,
{
    serialize_expr(ctx.get(*expr), ctx, writer, serialize_child)
}

impl SerializableIrNode for ExprRef {
    fn serialize<W: Write>(&self, ctx: &Context, writer: &mut W) -> std::io::Result<()> {
        ctx.get(*self).serialize(ctx, writer)
    }
}

impl SerializableIrNode for Type {
    fn serialize<W: Write>(&self, _ctx: &Context, writer: &mut W) -> std::io::Result<()> {
        write!(writer, "{}", self)
    }
}

fn inline_expr_for_transition_system(expr: &Expr, _use_count: u32) -> bool {
    let always_inline = expr.is_symbol() || expr.is_bv_lit();
    // TODO: re-enable using the use_count for inlining decisions after we add a way to turn it off
    always_inline // || use_count <= 1
}

fn serialize_transition_system<W: Write>(
    ctx: &Context,
    sys: &TransitionSystem,
    writer: &mut W,
) -> std::io::Result<()> {
    if !sys.name.is_empty() {
        writeln!(writer, "{}", sys.name)?;
    }

    let uses = count_expr_uses(ctx, sys);

    // this closure allows us to use node names instead of serializing all sub-expressions
    let serialize_child =
        |expr_ref: &ExprRef, ctx: &Context, writer: &mut W| -> std::io::Result<bool> {
            // we inline, if the expression has only one use
            let use_count = uses.get(expr_ref.index()).map(|v| *v).unwrap_or_default();
            assert!(use_count > 0, "{:?}", ctx.get(*expr_ref));
            let expr = ctx.get(*expr_ref);
            if inline_expr_for_transition_system(expr, use_count) {
                Ok(true) // recurse to child
            } else {
                // print the name of the signal
                let maybe_name: Option<&str> = sys
                    .get_signal(*expr_ref)
                    .and_then(|s| s.name)
                    .map(|r| ctx.get(r));
                match maybe_name {
                    None => write!(writer, "%{}", expr_ref.index())?,
                    Some(name) => write!(writer, "{}", name)?,
                };
                Ok(false)
            }
        };

    // signals
    for (ii, signal) in sys.get_signals(|s| !matches!(s.kind, SignalKind::State)) {
        let use_count = uses.get(ii.index()).map(|v| *v).unwrap_or_default();
        let expr = ctx.get(ii);

        // skip any expressions that not used multiple times, unless it us a usage root signal
        if inline_expr_for_transition_system(expr, use_count) && !is_usage_root_signal(&signal) {
            continue;
        }

        // print the kind
        write!(writer, "{} ", signal.kind)?;

        // we use the position as name if no name is available
        if let Some(name_ref) = signal.name {
            write!(writer, "{}", ctx.get(name_ref))?;
        } else {
            write!(writer, "%{}", ii.index())?;
        }

        // print the type
        let tpe = expr.get_type(ctx);
        write!(writer, " : {tpe}",)?;

        // do not print simple symbols
        if expr.is_symbol() {
            writeln!(writer, "")?;
        } else {
            write!(writer, " = ")?;
            serialize_expr(expr, ctx, writer, &serialize_child)?;
            writeln!(writer, "",)?;
        }
    }

    // states
    for state in sys.states() {
        let name = state
            .symbol
            .get_symbol_name(ctx)
            .expect("all states are required to have a name!");
        let tpe = state.symbol.get_type(ctx);
        writeln!(writer, "state {name} : {tpe}")?;

        if let Some(expr) = &state.init {
            write!(writer, "  [init] ")?;
            serialize_expr_ref(expr, ctx, writer, &serialize_child)?;
            writeln!(writer, "",)?;
        }
        if let Some(expr) = &state.next {
            write!(writer, "  [next] ")?;
            serialize_expr_ref(expr, ctx, writer, &serialize_child)?;
            writeln!(writer, "",)?;
        }
    }

    Ok(())
}

impl SerializableIrNode for TransitionSystem {
    fn serialize<W: Write>(&self, ctx: &Context, writer: &mut W) -> std::io::Result<()> {
        serialize_transition_system(ctx, self, writer)
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
