// Copyright 2023 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

use super::{Context, Expr, ExprRef};
use crate::ir::{
    analyze_for_serialization, SignalInfo, SignalLabels, TransitionSystem, Type, TypeCheck,
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
        serialize_expr(self, ctx, writer, &|_, _| Ok(false))
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
    F: Fn(&ExprRef, &mut W) -> std::io::Result<bool>,
    W: Write,
{
    match expr {
        Expr::BVSymbol { name, .. } => write!(writer, "{}", ctx.get_str(*name)),
        Expr::BVLiteral { value, width } => {
            if *width <= 8 {
                write!(writer, "{width}'b{value:b}")
            } else {
                write!(writer, "{width}'x{value:x}")
            }
        }
        Expr::BVZeroExt { e, by, .. } => {
            write!(writer, "zext(")?;
            if (serialize_child)(e, writer)? {
                serialize_expr_ref(e, ctx, writer, serialize_child)?;
            }
            write!(writer, ", {by})")
        }
        Expr::BVSignExt { e, by, .. } => {
            write!(writer, "sext(")?;
            if (serialize_child)(e, writer)? {
                serialize_expr_ref(e, ctx, writer, serialize_child)?;
            }
            write!(writer, ", {by})")
        }
        Expr::BVSlice { e, hi, lo, .. } => {
            if (serialize_child)(e, writer)? {
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
            if (serialize_child)(e, writer)? {
                serialize_expr_ref(e, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
        Expr::BVNegate(e, _) => {
            write!(writer, "neg(")?;
            if (serialize_child)(e, writer)? {
                serialize_expr_ref(e, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
        Expr::BVEqual(a, b) => {
            write!(writer, "eq(")?;
            if (serialize_child)(a, writer)? {
                serialize_expr_ref(a, ctx, writer, serialize_child)?;
            }
            write!(writer, ", ")?;
            if (serialize_child)(b, writer)? {
                serialize_expr_ref(b, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
        Expr::BVImplies(a, b) => {
            write!(writer, "implies(")?;
            if (serialize_child)(a, writer)? {
                serialize_expr_ref(a, ctx, writer, serialize_child)?;
            }
            write!(writer, ", ")?;
            if (serialize_child)(b, writer)? {
                serialize_expr_ref(b, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
        Expr::BVGreater(a, b) => {
            write!(writer, "ugt(")?;
            if (serialize_child)(a, writer)? {
                serialize_expr_ref(a, ctx, writer, serialize_child)?;
            }
            write!(writer, ", ")?;
            if (serialize_child)(b, writer)? {
                serialize_expr_ref(b, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
        Expr::BVGreaterSigned(a, b, _) => {
            write!(writer, "sgt(")?;
            if (serialize_child)(a, writer)? {
                serialize_expr_ref(a, ctx, writer, serialize_child)?;
            }
            write!(writer, ", ")?;
            if (serialize_child)(b, writer)? {
                serialize_expr_ref(b, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
        Expr::BVGreaterEqual(a, b) => {
            write!(writer, "ugte(")?;
            if (serialize_child)(a, writer)? {
                serialize_expr_ref(a, ctx, writer, serialize_child)?;
            }
            write!(writer, ", ")?;
            if (serialize_child)(b, writer)? {
                serialize_expr_ref(b, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
        Expr::BVGreaterEqualSigned(a, b, _) => {
            write!(writer, "sgte(")?;
            if (serialize_child)(a, writer)? {
                serialize_expr_ref(a, ctx, writer, serialize_child)?;
            }
            write!(writer, ", ")?;
            if (serialize_child)(b, writer)? {
                serialize_expr_ref(b, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
        Expr::BVConcat(a, b, _) => {
            write!(writer, "concat(")?;
            if (serialize_child)(a, writer)? {
                serialize_expr_ref(a, ctx, writer, serialize_child)?;
            }
            write!(writer, ", ")?;
            if (serialize_child)(b, writer)? {
                serialize_expr_ref(b, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
        Expr::BVAnd(a, b, _) => {
            write!(writer, "and(")?;
            if (serialize_child)(a, writer)? {
                serialize_expr_ref(a, ctx, writer, serialize_child)?;
            }
            write!(writer, ", ")?;
            if (serialize_child)(b, writer)? {
                serialize_expr_ref(b, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
        Expr::BVOr(a, b, _) => {
            write!(writer, "or(")?;
            if (serialize_child)(a, writer)? {
                serialize_expr_ref(a, ctx, writer, serialize_child)?;
            }
            write!(writer, ", ")?;
            if (serialize_child)(b, writer)? {
                serialize_expr_ref(b, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
        Expr::BVXor(a, b, _) => {
            write!(writer, "xor(")?;
            if (serialize_child)(a, writer)? {
                serialize_expr_ref(a, ctx, writer, serialize_child)?;
            }
            write!(writer, ", ")?;
            if (serialize_child)(b, writer)? {
                serialize_expr_ref(b, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
        Expr::BVShiftLeft(a, b, _) => {
            write!(writer, "logical_shift_left(")?;
            if (serialize_child)(a, writer)? {
                serialize_expr_ref(a, ctx, writer, serialize_child)?;
            }
            write!(writer, ", ")?;
            if (serialize_child)(b, writer)? {
                serialize_expr_ref(b, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
        Expr::BVArithmeticShiftRight(a, b, _) => {
            write!(writer, "arithmetic_shift_right(")?;
            if (serialize_child)(a, writer)? {
                serialize_expr_ref(a, ctx, writer, serialize_child)?;
            }
            write!(writer, ", ")?;
            if (serialize_child)(b, writer)? {
                serialize_expr_ref(b, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
        Expr::BVShiftRight(a, b, _) => {
            write!(writer, "logical_shift_right(")?;
            if (serialize_child)(a, writer)? {
                serialize_expr_ref(a, ctx, writer, serialize_child)?;
            }
            write!(writer, ", ")?;
            if (serialize_child)(b, writer)? {
                serialize_expr_ref(b, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
        Expr::BVAdd(a, b, _) => {
            write!(writer, "add(")?;
            if (serialize_child)(a, writer)? {
                serialize_expr_ref(a, ctx, writer, serialize_child)?;
            }
            write!(writer, ", ")?;
            if (serialize_child)(b, writer)? {
                serialize_expr_ref(b, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
        Expr::BVMul(a, b, _) => {
            write!(writer, "mul(")?;
            if (serialize_child)(a, writer)? {
                serialize_expr_ref(a, ctx, writer, serialize_child)?;
            }
            write!(writer, ", ")?;
            if (serialize_child)(b, writer)? {
                serialize_expr_ref(b, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
        Expr::BVSignedDiv(a, b, _) => {
            write!(writer, "sdiv(")?;
            if (serialize_child)(a, writer)? {
                serialize_expr_ref(a, ctx, writer, serialize_child)?;
            }
            write!(writer, ", ")?;
            if (serialize_child)(b, writer)? {
                serialize_expr_ref(b, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
        Expr::BVUnsignedDiv(a, b, _) => {
            write!(writer, "udiv(")?;
            if (serialize_child)(a, writer)? {
                serialize_expr_ref(a, ctx, writer, serialize_child)?;
            }
            write!(writer, ", ")?;
            if (serialize_child)(b, writer)? {
                serialize_expr_ref(b, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
        Expr::BVSignedMod(a, b, _) => {
            write!(writer, "smod(")?;
            if (serialize_child)(a, writer)? {
                serialize_expr_ref(a, ctx, writer, serialize_child)?;
            }
            write!(writer, ", ")?;
            if (serialize_child)(b, writer)? {
                serialize_expr_ref(b, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
        Expr::BVSignedRem(a, b, _) => {
            write!(writer, "srem(")?;
            if (serialize_child)(a, writer)? {
                serialize_expr_ref(a, ctx, writer, serialize_child)?;
            }
            write!(writer, ", ")?;
            if (serialize_child)(b, writer)? {
                serialize_expr_ref(b, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
        Expr::BVUnsignedRem(a, b, _) => {
            write!(writer, "urem(")?;
            if (serialize_child)(a, writer)? {
                serialize_expr_ref(a, ctx, writer, serialize_child)?;
            }
            write!(writer, ", ")?;
            if (serialize_child)(b, writer)? {
                serialize_expr_ref(b, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
        Expr::BVSub(a, b, _) => {
            write!(writer, "sub(")?;
            if (serialize_child)(a, writer)? {
                serialize_expr_ref(a, ctx, writer, serialize_child)?;
            }
            write!(writer, ", ")?;
            if (serialize_child)(b, writer)? {
                serialize_expr_ref(b, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
        Expr::BVArrayRead { array, index, .. } => {
            if (serialize_child)(array, writer)? {
                serialize_expr_ref(array, ctx, writer, serialize_child)?;
            }
            write!(writer, "[")?;
            if (serialize_child)(index, writer)? {
                serialize_expr_ref(index, ctx, writer, serialize_child)?;
            }
            write!(writer, "]")
        }
        Expr::BVIte {
            cond, tru, fals, ..
        } => {
            write!(writer, "ite(")?;
            if (serialize_child)(cond, writer)? {
                serialize_expr_ref(cond, ctx, writer, serialize_child)?;
            }
            write!(writer, ", ")?;
            if (serialize_child)(tru, writer)? {
                serialize_expr_ref(tru, ctx, writer, serialize_child)?;
            }
            write!(writer, ", ")?;
            if (serialize_child)(fals, writer)? {
                serialize_expr_ref(fals, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
        Expr::ArraySymbol { name, .. } => write!(writer, "{}", ctx.get_str(*name)),
        Expr::ArrayConstant { e, index_width, .. } => {
            write!(writer, "([")?;
            if (serialize_child)(e, writer)? {
                serialize_expr_ref(e, ctx, writer, serialize_child)?;
            }
            write!(writer, "] x 2^{index_width})")
        }
        Expr::ArrayEqual(a, b) => {
            write!(writer, "eq(")?;
            if (serialize_child)(a, writer)? {
                serialize_expr_ref(a, ctx, writer, serialize_child)?;
            }
            write!(writer, ", ")?;
            if (serialize_child)(b, writer)? {
                serialize_expr_ref(b, ctx, writer, serialize_child)?;
            }
            write!(writer, ")")
        }
        Expr::ArrayStore { array, index, data } => {
            if (serialize_child)(array, writer)? {
                serialize_expr_ref(array, ctx, writer, serialize_child)?;
            }
            write!(writer, "[")?;
            if (serialize_child)(index, writer)? {
                serialize_expr_ref(index, ctx, writer, serialize_child)?;
            }
            write!(writer, " := ")?;
            if (serialize_child)(data, writer)? {
                serialize_expr_ref(data, ctx, writer, serialize_child)?;
            }
            write!(writer, "]")
        }
        Expr::ArrayIte { cond, tru, fals } => {
            write!(writer, "ite(")?;
            if (serialize_child)(cond, writer)? {
                serialize_expr_ref(cond, ctx, writer, serialize_child)?;
            }
            write!(writer, ", ")?;
            if (serialize_child)(tru, writer)? {
                serialize_expr_ref(tru, ctx, writer, serialize_child)?;
            }
            write!(writer, ", ")?;
            if (serialize_child)(fals, writer)? {
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
    F: Fn(&ExprRef, &mut W) -> std::io::Result<bool>,
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

fn serialize_transition_system<W: Write>(
    ctx: &Context,
    sys: &TransitionSystem,
    writer: &mut W,
) -> std::io::Result<()> {
    if !sys.name.is_empty() {
        writeln!(writer, "{}", sys.name)?;
    }

    let signals = analyze_for_serialization(ctx, sys, true).signal_order;
    let max_id = signals
        .iter()
        .map(|s| s.expr.index())
        .max()
        .unwrap_or_default();
    let mut names = vec![None; max_id + 1];
    for root in signals.iter() {
        // try names in this order:
        // - symbol name
        // - signal name
        // - %{id}
        let name = root
            .expr
            .get_symbol_name(ctx)
            .map(|n| n.to_string())
            .unwrap_or_else(|| {
                sys.get_signal(root.expr)
                    .and_then(|i| i.name)
                    .map(|n| ctx.get_str(n).to_string())
                    .unwrap_or(format!("%{}", root.expr.index()))
            });
        names[root.expr.index()] = Some(name);
    }

    // this closure allows us to use node names instead of serializing all sub-expressions
    let serialize_child = |expr_ref: &ExprRef, writer: &mut W| -> std::io::Result<bool> {
        if let Some(Some(name)) = names.get(expr_ref.index()) {
            write!(writer, "{}", name)?;
            Ok(false)
        } else {
            Ok(true) // recurse to child
        }
    };

    // signals
    let mut aliases = Vec::new();
    for root in signals.iter() {
        let maybe_info = sys.get_signal(root.expr);
        let name = names[root.expr.index()].as_ref().unwrap();
        let expr = ctx.get(root.expr);

        // print the kind and name
        let kind = find_type(maybe_info, &mut aliases);
        write!(writer, "{} {}", kind, name)?;

        // print the type
        let tpe = expr.get_type(ctx);
        write!(writer, " : {tpe}",)?;

        if expr.is_symbol() && expr.get_symbol_name(ctx).unwrap() == name {
            writeln!(writer)?;
        } else {
            write!(writer, " = ")?;
            serialize_expr(expr, ctx, writer, &serialize_child)?;
            writeln!(writer)?;
        }

        // print aliases
        for alias in aliases.iter() {
            // for aliases, we prefer the signal name
            // this allows us to e.g. print the name of an output which is also an input correctly
            let alias_name = maybe_info
                .unwrap()
                .name
                .map(|n| ctx.get_str(n))
                .unwrap_or(name);
            writeln!(writer, "{alias} {alias_name} : {tpe} = {name}")?;
        }
    }

    // states
    for (_, state) in sys.states() {
        let name = state
            .symbol
            .get_symbol_name(ctx)
            .expect("all states are required to have a name!");
        let tpe = state.symbol.get_type(ctx);
        writeln!(writer, "state {name} : {tpe}")?;

        if let Some(expr) = &state.init {
            write!(writer, "  [init] ")?;
            serialize_expr_ref(expr, ctx, writer, &serialize_child)?;
            writeln!(writer)?;
        }
        if let Some(expr) = &state.next {
            write!(writer, "  [next] ")?;
            serialize_expr_ref(expr, ctx, writer, &serialize_child)?;
            writeln!(writer)?;
        }
    }

    Ok(())
}

fn find_type(maybe_info: Option<&SignalInfo>, aliases: &mut Vec<&'static str>) -> &'static str {
    aliases.clear();
    if let Some(info) = maybe_info {
        if info.is_input() {
            collect_aliases(info.labels, aliases);
            return "input";
        }
        // NOTE: state does not matter here since they are serialized later
        if info.labels.is_output() {
            collect_aliases(info.labels.clear(&SignalLabels::output()), aliases);
            return "output";
        }
        if info.labels.is_fair() {
            collect_aliases(info.labels.clear(&SignalLabels::fair()), aliases);
            return "fair";
        }
        if info.labels.is_bad() {
            collect_aliases(info.labels.clear(&SignalLabels::bad()), aliases);
            return "bad";
        }
        if info.labels.is_constraint() {
            collect_aliases(info.labels.clear(&SignalLabels::constraint()), aliases);
            return "constraint";
        }
    }
    "node"
}

fn collect_aliases(labels: SignalLabels, aliases: &mut Vec<&'static str>) {
    if labels.is_output() {
        aliases.push("output");
    }
    if labels.is_fair() {
        aliases.push("fair");
    }
    if labels.is_bad() {
        aliases.push("bad");
    }
    if labels.is_constraint() {
        aliases.push("constraint");
    }
}

impl SerializableIrNode for TransitionSystem {
    fn serialize<W: Write>(&self, ctx: &Context, writer: &mut W) -> std::io::Result<()> {
        serialize_transition_system(ctx, self, writer)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn simple_serialization() {
        let mut ctx = Context::default();
        let test_expr = ctx.bv_symbol("test", 3);
        assert_eq!("test", test_expr.serialize_to_str(&ctx));
    }
}
