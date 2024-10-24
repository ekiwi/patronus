// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>
use crate::ir;
use baa::WidthInt;
use egg::Id;

/// Shadow version of our `[crate::ir::Expr]` that abides by the `egg` rules.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
enum Expr {
    BVSymbol {
        name: ir::StringRef,
        width: WidthInt,
    },
    // TODO
    BVNot([Id; 1], WidthInt),
}

impl egg::Language for Expr {
    fn matches(&self, other: &Self) -> bool {
        // quick check to ensure that we are comparing the same kind of expression
        if std::mem::discriminant(self) != std::mem::discriminant(other) {
            return false;
        }
        // special comparisons for additional attributes
        todo!()
    }

    fn children(&self) -> &[Id] {
        match self {
            Expr::BVNot(cc, _) => cc,
            _ => &[],
        }
    }

    fn children_mut(&mut self) -> &mut [Id] {
        match self {
            Expr::BVNot(cc, _) => cc,
            _ => &mut [],
        }
    }
}

type ExprGraph<N> = egg::EGraph<Expr, N>;

/// Convert from our internal representation to the shadow version suitable for egg.
fn to_eclass<N: egg::Analysis<Expr>>(ctx: &ir::Context, e: ir::ExprRef, graph: &mut ExprGraph<N>) {}
