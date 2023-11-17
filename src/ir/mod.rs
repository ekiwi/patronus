// Copyright 2023 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>
mod analysis;
mod expr;
mod serialize;
mod transition_system;
mod type_check;

pub use analysis::{
    count_expr_uses, find_expr_with_multiple_uses, is_usage_root_signal, ForEachChild,
};
pub use expr::{
    bv_value_fits_width, AddNode, ArrayType, BVLiteralInt, Context, Expr, ExprNodeConstruction,
    ExprRef, GetNode, StringRef, Type, WidthInt,
};
pub use serialize::SerializableIrNode;
pub use transition_system::{SignalInfo, SignalKind, State, StateRef, TransitionSystem};
pub use type_check::{TypeCheck, TypeCheckError};
