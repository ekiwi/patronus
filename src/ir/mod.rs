// Copyright 2023 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>
mod analysis;
mod context;
mod expr;
mod serialize;
mod transform;
mod transition_system;
mod type_check;

pub use analysis::{
    analyze_for_serialization, cone_of_influence, cone_of_influence_comb, cone_of_influence_init,
    count_expr_uses, is_usage_root_signal, ExprMetaData, ForEachChild, SerializeMeta, UseCountInt,
    Uses,
};
pub use context::{Context, ExprRef, StringRef};
pub use expr::{ArrayType, Expr, Type};
pub use serialize::SerializableIrNode;
pub use transform::{
    do_transform, replace_anonymous_inputs_with_zero, simplify_expressions,
    simplify_single_expression,
};
pub use transition_system::{
    merge_signal_info, SignalInfo, SignalKind, SignalLabels, State, StateRef, TransitionSystem,
};
pub use type_check::{TypeCheck, TypeCheckError};
