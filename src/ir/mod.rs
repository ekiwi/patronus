// Copyright 2023 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>
mod analysis;
mod expr;
mod serialize;
mod transform;
mod transition_system;
mod type_check;
pub mod value;

pub use analysis::{
    analyze_for_serialization, cone_of_influence, count_expr_uses, is_usage_root_signal,
    ExprMetaData, ForEachChild, SerializeMeta, UseCountInt, Uses,
};
pub use expr::{
    bv_value_fits_width, AddNode, ArrayType, BVLiteralInt, Context, Expr, ExprNodeConstruction,
    ExprRef, GetNode, StringRef, Type, WidthInt,
};
pub use serialize::SerializableIrNode;
pub use transform::{do_transform, replace_anonymous_inputs_with_zero, simplify_expressions};
pub use transition_system::{
    merge_signal_info, SignalInfo, SignalKind, SignalLabels, State, StateRef, TransitionSystem,
};
pub use type_check::{TypeCheck, TypeCheckError};
pub use value::{width_to_words, Value, ValueRef, Word};
