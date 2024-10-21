// Copyright 2023 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

mod smt;
mod types;

pub use crate::sim::interpreter::Simulator;
pub use smt::{
    check_assuming, check_assuming_end, get_smt_value, ModelCheckResult, SmtModelChecker,
    SmtModelCheckerOptions, SmtSolverCmd, TransitionSystemEncoding, UnrollSmtEncoding,
    BITWUZLA_CMD, YICES2_CMD,
};
pub use types::Witness;
