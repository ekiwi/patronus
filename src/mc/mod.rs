// Copyright 2023 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

mod smt;
mod types;

pub use crate::sim::interpreter::Simulator;
pub use smt::{
    ModelCheckResult, SmtModelChecker, SmtModelCheckerOptions, SmtSolverCmd, BITWUZLA_CMD,
};
pub use types::{parse_big_uint_from_bit_string, Witness, WitnessArray, WitnessValue};
