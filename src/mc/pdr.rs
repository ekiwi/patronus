// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::ir::{Context, TransitionSystem};
use crate::mc::{ModelCheckResult, SmtModelCheckerOptions, SmtSolverCmd};

pub struct Pdr {
    solver: SmtSolverCmd,
    opts: SmtModelCheckerOptions,
}

type Result<T> = std::io::Result<T>;

impl Pdr {
    pub fn new(solver: SmtSolverCmd, opts: SmtModelCheckerOptions) -> Self {
        Self { solver, opts }
    }

    pub fn check(&self, ctx: &mut Context, sys: &TransitionSystem) -> Result<ModelCheckResult> {
        Ok(ModelCheckResult::Unknown)
    }
}
