// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::ir::{Context, TransitionSystem};
use crate::mc::{
    ModelCheckResult, SmtModelCheckerOptions, SmtSolverCmd, TransitionSystemEncoding,
    UnrollSmtEncoding,
};

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
        let replay_file = if self.opts.save_smt_replay {
            Some(std::fs::File::create("replay.smt")?)
        } else {
            None
        };
        let mut smt_ctx = easy_smt::ContextBuilder::new()
            .solver(self.solver.name, self.solver.args)
            .replay_file(replay_file)
            .build()?;

        // z3 only supports the non-standard as-const array syntax when the logic is set to ALL
        let logic = if self.solver.name == "z3" {
            "ALL"
        } else if self.solver.supports_uf {
            "QF_AUFBV"
        } else {
            "QF_ABV"
        };
        smt_ctx.set_logic(logic)?;

        let mut enc = UnrollSmtEncoding::new(ctx, sys, false);
        enc.define_header(&mut smt_ctx)?;

        // let mut trace = vec![];

        Ok(ModelCheckResult::Unknown)
    }
}
