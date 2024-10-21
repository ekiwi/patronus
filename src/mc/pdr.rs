// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::ir::{Context, TransitionSystem};
use crate::mc::{
    check_assuming, ModelCheckResult, SmtModelCheckerOptions, SmtSolverCmd,
    TransitionSystemEncoding, UnrollSmtEncoding,
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
        let constraints = sys.constraints();
        let bad_states = sys.bad_states();

        // no bad states means that the check always passes
        if bad_states.is_empty() {
            return Ok(ModelCheckResult::Success);
        }

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
        enc.init_at(ctx, &mut smt_ctx, 0)?;

        // check to see if bad state is reachable at init state
        // assume all constraints hold in this step
        for (expr_ref, _) in constraints.iter() {
            let expr = enc.get_at(ctx, &mut smt_ctx, *expr_ref, 0);
            smt_ctx.assert(expr)?;
        }
        let all_bads = bad_states
            .iter()
            .map(|(expr_ref, _)| enc.get_at(ctx, &mut smt_ctx, *expr_ref, 0))
            .collect::<Vec<_>>();
        let any_bad = smt_ctx.or_many(all_bads);
        let res = check_assuming(&mut smt_ctx, any_bad, &self.solver)?;

        println!("Response for R_0 & !P: {res:?}");

        // let mut trace = vec![];

        Ok(ModelCheckResult::Unknown)
    }
}
