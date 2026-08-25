use crate::expr::*;
use crate::smt::*;
use rustc_hash::FxHashMap;

const ACT_LIT_PREFIX: &str = "__act_lit_";

/// Collection of activation literals used in scope
#[derive(Default)]
pub(crate) struct ActLitScope {
    act_lits: Vec<ExprRef>,
}

impl ActLitScope {
    /// Permanently disable all activation literals in this scope
    pub(crate) fn release(
        &mut self,
        ctx: &mut Context,
        smt_ctx: &mut impl SolverContext,
    ) -> Result<()> {
        for lit in self.act_lits.drain(..) {
            let neg_lit = ctx.not(lit);
            smt_ctx.assert(ctx, neg_lit)?;
        }
        Ok(())
    }
}

#[derive(Default)]
pub(crate) struct ActLitPool {
    /// Activation literal ID tracker
    next_act_id: u64,

    /// Cache mapping from stepped literal to activation literal
    step_lit_cache: FxHashMap<ExprRef, ExprRef>,
}

impl ActLitPool {
    /// Create a new activation literal
    fn create(&mut self, ctx: &mut Context, smt_ctx: &mut impl SolverContext) -> Result<ExprRef> {
        // Intern activation literal and define in solver
        let lit = ctx.bv_symbol(format!("{ACT_LIT_PREFIX}{}", self.next_act_id).as_str(), 1);
        smt_ctx.declare_const(ctx, lit)?;

        // Update activation literal counter and return
        self.next_act_id += 1;
        Ok(lit)
    }

    /// Create a temporary activation literal that is coupled with `body` (i.e. `act => body`)
    /// and registered into `scope`
    pub(crate) fn imply(
        &mut self,
        ctx: &mut Context,
        smt_ctx: &mut impl SolverContext,
        scope: &mut ActLitScope,
        body: ExprRef,
    ) -> Result<ExprRef> {
        // If solver supports compound expression assumptions, then activation literals
        // are not needed
        if smt_ctx.supports_check_assuming_exprs() {
            return Ok(body);
        }

        // Create `act => body` and assert in solver
        let act = self.create(ctx, smt_ctx)?;
        let imp = ctx.implies(act, body);
        smt_ctx.assert(ctx, imp)?;

        // Register activation literal in scope
        scope.act_lits.push(act);
        Ok(act)
    }

    /// Create an activation literal for a stepped cube literal, caching the activation literal
    /// with the associated stepped cube literal
    ///
    /// # Precondition
    /// `stepped_lit` must be stepped
    ///
    /// # Note
    /// Produced activation literal remains in global solver context. This is sound since
    /// `act => stepped_lit` is a permanent fact.
    pub(crate) fn step_lit_act(
        &mut self,
        ctx: &mut Context,
        smt_ctx: &mut impl SolverContext,
        stepped_lit: ExprRef,
    ) -> Result<ExprRef> {
        // Check cache for activation literal
        if let Some(act) = self.step_lit_cache.get(&stepped_lit) {
            return Ok(*act);
        }

        // Create `act => stepped_lit` and assert in solver
        let act = self.create(ctx, smt_ctx)?;
        let imp = ctx.implies(act, stepped_lit);
        smt_ctx.assert(ctx, imp)?;

        // Register stepped literal and its activation literal in cache
        self.step_lit_cache.insert(stepped_lit, act);
        Ok(act)
    }
}

/// Execute closure with a fresh [`ActLitScope`] and clean up all used activation literals in the end
pub(crate) fn with_act_scope<S: SolverContext, T>(
    ctx: &mut Context,
    smt_ctx: &mut S,
    f: impl FnOnce(&mut Context, &mut S, &mut ActLitScope) -> Result<T>,
) -> Result<T> {
    // Create new activation literal scope, run closure, and clean up used activation literals
    let mut scope = ActLitScope::default();
    let res = f(ctx, smt_ctx, &mut scope);
    let cleanup = scope.release(ctx, smt_ctx);

    match res {
        Ok(v) => cleanup.map(|()| v), // Return result from closure, noting cleanup errors
        Err(e) => Err(e),             // Return error produced by closure
    }
}
