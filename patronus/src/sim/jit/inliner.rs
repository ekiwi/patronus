use cranelift::codegen::inline::{Inline, InlineCommand};
use cranelift::codegen::ir::{self, entities, function};

type CalleeQueryServer<'a> =
    &'a dyn Fn(entities::FuncRef, &function::Function) -> Option<&'a function::Function>;

pub(super) struct JITInliner<'a> {
    callee_query_server: CalleeQueryServer<'a>,
}

impl<'a> JITInliner<'a> {
    pub(super) fn new(callee_query_server: CalleeQueryServer<'a>) -> Self {
        Self {
            callee_query_server,
        }
    }
}

impl Inline for JITInliner<'_> {
    fn inline(
        &mut self,
        caller: &function::Function,
        _call_inst: entities::Inst,
        _call_opcode: ir::Opcode,
        callee: entities::FuncRef,
        _call_args: &[entities::Value],
    ) -> InlineCommand<'_> {
        if let Some(callee) = (self.callee_query_server)(callee, caller) {
            InlineCommand::Inline {
                callee: std::borrow::Cow::Borrowed(callee),
                visit_callee: true,
            }
        } else {
            InlineCommand::KeepCall
        }
    }
}
