// Copyright 2023 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

use super::exec::*;
use crate::ir::*;

/// Specifies how to initialize states that do not have
#[derive(Debug, PartialEq, Copy, Clone)]
pub enum InitKind {
    Zero,
    Random,
}

pub trait Simulator {
    /// Load the initial state values.
    fn init(&mut self, kind: InitKind);

    /// Advance the state.
    fn step(&mut self);

    /// Change the value or an expression in the simulator. Be careful!
    fn set(&mut self, expr: ExprRef, value: u64);
}

/// Interpreter based simulator for a transition system.
pub struct Interpreter {
    meta: Vec<Option<Instruction>>,
    data: Vec<Word>,
}

/// Meta data for each expression.
#[derive(Debug, Clone)]
struct Instruction {
    /// Start of the value in the data array.
    offset: u32,
    /// Number of words.
    words: u16,
    /// Expression that we are executing.
    expr: Expr,
}

impl Interpreter {
    pub fn new(ctx: &Context, sys: &TransitionSystem) -> Self {
        let (meta, data_len) = compile(ctx, sys);
        let mut data = Vec::with_capacity(data_len);
        data.resize(data_len, 0);
        Self { meta, data }
    }
}

/// Converts a transitions system into instructions and the number of Words that need to be allocated
fn compile(ctx: &Context, sys: &TransitionSystem) -> (Vec<Option<Instruction>>, usize) {
    let use_counts = count_expr_uses(ctx, sys);
    let mut meta = Vec::with_capacity(use_counts.len());
    let mut word_count = 0u32;
    for (idx, count) in use_counts.iter().enumerate() {
        if *count == 0 {
            meta.push(None);
        } else {
            let inst = compile_expr(ctx, ctx.get(ExprRef::from_index(idx)), word_count);
            word_count += inst.words as u32;
            meta.push(Some(inst));
        }
    }
    (meta, word_count as usize)
}

fn compile_expr(ctx: &Context, expr: &Expr, offset: u32) -> Instruction {
    let tpe = expr.get_type(ctx);
    match tpe.get_bit_vector_width() {
        None => todo!("array support"),
        Some(width) => {
            let words = width.div_ceil(Word::BITS as WidthInt) as u16;
            Instruction {
                offset,
                words,
                expr: expr.clone(),
            }
        }
    }
}

impl Simulator for Interpreter {
    fn init(&mut self, kind: InitKind) {
        println!("TODO: init")
    }

    fn step(&mut self) {
        todo!()
    }

    fn set(&mut self, expr: ExprRef, value: u64) {
        todo!("set({expr:?}, {value})")
    }
}

impl Instruction {
    fn range(&self) -> std::ops::Range<usize> {
        let start = self.offset as usize;
        let end = start + self.words as usize;
        start..end
    }
}

fn update_signal(data: &mut [Word], inst: &Instruction, instructions: &[Instruction]) {
    let dest = &mut data[inst.range()];
    match inst.expr {
        Expr::BVSymbol { .. } => {} // nothing to do, value will be set externally
        Expr::BVLiteral { .. } => {} // nothing to do, value will be calculated once
        // operations that change the bit-width
        Expr::BVZeroExt { e, by, width } => {
            todo!("zext")
        }
        Expr::BVSignExt { .. } => {
            todo!("sext")
        }
        Expr::BVSlice { .. } => {
            todo!("slice")
        }
        Expr::BVNot(_, _) => {}
        Expr::BVNegate(_, _) => {}
        Expr::BVEqual(_, _) => {}
        Expr::BVImplies(_, _) => {}
        Expr::BVGreater(_, _) => {}
        Expr::BVGreaterSigned(_, _) => {}
        Expr::BVGreaterEqual(_, _) => {}
        Expr::BVGreaterEqualSigned(_, _) => {}
        Expr::BVConcat(_, _, _) => {}
        Expr::BVAnd(_, _, _) => {}
        Expr::BVOr(_, _, _) => {}
        Expr::BVXor(_, _, _) => {}
        Expr::BVShiftLeft(_, _, _) => {}
        Expr::BVArithmeticShiftRight(_, _, _) => {}
        Expr::BVShiftRight(_, _, _) => {}
        Expr::BVAdd(_, _, _) => {}
        Expr::BVMul(_, _, _) => {}
        Expr::BVSignedDiv(_, _, _) => {}
        Expr::BVUnsignedDiv(_, _, _) => {}
        Expr::BVSignedMod(_, _, _) => {}
        Expr::BVSignedRem(_, _, _) => {}
        Expr::BVUnsignedRem(_, _, _) => {}
        Expr::BVSub(_, _, _) => {}
        Expr::BVArrayRead { .. } => {}
        Expr::BVIte { .. } => {}
        Expr::ArraySymbol { .. } => {}
        Expr::ArrayConstant { .. } => {}
        Expr::ArrayEqual(_, _) => {}
        Expr::ArrayStore { .. } => {}
        Expr::ArrayIte { .. } => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn type_size() {
        // 16-bytes for the expression + 8 bytes for storage details
        assert_eq!(
            std::mem::size_of::<Instruction>(),
            std::mem::size_of::<Expr>() + 8
        );
    }
}
