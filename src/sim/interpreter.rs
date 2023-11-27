// Copyright 2023 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

use super::exec;
use super::exec::Word;
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

    /// Recalculate signals.
    fn update(&mut self);

    /// Advance the state.
    fn step(&mut self);

    /// Change the value or an expression in the simulator. Be careful!
    fn set(&mut self, expr: ExprRef, value: u64);

    fn get(&mut self, expr: ExprRef) -> Option<u64>;

    fn step_count(&self) -> u64;
}

/// Interpreter based simulator for a transition system.
pub struct Interpreter {
    meta: Vec<Option<Instruction>>,
    states: Vec<State>,
    data: Vec<Word>,
    step_count: u64,
}

impl Interpreter {
    pub fn new(ctx: &Context, sys: &TransitionSystem) -> Self {
        let (meta, data_len) = compile(ctx, sys);
        let data = vec![0; data_len];
        let states = sys.states().cloned().collect::<Vec<_>>();
        Self {
            meta,
            data,
            states,
            step_count: 0,
        }
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
            let inst = compile_expr(ctx, sys, ExprRef::from_index(idx), word_count);
            word_count += inst.words as u32;
            meta.push(Some(inst));
        }
    }
    (meta, word_count as usize)
}

fn compile_expr(
    ctx: &Context,
    sys: &TransitionSystem,
    expr_ref: ExprRef,
    offset: u32,
) -> Instruction {
    let expr = ctx.get(expr_ref);
    let kind = sys
        .get_signal(expr_ref)
        .map(|s| s.kind.clone())
        .unwrap_or(SignalKind::Node);
    let tpe = expr.get_type(ctx);
    match tpe.get_bit_vector_width() {
        None => todo!("array support"),
        Some(width) => {
            let words = width.div_ceil(Word::BITS as WidthInt) as u16;
            Instruction {
                offset,
                words,
                expr: expr.clone(),
                result_width: width,
                kind,
                expr_ref,
            }
        }
    }
}

/// Helps execute a unary operation without borrowing conflicts.
macro_rules! exec_unary {
    ($f:path, $data:expr, $d:expr, $s:expr) => {
        if $d.len() == 1 {
            let _src_val = $data[$s][0];
            $f(&mut $data[$d], &[_src_val])
        } else {
            let (_dst_ref, _src_ref) = $crate::sim::exec::split_borrow_1($data, $d, $s);
            $f(_dst_ref, _src_ref)
        }
    };
}

impl Simulator for Interpreter {
    fn init(&mut self, kind: InitKind) {
        // assign default value to all inputs and states
        for inst in self.meta.iter().flatten() {
            if matches!(inst.kind, SignalKind::Input | SignalKind::State) {
                exec::clear(&mut self.data[inst.range()]);
            }
        }

        // update signals since signal init values might need to be computed
        // TODO: more efficient would be to only update expressions that are needed for init
        self.update_all_signals();

        // assign init expressions to signals
        for state in self.states.iter() {
            if let Some(init) = state.init {
                let dst = self.meta[state.symbol.index()].as_ref().unwrap().range();
                let src = self.meta[init.index()].as_ref().unwrap().range();
                exec_unary!(exec::assign, &mut self.data, dst, src);
            }
        }
    }

    fn update(&mut self) {
        self.update_all_signals();
    }

    fn step(&mut self) {
        // assign next expressions to state
        for state in self.states.iter() {
            if let Some(next) = state.next {
                let dst = self.meta[state.symbol.index()].as_ref().unwrap().range();
                let src = self.meta[next.index()].as_ref().unwrap().range();
                exec_unary!(exec::assign, &mut self.data, dst, src);
            }
        }
        self.step_count += 1;
    }

    fn set(&mut self, expr: ExprRef, value: u64) {
        if let Some(m) = &self.meta[expr.index()] {
            let data = &mut self.data[m.range()];
            data[0] = value;
            for other in data.iter_mut().skip(1) {
                *other = 0;
            }
            // println!("Set [{}] = {}", expr.index(), data[0]);
        }
    }

    fn get(&mut self, expr: ExprRef) -> Option<u64> {
        if let Some(m) = &self.meta[expr.index()] {
            let data = &self.data[m.range()];
            let mask = (1u64 << m.result_width) - 1;
            let res = data[0] & mask;
            for other in data.iter().skip(1) {
                assert_eq!(*other, 0, "missing MSB!");
            }
            Some(res)
        } else {
            None
        }
    }

    fn step_count(&self) -> u64 {
        self.step_count
    }
}

impl Interpreter {
    /// Eagerly re-computes all signals in the system.
    fn update_all_signals(&mut self) {
        for inst in self.meta.iter().flatten() {
            update_signal(inst, &mut self.data, &self.meta);
        }
    }
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
    kind: SignalKind,
    result_width: WidthInt,
    // for debugging
    expr_ref: ExprRef,
}

impl Instruction {
    fn range(&self) -> std::ops::Range<usize> {
        let start = self.offset as usize;
        let end = start + self.words as usize;
        start..end
    }
}

/// Helps execute a compare in the context of the update_signal function.
macro_rules! exec_cmp {
    ($f:path, $data:expr, $d:expr, $s:expr) => {
        if $d.len() == 1 {
            let _src_val = $data[$s][0];
            $f(&mut $data[$d], &[_src_val])
        } else {
            let (_dst_ref, _src_ref) =
                $crate::sim::exec::split_borrow_1(&mut $data, $d, $s).expect("aliasing");
            $f(_dst_ref, _src_ref)
        }
    };
}

fn update_signal(inst: &Instruction, data: &mut [Word], instructions: &[Option<Instruction>]) {
    // print!("Executing: {} {:?}", inst.expr_ref.index(), inst.expr);
    match inst.expr {
        Expr::BVSymbol { .. } => {} // nothing to do, value will be set externally
        Expr::BVLiteral { value, width } => {
            // TODO: optimize by only calculating once!
            assert!(width <= BVLiteralInt::BITS);
            data[inst.range()][0] = value;
        }
        // operations that change the bit-width
        Expr::BVZeroExt { e, by, width } => {
            todo!("zext")
        }
        Expr::BVSignExt { .. } => {
            todo!("sext")
        }
        Expr::BVSlice { e, hi, lo } => {
            let e_range = instructions[e.index()].as_ref().unwrap().range();
            let width = hi - lo + 1;
            if width <= 64 {
                data[inst.range()][0] = exec::slice_to_word(&data[e_range], hi, lo);
            } else {
                todo!("deal with larger slices")
            }
        }
        Expr::BVConcat(_, _, _) => {
            todo!("concat")
        }
        // operations that always return a 1-bit value
        Expr::BVEqual(a, b) => {
            let a_range = instructions[a.index()].as_ref().unwrap().range();
            let b_range = instructions[b.index()].as_ref().unwrap().range();
            if exec::cmp_equal(&data[a_range], &data[b_range]) {
                data[inst.range()][0] = 1;
            } else {
                data[inst.range()][0] = 0;
            }
        }
        Expr::BVImplies(_, _) => {
            todo!("implies")
        }
        Expr::BVGreater(_, _) => {
            todo!("greater")
        }
        Expr::BVGreaterSigned(_, _) => {
            todo!("greater signed")
        }
        Expr::BVGreaterEqual(_, _) => {
            todo!("greater equal")
        }
        Expr::BVGreaterEqualSigned(_, _) => {
            todo!("greater equal signed")
        }

        // operations that keep the size
        Expr::BVNot(e, _) => {
            let src = instructions[e.index()].as_ref().unwrap().range();
            exec_unary!(exec::not, data, inst.range(), src);
        }
        Expr::BVNegate(_, _) => {
            todo!("negate")
        }
        Expr::BVAnd(_, _, _) => {
            todo!("and")
        }
        Expr::BVOr(_, _, _) => {
            todo!("or")
        }
        Expr::BVXor(_, _, _) => {
            todo!("xor")
        }
        Expr::BVShiftLeft(_, _, _) => {
            todo!("shift left")
        }
        Expr::BVArithmeticShiftRight(_, _, _) => {
            todo!("arith shift right")
        }
        Expr::BVShiftRight(_, _, _) => {
            todo!("shift right")
        }
        Expr::BVAdd(_, _, _) => {
            todo!("add")
        }
        Expr::BVMul(_, _, _) => {
            todo!("mul")
        }
        Expr::BVSignedDiv(_, _, _) => {
            todo!("signed div")
        }
        Expr::BVUnsignedDiv(_, _, _) => {
            todo!("div")
        }
        Expr::BVSignedMod(_, _, _) => {
            todo!("signed mod")
        }
        Expr::BVSignedRem(_, _, _) => {
            todo!("signed rem")
        }
        Expr::BVUnsignedRem(_, _, _) => {
            todo!("rem")
        }
        Expr::BVSub(_, _, _) => {
            todo!("sub")
        }
        Expr::BVArrayRead { .. } => {
            todo!("array read")
        }
        Expr::BVIte { cond, tru, fals } => {
            let cond_range = instructions[cond.index()].as_ref().unwrap().range();
            let cond_value = data[cond_range][0] != 0;
            let dst = inst.range();
            if cond_value {
                let src = instructions[tru.index()].as_ref().unwrap().range();
                exec_unary!(exec::assign, data, dst, src);
            } else {
                let src = instructions[fals.index()].as_ref().unwrap().range();
                exec_unary!(exec::assign, data, dst, src);
            }
        }
        Expr::ArraySymbol { .. } => {} // nothing to do for symbol
        Expr::ArrayConstant { .. } => {
            todo!("array const")
        }
        Expr::ArrayEqual(_, _) => {
            todo!("array eq")
        }
        Expr::ArrayStore { .. } => {
            todo!("array store")
        }
        Expr::ArrayIte { .. } => {
            todo!("array ite")
        }
    }
    // println!("  --> {:?}", &data[inst.range()]);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn type_size() {
        // 16-bytes for the expression + 8 bytes for storage details
        assert_eq!(
            std::mem::size_of::<Instruction>(),
            std::mem::size_of::<Expr>() + 8 + 8 // debugging data
        );
    }
}
