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

    fn get(&mut self, expr: ExprRef) -> Option<ValueRef<'_>>;

    fn step_count(&self) -> u64;
}

/// Interpreter based simulator for a transition system.
pub struct Interpreter<'a> {
    ctx: &'a Context,
    instructions: Vec<Option<Instr>>,
    states: Vec<State>,
    data: Vec<Word>,
    step_count: u64,
}

impl<'a> Interpreter<'a> {
    pub fn new(ctx: &'a Context, sys: &TransitionSystem) -> Self {
        let use_counts = count_expr_uses_without_init(ctx, sys);
        let (meta, data_len) = compile(ctx, sys, &use_counts);
        let data = vec![0; data_len];
        let mut states = Vec::with_capacity(sys.states().len());
        for state in sys.states() {
            if use_counts[state.symbol.index()] > 0 {
                states.push(state.clone());
            }
        }
        Self {
            ctx,
            instructions: meta,
            data,
            states,
            step_count: 0,
        }
    }
}

/// Converts a transitions system into instructions and the number of Words that need to be allocated
fn compile(
    ctx: &Context,
    sys: &TransitionSystem,
    use_counts: &[u32],
) -> (Vec<Option<Instr>>, usize) {
    // used to track instruction result allocations
    let mut locs: Vec<Option<(Loc, WidthInt)>> = Vec::with_capacity(use_counts.len());
    let mut instructions = Vec::new();
    let mut word_count = 0u32;
    for (idx, count) in use_counts.iter().enumerate() {
        let expr = ExprRef::from_index(idx);
        if *count == 0 {
            locs.push(None); // no space needed
            instructions.push(None); // TODO: we would like to store the instructions compacted
        } else {
            let tpe = expr.get_type(ctx);
            let (loc, width, index_width) = allocate_result_space(tpe, &mut word_count);
            locs.push(Some((loc, index_width)));
            let instr = compile_expr(ctx, sys, expr, loc, &locs, width);
            instructions.push(Some(instr));
        }
    }
    (instructions, word_count as usize)
}

fn allocate_result_space(tpe: Type, word_count: &mut u32) -> (Loc, WidthInt, WidthInt) {
    match tpe {
        Type::BV(width) => {
            let words = width.div_ceil(Word::BITS as WidthInt) as u16;
            let offset = *word_count;
            *word_count += words as u32;
            let loc = Loc { offset, words };
            (loc, width, 0)
        }
        Type::Array(ArrayType {
            index_width,
            data_width,
        }) => {
            let words = data_width.div_ceil(Word::BITS as WidthInt) as u16;
            let offset = *word_count;
            let entries = 1u32 << index_width;
            *word_count += words as u32 * entries;
            let loc = Loc { offset, words };
            (loc, data_width, index_width)
        }
    }
}

fn compile_expr(
    ctx: &Context,
    sys: &TransitionSystem,
    expr_ref: ExprRef,
    dst: Loc,
    locs: &[Option<(Loc, WidthInt)>],
    result_width: WidthInt,
) -> Instr {
    let expr = ctx.get(expr_ref);
    let kind = sys
        .get_signal(expr_ref)
        .map(|s| s.kind.clone())
        .unwrap_or(SignalKind::Node);
    let tpe = compile_expr_type(expr, locs, ctx);
    let do_trace = false; // set to true for debugging
    Instr {
        dst,
        tpe,
        kind,
        result_width,
        do_trace,
    }
}

fn compile_expr_type(expr: &Expr, locs: &[Option<(Loc, WidthInt)>], ctx: &Context) -> InstrType {
    match expr {
        Expr::BVSymbol { .. } => InstrType::Nullary(NullaryOp::BVSymbol),
        Expr::BVLiteral { value, .. } => InstrType::Nullary(NullaryOp::BVLiteral(*value)),
        Expr::BVZeroExt { e, .. } => InstrType::Unary(UnaryOp::ZeroExt, locs[e.index()].unwrap().0),
        Expr::BVSignExt { .. } => todo!("compile sext"),
        Expr::BVSlice { e, hi, lo } => {
            InstrType::Unary(UnaryOp::Slice(*hi, *lo), locs[e.index()].unwrap().0)
        }
        Expr::BVNot(e, width) => InstrType::Unary(UnaryOp::Not(*width), locs[e.index()].unwrap().0),
        Expr::BVNegate(_, _) => todo!(),
        Expr::BVEqual(a, b) => InstrType::Binary(
            BinaryOp::BVEqual,
            locs[a.index()].unwrap().0,
            locs[b.index()].unwrap().0,
        ),
        Expr::BVImplies(_, _) => todo!(),
        Expr::BVGreater(a, b) => InstrType::Binary(
            BinaryOp::Greater,
            locs[a.index()].unwrap().0,
            locs[b.index()].unwrap().0,
        ),
        Expr::BVGreaterSigned(_, _) => todo!(),
        Expr::BVGreaterEqual(a, b) => InstrType::Binary(
            BinaryOp::GreaterEqual,
            locs[a.index()].unwrap().0,
            locs[b.index()].unwrap().0,
        ),
        Expr::BVGreaterEqualSigned(_, _) => todo!(),
        Expr::BVConcat(a, b, _) => InstrType::Binary(
            BinaryOp::Concat(b.get_bv_type(ctx).unwrap()), // LSB width
            locs[a.index()].unwrap().0,
            locs[b.index()].unwrap().0,
        ),
        Expr::BVAnd(a, b, _) => InstrType::Binary(
            BinaryOp::And,
            locs[a.index()].unwrap().0,
            locs[b.index()].unwrap().0,
        ),
        Expr::BVOr(a, b, _) => InstrType::Binary(
            BinaryOp::Or,
            locs[a.index()].unwrap().0,
            locs[b.index()].unwrap().0,
        ),
        Expr::BVXor(a, b, _) => InstrType::Binary(
            BinaryOp::Xor,
            locs[a.index()].unwrap().0,
            locs[b.index()].unwrap().0,
        ),
        Expr::BVShiftLeft(_, _, _) => todo!(),
        Expr::BVArithmeticShiftRight(_, _, _) => todo!(),
        Expr::BVShiftRight(_, _, _) => todo!(),
        Expr::BVAdd(a, b, width) => InstrType::Binary(
            BinaryOp::Add(*width),
            locs[a.index()].unwrap().0,
            locs[b.index()].unwrap().0,
        ),
        Expr::BVMul(_, _, _) => todo!(),
        Expr::BVSignedDiv(_, _, _) => todo!(),
        Expr::BVUnsignedDiv(_, _, _) => todo!(),
        Expr::BVSignedMod(_, _, _) => todo!(),
        Expr::BVSignedRem(_, _, _) => todo!(),
        Expr::BVUnsignedRem(_, _, _) => todo!(),
        Expr::BVSub(a, b, width) => InstrType::Binary(
            BinaryOp::Sub(*width),
            locs[a.index()].unwrap().0,
            locs[b.index()].unwrap().0,
        ),
        Expr::BVArrayRead { array, index, .. } => {
            let (array_loc, index_width) = locs[array.index()].unwrap();
            assert!(index_width <= Word::BITS, "array too large!");
            InstrType::ArrayRead(array_loc, index_width, locs[index.index()].unwrap().0)
        }
        Expr::BVIte { cond, tru, fals } => InstrType::Tertiary(
            TertiaryOp::BVIte,
            locs[cond.index()].unwrap().0,
            locs[tru.index()].unwrap().0,
            locs[fals.index()].unwrap().0,
        ),
        Expr::ArraySymbol { .. } => InstrType::Nullary(NullaryOp::ArraySymbol),
        Expr::ArrayConstant { .. } => todo!(),
        Expr::ArrayEqual(_, _) => todo!(),
        Expr::ArrayStore { .. } => panic!("Array stores should have been preprocessed!"),
        Expr::ArrayIte { .. } => todo!(),
    }
}

impl<'a> Simulator for Interpreter<'a> {
    fn init(&mut self, kind: InitKind) {
        // assign default value to all inputs and states
        for inst in self.instructions.iter().flatten() {
            if matches!(inst.kind, SignalKind::Input | SignalKind::State) {
                exec::clear(&mut self.data[inst.dst.range()]);
            }
        }

        // update signals since signal init values might need to be computed
        // TODO: more efficient would be to only update expressions that are needed for init
        self.update_all_signals();

        // assign init expressions to signals
        for state in self.states.iter() {
            if let Some(init) = state.init {
                let dst_range = self.instructions[state.symbol.index()]
                    .as_ref()
                    .unwrap()
                    .dst
                    .range();
                let src_range = self.instructions[init.index()]
                    .as_ref()
                    .unwrap()
                    .dst
                    .range();
                let (dst, src) = exec::split_borrow_1(&mut self.data, dst_range, src_range);
                exec::assign(dst, src);
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
                let dst_range = self.instructions[state.symbol.index()]
                    .as_ref()
                    .unwrap()
                    .dst
                    .range();
                let src_range = self.instructions[next.index()]
                    .as_ref()
                    .unwrap()
                    .dst
                    .range();
                let (dst, src) = exec::split_borrow_1(&mut self.data, dst_range, src_range);
                exec::assign(dst, src);
            }
        }
        self.step_count += 1;
    }

    fn set(&mut self, expr: ExprRef, value: u64) {
        if let Some(m) = &self.instructions[expr.index()] {
            let dst = &mut self.data[m.dst.range()];
            exec::assign_word(dst, value);
            // println!("Set [{}] = {}", expr.index(), data[0]);
        }
    }

    fn get(&mut self, expr: ExprRef) -> Option<ValueRef<'_>> {
        if let Some(m) = &self.instructions[expr.index()] {
            let words = &self.data[m.dst.range()];
            let bits = m.result_width;
            Some(ValueRef { words, bits })
        } else {
            None
        }
    }

    fn step_count(&self) -> u64 {
        self.step_count
    }
}

impl<'a> Interpreter<'a> {
    /// Eagerly re-computes all signals in the system.
    fn update_all_signals(&mut self) {
        for instr in self.instructions.iter().flatten() {
            exec_instr(instr, &mut self.data);
        }
    }
}

/// Contains a pointer to a value.
pub struct ValueRef<'a> {
    bits: WidthInt,
    words: &'a [Word],
}

impl<'a> ValueRef<'a> {
    pub fn to_u64(&self) -> Option<u64> {
        match self.words.len() {
            0 => Some(0),
            1 => Some(self.words[0] & exec::mask(self.bits)),
            _ => {
                // check to see if all msbs are zero
                for word in self.words.iter().skip(1) {
                    if *word != 0 {
                        return None;
                    }
                }
                Some(self.words[0])
            }
        }
    }

    pub fn to_bit_string(&self) -> String {
        exec::to_bit_str(self.words, self.bits)
    }

    pub fn to_big_uint(&self) -> num_bigint::BigUint {
        exec::to_big_uint(self.words)
    }
}

#[derive(Debug, Clone)]
struct Instr {
    dst: Loc,
    tpe: InstrType,
    kind: SignalKind,       // TODO: move to symbol meta-data or similar structure
    result_width: WidthInt, // TODO: move to symbol meta-data
    do_trace: bool,         // for debugging
}

#[derive(Debug, Clone)]
enum InstrType {
    Nullary(NullaryOp),
    Unary(UnaryOp, Loc),
    Binary(BinaryOp, Loc, Loc),
    Tertiary(TertiaryOp, Loc, Loc, Loc),
    ArrayRead(Loc, WidthInt, Loc), // array loc + array index width + index loc
}

#[derive(Debug, Clone)]
enum NullaryOp {
    BVSymbol,
    ArraySymbol,
    BVLiteral(BVLiteralInt),
}

#[derive(Debug, Clone)]
enum UnaryOp {
    Slice(WidthInt, WidthInt),
    ZeroExt,
    Not(WidthInt),
}

#[derive(Debug, Clone)]
enum BinaryOp {
    BVEqual,
    Greater,
    GreaterEqual,
    Concat(WidthInt), // width of the lsb
    Or,
    And,
    Xor,
    Add(WidthInt),
    Sub(WidthInt),
}

#[derive(Debug, Clone)]
enum TertiaryOp {
    BVIte,
}

#[derive(Debug, Clone, Copy)]
struct Loc {
    /// Start of the value in the data array.
    offset: u32,
    /// Number of words.
    words: u16,
}

impl Loc {
    fn range(&self) -> std::ops::Range<usize> {
        let start = self.offset as usize;
        let end = start + self.words as usize;
        start..end
    }
}

fn exec_instr(instr: &Instr, data: &mut [Word]) {
    match &instr.tpe {
        InstrType::Nullary(tpe) => {
            match tpe {
                NullaryOp::BVSymbol => {}
                NullaryOp::ArraySymbol => {}
                NullaryOp::BVLiteral(value) => {
                    // TODO: optimize by only calculating once!
                    let dst = &mut data[instr.dst.range()];
                    exec::assign_word(dst, *value);
                    if instr.do_trace {
                        println!(
                            "{} <= {tpe:?} = ",
                            exec::to_bit_str(dst, instr.result_width)
                        );
                    }
                }
            }
        }
        InstrType::Unary(tpe, a_loc) => {
            let (dst, a) = exec::split_borrow_1(data, instr.dst.range(), a_loc.range());
            match tpe {
                UnaryOp::Slice(hi, lo) => exec::slice(dst, a, *hi, *lo),
                UnaryOp::Not(width) => exec::not(dst, a, *width),
                UnaryOp::ZeroExt => exec::zero_extend(dst, a),
            }
            if instr.do_trace {
                println!(
                    "{} <= {tpe:?} = {}",
                    exec::to_bit_str(dst, instr.result_width),
                    exec::to_bit_str(a, a.len() as WidthInt * Word::BITS)
                );
            }
        }
        InstrType::Binary(tpe, a_loc, b_loc) => {
            let (dst, a, b) =
                exec::split_borrow_2(data, instr.dst.range(), a_loc.range(), b_loc.range());
            if instr.do_trace {
                println!("Old dst: {}", exec::to_bit_str(dst, instr.result_width));
            }
            match tpe {
                BinaryOp::BVEqual => dst[0] = exec::bool_to_word(exec::cmp_equal(a, b)),
                BinaryOp::Greater => dst[0] = exec::bool_to_word(exec::cmp_greater(a, b)),
                BinaryOp::GreaterEqual => {
                    dst[0] = exec::bool_to_word(exec::cmp_greater_equal(a, b))
                }
                BinaryOp::Concat(lsb_width) => exec::concat(dst, a, b, *lsb_width),
                BinaryOp::Or => exec::or(dst, a, b),
                BinaryOp::And => exec::and(dst, a, b),
                BinaryOp::Xor => exec::xor(dst, a, b),
                BinaryOp::Add(width) => exec::add(dst, a, b, *width),
                BinaryOp::Sub(width) => exec::sub(dst, a, b, *width),
            }
            if instr.do_trace {
                println!(
                    "{} <= {tpe:?} = {}, {}",
                    exec::to_bit_str(dst, instr.result_width),
                    exec::to_bit_str(a, a.len() as WidthInt * Word::BITS),
                    exec::to_bit_str(b, b.len() as WidthInt * Word::BITS)
                );
            }
        }
        InstrType::Tertiary(tpe, a_loc, b_loc, c_loc) => match tpe {
            TertiaryOp::BVIte => {
                let cond_value = exec::read_bool(&data[a_loc.range()]);
                if cond_value {
                    let (dst, src) = exec::split_borrow_1(data, instr.dst.range(), b_loc.range());
                    exec::assign(dst, src);
                } else {
                    let (dst, src) = exec::split_borrow_1(data, instr.dst.range(), c_loc.range());
                    exec::assign(dst, src);
                }
            }
        },
        InstrType::ArrayRead(array, index_width, index) => {
            let index_value = data[index.range()][0] & exec::mask(*index_width);
            let src_start = array.offset as usize + array.words as usize * index_value as usize;
            let src_range = src_start..(src_start + array.words as usize);
            let (dst, src) = exec::split_borrow_1(data, instr.dst.range(), src_range);
            exec::assign(dst, src);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn type_size() {
        // 4 bytes for offset, 2 bytes for number of words
        assert_eq!(std::mem::size_of::<Loc>(), 8);

        // contains value and width for literals
        assert_eq!(std::mem::size_of::<NullaryOp>(), 16);

        // contains a width for concatenation
        assert_eq!(std::mem::size_of::<BinaryOp>(), 8);

        // currently there is only one option
        assert_eq!(std::mem::size_of::<TertiaryOp>(), 0);

        // instruction type is twice as large as the expr because it includes all storage details
        assert_eq!(std::mem::size_of::<InstrType>(), 32);

        // 16-bytes for the instruction type + 16 bytes for storage details and other meta info
        assert_eq!(
            std::mem::size_of::<Instr>(),
            std::mem::size_of::<InstrType>() + 16
        );
    }
}
