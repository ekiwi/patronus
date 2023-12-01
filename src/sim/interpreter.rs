// Copyright 2023 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

use super::exec;
use super::exec::Word;
use crate::ir::*;
use std::collections::{HashMap, HashSet};

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
    update: Program,
    init: Program,
    states: Vec<State>,
    inputs: Vec<ExprRef>,
    data: Vec<Word>,
    step_count: u64,
}

impl<'a> Interpreter<'a> {
    pub fn new(ctx: &'a Context, sys: &TransitionSystem) -> Self {
        let init = compile(ctx, sys, true);
        let update = compile(ctx, sys, false);
        let states = sys.states().cloned().collect::<Vec<_>>();
        let inputs = sys
            .get_signals(|s| s.kind == SignalKind::Input)
            .iter()
            .map(|(e, _)| *e)
            .collect::<Vec<_>>();
        let data = vec![0; update.mem_words as usize];
        Self {
            ctx,
            update,
            init,
            states,
            inputs,
            data,
            step_count: 0,
        }
    }
}

impl<'a> Simulator for Interpreter<'a> {
    fn init(&mut self, kind: InitKind) {
        // allocate memory to execute the init program
        let mut init_data = vec![0; self.init.mem_words as usize];

        // assign default value to all inputs
        for sym in self.inputs.iter() {
            let dst = self.init.get_range(sym).unwrap();
            exec::clear(&mut init_data[dst]);
        }

        // assign default value to all states
        for state in self.states.iter() {
            let dst = self.init.get_range(&state.symbol).unwrap();
            exec::clear(&mut init_data[dst]);
        }

        // execute the init program
        self.init.execute(&mut init_data);

        // copy init values from init to update program
        for state in self.states.iter() {
            // println!("{}", state.symbol.get_symbol_name(self.ctx).unwrap());
            let src = self.init.get_range(&state.symbol).unwrap();
            let dst = self.update.get_range(&state.symbol).unwrap();
            exec::assign(&mut self.data[dst], &init_data[src]);
        }
    }

    fn update(&mut self) {
        self.update.execute(&mut self.data);
    }

    fn step(&mut self) {
        // assign next expressions to state
        for state in self.states.iter() {
            if let Some(next) = state.next {
                let dst_range = self.update.get_range(&state.symbol).unwrap();
                let src_range = self.update.get_range(&next).unwrap();
                let (dst, src) = exec::split_borrow_1(&mut self.data, dst_range, src_range);
                exec::assign(dst, src);
            }
        }
        self.step_count += 1;
    }

    fn set(&mut self, expr: ExprRef, value: u64) {
        if let Some(m) = &self.update.symbols.get(&expr) {
            assert_eq!(m.elements, 1, "cannot set array values with this function");
            let dst = &mut self.data[m.loc.range()];
            exec::assign_word(dst, value);
            // println!("Set [{}] = {}", expr.index(), data[0]);
        }
    }

    fn get(&mut self, expr: ExprRef) -> Option<ValueRef<'_>> {
        // println!("{:?}", expr.get_symbol_name(self.ctx));
        if let Some(m) = &self.update.symbols.get(&expr) {
            assert_eq!(m.elements, 1, "cannot get array values with this function");
            let words = &self.data[m.loc.range()];
            let bits = m.width;
            Some(ValueRef { words, bits })
        } else {
            None
        }
    }

    fn step_count(&self) -> u64 {
        self.step_count
    }
}

/// the result of a compilation
struct Program {
    instructions: Vec<Instr>,
    symbols: HashMap<ExprRef, SymbolInfo>,
    mem_words: u32,
}

struct SymbolInfo {
    loc: Loc,
    width: WidthInt,
    elements: u64,
}

impl Program {
    fn execute(&self, data: &mut [Word]) {
        for instr in self.instructions.iter() {
            exec_instr(instr, data);
        }
    }

    fn get_range(&self, e: &ExprRef) -> Option<std::ops::Range<usize>> {
        if let Some(info) = self.symbols.get(e) {
            let start = info.loc.offset as usize;
            let len = info.elements as usize * info.loc.words as usize;
            Some(start..(start + len))
        } else {
            None
        }
    }
}

/// Converts a transitions system into instructions and the number of Words that need to be allocated
/// * `init_mode` - Indicates whether we want to generate a program for the system init or the system update.
fn compile(ctx: &Context, sys: &TransitionSystem, init_mode: bool) -> Program {
    // we need to be able to indentiy expressions that represent states
    let expr_to_state: HashMap<ExprRef, &State> =
        HashMap::from_iter(sys.states().map(|s| (s.symbol, s)));

    // used to track instruction result allocations
    let mut locs: ExprMetaData<Option<(Loc, WidthInt)>> = ExprMetaData::default();
    let mut symbols = HashMap::new();
    // generated instructions
    let mut instructions = Vec::new();
    // bump allocator
    let mut mem_words = 0u32;

    // keep track of which instructions need to be compiled next
    let mut todo = Vec::new();

    // we want to be able to identify these expression to add them to the `symbol` lookup
    let init_and_next_exprs = get_next_and_init_refs(sys);

    // define roots depending on mode
    if init_mode {
        // calculate the value for each state (which in init mode is the value of the init expression)
        for state in sys.states() {
            todo.push(state.symbol);
        }
        // allocate space for inputs
        for (signal_expr, _) in sys.get_signals(|s| matches!(s.kind, SignalKind::Input)) {
            todo.push(signal_expr);
        }
    } else {
        // calculate the next expression for each state
        for state in sys.states() {
            if let Some(next) = state.next {
                if next != state.symbol {
                    todo.push(next);
                }
            }
        }
        // calculate all other signals that might be observable
        for (signal_expr, _) in sys.get_signals(is_usage_root_signal) {
            todo.push(signal_expr);
        }
    }

    // compile until we are done
    while !todo.is_empty() {
        let expr_ref = todo.pop().unwrap();

        // states get special handling in init mode
        let mut compile_expr_ref = expr_ref;
        if let Some(state) = expr_to_state.get(&expr_ref) {
            if init_mode {
                if let Some(init) = state.init {
                    // compute the init expression instead of the state
                    compile_expr_ref = init; // overwrite!
                }
            }
        }

        // check to see if all children are already compiled
        let expr = ctx.get(compile_expr_ref);
        let mut all_compiled = true;
        expr.for_each_child(|c| {
            if locs.get(*c).is_none() {
                if all_compiled {
                    todo.push(expr_ref); // return expression to the todo list
                }
                all_compiled = false;
                // we need to compile the child first
                todo.push(*c);
            }
        });
        if !all_compiled {
            // something was missing, try again later
            continue;
        }

        // allocate space to store the expression result
        let (loc, width, index_width) = allocate_result_space(expr.get_type(ctx), &mut mem_words);
        *locs.get_mut(expr_ref) = Some((loc, index_width));
        // if the expression is a symbol or a state expression or a usage root, we create a lookup
        let is_root = sys
            .get_signal(compile_expr_ref)
            .map(is_usage_root_signal)
            .unwrap_or(false);
        if expr.is_symbol() || init_and_next_exprs.contains(&compile_expr_ref) || is_root {
            // it is important to use `expr_ref` here!
            symbols.insert(
                expr_ref,
                SymbolInfo {
                    loc,
                    width,
                    elements: 1u64 << index_width,
                },
            );
        }
        // compile expression
        let instr = compile_expr(ctx, sys, compile_expr_ref, loc, &locs, width);
        instructions.push(instr);
    }

    Program {
        instructions,
        symbols,
        mem_words,
    }
}

fn get_next_and_init_refs(sys: &TransitionSystem) -> HashSet<ExprRef> {
    let mut out: HashSet<ExprRef> = HashSet::new();
    for state in sys.states() {
        if let Some(init) = state.init {
            out.insert(init);
        }
        if let Some(next) = state.next {
            out.insert(next);
        }
    }
    out
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
    locs: &ExprMetaData<Option<(Loc, WidthInt)>>,
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

fn compile_expr_type(
    expr: &Expr,
    locs: &ExprMetaData<Option<(Loc, WidthInt)>>,
    ctx: &Context,
) -> InstrType {
    match expr {
        Expr::BVSymbol { .. } => InstrType::Nullary(NullaryOp::BVSymbol),
        Expr::BVLiteral { value, .. } => InstrType::Nullary(NullaryOp::BVLiteral(*value)),
        Expr::BVZeroExt { e, .. } => InstrType::Unary(UnaryOp::ZeroExt, locs[e].unwrap().0),
        Expr::BVSignExt { .. } => todo!("compile sext"),
        Expr::BVSlice { e, hi, lo } => {
            InstrType::Unary(UnaryOp::Slice(*hi, *lo), locs[e].unwrap().0)
        }
        Expr::BVNot(e, width) => InstrType::Unary(UnaryOp::Not(*width), locs[e].unwrap().0),
        Expr::BVNegate(_, _) => todo!(),
        Expr::BVEqual(a, b) => {
            InstrType::Binary(BinaryOp::BVEqual, locs[a].unwrap().0, locs[b].unwrap().0)
        }
        Expr::BVImplies(_, _) => todo!(),
        Expr::BVGreater(a, b) => {
            InstrType::Binary(BinaryOp::Greater, locs[a].unwrap().0, locs[b].unwrap().0)
        }
        Expr::BVGreaterSigned(_, _) => todo!(),
        Expr::BVGreaterEqual(a, b) => InstrType::Binary(
            BinaryOp::GreaterEqual,
            locs[a].unwrap().0,
            locs[b].unwrap().0,
        ),
        Expr::BVGreaterEqualSigned(_, _) => todo!(),
        Expr::BVConcat(a, b, _) => InstrType::Binary(
            BinaryOp::Concat(b.get_bv_type(ctx).unwrap()), // LSB width
            locs[a].unwrap().0,
            locs[b].unwrap().0,
        ),
        Expr::BVAnd(a, b, _) => {
            InstrType::Binary(BinaryOp::And, locs[a].unwrap().0, locs[b].unwrap().0)
        }
        Expr::BVOr(a, b, _) => {
            InstrType::Binary(BinaryOp::Or, locs[a].unwrap().0, locs[b].unwrap().0)
        }
        Expr::BVXor(a, b, _) => {
            InstrType::Binary(BinaryOp::Xor, locs[a].unwrap().0, locs[b].unwrap().0)
        }
        Expr::BVShiftLeft(_, _, _) => todo!(),
        Expr::BVArithmeticShiftRight(_, _, _) => todo!(),
        Expr::BVShiftRight(_, _, _) => todo!(),
        Expr::BVAdd(a, b, width) => InstrType::Binary(
            BinaryOp::Add(*width),
            locs[a].unwrap().0,
            locs[b].unwrap().0,
        ),
        Expr::BVMul(_, _, _) => todo!(),
        Expr::BVSignedDiv(_, _, _) => todo!(),
        Expr::BVUnsignedDiv(_, _, _) => todo!(),
        Expr::BVSignedMod(_, _, _) => todo!(),
        Expr::BVSignedRem(_, _, _) => todo!(),
        Expr::BVUnsignedRem(_, _, _) => todo!(),
        Expr::BVSub(a, b, width) => InstrType::Binary(
            BinaryOp::Sub(*width),
            locs[a].unwrap().0,
            locs[b].unwrap().0,
        ),
        Expr::BVArrayRead { array, index, .. } => {
            let (array_loc, index_width) = locs[array].unwrap();
            assert!(index_width <= Word::BITS, "array too large!");
            InstrType::ArrayRead(array_loc, index_width, locs[index].unwrap().0)
        }
        Expr::BVIte { cond, tru, fals } => InstrType::Tertiary(
            TertiaryOp::BVIte,
            locs[cond].unwrap().0,
            locs[tru].unwrap().0,
            locs[fals].unwrap().0,
        ),
        Expr::ArraySymbol { index_width, .. } => {
            InstrType::Nullary(NullaryOp::ArraySymbol(*index_width))
        }
        Expr::ArrayConstant { .. } => todo!(),
        Expr::ArrayEqual(_, _) => todo!(),
        Expr::ArrayStore { .. } => panic!("Array stores should have been preprocessed!"),
        Expr::ArrayIte { .. } => todo!(),
    }
}

/// Function to evaluate a limited set of expressions that are often used by yosys to define init values.
/// Uses only the destination space to store values.
fn eval_init_value(ctx: &Context, expr_ref: ExprRef, dst: &mut [Word], words: u16) {
    let expr = ctx.get(expr_ref);
    match expr {
        Expr::ArrayStore { array, index, data } => {
            // first evaluate the sub array
            eval_init_value(ctx, *array, dst, words);
            // then apply the write
            let index_value = eval_init_value_bv(ctx, *index);
            let data_value = eval_init_value_bv(ctx, *data);
            println!("TODO: assign @{index_value} := {data_value} ({expr_ref:?})");
        }
        Expr::ArraySymbol { .. } => {
            println!("TODO: implement array copy")
        }
        _ => todo!("Implement support for init expression: {expr:?}"),
    }
}

fn eval_init_value_bv(ctx: &Context, expr_ref: ExprRef) -> u64 {
    let expr = ctx.get(expr_ref);
    match expr {
        Expr::BVLiteral { value, .. } => *value,
        Expr::BVOr(a, b, _) => eval_init_value_bv(ctx, *a) | eval_init_value_bv(ctx, *b),
        Expr::BVAnd(a, b, _) => eval_init_value_bv(ctx, *a) & eval_init_value_bv(ctx, *b),
        _ => todo!("Implement support for init expression: {expr:?}"),
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

impl Instr {
    /// Computes the data range while taking the number of array elements into account
    fn range(&self) -> std::ops::Range<usize> {
        let num_elements = match self.tpe {
            InstrType::Nullary(NullaryOp::ArraySymbol(index_width)) => 1usize << index_width,
            _ => 1,
        };
        let start = self.dst.offset as usize;
        let len = num_elements * self.dst.words as usize;
        start..(start + len)
    }
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
    ArraySymbol(WidthInt), // index width
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
                NullaryOp::ArraySymbol(_) => {}
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
