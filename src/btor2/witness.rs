// Copyright 2023 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

use crate::btor2::parse::tokenize_line;
use crate::ir;
use crate::ir::{SignalKind, TypeCheck};
use crate::mc::{State, Value, Witness};
use std::io::{BufRead, Write};

enum ParserState {
    Start,
    WaitForProp,
    WaitForFrame,
    ParsingStatesAt(u64),
    ParsingInputsAt(u64),
    Done,
}

type Result<T> = std::io::Result<T>;

pub fn parse_witness(input: &mut impl BufRead) -> Result<Witness> {
    let witnesses = parse_witnesses(input, 1)?;
    Ok(witnesses.into_iter().next().unwrap())
}

pub fn parse_witnesses(input: &mut impl BufRead, parse_max: usize) -> Result<Vec<Witness>> {
    let mut state = ParserState::Start;
    let mut out = Vec::with_capacity(1);
    let mut wit = Witness::default();
    let mut inputs = State::default();

    let finish_witness = |out: &mut Vec<Witness>, wit: &mut Witness| {
        out.push(std::mem::replace(wit, Witness::default()));
        if out.len() >= parse_max {
            ParserState::Done
        } else {
            ParserState::Start
        }
    };
    let start_inputs = |line: &str, wit: &Witness| {
        let at = u64::from_str_radix(&line[1..], 10).unwrap();
        assert_eq!(at as usize, wit.inputs.len());
        ParserState::ParsingInputsAt(at)
    };
    let finish_inputs = |wit: &mut Witness, inputs: &mut State| {
        wit.inputs.push(std::mem::replace(inputs, State::default()));
    };
    let start_state = |line: &str| {
        let at = u64::from_str_radix(&line[1..], 10).unwrap();
        ParserState::ParsingStatesAt(at)
    };

    for line_res in input.lines() {
        let full_line = line_res?;
        let line = full_line.trim();
        if line.is_empty() || line.starts_with(";") {
            continue; // skip blank lines and comments
        }

        state = match state {
            ParserState::Start => {
                assert_eq!(
                    line, "sat",
                    "Expected witness header to be `sat`, not `{}`",
                    line
                );
                ParserState::WaitForProp
            }
            ParserState::Done => break,
            ParserState::WaitForProp => {
                let tok = tokenize_line(line);
                for token in tok.tokens {
                    if token.starts_with("b") {
                        let num = u32::from_str_radix(&token[1..], 10).unwrap();
                        wit.failed_safety.push(num);
                    } else if token.starts_with("j") {
                        panic!("justice props are not supported");
                    } else {
                        panic!("unexpected property token: {}", token);
                    }
                }
                ParserState::WaitForFrame
            }
            ParserState::WaitForFrame => {
                if line.starts_with("@") {
                    // no state initialization frame -> jump straight to inputs
                    start_inputs(line, &wit)
                } else {
                    assert_eq!(line, "#0", "Expected initial state frame, not: {}", line);
                    start_state(line)
                }
            }
            ParserState::ParsingStatesAt(at) => {
                if line == "." {
                    let next = finish_witness(&mut out, &mut wit);
                    if out.len() >= parse_max {
                        break;
                    }
                    next
                } else if line.starts_with("@") {
                    start_inputs(line, &wit)
                } else {
                    let tok = tokenize_line(line);
                    let (ii, _, data, index) = parse_assignment(&tok.tokens);
                    println!("TODO: {ii} = {data:?}");
                    // continue reading in state
                    ParserState::ParsingStatesAt(at)
                }
            }
            ParserState::ParsingInputsAt(at) => {
                if line == "." {
                    finish_inputs(&mut wit, &mut inputs);
                    finish_witness(&mut out, &mut wit)
                } else if line.starts_with("@") {
                    finish_inputs(&mut wit, &mut inputs);
                    start_inputs(line, &wit)
                } else if line.starts_with("#") {
                    finish_inputs(&mut wit, &mut inputs);
                    start_state(line)
                } else {
                    let tok = tokenize_line(line);
                    let (ii, _, data, index) = parse_assignment(&tok.tokens);
                    println!("TODO: {ii} = {data:?}");
                    // continue reading in inputs
                    ParserState::ParsingInputsAt(at)
                }
            }
        };
    }

    Ok(out)
}

fn parse_assignment<'a>(tokens: &'a [&'a str]) -> (u64, &'a str, Value, Option<Value>) {
    let is_array = match tokens.len() {
        3 => false, // its a bit vector
        4 => true,
        _ => panic!(
            "Expected assignment to consist of 3-4 parts, not: {:?}",
            tokens
        ),
    };
    // index of the state or input
    let index = u64::from_str_radix(tokens[0], 10).unwrap();
    let name = *tokens.last().unwrap();
    let (value, array_index) = if is_array {
        let index_str = tokens[1];
        assert!(index_str.starts_with("[") && index_str.ends_with("]"));
        let array_index = Value::from_bit_string(&index_str[1..index_str.len() - 1]);
        (Value::from_bit_string(tokens[2]), Some(array_index))
    } else {
        (Value::from_bit_string(tokens[1]), None)
    };
    (index, name, value, array_index)
}

pub fn print_witness(
    out: &mut impl Write,
    witness: &Witness,
    sys: &ir::TransitionSystem,
    ctx: &ir::Context,
) -> std::io::Result<()> {
    writeln!(out, "sat")?;

    // declare failed properties
    for (ii, bad_id) in witness.failed_safety.iter().enumerate() {
        let is_last = ii + 1 == witness.failed_safety.len();
        write!(out, "b{bad_id}")?;
        if is_last {
            writeln!(out, "")?;
        } else {
            write!(out, " ")?;
        }
    }

    // print starting state (if non-empty)
    if !witness.init.is_empty() {
        writeln!(out, "#0")?;
        for (id, (maybe_value, state)) in witness.init.iter().zip(sys.states()).enumerate() {
            if let Some(value) = maybe_value {
                let width = state.symbol.get_type(ctx).get_bit_vector_width().unwrap();
                let name = state.symbol.get_symbol_name(ctx).unwrap();
                writeln!(
                    out,
                    "{id} {} {}@0",
                    value.to_bit_string(width).unwrap(),
                    name
                )?;
            }
        }
    }

    // print inputs
    let inputs = sys.get_signals(|s| s.kind == SignalKind::Input);
    for (k, values) in witness.inputs.iter().enumerate() {
        writeln!(out, "@{k}")?;
        for (id, (maybe_value, (input_sym, _))) in values.iter().zip(inputs.iter()).enumerate() {
            if let Some(value) = maybe_value {
                let width = input_sym.get_type(ctx).get_bit_vector_width().unwrap();
                let name = input_sym.get_symbol_name(ctx).unwrap();
                writeln!(
                    out,
                    "{id} {} {}@{k}",
                    value.to_bit_string(width).unwrap(),
                    name
                )?;
            }
        }
    }

    writeln!(out, ".")?;

    Ok(())
}
