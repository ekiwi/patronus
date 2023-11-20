// Copyright 2023 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

use crate::btor2::parse::tokenize_line;
use crate::ir;
use crate::mc::{parse_big_uint_from_bit_string, Witness, WitnessArray, WitnessValue};
use num_bigint::BigUint;
use std::borrow::Cow;
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
    let mut inputs = Vec::default();

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
    let finish_inputs = |wit: &mut Witness, inputs: &mut Vec<_>| {
        wit.inputs.push(std::mem::replace(inputs, Vec::default()));
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
                    if at == 0 {
                        // we ignore anything but the starting state
                        let (ii, name, value) = parse_assignment(&tok.tokens);
                        ensure_space(&mut wit.init, ii);
                        wit.init[ii] = Some(value);
                        ensure_space(&mut wit.init_names, ii);
                        wit.init_names[ii] = Some(name.to_string());
                    }
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
                    let (ii, name, value) = parse_assignment(&tok.tokens);
                    ensure_space(&mut inputs, ii);
                    inputs[ii] = Some(value);
                    if wit.inputs.is_empty() {
                        // the first time around, we save the names
                        ensure_space(&mut wit.input_names, ii);
                        wit.input_names[ii] = Some(name.to_string());
                    }
                    // continue reading in inputs
                    ParserState::ParsingInputsAt(at)
                }
            }
        };
    }

    Ok(out)
}

/// Expands the vector `v` if necessary to ensure that `index` is a valid entry.
fn ensure_space<T: Default + Clone>(v: &mut Vec<T>, index: usize) {
    if index >= v.len() {
        v.resize(index + 1, T::default());
    }
}

fn parse_assignment<'a>(tokens: &'a [&'a str]) -> (usize, &'a str, WitnessValue) {
    let is_array = match tokens.len() {
        3 => false, // its a bit vector
        4 => true,
        _ => panic!(
            "Expected assignment to consist of 3-4 parts, not: {:?}",
            tokens
        ),
    };
    // index of the state or input
    let index = u64::from_str_radix(tokens[0], 10).unwrap() as usize;
    // often the real name is followed by `@0` or `#0`, etc.
    // while `#` is generally used for states, it is not 100% consistent, e.g., btormc
    // might use `@0` instead of `#0` for arrays
    let name = tokens
        .last()
        .unwrap()
        .split("@")
        .next()
        .unwrap()
        .split("#")
        .next()
        .unwrap();
    if is_array {
        let index_str = tokens[1];
        assert!(index_str.starts_with("[") && index_str.ends_with("]"));
        let (index_value, index_width) =
            parse_big_uint_from_bit_string(&index_str[1..index_str.len() - 1]);
        let (data_value, data_width) = parse_big_uint_from_bit_string(tokens[2]);
        let value = WitnessArray {
            tpe: ir::ArrayType {
                index_width,
                data_width,
            },
            default: None,
            updates: vec![(index_value, data_value)],
        };
        (index, name, WitnessValue::Array(value))
    } else {
        let (value, width) = parse_big_uint_from_bit_string(tokens[1]);
        (index, name, WitnessValue::Scalar(value, width))
    }
}

pub fn witness_to_string(witness: &Witness) -> String {
    let mut buf = Vec::new();
    print_witness(&mut buf, witness).expect("Failed to write to string!");
    String::from_utf8(buf).expect("Failed to read string we wrote!")
}

pub fn print_witness(out: &mut impl Write, witness: &Witness) -> std::io::Result<()> {
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
        assert_eq!(witness.init.len(), witness.init_names.len());
        writeln!(out, "#0")?;
        for (id, (maybe_value, maybe_name)) in witness
            .init
            .iter()
            .zip(witness.init_names.iter())
            .enumerate()
        {
            if let Some(value) = maybe_value {
                let name = maybe_name
                    .as_ref()
                    .map(Cow::from)
                    .unwrap_or(Cow::from(format!("state_{}", id)));
                print_witness_value(out, value, &name, id, "#0")?;
            }
        }
    }

    // print inputs
    for (k, values) in witness.inputs.iter().enumerate() {
        assert_eq!(values.len(), witness.input_names.len());
        writeln!(out, "@{k}")?;
        let suffix = format!("@{k}");
        for (id, (maybe_value, maybe_name)) in
            values.iter().zip(witness.input_names.iter()).enumerate()
        {
            if let Some(value) = maybe_value {
                let name = maybe_name
                    .as_ref()
                    .map(Cow::from)
                    .unwrap_or(Cow::from(format!("input_{}", id)));
                print_witness_value(out, value, &name, id, &suffix)?;
            }
        }
    }

    writeln!(out, ".")?;

    Ok(())
}

/// Returns the value as a fixed with bit string.
fn to_bit_string(value: &BigUint, width: ir::WidthInt) -> Option<String> {
    let base_str = value.to_str_radix(2);
    let base_len = base_str.len();
    if base_len == width as usize {
        Some(base_str)
    } else {
        // pad with zeros
        assert!(base_len < width as usize);
        let zeros = width as usize - base_len;
        let mut out = "0".repeat(zeros);
        out.push_str(&base_str);
        Some(out)
    }
}

fn print_witness_value(
    out: &mut impl Write,
    value: &WitnessValue,
    name: &str,
    id: usize,
    suffix: &str,
) -> std::io::Result<()> {
    match value {
        WitnessValue::Scalar(value, width) => {
            writeln!(
                out,
                "{id} {} {}{suffix}",
                to_bit_string(value, *width).unwrap(),
                name
            )
        }
        WitnessValue::Array(a) => {
            match a.default {
                None => {} // nothing to do
                Some(_) => todo!("serialize array default value in witness"),
            }
            for (index, value) in a.updates.iter() {
                writeln!(
                    out,
                    "{id} [{}] {} {}{suffix}",
                    to_bit_string(index, a.tpe.index_width).unwrap(),
                    to_bit_string(value, a.tpe.data_width).unwrap(),
                    name
                )?;
            }
            Ok(())
        }
    }
}
