// Copyright 2023 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

use clap::{arg, Parser};
use libpatron::ir::*;
use libpatron::mc::Simulator;
use libpatron::sim::interpreter::{InitKind, Interpreter};
use libpatron::*;
use std::collections::HashMap;
use std::io::BufRead;

#[derive(Parser, Debug)]
#[command(name = "sim")]
#[command(author = "Kevin Laeufer <laeufer@berkeley.edu>")]
#[command(version)]
#[command(about = "Simulates a transitions system from a btor2 file.", long_about = None)]
struct Args {
    #[arg(short, long)]
    verbose: bool,
    #[arg(long, help = "Filename of a testbench.")]
    testbench: String,
    #[arg(value_name = "BTOR2", index = 1)]
    filename: String,
}

fn main() {
    let args = Args::parse();
    let (ctx, sys) = btor2::parse_file(&args.filename).expect("Failed to load btor2 file!");
    if args.verbose {
        println!("Loaded: {}", sys.name);
        println!("{}", sys.serialize_to_str(&ctx));
        println!();
        println!();
    }
    let mut tb = std::io::BufReader::new(
        std::fs::File::open(args.testbench).expect("Failed to load testbench file"),
    );

    let name_to_ref = sys.generate_name_to_ref(&ctx);
    let (inputs, outputs) =
        read_header(&mut tb, &name_to_ref, &sys).expect("Failed to read testbench header");
    if args.verbose {
        println!("Inputs: {inputs:?}");
        println!("Outputs: {outputs:?}");
    }

    // start execution
    let start = std::time::Instant::now();
    let mut sim = Interpreter::new(&ctx, &sys);
    sim.init(InitKind::Zero);

    for (step_id, line) in tb.lines().flatten().enumerate() {
        do_step(step_id, &mut sim, &line, &inputs, &outputs);
    }
    let delta = std::time::Instant::now() - start;
    println!("Executed {} steps in {:?}", sim.step_count(), delta);
}

type IOInfo = Vec<(usize, ExprRef, String)>;

/// Correlates the header with the inputs and outputs of the system.
fn read_header(
    input: &mut impl BufRead,
    name_to_ref: &HashMap<String, ExprRef>,
    sys: &TransitionSystem,
) -> std::io::Result<(IOInfo, IOInfo)> {
    let mut line = String::new();
    input.read_line(&mut line)?;
    let mut inputs = Vec::new();
    let mut outputs = Vec::new();
    for (cell_id, cell) in line.split(",").enumerate() {
        let name = cell.trim();
        if let Some(signal_ref) = name_to_ref.get(name) {
            let signal = sys.get_signal(*signal_ref).unwrap();
            match signal.kind {
                SignalKind::Input => inputs.push((cell_id, *signal_ref, name.to_string())),
                SignalKind::Output => outputs.push((cell_id, *signal_ref, name.to_string())),
                _ => {} // ignore
            }
        }
    }
    Ok((inputs, outputs))
}

/// Reads one line in the CSV, applies inputs, checks outputs and finally steps the system.
fn do_step(
    step_id: usize,
    sim: &mut impl Simulator,
    line: &str,
    inputs: &[(usize, ExprRef, String)],
    outputs: &[(usize, ExprRef, String)],
) {
    // apply inputs
    let mut input_iter = inputs.iter();
    if let Some(mut input) = input_iter.next() {
        for (cell_id, cell) in line.split(",").enumerate() {
            if cell_id == input.0 {
                // apply input
                let trimmed = cell.trim();
                if trimmed.to_ascii_lowercase() != "x" {
                    let value = u64::from_str_radix(trimmed, 10).unwrap();
                    sim.set(input.1, value);
                }

                // get next input
                if let Some(next_input) = input_iter.next() {
                    input = next_input;
                } else {
                    break;
                }
            }
        }
    }

    sim.update();

    // check outputs
    let mut output_iter = outputs.iter();
    if let Some(mut output) = output_iter.next() {
        for (cell_id, cell) in line.split(",").enumerate() {
            if cell_id == output.0 {
                // apply input
                let trimmed = cell.trim();
                if trimmed.to_ascii_lowercase() != "x" {
                    let expected = u64::from_str_radix(trimmed, 10).unwrap();
                    let actual = sim.get(output.1).unwrap();
                    assert_eq!(expected, actual, "{}@{step_id}", output.2);
                }

                // get next output
                if let Some(next_output) = output_iter.next() {
                    output = next_output;
                } else {
                    break;
                }
            }
        }
    }

    // advance simulation
    sim.step();
}
