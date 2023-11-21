// Copyright 2023 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

use clap::Parser;
use libpatron::ir::*;
use libpatron::*;
use std::collections::HashMap;
use std::io::BufRead;
use libpatron::mc::Simulator;
use libpatron::sim::interpreter::{InitKind, Interpreter};

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
    let mut tb = std::io::BufReader::new(std::fs::File::open(args.testbench).expect("Failed to load testbench file"));

    let input_name_to_ref: HashMap<String, usize> = HashMap::from_iter(
        sys.get_signals(|s| s.kind == SignalKind::Input)
            .iter()
            .enumerate()
            .map(|(idx, (e, _))| (e.get_symbol_name(&ctx).unwrap().to_string(), idx)),
    );
    println!("{:?}", input_name_to_ref);

    let mut sim = Interpreter::new(&ctx, &sys);
    sim.init(InitKind::Zero);
    let input_ids = read_header(&mut tb, &input_name_to_ref).expect("Failed to read testbench header");
    println!("Input ids: {input_ids:?}")
}

fn read_header(input: &mut impl BufRead, input_name_to_ref: &HashMap<String, usize>) -> std::io::Result<Vec<usize>> {
    let mut line = String::new();
    input.read_line(&mut line)?;
    let mut out = Vec::new();
    for cell in line.split(",") {
        let name = cell.trim();
        if let Some(input_id) = input_name_to_ref.get(name) {
            out.push(*input_id);
        }
    }
    Ok(out)
}

fn get_ref_by_name(sys: &TransitionSystem, ctx: &Context) -> HashMap<String, usize> {
    HashMap::from_iter(
        sys.get_signals(|s| s.kind == SignalKind::Input)
            .iter()
            .enumerate()
            .map(|(idx, (e, _))| (e.get_symbol_name(ctx).unwrap().to_string(), idx)),
    )
}