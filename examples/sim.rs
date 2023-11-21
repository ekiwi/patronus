// Copyright 2023 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

use clap::Parser;
use libpatron::ir::*;
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

    let input_name_to_ref: HashMap<String, usize> = HashMap::from_iter(
        sys.get_signals(|s| s.kind == SignalKind::Input)
            .iter()
            .enumerate()
            .map(|(idx, (e, _))| (e.get_symbol_name(&ctx).unwrap().to_string(), idx)),
    );
    println!("{:?}", input_name_to_ref);

    let sim = libpatron::sim::interpreter::Interpreter::new(&ctx, &sys);
}
