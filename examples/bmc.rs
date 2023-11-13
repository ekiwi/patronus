// Copyright 2023 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

use clap::Parser;
use libpatron::ir::SerializableIrNode;
use libpatron::*;

#[derive(Parser, Debug)]
#[command(name = "bmc")]
#[command(author = "Kevin Laeufer <laeufer@berkeley.edu>")]
#[command(version)]
#[command(about = "Performs bounded model checking on a btor2 file.", long_about = None)]
struct Args {
    #[arg(value_name = "BTOR2", index = 1)]
    filename: String,
}

fn main() {
    let args = Args::parse();
    let (ctx, sys) = btor2::parse_file(&args.filename).expect("Failed to load btor2 file!");
    println!("Loaded: {}", sys.name);
    println!("{}", sys.serialize_to_str(&ctx));
}
