// Copyright 2023 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

use clap::Parser;
use libpatron::btor2::print_witness;
use libpatron::ir::*;
use libpatron::*;

#[derive(Parser, Debug)]
#[command(name = "bmc")]
#[command(author = "Kevin Laeufer <laeufer@berkeley.edu>")]
#[command(version)]
#[command(about = "Performs bounded model checking on a btor2 file.", long_about = None)]
struct Args {
    #[arg(short, long)]
    verbose: bool,
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
    let k_max = 25;
    let checker_opts = mc::SmtModelCheckerOptions {
        check_constraints: true,
        check_bad_states_individually: true,
        save_smt_replay: false,
    };
    let solver = mc::BITWUZLA_CMD;
    if args.verbose {
        println!(
            "Checking up to {k_max} using {} and the following options:\n{checker_opts:?}",
            solver.name
        );
    }
    let checker = mc::SmtModelChecker::new(solver, checker_opts);
    let res = checker.check(&ctx, &sys, k_max).unwrap();
    match res {
        mc::ModelCheckResult::Success => {
            println!("unsat");
        }
        mc::ModelCheckResult::Fail(wit) => {
            print_witness(&mut std::io::stdout(), &wit).unwrap();
        }
    }
}
