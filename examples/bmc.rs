// Copyright 2023 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

use clap::{Parser, ValueEnum};
use patronus::ir::*;
use patronus::*;
use std::process::ExitCode;

#[derive(Parser, Debug)]
#[command(name = "bmc")]
#[command(author = "Kevin Laeufer <laeufer@berkeley.edu>")]
#[command(version)]
#[command(about = "Performs bounded model checking on a btor2 file.", long_about = None)]
struct Args {
    #[arg(
        long,
        value_enum,
        default_value = "bitwuzla",
        help = "the SMT solver to use"
    )]
    solver: Solver,
    #[arg(short, long)]
    verbose: bool,
    #[arg(short, long)]
    dump_smt: bool,
    #[arg(short, long)]
    pdr: bool,
    #[arg(value_name = "BTOR2", index = 1)]
    filename: String,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, ValueEnum)]
pub enum Solver {
    Bitwuzla,
    Yices2,
}

fn main() -> ExitCode {
    let args = Args::parse();
    let (mut ctx, sys) = btor2::parse_file(&args.filename).expect("Failed to load btor2 file!");
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
        save_smt_replay: args.dump_smt,
    };
    let solver = match args.solver {
        Solver::Bitwuzla => mc::BITWUZLA_CMD,
        Solver::Yices2 => mc::YICES2_CMD,
    };
    if args.verbose {
        println!(
            "Checking up to {k_max} using {} and the following options:\n{checker_opts:?}",
            solver.name
        );
    }

    let res = if args.pdr {
        let checker = mc::Pdr::new(solver, checker_opts);
        checker.check(&mut ctx, &sys).unwrap()
    } else {
        let checker = mc::SmtModelChecker::new(solver, checker_opts);
        checker.check(&mut ctx, &sys, k_max).unwrap()
    };

    match res {
        mc::ModelCheckResult::Success => {
            println!("unsat");
            ExitCode::SUCCESS
        }
        mc::ModelCheckResult::Unknown => {
            println!("Failed to produce a result!");
            ExitCode::FAILURE
        }
        mc::ModelCheckResult::Fail(wit) => {
            btor2::print_witness(&mut std::io::stdout(), &wit).unwrap();
            ExitCode::SUCCESS
        }
    }
}
