// Copyright 2023 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

use libpatron::btor2;
use libpatron::ir::{replace_anonymous_inputs_with_zero, Context};
use libpatron::ir::{simplify_expressions, SerializableIrNode};

const COUNT_2: &str = r#"
1 sort bitvec 3
2 zero 1
3 state 1
4 init 1 3 2
5 one 1
6 add 1 3 5
7 next 1 3 6
8 ones 1
9 sort bitvec 1
10 eq 9 3 8
11 bad 10
"#;

#[test]
fn parse_count2() {
    let mut ctx = Context::default();
    let sys = btor2::parse_str(&mut ctx, COUNT_2, Some("count2")).unwrap();
    insta::assert_snapshot!(sys.serialize_to_str(&ctx));
}

#[test]
fn serialize_count2() {
    let mut ctx = Context::default();
    let sys = btor2::parse_str(&mut ctx, COUNT_2, Some("count2")).unwrap();
    insta::assert_snapshot!(skip_first_line(&btor2::serialize_to_str(&ctx, &sys)));
}

#[test]
fn parse_quiz1() {
    let (ctx, sys) = btor2::parse_file("inputs/chiseltest/Quiz1.btor").unwrap();
    insta::assert_snapshot!(sys.serialize_to_str(&ctx));
}

#[test]
fn serialize_quiz1() {
    let (ctx, sys) = btor2::parse_file("inputs/chiseltest/Quiz1.btor").unwrap();
    insta::assert_snapshot!(skip_first_line(&btor2::serialize_to_str(&ctx, &sys)));
}

#[test]
fn parse_instrumented_decoder() {
    let (ctx, sys) = btor2::parse_file("inputs/repair/decoder_3_to_8.instrumented.btor").unwrap();
    insta::assert_snapshot!(sys.serialize_to_str(&ctx));
    println!("{}", sys.serialize_to_str(&ctx));
}

#[test]
fn parse_sdram() {
    let (mut ctx, mut sys) =
        btor2::parse_file("inputs/repair/sdram_controller.original.btor").unwrap();
    replace_anonymous_inputs_with_zero(&mut ctx, &mut sys);
    insta::assert_snapshot!(sys.serialize_to_str(&ctx));
}

#[test]
fn parse_sdram_and_remove_anonymous_inputs() {
    let (mut ctx, mut sys) =
        btor2::parse_file("inputs/repair/sdram_controller.original.btor").unwrap();
    replace_anonymous_inputs_with_zero(&mut ctx, &mut sys);
    insta::assert_snapshot!(sys.serialize_to_str(&ctx));
}

#[test]
fn parse_sdram_and_simplify_expressions() {
    let (mut ctx, mut sys) =
        btor2::parse_file("inputs/repair/sdram_controller.original.btor").unwrap();
    replace_anonymous_inputs_with_zero(&mut ctx, &mut sys);
    simplify_expressions(&mut ctx, &mut sys);
    // println!("{}", sys.serialize_to_str(&ctx));
    insta::assert_snapshot!(sys.serialize_to_str(&ctx));
}

/// Regression test for a bug that would prevent "_input_0" from being listed as a system input.
/// The reason was that we did not handle inputs that are also outputs well.
#[test]
fn parse_sha3_keccak_and_check_that_all_anonymous_inputs_are_there() {
    let (ctx, sys) =
        btor2::parse_file("inputs/repair/sha3_keccak.w2.replace_variables.btor").unwrap();
    insta::assert_snapshot!(sys.serialize_to_str(&ctx));
}

/// Regression test to make sure that when an input that is also an output is set to zero,
/// it is maintained.
#[test]
fn parse_sha3_keccak_and_replace_anonymous_inputs() {
    let (mut ctx, mut sys) =
        btor2::parse_file("inputs/repair/sha3_keccak.w2.replace_variables.btor").unwrap();
    replace_anonymous_inputs_with_zero(&mut ctx, &mut sys);
    insta::assert_snapshot!(sys.serialize_to_str(&ctx));
}

fn skip_first_line(value: &str) -> &str {
    match value.char_indices().find(|(_, c)| *c == '\n') {
        None => "",
        Some((char_ii, _)) => &value[(char_ii + 1)..],
    }
}
