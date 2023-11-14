// Copyright 2023 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

use libpatron::btor2;
use libpatron::ir::Context;
use libpatron::ir::SerializableIrNode;

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
fn parse_quiz1() {
    let (ctx, sys) = btor2::parse_file("inputs/Quiz1.btor").unwrap();
    insta::assert_snapshot!(sys.serialize_to_str(&ctx));
}