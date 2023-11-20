// Copyright 2023 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

use libpatron::btor2;

#[test]
fn test_no_state_witness() {
    let wit = btor2::parse_witness(&mut NO_STATE.as_bytes()).unwrap();
    let serialized = btor2::witness_to_string(&wit);
    insta::assert_snapshot!(serialized);
}

#[test]
fn test_fsm_witness() {
    let wit = btor2::parse_witness(&mut FSM.as_bytes()).unwrap();
    let serialized = btor2::witness_to_string(&wit);
    insta::assert_snapshot!(serialized);
}

#[test]
fn test_const_array_example_witness() {
    let wit = btor2::parse_witness(&mut CONST_ARRAY_EXAMPLE.as_bytes()).unwrap();
    let serialized = btor2::witness_to_string(&wit);
    insta::assert_snapshot!(serialized);
}

#[test]
fn test_const_array_example_witness_2() {
    let wit = btor2::parse_witness(&mut CONST_ARRAY_EXAMPLE_2.as_bytes()).unwrap();
    let serialized = btor2::witness_to_string(&wit);
    assert_eq!(serialized.trim(), CONST_ARRAY_EXAMPLE_2.trim());
}

#[test]
fn test_multiple_witnesses() {
    let wit = btor2::parse_witness(&mut MULTIPLE.as_bytes()).unwrap();
    let serialized = btor2::witness_to_string(&wit);
    insta::assert_snapshot!(serialized);
    let _wits = btor2::parse_witnesses(&mut MULTIPLE.as_bytes(), 30).unwrap();
}

const NO_STATE: &str = r#"
sat
b0
@0
0 0 reset@0
1 11111011 a@0
2 00000101 b@0
.

"#;

const FSM: &str = r#"
sat
b0
#0
0 00 state#0
@0
0 1 reset@0
1 1 in@0
@1
0 0 reset@1
1 1 in@1
.

"#;

/// Witness obtained by running `btormc const_array_example.btor`
const CONST_ARRAY_EXAMPLE: &str = r#"
sat
b0
#0
0 11111 addr#0
1 11111111111111111111111111111111 data#0
2 [11111] 11111111111111111111111111111110 mem@0
4 11111 a#0
@0
.
"#;

// modified version of the original, to test multiple array updates
const CONST_ARRAY_EXAMPLE_2: &str = r#"
sat
b0
#0
0 11111 addr#0
1 11111111111111111111111111111111 data#0
2 [11111] 11111111111111111111111111111110 mem#0
2 [11110] 11111111111111111111111111111110 mem#0
4 11111 a#0
@0
.
"#;

const MULTIPLE: &str = r#"
sat
b0
#0
0 0 state0#0
2 0 state2#0
3 0 state3#0
4 0 state4#0
6 1 state6#0
7 0 state7#0
8 0 state8#0
9 0 state9#0
10 0 state10#0
11 0 state11#0
12 1 state12#0
@0
0 0 clock@0
1 1 in@0
2 1 reset@0
#1
8 0 state8#1
9 0 state9#1
10 0 state10#1
11 0 state11#1
12 0 state12#1
@1
0 0 clock@1
1 0 in@1
2 0 reset@1
#2
8 0 state8#2
9 0 state9#2
10 0 state10#2
11 0 state11#2
12 0 state12#2
@2
0 0 clock@2
1 0 in@2
2 0 reset@2
.
sat
b1
#0
0 0 state0#0
2 0 state2#0
3 0 state3#0
4 0 state4#0
6 1 state6#0
7 0 state7#0
8 0 state8#0
9 0 state9#0
10 0 state10#0
11 0 state11#0
12 1 state12#0
@0
0 0 clock@0
1 1 in@0
2 1 reset@0
#1
8 0 state8#1
9 0 state9#1
10 0 state10#1
11 0 state11#1
12 0 state12#1
@1
0 0 clock@1
1 1 in@1
2 0 reset@1
#2
8 0 state8#2
9 0 state9#2
10 0 state10#2
11 0 state11#2
12 0 state12#2
@2
0 0 clock@2
1 0 in@2
2 0 reset@2
#3
8 0 state8#3
9 0 state9#3
10 0 state10#3
11 0 state11#3
12 0 state12#3
@3
0 0 clock@3
1 0 in@3
2 0 reset@3
.
sat
b2
#0
0 0 state0#0
2 0 state2#0
3 0 state3#0
4 0 state4#0
6 1 state6#0
7 0 state7#0
8 0 state8#0
9 0 state9#0
10 0 state10#0
11 0 state11#0
12 1 state12#0
@0
0 0 clock@0
1 1 in@0
2 1 reset@0
#1
8 0 state8#1
9 0 state9#1
10 0 state10#1
11 0 state11#1
12 0 state12#1
@1
0 0 clock@1
1 1 in@1
2 0 reset@1
#2
8 0 state8#2
9 0 state9#2
10 0 state10#2
11 0 state11#2
12 1 state12#2
@2
0 0 clock@2
1 1 in@2
2 0 reset@2
#3
8 0 state8#3
9 0 state9#3
10 0 state10#3
11 0 state11#3
12 0 state12#3
@3
0 0 clock@3
1 0 in@3
2 0 reset@3
#4
8 0 state8#4
9 0 state9#4
10 0 state10#4
11 0 state11#4
12 0 state12#4
@4
0 0 clock@4
1 0 in@4
2 0 reset@4
.

"#;
