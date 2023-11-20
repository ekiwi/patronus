// Copyright 2023 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

use crate::ir::{ArrayType, WidthInt};
use num_bigint::BigUint;
use num_traits::{Num, Zero};

/// Contains the initial state and the inputs over `len` cycles.
#[derive(Debug, Default)]
pub struct Witness {
    /// The starting state. Contains an optional value for each state.
    pub init: Vec<Option<WitnessValue>>,
    /// Optional name for each init value.
    pub init_names: Vec<Option<String>>,
    /// The inputs over time. Each entry contains an optional value for each input.
    pub inputs: Vec<Vec<Option<WitnessValue>>>,
    /// Optional name for each input
    pub input_names: Vec<Option<String>>,
    /// Index of all safety properties (bad state predicates) that are violated by this witness.
    pub failed_safety: Vec<u32>,
}

impl Witness {
    pub fn len(&self) -> usize {
        self.inputs.len()
    }
}

#[derive(Debug, Clone)]
pub enum WitnessValue {
    Scalar(BigUint, WidthInt),
    Array(WitnessArray),
}

impl WitnessValue {
    pub fn is_zero(&self) -> bool {
        match self {
            WitnessValue::Scalar(value, _) => value.is_zero(),
            WitnessValue::Array(_) => false,
        }
    }
}

#[derive(Debug, Clone)]
pub struct WitnessArray {
    pub tpe: ArrayType,
    pub default: Option<BigUint>,
    pub updates: Vec<(BigUint, BigUint)>,
}

pub fn parse_big_uint_from_bit_string(value: &str) -> (BigUint, WidthInt) {
    let int_val = BigUint::from_str_radix(value, 2).unwrap();
    (int_val, value.len() as WidthInt)
}
