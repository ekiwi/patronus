// Copyright 2023 The Regents of the University of California
// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use baa::Value;

#[derive(Debug, Clone)]
pub enum InitValue {
    BitVec(baa::BitVecValue),
    /// For arrays we store the array data + the entries that are relevant.
    Array(baa::ArrayValue, Vec<baa::BitVecValue>),
    /// No value available
    None,
}

impl TryFrom<InitValue> for baa::Value {
    type Error = ();

    fn try_from(value: InitValue) -> Result<Self, Self::Error> {
        match value {
            InitValue::BitVec(v) => Ok(Value::BitVec(v)),
            InitValue::Array(v, _) => Ok(Value::Array(v)),
            InitValue::None => Err(()),
        }
    }
}

impl Default for InitValue {
    fn default() -> Self {
        InitValue::None
    }
}

/// Contains the initial state and the inputs over `len` cycles.
#[derive(Debug, Default)]
pub struct Witness {
    /// The starting state. Contains an optional value for each state.
    pub init: Vec<InitValue>,
    /// Optional name for each init value.
    pub init_names: Vec<Option<String>>,
    /// The inputs over time. Each entry contains an optional value for each input.
    pub inputs: Vec<Vec<Option<baa::Value>>>,
    /// Optional name for each input
    pub input_names: Vec<Option<String>>,
    /// Index of all safety properties (bad state predicates) that are violated by this witness.
    pub failed_safety: Vec<u32>,
}
