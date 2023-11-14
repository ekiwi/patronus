// Copyright 2023 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

use crate::ir::Type;
use num_bigint::BigUint;

/// Contains the initial state and the inputs over `len` cycles.
pub struct Witness {
    /// The starting state. Contains an optional value for each state.
    init: State,
    /// The inputs over time. Each entry contains an optional value for each input.
    inputs: Vec<State>,
}

impl Witness {
    pub fn len(&self) -> usize {
        self.inputs.len()
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
enum StorageType {
    Long,
    Big,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
struct StorageMetaData {
    /// Indicates in what format the data is stored.
    tpe: StorageType,
    /// Index into the storage type specific array.
    index: u16,
    /// Indicates whether the store contains valid data. A `get` will return `None` for invalid data.
    is_valid: bool,
}

fn smt_tpe_to_storage_tpe(tpe: Type) -> StorageType {
    match tpe {
        Type::BV(len) if len <= 64 => StorageType::Long,
        Type::BV(_) => StorageType::Big,
        Type::Array(_) => todo!("add array support"),
    }
}

/// Represents concrete values which can be updated, but state cannot be added once created.
pub struct State {
    meta: Vec<StorageMetaData>,
    longs: Vec<u64>,
    bigs: Vec<BigUint>,
    // TODO: add array support
    //arrays: Vec<ArrayValue>,
}

impl Default for State {
    fn default() -> Self {
        State {
            meta: Vec::default(),
            longs: Vec::default(),
            bigs: Vec::default(),
        }
    }
}

impl State {
    pub fn new(types: impl Iterator<Item = Type>) -> Self {
        let mut state = State::default();
        let mut long_count = 0;
        let mut big_count = 0;
        for tpe in types {
            let storage_tpe = smt_tpe_to_storage_tpe(tpe);
            let index = match storage_tpe {
                StorageType::Long => {
                    long_count += 1;
                    long_count - 1
                }
                StorageType::Big => {
                    big_count += 1;
                    big_count - 1
                }
            };
            let meta = StorageMetaData {
                tpe: storage_tpe,
                index: index as u16,
                is_valid: false,
            };
            state.meta.push(meta);
        }
        // initialize arrays with default data
        state.longs.resize(long_count, u64::default());
        state.bigs.resize(big_count, BigUint::default());

        state
    }

    pub fn get(&self, index: usize) -> Option<ValueRef> {
        let meta = self.meta.get(index)?;
        if !meta.is_valid {
            return None;
        }
        let res: ValueRef = match meta.tpe {
            StorageType::Long => ValueRef::Long(self.longs[meta.index as usize]),
            StorageType::Big => ValueRef::Big(&self.bigs[meta.index as usize]),
        };
        Some(res)
    }

    pub fn update(&mut self, index: usize, value: Value) {
        let meta = self.meta.get(index).unwrap();
        match (meta.tpe, value) {
            (StorageType::Long, Value::Long(value)) => {
                self.longs[meta.index as usize] = value;
            }
            (StorageType::Big, Value::Big(value)) => {
                self.bigs[meta.index as usize] = value;
            }
            (StorageType::Big, Value::Long(value)) => {
                self.bigs[meta.index as usize] = BigUint::from(value);
            }
            _ => panic!("Incompatible value for storage type: {:?}", meta.tpe),
        };
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum Value {
    Long(u64),
    Big(BigUint),
}

#[derive(Debug, PartialEq)]
pub enum ValueRef<'a> {
    Long(u64),
    Big(&'a BigUint),
}

impl<'a> ValueRef<'a> {
    fn cloned(&self) -> Value {
        match self {
            ValueRef::Long(value) => Value::Long(*value),
            ValueRef::Big(value) => Value::Big((*value).clone()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ir_type_size() {
        // External BigUInt
        assert_eq!(std::mem::size_of::<BigUint>(), 24);

        // Not sure how we are fitting that, but it's nice that Value is no bigger than a BigUInt
        assert_eq!(std::mem::size_of::<Value>(), 24);

        // We store 4 bytes of meta-data for every item in the storage
        assert_eq!(std::mem::size_of::<StorageMetaData>(), 4);
    }
}
