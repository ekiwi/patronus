// Copyright 2023 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

use crate::ir::{Type, WidthInt};
use num_bigint::BigUint;
use num_traits::{Num, Zero};

/// Contains the initial state and the inputs over `len` cycles.
#[derive(Debug, Default)]
pub struct Witness {
    /// The starting state. Contains an optional value for each state.
    pub init: State,
    /// The inputs over time. Each entry contains an optional value for each input.
    pub inputs: Vec<State>,
    /// Index of all safety properties (bad state predicates) that are violated by this witness.
    pub failed_safety: Vec<u32>,
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
#[derive(Debug)]
pub struct State {
    meta: Vec<Option<StorageMetaData>>,
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
            state.meta.push(Some(meta));
        }
        // initialize arrays with default data
        state.longs.resize(long_count, u64::default());
        state.bigs.resize(big_count, BigUint::default());

        state
    }

    pub fn get(&self, index: usize) -> Option<ValueRef> {
        let meta = self.meta.get(index)?.as_ref()?;
        self.get_from_meta(meta)
    }

    fn get_from_meta(&self, meta: &StorageMetaData) -> Option<ValueRef> {
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
        let meta = self.meta.get_mut(index).unwrap().as_mut().unwrap();
        meta.is_valid = true;
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

    pub fn insert(&mut self, index: usize, value: Value) {
        match self.meta.get(index) {
            Some(_) => self.update(index, value),
            None => {
                // expand meta
                self.meta.resize(index + 1, None);
                // allocate storage and store value
                self.meta[index] = Some(self.allocate_for_value(value));
            }
        };
    }

    fn allocate_for_value(&mut self, value: Value) -> StorageMetaData {
        let (tpe, index) = match value {
            Value::Long(val) => {
                self.longs.push(val);
                (StorageType::Long, self.longs.len() - 1)
            }
            Value::Big(val) => {
                self.bigs.push(val);
                (StorageType::Big, self.bigs.len() - 1)
            }
        };
        StorageMetaData {
            tpe,
            index: index as u16,
            is_valid: true,
        }
    }

    pub fn is_empty(&self) -> bool {
        self.meta.is_empty()
    }

    pub fn iter(&self) -> StateIter<'_> {
        StateIter::new(&self)
    }
}

pub struct StateIter<'a> {
    state: &'a State,
    underlying: std::slice::Iter<'a, Option<StorageMetaData>>,
}

impl<'a> StateIter<'a> {
    fn new(state: &'a State) -> Self {
        let underlying = state.meta.iter();
        Self { state, underlying }
    }
}

impl<'a> Iterator for StateIter<'a> {
    type Item = Option<ValueRef<'a>>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.underlying.next() {
            None => None,             // we are done!
            Some(None) => Some(None), // invalid / unallocated element
            Some(Some(m)) => Some(self.state.get_from_meta(m)),
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum Value {
    Long(u64),
    Big(BigUint),
}

impl Value {
    /// parses a string of 1s and 0s into a value.
    pub fn from_bit_string(value: &str) -> Self {
        if value.len() <= 64 {
            Value::Long(u64::from_str_radix(value, 2).unwrap())
        } else {
            Value::Big(BigUint::from_str_radix(value, 2).unwrap())
        }
    }

    pub fn from_hex_string(value: &str) -> Self {
        if value.len() <= (64 / 4) {
            Value::Long(u64::from_str_radix(value, 16).unwrap())
        } else {
            Value::Big(BigUint::from_str_radix(value, 16).unwrap())
        }
    }

    pub fn from_decimal_string(value: &str) -> Self {
        match u64::from_str_radix(value, 10) {
            Ok(value) => Value::Long(value),
            Err(_) => Value::Big(BigUint::from_str_radix(value, 10).unwrap()),
        }
    }

    pub fn is_zero(&self) -> bool {
        match &self {
            Value::Long(value) => *value == 0,
            Value::Big(value) => value.is_zero(),
        }
    }

    /// Returns the value as a fixed with bit string. Returns None if the value is an array.
    pub fn to_bit_string(&self, width: WidthInt) -> Option<String> {
        let base_str = match &self {
            Value::Long(value) => format!("{value:b}"),
            Value::Big(value) => value.to_str_radix(2),
        };
        let base_len = base_str.len();
        if base_len == width as usize {
            Some(base_str)
        } else {
            // pad with zeros
            assert!(base_len < width as usize);
            let zeros = width as usize - base_len;
            let mut out = "0".repeat(zeros);
            out.push_str(&base_str);
            Some(out)
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum ValueRef<'a> {
    Long(u64),
    Big(&'a BigUint),
}

impl<'a> ValueRef<'a> {
    pub fn cloned(&self) -> Value {
        match self {
            ValueRef::Long(value) => Value::Long(*value),
            ValueRef::Big(value) => Value::Big((*value).clone()),
        }
    }

    pub fn is_zero(&self) -> bool {
        match self {
            ValueRef::Long(value) => *value == 0,
            ValueRef::Big(value) => value.is_zero(),
        }
    }

    /// Returns the value as a fixed with bit string. Returns None if the value is an array.
    pub fn to_bit_string(&self, width: WidthInt) -> Option<String> {
        self.cloned().to_bit_string(width) // TODO: optimize
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
        assert_eq!(std::mem::size_of::<Option<StorageMetaData>>(), 4);
    }
}
