// Copyright 2023 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

use super::exec;
use crate::ir::WidthInt;
use smallvec::SmallVec;
use std::cmp::Ordering;

pub type Word = u64;

pub fn width_to_words(width: WidthInt) -> u16 {
    width.div_ceil(Word::BITS as WidthInt) as u16
}

/// Contains a pointer to a value.
pub struct ValueRef<'a> {
    width: WidthInt,
    words: &'a [Word],
}

impl<'a> ValueRef<'a> {
    pub fn new(words: &'a [Word], width: WidthInt) -> Self {
        assert_eq!(width_to_words(width) as usize, words.len());
        Self { words, width }
    }

    pub fn to_u64(&self) -> Option<u64> {
        match self.words.len() {
            0 => Some(0),
            1 => Some(self.words[0] & exec::mask(self.width)),
            _ => {
                // check to see if all msbs are zero
                for word in self.words.iter().skip(1) {
                    if *word != 0 {
                        return None;
                    }
                }
                Some(self.words[0])
            }
        }
    }

    pub fn to_bit_string(&self) -> String {
        exec::to_bit_str(self.words, self.width)
    }

    pub fn to_big_uint(&self) -> num_bigint::BigUint {
        exec::to_big_uint(self.words)
    }

    pub fn word_len(&self) -> usize {
        self.words.len()
    }

    pub fn words(&self) -> &[Word] {
        self.words
    }
}

impl<'a> From<&'a Value> for ValueRef<'a> {
    fn from(value: &'a Value) -> Self {
        ValueRef {
            width: value.width,
            words: value.words.as_ref(),
        }
    }
}

impl<'a> PartialEq for ValueRef<'a> {
    fn eq(&self, other: &Self) -> bool {
        let same = self
            .words
            .iter()
            .zip(other.words.iter())
            .all(|(a, b)| *a == *b);
        if same {
            // check to make sure that the msbs of the longer value are all zero
            match self.words.len().cmp(&other.words.len()) {
                Ordering::Less => other.words.iter().skip(self.words.len()).all(|w| *w == 0),
                Ordering::Equal => true,
                Ordering::Greater => self.words.iter().skip(other.words.len()).all(|w| *w == 0),
            }
        } else {
            false
        }
    }
}

impl<'a> Eq for ValueRef<'a> {}

impl<'a> PartialEq<Value> for ValueRef<'a> {
    fn eq(&self, other: &Value) -> bool {
        let other_ref: ValueRef = other.into();
        self.eq(&other_ref)
    }
}

impl<'a> PartialEq<ValueRef<'a>> for Value {
    fn eq(&self, other: &ValueRef<'a>) -> bool {
        other.eq(self)
    }
}

impl<'a> std::fmt::Debug for ValueRef<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "ValueRef({})", self.to_bit_string())
    }
}

pub struct Value {
    width: WidthInt,
    words: SmallVec<[Word; 1]>,
}

impl Value {
    pub fn from_u64(value: u64, width: WidthInt) -> Self {
        assert!(width <= Word::BITS);
        let buf = [value];
        Self {
            words: SmallVec::from_buf(buf),
            width,
        }
    }

    pub fn from_words(words: &[Word], width: WidthInt) -> Self {
        assert_eq!(width_to_words(width) as usize, words.len());
        Self {
            words: SmallVec::from_slice(words),
            width,
        }
    }

    pub fn from_big_uint(value: &num_bigint::BigUint, width: WidthInt) -> Self {
        let words = exec::from_big_uint(value, width);
        Self {
            words: SmallVec::from_vec(words),
            width,
        }
    }

    pub fn to_bit_string(&self) -> String {
        exec::to_bit_str(&self.words, self.width)
    }

    pub fn word_len(&self) -> usize {
        self.words.len()
    }

    pub fn words(&self) -> &[Word] {
        &self.words
    }
}

impl std::fmt::Debug for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Value({})", self.to_bit_string())
    }
}
