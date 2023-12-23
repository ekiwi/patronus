// Copyright 2023 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

use crate::ir::WidthInt;
use crate::sim::exec;
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
            1 => Some(self.words[0] & mask(self.width)),
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
        to_bit_str(self.words, self.width)
    }

    pub fn to_big_uint(&self) -> num_bigint::BigUint {
        to_big_uint(self.words)
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

pub(crate) type ValueVec = SmallVec<[Word; 1]>;

pub struct Value {
    width: WidthInt,
    words: ValueVec,
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
        let words = from_big_uint(value, width);
        Self { words, width }
    }

    pub fn from_bit_str(bits: &str) -> Self {
        let (words, width) = from_bit_str(bits);
        Self { words, width }
    }

    pub fn to_bit_string(&self) -> String {
        to_bit_str(&self.words, self.width)
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

#[inline]
pub fn mask(bits: WidthInt) -> Word {
    if bits == Word::BITS || bits == 0 {
        Word::MAX
    } else {
        assert!(bits < Word::BITS);
        ((1 as Word) << bits) - 1
    }
}

pub(crate) fn to_bit_str(values: &[Word], width: WidthInt) -> String {
    let start_bit = (width - 1) % Word::BITS;
    let mut out = String::with_capacity(width as usize);
    let msb = values.last().unwrap();
    for ii in (0..(start_bit + 1)).rev() {
        let value = (msb >> ii) & 1;
        if value == 1 {
            out.push('1');
        } else {
            out.push('0');
        }
    }
    for word in values.iter().rev().skip(1) {
        for ii in (0..Word::BITS).rev() {
            let value = (word >> ii) & 1;
            if value == 1 {
                out.push('1');
            } else {
                out.push('0');
            }
        }
    }
    out
}

pub(crate) fn to_big_uint(words: &[Word]) -> num_bigint::BigUint {
    let words32 = words_to_u32(words);
    num_bigint::BigUint::from_slice(&words32)
}

fn words_to_u32(words: &[Word]) -> Vec<u32> {
    let mut words32 = Vec::with_capacity(words.len() * 2);
    let mask32 = mask(32);
    for w in words.iter() {
        let word = *w;
        let lsb = (word & mask32) as u32;
        let msb = ((word >> 32) & mask32) as u32;
        words32.push(lsb);
        words32.push(msb);
    }
    words32
}

pub(crate) fn from_big_uint(value: &num_bigint::BigUint, width: WidthInt) -> ValueVec {
    let mut words = value.iter_u64_digits().collect::<ValueVec>();
    let num_words = width.div_ceil(Word::BITS);
    // add any missing (because they are zero) msb words
    words.resize(num_words as usize, 0);
    exec::mask_msb(&mut words, width);
    words
}

#[cfg(test)]
fn get_sign(value: &[Word], width: WidthInt) -> num_bigint::Sign {
    let sign_bit = (width - 1) % Word::BITS;
    let sign_value = (value.last().unwrap() >> sign_bit) & 1;
    if sign_value == 1 {
        num_bigint::Sign::Minus
    } else {
        num_bigint::Sign::Plus
    }
}

#[cfg(test)]
pub(crate) fn to_big_int(words: &[Word], width: WidthInt) -> num_bigint::BigInt {
    let sign = get_sign(words, width);
    // calculate the magnitude
    let words64 = if sign == num_bigint::Sign::Minus {
        let mut negated = vec![0; words.len()];
        exec::negate(&mut negated, words, width);
        negated
    } else {
        Vec::from(words)
    };

    let words32 = words_to_u32(&words64);
    num_bigint::BigInt::from_slice(sign, &words32)
}

#[cfg(test)]
pub(crate) fn from_big_int(value: &num_bigint::BigInt, width: WidthInt) -> ValueVec {
    let mut words = value.iter_u64_digits().collect::<ValueVec>();
    let num_words = width.div_ceil(Word::BITS);
    // add any missing (because they are zero) msb words
    words.resize(num_words as usize, 0);
    exec::mask_msb(&mut words, width);
    // negate if sign is minus
    if value.sign() == num_bigint::Sign::Minus {
        let word_copy = words.clone();
        exec::negate(&mut words, &word_copy, width);
    }
    words
}

pub(crate) fn from_bit_str(bits: &str) -> (ValueVec, WidthInt) {
    let width = bits.len() as WidthInt;
    let mut out = ValueVec::new();
    let mut word = 0 as Word;

    for (ii, cc) in bits.chars().enumerate() {
        let ii_rev = width as usize - ii - 1;
        if ii > 0 && ((ii_rev + 1) % Word::BITS as usize) == 0 {
            out.push(word);
            word = 0;
        }

        let value = match cc {
            '1' => 1,
            '0' => 0,
            other => panic!("Unexpected character: {other}"),
        };
        word = (word << 1) | value;
    }
    out.push(word);
    out.reverse(); // little endian

    (out, width)
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use rand::{Rng, SeedableRng};
    use smallvec::smallvec;

    pub(crate) fn assert_unused_bits_zero(value: &[Word], width: WidthInt) {
        let offset = width % Word::BITS;
        if offset > 0 {
            let msb = *value.last().unwrap();
            let m = !mask(offset);
            let unused = msb & m;
            assert_eq!(unused, 0, "unused msb bits need to be zero!")
        }
    }

    pub(crate) fn random_bit_str(width: WidthInt, rng: &mut impl Rng) -> String {
        let mut out = String::with_capacity(width as usize);
        for _ in 0..width {
            let cc = if rng.gen_bool(0.5) { '1' } else { '0' };
            out.push(cc);
        }
        out
    }

    #[test]
    fn test_bit_string_conversion() {
        let mut rng = rand_xoshiro::Xoshiro256PlusPlus::seed_from_u64(1);
        let a = "01100";
        let (a_vec, a_width) = from_bit_str(a);
        assert_unused_bits_zero(&a_vec, a_width);
        assert_eq!(a_width, 5);
        let a_expected: ValueVec = smallvec![0b1100];
        assert_eq!(a_vec, a_expected);

        let b = "10100001101000100000001010101010101000101010";
        let (b_vec, b_width) = from_bit_str(b);
        assert_unused_bits_zero(&b_vec, b_width);
        assert_eq!(b_width, 44);
        let b_expected: ValueVec = smallvec![0b10100001101000100000001010101010101000101010];
        assert_eq!(b_vec, b_expected);

        assert_eq!(to_bit_str(&b_vec, b_width), b);

        let c = "1010000110100010000000101010101010100010101010100001101000100000001010101010101000101010";
        let (c_vec, c_width) = from_bit_str(c);
        assert_unused_bits_zero(&c_vec, c_width);
        assert_eq!(c_width, 88);
        let c_expected: ValueVec = smallvec![
            0b1010101010100010101010100001101000100000001010101010101000101010, // lsb
            0b101000011010001000000010,                                         // msb
        ];
        assert_eq!(c_vec, c_expected);

        assert_eq!(to_bit_str(&c_vec, c_width), c);

        // no unnecessary vec entries
        let d = random_bit_str(Word::BITS * 2, &mut rng);
        let (d_vec, d_width) = from_bit_str(&d);
        assert_unused_bits_zero(&d_vec, d_width);
        assert_eq!(d_width, Word::BITS * 2);
        assert_eq!(d_vec.len(), 2);
        assert_eq!(to_bit_str(&d_vec, d_width), d);
    }

    #[test]
    fn test_big_uint_conversion() {
        let mut rng = rand_xoshiro::Xoshiro256PlusPlus::seed_from_u64(1);
        for _ in 0..10 {
            let (a_vec, a_width) = from_bit_str(&random_bit_str(1345, &mut rng));
            assert_eq!(a_vec, from_big_uint(&to_big_uint(&a_vec), a_width));
            assert_eq!(a_vec, from_big_int(&to_big_int(&a_vec, a_width), a_width));
        }
    }
}
