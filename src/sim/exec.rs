// Copyright 2023 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

// contains implementations of our smt operations
// values are stored in an array of words in little endian form

use super::value::Word;
use crate::ir::WidthInt;
use crate::sim::mask;
use std::cmp::Ordering;
use std::ops::Range;

type DoubleWord = u128;

#[inline]
pub(crate) fn clear(dst: &mut [Word]) {
    for w in dst.iter_mut() {
        *w = 0;
    }
}

#[inline]
pub(crate) fn assign(dst: &mut [Word], source: &[Word]) {
    for (d, s) in dst.iter_mut().zip(source.iter()) {
        *d = *s;
    }
}

#[inline]
pub(crate) fn read_bool(source: &[Word]) -> bool {
    word_to_bool(source[0])
}

#[inline]
pub(crate) fn assign_word(dst: &mut [Word], value: Word) {
    // assign the lsb
    dst[0] = value;

    // zero extend
    for other in dst.iter_mut().skip(1) {
        *other = 0;
    }
}

#[inline]
pub(crate) fn zero_extend(dst: &mut [Word], source: &[Word]) {
    // copy source to dst
    assign(dst, source);
    // zero out remaining words
    clear(&mut dst[source.len()..]);
}

#[inline]
pub(crate) fn mask_msb(dst: &mut [Word], width: WidthInt) {
    let m = mask(width % Word::BITS);
    *dst.last_mut().unwrap() &= m;
}

#[inline]
pub(crate) fn slice(dst: &mut [Word], source: &[Word], hi: WidthInt, lo: WidthInt) {
    let lo_offset = lo % Word::BITS;
    let hi_word = (hi / Word::BITS) as usize;
    let lo_word = (lo / Word::BITS) as usize;
    let src = &source[lo_word..(hi_word + 1)];

    let shift_right = lo_offset;
    if shift_right == 0 {
        assign(dst, src);
    } else {
        // assign with a shift
        let shift_left = Word::BITS - shift_right;
        let m = mask(shift_right);
        let mut prev = src[0] >> shift_right;
        // We append a zero to the src iter in case src.len() == dst.len().
        // If src.len() == dst.len() + 1, then the 0 will just be ignored by `zip`.
        for (d, s) in dst.iter_mut().zip(src.iter().skip(1).chain([0].iter())) {
            *d = prev | ((*s) & m) << shift_left;
            prev = (*s) >> shift_right;
        }
    }
    // mask the result msb
    mask_msb(dst, hi - lo + 1);
}

#[inline]
pub(crate) fn concat(dst: &mut [Word], msb: &[Word], lsb: &[Word], lsb_width: WidthInt) {
    // copy lsb to dst
    assign(dst, lsb);

    let lsb_offset = lsb_width % Word::BITS;
    if lsb_offset == 0 {
        // copy msb to dst
        for (d, m) in dst.iter_mut().skip(lsb.len()).zip(msb.iter()) {
            *d = *m;
        }
    } else {
        // copy a shifted version of the msb to dst
        let shift_right = Word::BITS - lsb_offset;
        let m = mask(shift_right);
        let mut prev = dst[lsb.len() - 1]; // the msb of the lsb
        for (d, s) in dst
            .iter_mut()
            .skip(lsb.len() - 1)
            .zip(msb.iter().chain([0].iter()))
        {
            *d = prev | ((*s) & m) << lsb_offset;
            prev = (*s) >> shift_right;
        }
    }
}

#[inline]
pub(crate) fn not(dst: &mut [Word], source: &[Word], width: WidthInt) {
    bitwise_un_op(dst, source, |e| !e);
    mask_msb(dst, width);
}

#[inline]
fn bitwise_un_op(dst: &mut [Word], source: &[Word], op: fn(Word) -> Word) {
    for (d, s) in dst.iter_mut().zip(source.iter()) {
        *d = (op)(*s);
    }
}

#[inline]
pub(crate) fn and(dst: &mut [Word], a: &[Word], b: &[Word]) {
    bitwise_bin_op(dst, a, b, |a, b| a & b)
}

#[inline]
pub(crate) fn or(dst: &mut [Word], a: &[Word], b: &[Word]) {
    bitwise_bin_op(dst, a, b, |a, b| a | b)
}

#[inline]
pub(crate) fn xor(dst: &mut [Word], a: &[Word], b: &[Word]) {
    bitwise_bin_op(dst, a, b, |a, b| a ^ b)
}

#[inline]
fn bitwise_bin_op(dst: &mut [Word], a: &[Word], b: &[Word], op: fn(Word, Word) -> Word) {
    for (d, (a, b)) in dst.iter_mut().zip(a.iter().zip(b.iter())) {
        *d = (op)(*a, *b);
    }
}

#[inline]
fn adc(dst: &mut Word, carry: u8, a: Word, b: Word) -> u8 {
    let sum = carry as DoubleWord + a as DoubleWord + b as DoubleWord;
    let new_carry = (sum >> Word::BITS) as u8;
    *dst = sum as Word;
    new_carry
}

/// Add function inspired by the num-bigint implementation: https://docs.rs/num-bigint/0.4.4/src/num_bigint/biguint/addition.rs.html
#[inline]
pub(crate) fn add(dst: &mut [Word], a: &[Word], b: &[Word], width: WidthInt) {
    let mut carry = 0;
    for (dd, (aa, bb)) in dst.iter_mut().zip(a.iter().zip(b.iter())) {
        carry = adc(dd, carry, *aa, *bb);
    }
    mask_msb(dst, width);
}

/// Sub function inspired by the num-bigint implementation: https://docs.rs/num-bigint/0.4.4/src/num_bigint/biguint/subtraction.rs.html
#[inline]
pub(crate) fn sub(dst: &mut [Word], a: &[Word], b: &[Word], width: WidthInt) {
    // we add one by setting the input carry to one
    let mut carry = 1;
    for (dd, (aa, bb)) in dst.iter_mut().zip(a.iter().zip(b.iter())) {
        // we invert b which in addition to adding 1 turns it into `-b`
        carry = adc(dd, carry, *aa, !(*bb));
    }
    mask_msb(dst, width);
}

#[inline]
pub(crate) fn shift_right(dst: &mut [Word], a: &[Word], b: &[Word], width: WidthInt) {
    // clear the destination
    clear(dst);

    // check to see if we are shifting for more than our width
    let shift_amount = match get_shift_amount(b, width) {
        None => return,
        Some(value) => value,
    };

    // otherwise we actually perform the shift by converting it to a slice
    let hi = width - 1;
    let lo = shift_amount;
    let result_width = hi - lo + 1;
    let result_words = result_width.div_ceil(Word::BITS) as usize;
    slice(&mut dst[..result_words], a, hi, lo);
}

#[inline]
pub(crate) fn shift_left(dst: &mut [Word], a: &[Word], b: &[Word], width: WidthInt) {
    // check to see if we are shifting for more than our width
    let shift_amount = match get_shift_amount(b, width) {
        None => {
            clear(dst);
            return;
        }
        Some(value) => value,
    };

    // otherwise we actually perform the shift
    let shift_left = shift_amount % Word::BITS;
    let shift_words = shift_amount / Word::BITS;
    let shift_right = Word::BITS - shift_left;
    let zeros = std::iter::repeat(&(0 as Word)).take(shift_words as usize);
    let mut prev = 0;
    for (d, s) in dst.iter_mut().zip(zeros.chain(a.iter())) {
        if shift_left == 0 {
            *d = *s;
        } else {
            *d = (*s << shift_left) | prev;
            prev = *s >> shift_right;
        }
    }
    if shift_left > 0 {
        mask_msb(dst, width);
    }
}

#[inline]
fn get_shift_amount(b: &[Word], width: WidthInt) -> Option<WidthInt> {
    let msb_set = b.iter().skip(1).any(|w| *w != 0);
    let shift_amount = b[0];
    if msb_set || shift_amount >= width as Word {
        None // result is just zero or the sign bit
    } else {
        Some(shift_amount as WidthInt)
    }
}

#[inline]
pub(crate) fn negate(dst: &mut [Word], b: &[Word], width: WidthInt) {
    // we add one by setting the input carry to one
    let mut carry = 1;
    for (dd, bb) in dst.iter_mut().zip(b.iter()) {
        // we invert b which in addition to adding 1 turns it into `-b`
        carry = adc(dd, carry, 0, !(*bb));
    }
    mask_msb(dst, width);
}

#[inline]
pub(crate) fn cmp_equal(a: &[Word], b: &[Word]) -> bool {
    a.iter().zip(b.iter()).all(|(a, b)| a == b)
}

#[inline]
pub(crate) fn cmp_greater(a: &[Word], b: &[Word]) -> bool {
    is_greater_and_not_less(a, b).unwrap_or(false)
}

#[inline]
fn is_neg(src: &[Word], width: WidthInt) -> bool {
    let msb_bit_id = (width - 1) % WidthInt::BITS;
    let msb_bit_value = (src.last().unwrap() >> msb_bit_id) & 1;
    msb_bit_value == 1
}

#[inline]
pub(crate) fn cmp_greater_signed(a: &[Word], b: &[Word], width: WidthInt) -> bool {
    match (is_neg(a, width), is_neg(b, width)) {
        (true, false) => false, // -|a| < |b|
        (false, true) => true,  // |a| > -|b|
        (false, false) => cmp_greater(a, b),
        (true, true) => cmp_greater(a, b), // TODO: does this actually work?
    }
}

/// `Some(true)` if `a > b`, `Some(false)` if `a < b`, None if `a == b`
#[inline]
fn is_greater_and_not_less(a: &[Word], b: &[Word]) -> Option<bool> {
    for (a, b) in a.iter().rev().zip(b.iter().rev()) {
        match a.cmp(b) {
            Ordering::Less => return Some(false),
            Ordering::Equal => {} // continue
            Ordering::Greater => return Some(true),
        }
    }
    None
}

#[inline]
pub(crate) fn cmp_greater_equal(a: &[Word], b: &[Word]) -> bool {
    is_greater_and_not_less(a, b).unwrap_or(true)
}

#[inline]
pub(crate) fn cmp_greater_equal_signed(a: &[Word], b: &[Word], width: WidthInt) -> bool {
    match (is_neg(a, width), is_neg(b, width)) {
        (true, false) => false, // -|a| < |b|
        (false, true) => true,  // |a| > -|b|
        (false, false) => cmp_greater_equal(a, b),
        (true, true) => cmp_greater_equal(a, b), // TODO: does this actually work?
    }
}

#[inline]
pub(crate) fn bool_to_word(value: bool) -> Word {
    if value {
        1
    } else {
        0
    }
}

#[inline]
fn word_to_bool(value: Word) -> bool {
    (value & 1) == 1
}

#[inline]
pub(crate) fn split_borrow_1(
    data: &mut [Word],
    dst: Range<usize>,
    src: Range<usize>,
) -> (&mut [Word], &[Word]) {
    let (before_dst, after_dst_start) = data.split_at_mut(dst.start);
    let (dst_words, after_dst) = after_dst_start.split_at_mut(dst.end - dst.start);
    let after_dst_offset = dst.end;
    let src_words = if src.start >= after_dst_offset {
        &after_dst[move_range(src, after_dst_offset)]
    } else {
        &before_dst[src]
    };
    (dst_words, src_words)
}

#[inline]
fn move_range(rng: Range<usize>, offset: usize) -> Range<usize> {
    Range {
        start: rng.start - offset,
        end: rng.end - offset,
    }
}

#[inline]
pub(crate) fn split_borrow_2(
    data: &mut [Word],
    dst: Range<usize>,
    src_a: Range<usize>,
    src_b: Range<usize>,
) -> (&mut [Word], &[Word], &[Word]) {
    let (before_dst, after_dst_start) = data.split_at_mut(dst.start);
    let (dst_words, after_dst) = after_dst_start.split_at_mut(dst.end - dst.start);
    let after_dst_offset = dst.end;
    let a_words = if src_a.start >= after_dst_offset {
        &after_dst[move_range(src_a, after_dst_offset)]
    } else {
        &before_dst[src_a]
    };
    let b_words = if src_b.start >= after_dst_offset {
        &after_dst[move_range(src_b, after_dst_offset)]
    } else {
        &before_dst[src_b]
    };
    (dst_words, a_words, b_words)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sim::value::tests::*;
    use crate::sim::value::*;
    use num_bigint::{BigInt, BigUint, Sign};
    use rand::{Rng, SeedableRng};
    use smallvec::smallvec;

    #[test]
    fn test_split_borrow() {
        let data: &mut [Word] = &mut [0, 1, 2, 3];
        let (dst, src) = split_borrow_1(data, 0..1, 2..4);
        assert_eq!(dst, &[0]);
        assert_eq!(src, &[2, 3]);
        let (dst2, src2) = split_borrow_1(data, 2..4, 0..2);
        assert_eq!(dst2, &[2, 3]);
        assert_eq!(src2, &[0, 1]);

        let (dst3, src_a_3, src_b_3) = split_borrow_2(data, 2..4, 1..2, 0..2);
        assert_eq!(dst3, &[2, 3]);
        assert_eq!(src_a_3, &[1]);
        assert_eq!(src_b_3, &[0, 1]);
    }

    fn do_test_concat(a: &str, b: &str, c_init: &str) {
        let (a_vec, a_width) = from_bit_str(a);
        let (b_vec, b_width) = from_bit_str(b);
        let (mut c_vec, c_width) = from_bit_str(c_init);
        assert_eq!(c_width, a_width + b_width);
        concat(&mut c_vec, &a_vec, &b_vec, b_width);
        assert_unused_bits_zero(&c_vec, c_width);
        let expected = format!("{a}{b}");
        assert_eq!(to_bit_str(&c_vec, c_width), expected);
    }

    #[test]
    fn test_concat() {
        let mut rng = rand_xoshiro::Xoshiro256PlusPlus::seed_from_u64(1);
        // simple
        do_test_concat("0", "0", "11");

        // word aligned
        do_test_concat(
            &random_bit_str(Word::BITS, &mut rng),
            &random_bit_str(Word::BITS * 2, &mut rng),
            &random_bit_str(Word::BITS + Word::BITS * 2, &mut rng),
        );
        // unaligned
        do_test_concat(
            &random_bit_str(38, &mut rng),
            &random_bit_str(44, &mut rng),
            &random_bit_str(38 + 44, &mut rng),
        );
        do_test_concat(
            &random_bit_str(38, &mut rng),
            &random_bit_str(8, &mut rng),
            &random_bit_str(38 + 8, &mut rng),
        );
        // test a concat where dst and msb have the same number of words
        do_test_concat(
            &random_bit_str(10 + Word::BITS, &mut rng),
            &random_bit_str(8, &mut rng),
            &random_bit_str(10 + Word::BITS + 8, &mut rng),
        );
    }

    fn do_test_slice(src: &str, hi: WidthInt, lo: WidthInt) {
        let (src_vec, src_width) = from_bit_str(src);
        assert!(hi >= lo);
        assert!(hi < src_width);
        let res_width = hi - lo + 1;
        let mut res_vec = vec![0 as Word; res_width.div_ceil(Word::BITS) as usize];
        slice(&mut res_vec, &src_vec, hi, lo);
        assert_unused_bits_zero(&res_vec, res_width);
        let expected: String = src
            .chars()
            .skip((src_width - 1 - hi) as usize)
            .take(res_width as usize)
            .collect();
        assert_eq!(to_bit_str(&res_vec, res_width), expected);
    }

    #[test]
    fn test_slice() {
        let mut rng = rand_xoshiro::Xoshiro256PlusPlus::seed_from_u64(1);
        let in0 = random_bit_str(15, &mut rng);
        // do_test_slice(&in0, 0, 0);
        do_test_slice(&in0, 1, 1);
        do_test_slice(&in0, 6, 0);
        do_test_slice(&in0, 6, 4);

        // test slice across two words
        let in1 = random_bit_str((2 * Word::BITS) - 5, &mut rng);
        do_test_slice(&in1, Word::BITS, Word::BITS - 5);
        do_test_slice(&in1, Word::BITS + 5, Word::BITS - 5);

        // test larger slices
        let in2 = random_bit_str(1354, &mut rng);
        do_test_slice(&in2, 400, 400); // 400 = 6 * 64 +  16
        do_test_slice(&in2, 400, 400 - 20);
        do_test_slice(&in2, 400 + 13, 400 - 20);

        // result is larger than one word
        do_test_slice(&in2, 875, Word::BITS * 13); // aligned to word boundaries
        do_test_slice(&in2, 3 + (Word::BITS * 2) + 11, 3);
        do_test_slice(&in2, 875, 875 - (Word::BITS * 2) - 15);
    }

    fn width_int_to_bit_str(value: WidthInt, width: WidthInt) -> String {
        let mut words = vec![0 as Word; width.div_ceil(Word::BITS) as usize];
        words[0] = value as Word;
        to_bit_str(&words, width)
    }

    fn do_test_shift(src: &str, by: WidthInt, right: bool) {
        let (a_vec, a_width) = from_bit_str(src);
        let (b_vec, b_width) = from_bit_str(&width_int_to_bit_str(by, a_width));
        assert_eq!(a_width, b_width);
        let mut res_vec = vec![0 as Word; a_vec.len()];
        if right {
            shift_right(&mut res_vec, &a_vec, &b_vec, a_width);
        } else {
            shift_left(&mut res_vec, &a_vec, &b_vec, a_width);
        }
        assert_unused_bits_zero(&res_vec, a_width);
        let zeros = std::cmp::min(by, a_width) as usize;
        let mut expected: String = "0".repeat(zeros);
        if right {
            let msb: String = src.chars().take(a_width as usize - zeros).collect();
            expected.push_str(&msb);
        } else {
            let mut msb: String = src.chars().skip(zeros).collect();
            msb.push_str(&expected);
            expected = msb;
        }
        assert_eq!(to_bit_str(&res_vec, a_width), expected);
    }

    fn do_test_shift_right(src: &str, by: WidthInt) {
        do_test_shift(src, by, true)
    }
    fn do_test_shift_left(src: &str, by: WidthInt) {
        do_test_shift(src, by, false)
    }

    #[test]
    fn test_shift_right() {
        let mut rng = rand_xoshiro::Xoshiro256PlusPlus::seed_from_u64(1);
        let in0 = random_bit_str(15, &mut rng);
        do_test_shift_right(&in0, 0);
        do_test_shift_right(&in0, 3);
        do_test_shift_right(&in0, 14);
        do_test_shift_right(&in0, 30);

        let in1 = random_bit_str(157, &mut rng);
        do_test_shift_right(&in1, 0);
        do_test_shift_right(&in1, 3);
        do_test_shift_right(&in1, 14);
        do_test_shift_right(&in1, 150);
        do_test_shift_right(&in1, 200);
    }

    #[test]
    fn test_shift_left() {
        let mut rng = rand_xoshiro::Xoshiro256PlusPlus::seed_from_u64(1);
        let in0 = random_bit_str(15, &mut rng);
        do_test_shift_left(&in0, 0);
        do_test_shift_left(&in0, 3);
        do_test_shift_left(&in0, 14);
        do_test_shift_left(&in0, 30);

        let in1 = random_bit_str(157, &mut rng);
        do_test_shift_left(&in1, 0);
        do_test_shift_left(&in1, 3);
        do_test_shift_left(&in1, 14);
        do_test_shift_left(&in1, 150);
        do_test_shift_left(&in1, 200);
    }

    fn do_test_zero_ext(src: &str, by: WidthInt) {
        let (src_vec, src_width) = from_bit_str(src);
        let res_width = src_width + by;
        let mut res_vec = vec![0 as Word; res_width.div_ceil(Word::BITS) as usize];
        zero_extend(&mut res_vec, &src_vec);
        assert_unused_bits_zero(&res_vec, res_width);
        let expected: String = format!("{}{}", "0".repeat(by as usize), src);
        assert_eq!(to_bit_str(&res_vec, res_width), expected);
    }

    #[test]
    fn test_zero_ext() {
        do_test_zero_ext("0", 1);
        do_test_zero_ext("1", 1);
        do_test_zero_ext("0", 16);
        do_test_zero_ext("1", 16);
        do_test_zero_ext("0", 13 + Word::BITS);
        do_test_zero_ext("1", 13 + Word::BITS);
    }

    fn do_test_arith(
        width: WidthInt,
        our: fn(&mut [Word], &[Word], &[Word], WidthInt),
        big: fn(BigInt, BigInt) -> BigInt,
        rng: &mut impl Rng,
    ) {
        let (a_vec, _) = from_bit_str(&random_bit_str(width, rng));
        let (b_vec, _) = from_bit_str(&random_bit_str(width, rng));
        let mut res_vec: ValueVec = smallvec![0 as Word; width.div_ceil(Word::BITS) as usize];
        (our)(&mut res_vec, &a_vec, &b_vec, width);
        assert_unused_bits_zero(&res_vec, width);

        // check result
        let (a_num, b_num) = (to_big_int(&a_vec, width), to_big_int(&b_vec, width));
        let expected_num = (big)(a_num.clone(), b_num.clone());
        let expected = from_big_int(&expected_num, width);
        assert_eq!(expected, res_vec, "{a_num} {b_num} {expected_num}");
    }

    fn do_test_add(width: WidthInt, rng: &mut impl Rng) {
        do_test_arith(width, add, |a, b| a + b, rng)
    }

    #[test]
    fn test_add() {
        let mut rng = rand_xoshiro::Xoshiro256PlusPlus::seed_from_u64(1);
        do_test_add(1, &mut rng);
        do_test_add(1, &mut rng);
        do_test_add(1, &mut rng);
        do_test_add(35, &mut rng);
        do_test_add(35, &mut rng);
        do_test_add(1789, &mut rng);
    }

    fn do_test_sub(width: WidthInt, rng: &mut impl Rng) {
        do_test_arith(width, sub, |a, b| a - b, rng)
    }

    #[test]
    fn test_sub() {
        let mut rng = rand_xoshiro::Xoshiro256PlusPlus::seed_from_u64(1);
        do_test_sub(1, &mut rng);
        do_test_sub(1, &mut rng);
        do_test_sub(1, &mut rng);
        do_test_sub(35, &mut rng);
        do_test_sub(35, &mut rng);
        do_test_sub(1789, &mut rng);
    }

    fn do_test_cmp(
        a: BigInt,
        b: BigInt,
        width: WidthInt,
        our: fn(&[Word], &[Word], WidthInt) -> bool,
        big: fn(BigInt, BigInt) -> bool,
    ) {
        let a_vec = from_big_int(&a, width);
        let b_vec = from_big_int(&b, width);
        let res_bool = (our)(&a_vec, &b_vec, width);
        let expected_bool = (big)(a.clone(), b.clone());
        assert_eq!(expected_bool, res_bool, "{a} {b} {expected_bool}");
    }

    fn do_test_cmp_greater(a: BigUint, b: BigUint, width: WidthInt) {
        let a_signed = BigInt::from_biguint(Sign::Plus, a);
        let b_signed = BigInt::from_biguint(Sign::Plus, b);
        do_test_cmp(
            a_signed,
            b_signed,
            width,
            |a, b, _| cmp_greater(a, b),
            |a, b| a > b,
        )
    }
    fn do_test_cmp_greater_signed(a: BigInt, b: BigInt, width: WidthInt) {
        do_test_cmp(a, b, width, cmp_greater_signed, |a, b| a > b)
    }

    fn do_test_cmp_greater_equal_signed(a: BigInt, b: BigInt, width: WidthInt) {
        do_test_cmp(a, b, width, cmp_greater_equal_signed, |a, b| a >= b)
    }

    #[test]
    fn test_cmp_greater() {
        do_test_cmp_greater(BigUint::from(4u32), BigUint::from(3u32), 8);
    }

    #[test]
    fn test_cmp_greater_signed() {
        do_test_cmp_greater_signed(BigInt::from(-4), BigInt::from(3), 8);
        do_test_cmp_greater_signed(BigInt::from(4), BigInt::from(-3), 8);
        do_test_cmp_greater_signed(BigInt::from(4), BigInt::from(3), 8);
        do_test_cmp_greater_signed(BigInt::from(3), BigInt::from(4), 8);
        do_test_cmp_greater_signed(BigInt::from(-4), BigInt::from(-3), 8);
        do_test_cmp_greater_signed(BigInt::from(-3), BigInt::from(-4), 8);
    }

    #[test]
    fn test_cmp_greater_equal_signed() {
        do_test_cmp_greater_equal_signed(BigInt::from(-4), BigInt::from(3), 8);
        do_test_cmp_greater_equal_signed(BigInt::from(4), BigInt::from(-3), 8);
        do_test_cmp_greater_equal_signed(BigInt::from(4), BigInt::from(3), 8);
        do_test_cmp_greater_equal_signed(BigInt::from(3), BigInt::from(4), 8);
        do_test_cmp_greater_equal_signed(BigInt::from(-4), BigInt::from(-3), 8);
        do_test_cmp_greater_equal_signed(BigInt::from(-3), BigInt::from(-4), 8);
        do_test_cmp_greater_equal_signed(BigInt::from(-4), BigInt::from(-4), 8);
        do_test_cmp_greater_equal_signed(BigInt::from(4), BigInt::from(4), 8);
    }
}
