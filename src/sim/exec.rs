// Copyright 2023 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

// contains implementations of our smt operations
// values are stored in an array of words in little endian form

use crate::ir::WidthInt;
use std::ops::Range;

pub(crate) type Word = u64;

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
pub(crate) fn assign_word(dst: &mut [Word], value: Word) {
    // assign the lsb
    dst[0] = value;

    // zero extend
    for other in dst.iter_mut().skip(1) {
        *other = 0;
    }
}

#[inline]
pub(crate) fn mask(bits: WidthInt) -> Word {
    if bits == Word::BITS {
        Word::MAX
    } else {
        assert!(bits < Word::BITS);
        ((1 as Word) << bits) - 1
    }
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
        let mut prev = src[0];
        // We append a zero to the src iter in case src.len() == dst.len().
        // If src.len() == dst.len() + 1, then the 0 will just be ignored by `zip`.
        for (d, s) in dst.iter_mut().zip(src.iter().skip(1).chain([0].iter())) {
            let d0 = prev >> shift_right;
            let d1 = d0 | ((*s) & m) << shift_left;
            *d = d1;
            prev = *s;
        }
    }
}

#[inline]
pub(crate) fn concat(dst: &mut [Word], msb: &[Word], lsb: &[Word], lsb_width: WidthInt) {
    let lsb_offset = dst.len() - lsb.len();
    // copy lsb to dst
    for (d, l) in dst.iter_mut().skip(lsb_offset).zip(lsb.iter()) {
        *d = *l;
    }
    //
    let msb_shift = lsb_width % Word::BITS;
    if msb_shift == 0 {
        assert_eq!(msb.len(), lsb_offset);
        for (d, m) in dst.iter_mut().zip(msb.iter()) {
            *d = *m;
        }
    } else {
        let top_shift = Word::BITS - msb_shift;
        //                         msb_shift
        //         |-----m-----|<-------->
        // |- dst[ii] -| |- dst[ii + 1] -|
        for (ii, m) in msb.iter().enumerate() {
            if ii == 0 {
                dst[ii] = m >> top_shift;
            } else {
                dst[ii] |= m >> top_shift;
            }
            let is_last = ii + 1 == msb.len();
            if is_last {
                dst[ii + 1] |= m << msb_shift; // merge with lsb
            } else {
                dst[ii + 1] = m << msb_shift; // overwrite any prior value
            }
        }
    }
}

#[inline]
pub(crate) fn not(dst: &mut [Word], source: &[Word]) {
    bitwise_un_op(dst, source, |e| !e)
}

#[inline]
fn bitwise_un_op(dst: &mut [Word], source: &[Word], foo: fn(Word) -> Word) {
    for (d, s) in dst.iter_mut().zip(source.iter()) {
        *d = (foo)(*s);
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
fn bitwise_bin_op(dst: &mut [Word], a: &[Word], b: &[Word], foo: fn(Word, Word) -> Word) {
    for (d, (a, b)) in dst.iter_mut().zip(a.iter().zip(b.iter())) {
        *d = (foo)(*a, *b);
    }
}

#[inline]
pub(crate) fn cmp_equal(a: &[Word], b: &[Word]) -> Word {
    let bool_res = a.iter().zip(b.iter()).all(|(a, b)| a == b);
    bool_to_word(bool_res)
}

#[inline]
fn bool_to_word(value: bool) -> Word {
    if value {
        1
    } else {
        0
    }
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
    use rand::Rng;
    use rand_xoshiro::rand_core::SeedableRng;

    fn from_bit_str(bits: &str) -> (Vec<Word>, WidthInt) {
        let width = bits.len() as WidthInt;
        let mut out: Vec<Word> = Vec::new();
        let mut word = 0 as Word;

        for (ii, cc) in bits.chars().enumerate() {
            let ii_rev = width as usize - ii - 1;
            if ii_rev > 0 && ((ii_rev + 1) % Word::BITS as usize) == 0 {
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

    fn to_bit_str(values: &[Word], width: WidthInt) -> String {
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

    #[test]
    fn test_bit_string_conversion() {
        let a = "01100";
        let (a_vec, a_width) = from_bit_str(a);
        assert_eq!(a_width, 5);
        assert_eq!(a_vec, vec![0b1100]);

        let b = "10100001101000100000001010101010101000101010";
        let (b_vec, b_width) = from_bit_str(b);
        assert_eq!(b_width, 44);
        assert_eq!(b_vec, vec![0b10100001101000100000001010101010101000101010]);

        assert_eq!(to_bit_str(&b_vec, b_width), b);

        let c = "1010000110100010000000101010101010100010101010100001101000100000001010101010101000101010";
        let (c_vec, c_width) = from_bit_str(c);
        assert_eq!(c_width, 88);
        assert_eq!(
            c_vec,
            vec![
                0b1010101010100010101010100001101000100000001010101010101000101010, // lsb
                0b101000011010001000000010,                                         // msb
            ]
        );

        assert_eq!(to_bit_str(&c_vec, c_width), c);
    }

    fn random_bit_str(width: WidthInt, rnd: &mut impl Rng) -> String {
        let mut out = String::with_capacity(width as usize);
        for _ in 0..width {
            let cc = if rnd.gen_bool(0.5) { '1' } else { '0' };
            out.push(cc);
        }
        out
    }

    fn do_test_concat(a: &str, b: &str) {
        let (a_vec, a_width) = from_bit_str(a);
        let (b_vec, b_width) = from_bit_str(b);
        let c_width = a_width + b_width;
        let mut c_vec = vec![0 as Word; c_width.div_ceil(Word::BITS) as usize];
        concat(&mut c_vec, &a_vec, &b_vec, b_width);
        let expected = format!("{a}{b}");
        assert_eq!(to_bit_str(&c_vec, c_width), expected);
    }

    #[test]
    fn test_concat() {
        let mut rng = rand_xoshiro::Xoshiro256PlusPlus::seed_from_u64(1);
        do_test_concat(&random_bit_str(38, &mut rng), &random_bit_str(44, &mut rng));
        do_test_concat(&random_bit_str(38, &mut rng), &random_bit_str(8, &mut rng));
        // test a concat where dst and msb have the same number of words
        do_test_concat(
            &random_bit_str(10 + Word::BITS, &mut rng),
            &random_bit_str(8, &mut rng),
        );
    }

    fn do_test_slice(src: &str, hi: WidthInt, lo: WidthInt) {
        let (src_vec, src_width) = from_bit_str(src);
        assert!(hi >= lo);
        assert!(hi < src_width);
        let res_width = hi - lo + 1;
        let mut res_vec = vec![0 as Word; res_width.div_ceil(Word::BITS) as usize];
        slice(&mut res_vec, &src_vec, hi, lo);
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
        do_test_slice(&in0, 0, 0);
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
}
