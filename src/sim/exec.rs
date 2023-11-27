// Copyright 2023 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

// contains implementations of our smt operations

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
pub(crate) fn mask(bits: WidthInt) -> Word {
    if bits == Word::BITS {
        Word::MAX
    } else {
        assert!(bits < Word::BITS);
        (1 as Word) << bits
    }
}

#[inline]
pub(crate) fn slice_to_word(source: &[Word], hi: WidthInt, lo: WidthInt) -> Word {
    let lo_word = lo / Word::BITS;
    let lo_offset = lo - (lo_word * Word::BITS);
    let hi_word = hi / Word::BITS;
    let hi_offset = hi - (hi_word * Word::BITS);

    let lsb = source[lo_word as usize] >> lo_offset;
    if hi_word == lo_word {
        lsb & mask(hi - lo + 1)
    } else {
        let lo_width = Word::BITS - lo_offset;
        let msb = source[hi_word as usize] & mask(hi_offset + 1);
        lsb | (msb << lo_width)
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
    for (d, s) in dst.iter_mut().zip(source.iter()) {
        *d = !(*s);
    }
}

#[inline]
pub(crate) fn cmp_equal(a: &[Word], b: &[Word]) -> bool {
    a.iter().zip(b.iter()).all(|(a, b)| a == b)
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

        (out, width)
    }

    fn to_bit_str(values: &[Word], width: WidthInt) -> String {
        let start_bit = (width - 1) % Word::BITS;
        let mut out = String::with_capacity(width as usize);
        for ii in (0..(start_bit + 1)).rev() {
            let value = (values[0] >> ii) & 1;
            if value == 1 {
                out.push('1');
            } else {
                out.push('0');
            }
        }
        for word in values.iter().skip(1) {
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
                0b101000011010001000000010,
                0b1010101010100010101010100001101000100000001010101010101000101010
            ]
        );

        assert_eq!(to_bit_str(&c_vec, c_width), c);
    }

    #[test]
    fn test_concat() {
        let a = "10101010100000001010101010101000101010";
        let b = "10100001101000100000001010101010101000101010";
        let (a_vec, a_width) = from_bit_str(a);
        let (b_vec, b_width) = from_bit_str(b);
        let c_width = a_width + b_width;
        let mut c_vec = vec![0 as Word; c_width.div_ceil(Word::BITS) as usize];
        concat(&mut c_vec, &a_vec, &b_vec, b_width);
        let expected = format!("{a}{b}");
        assert_eq!(to_bit_str(&c_vec, c_width), expected);
    }
}
