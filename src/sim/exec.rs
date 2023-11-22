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
) -> Option<(&mut [Word], &mut [Word])> {
    if dst.end >= src.start {
        let (a, b) = data.split_at_mut(src.end);
        let adjusted_dst = (dst.start - src.end)..(dst.end - src.end);
        Some((&mut b[adjusted_dst], &mut a[src.start..]))
    } else if src.end >= dst.start {
        let (a, b) = data.split_at_mut(dst.end);
        let adjusted_src = (src.start - dst.end)..(src.end - dst.end);
        Some((&mut a[dst.start..], &mut b[adjusted_src]))
    } else {
        None // overlap
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_split_borrow() {
        let data: &mut [Word] = &mut [0, 1, 2, 3];
        let (dst, src) = split_borrow_1(data, 0..1, 2..4).unwrap();
        assert_eq!(dst, &[0]);
        assert_eq!(src, &[2, 3]);
        let (dst2, src2) = split_borrow_1(data, 2..4, 0..2).unwrap();
        assert_eq!(dst2, &[2, 3]);
        assert_eq!(src2, &[0, 1]);
    }
}
