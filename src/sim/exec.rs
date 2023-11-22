// Copyright 2023 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>

// contains implementations of our smt operations

use std::ops::Range;

pub(crate) type Word = u64;

#[inline]
pub(crate) fn add(dst: &mut [Word], a: &[Word], b: &[Word]) {}

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
