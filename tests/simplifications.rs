// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use patronus::ir::*;

#[test]
fn test_simplify_and_or() {
    let mut ctx = Context::default();
    let tru = ctx.one(1);
    assert_eq!(simplify_single_expression(&mut ctx, tru), tru);
    let fals = ctx.zero(1);
    assert_eq!(simplify_single_expression(&mut ctx, fals), fals);
    let tru_and_fals = ctx.and(tru, fals);
    assert_eq!(simplify_single_expression(&mut ctx, tru_and_fals), fals);
    let tru_and_tru = ctx.and(tru, tru);
    assert_eq!(simplify_single_expression(&mut ctx, tru_and_tru), tru);
    let fals_or_tru = ctx.or(fals, tru);
    assert_eq!(simplify_single_expression(&mut ctx, fals_or_tru), tru);
    let fals_or_fals = ctx.or(fals, fals);
    assert_eq!(simplify_single_expression(&mut ctx, fals_or_fals), fals);
    let a = ctx.bv_symbol("a", 1);
    let a_and_tru = ctx.and(a, tru);
    assert_eq!(simplify_single_expression(&mut ctx, a_and_tru), a);
    let a_or_tru = ctx.or(a, tru);
    assert_eq!(simplify_single_expression(&mut ctx, a_or_tru), tru);
}

#[test]
fn test_simplify_ite() {
    let mut ctx = Context::default();
    let a = ctx.bv_symbol("a", 12);
    let b = ctx.bv_symbol("b", 12);
    let c = ctx.bv_symbol("c", 1);
    let tru = ctx.one(1);
    let fals = ctx.zero(1);

    // outcome is always the same
    let ite_c_a_a = ctx.bv_ite(c, a, a);
    assert_eq!(simplify_single_expression(&mut ctx, ite_c_a_a), a);

    // constant condition
    let ite_tru_a_b = ctx.bv_ite(tru, a, b);
    assert_eq!(simplify_single_expression(&mut ctx, ite_tru_a_b), a);
    let ite_fals_a_b = ctx.bv_ite(fals, a, b);
    assert_eq!(simplify_single_expression(&mut ctx, ite_fals_a_b), b);

    // both true and false value are boolean constants
    let ite_c_tru_fals = ctx.bv_ite(c, tru, fals);
    assert_eq!(simplify_single_expression(&mut ctx, ite_c_tru_fals), c);
    let ite_c_tru_tru = ctx.bv_ite(c, tru, tru);
    assert_eq!(simplify_single_expression(&mut ctx, ite_c_tru_tru), tru);
    let ite_c_fals_tru = ctx.bv_ite(c, fals, tru);
    let not_c = ctx.not(c);
    assert_eq!(simplify_single_expression(&mut ctx, ite_c_fals_tru), not_c);
}
