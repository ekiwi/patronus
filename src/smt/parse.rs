// Copyright 2023 The Regents of the University of California
// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::ir::*;
use baa::{ArrayMutOps, ArrayValue, BitVecValue, WidthInt};
use easy_smt as smt;

pub fn parse_smt_bit_vec(smt_ctx: &smt::Context, expr: smt::SExpr) -> Option<BitVecValue> {
    let data = smt_ctx.get(expr);
    match data {
        smt::SExprData::Atom(value) => Some(smt_bit_vec_str_to_value(value)),
        // unwraps expressions like: ((a true))
        smt::SExprData::List([inner]) => parse_smt_bit_vec(smt_ctx, *inner),
        // unwraps expressions like: (a true)
        smt::SExprData::List([_, value]) => parse_smt_bit_vec(smt_ctx, *value),
        _ => None,
    }
}

pub fn parse_smt_array(smt_ctx: &smt::Context, expr: smt::SExpr) -> Option<baa::ArrayValue> {
    let data = smt_ctx.get(expr);
    match data {
        smt::SExprData::List([p0, p1]) => parse_smt_as_const(smt_ctx, *p0, *p1),
        smt::SExprData::List([id, array, index, value]) => {
            parse_smt_store(smt_ctx, *id, *array, *index, *value)
        }
        _ => todo!("Unexpected array expression: {}", smt_ctx.display(expr)),
    }
}

fn parse_smt_as_const(
    smt_ctx: &smt::Context,
    p0: smt::SExpr,
    p1: smt::SExpr,
) -> Option<ArrayValue> {
    match smt_ctx.get(p0) {
        smt::SExprData::List([as_str, const_str, array_tpe]) => {
            parse_smt_id(smt_ctx, *as_str, "as")?;
            parse_smt_id(smt_ctx, *const_str, "const")?;
            let tpe = parse_smt_array_tpe(smt_ctx, *array_tpe)?;
            let default_value = parse_smt_bit_vec(smt_ctx, p1)?;
            let array = ArrayValue::new_sparse(tpe.index_width, &default_value);
            Some(array)
        }
        _ => None,
    }
}

fn parse_smt_store(
    smt_ctx: &smt::Context,
    id: smt::SExpr,
    array: smt::SExpr,
    index: smt::SExpr,
    value: smt::SExpr,
) -> Option<baa::ArrayValue> {
    parse_smt_id(smt_ctx, id, "store")?;
    let mut inner = parse_smt_array(smt_ctx, array)?;
    let index = parse_smt_bit_vec(smt_ctx, index)?;
    let data = parse_smt_bit_vec(smt_ctx, value)?;
    inner.store(&index, &data);
    Some(inner)
}

fn parse_smt_array_tpe(smt_ctx: &smt::Context, expr: smt::SExpr) -> Option<ArrayType> {
    match smt_ctx.get(expr) {
        smt::SExprData::List([array, index, data]) => {
            parse_smt_id(smt_ctx, *array, "Array")?;
            let index_width = parse_smt_bit_vec_tpe(smt_ctx, *index)?;
            let data_width = parse_smt_bit_vec_tpe(smt_ctx, *data)?;
            Some(ArrayType {
                index_width,
                data_width,
            })
        }
        _ => None,
    }
}

fn parse_smt_bit_vec_tpe(smt_ctx: &smt::Context, expr: smt::SExpr) -> Option<WidthInt> {
    match smt_ctx.get(expr) {
        smt::SExprData::List([under_score, bit_vec, width]) => {
            parse_smt_id(smt_ctx, *under_score, "_")?;
            parse_smt_id(smt_ctx, *bit_vec, "BitVec")?;
            match smt_ctx.get(*width) {
                smt::SExprData::Atom(val) => Some(WidthInt::from_str_radix(val, 10).unwrap()),
                _ => None,
            }
        }
        _ => None,
    }
}

fn parse_smt_id(smt_ctx: &smt::Context, expr: smt::SExpr, expected: &str) -> Option<()> {
    match smt_ctx.get(expr) {
        smt::SExprData::Atom(val) if val == expected => Some(()),
        _ => None,
    }
}

fn smt_bit_vec_str_to_value(a: &str) -> BitVecValue {
    if let Some(suffix) = a.strip_prefix("#b") {
        BitVecValue::from_bit_str(suffix).unwrap()
    } else if let Some(suffix) = a.strip_prefix("#x") {
        BitVecValue::from_hex_str(suffix).unwrap()
    } else if a == "true" {
        BitVecValue::tru()
    } else if a == "false" {
        BitVecValue::fals()
    } else {
        todo!("decimal string: {a}")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::smt::serialize::PatronSmtHelpers;
    use baa::ArrayOps;
    use baa::*;
    use easy_smt::*;

    #[test]
    fn test_parse_smt_array_const_and_store() {
        let ctx = ContextBuilder::new().build().unwrap();
        let data_width = 32usize;
        let index_width = 5usize;
        let default_value = 0b110011u64;
        let tpe = ctx.array_sort(
            ctx.bit_vec_sort(ctx.numeral(index_width)),
            ctx.bit_vec_sort(ctx.numeral(data_width)),
        );
        let default = ctx.binary(data_width, default_value);

        // check the base expression
        // ((as const (Array (_ BitVec 5) (_ BitVec 32))) #b00000000000000000000000000110011)
        let base = ctx.const_array(tpe, default);
        let base_val = parse_smt_array(&ctx, base).unwrap();
        for ii in 0..(1 << 5) {
            assert_eq!(
                base_val
                    .select(&BitVecValue::from_u64(ii, 5))
                    .to_u64()
                    .unwrap(),
                default_value
            );
        }

        // store
        // (store <base> #b01110 #x00000000)
        let store_index: usize = 14;
        let store_data: usize = 0;
        let store = ctx.store(
            base,
            ctx.binary(index_width, store_index),
            ctx.binary(data_width, store_data),
        );
        let store_val = parse_smt_array(&ctx, store).unwrap();
        for ii in 0..(1 << 5) {
            let data = store_val
                .select(&BitVecValue::from_u64(ii, 5))
                .to_u64()
                .unwrap();
            if ii == store_index as u64 {
                assert_eq!(data, store_data as u64);
            } else {
                assert_eq!(data, default_value);
            }
        }

        // two stores
        // (store <store> #b01110 #x00000011)
        let store2_index: usize = 14;
        let store2_data: usize = 3;
        let store2 = ctx.store(
            store,
            ctx.binary(index_width, store2_index),
            ctx.binary(data_width, store2_data),
        );
        let store2_val = parse_smt_array(&ctx, store2).unwrap();
        for ii in 0..(1 << 5) {
            let data = store2_val
                .select(&BitVecValue::from_u64(ii, 5))
                .to_u64()
                .unwrap();
            if ii == store_index as u64 {
                assert_eq!(store_index, store2_index);
                assert_eq!(data, store2_data as u64);
            } else {
                assert_eq!(data, default_value);
            }
        }
    }

    #[test]
    fn test_yices2_result_parsing() {
        // yices will produce responses like this for a `get-value` call:
        // ((n9@0 true))
        let ctx = ContextBuilder::new().build().unwrap();
        let r0 = ctx.list(vec![ctx.list(vec![ctx.atom("n9@0"), ctx.true_()])]);
        let val0 = parse_smt_bit_vec(&ctx, r0).unwrap();
        assert_eq!(val0.to_u64().unwrap(), 1);
        assert_eq!(val0.width(), 1);
        assert!(val0.is_tru());
    }
}
