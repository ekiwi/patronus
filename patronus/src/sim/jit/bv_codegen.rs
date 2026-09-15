// Copyright 2025 Cornell University
// released under BSD 3-Clause License
// author: Zihan Li <zl2225@cornell.edu>
use crate::expr::{self, *};
use baa::{BitVecOps, BitVecValueRef};
use cranelift::codegen::ir::FuncRef;
use cranelift::prelude::*;

use super::compiler::{BVCodeGenVTable, CodeGenContext, TaggedValue};

/// Contains width of result bit vector type.
pub(super) struct BVWord(pub(super) WidthInt);
pub(super) struct BVIndirect(pub(super) WidthInt);

macro_rules! iconst {
    ($ctx: expr, $value: expr) => {
        $ctx.fn_builder.ins().iconst($ctx.int, ($value) as i64)
    };
}
pub(super) use iconst;

/// Given width of a bit vec value, select the smallest primitive type that is able to represent it
pub(super) fn select_container_primitive(width: WidthInt) -> cranelift::prelude::Type {
    match width {
        1..=8 => types::I8,
        9..=16 => types::I16,
        17..=32 => types::I32,
        33..=64 => types::I64,
        _ => panic!("unsupported width for thin bit vec"),
    }
}

impl BVWord {
    pub(super) fn new(width: WidthInt) -> Self {
        Self(width)
    }
}

impl BVWord {
    /// Unsigned extend input `value` to fit target width.
    pub(super) fn extend_to_fit(&self, value: TaggedValue, ctx: &mut CodeGenContext) -> Value {
        debug_assert!(self.0 >= value.expect_bv_type());
        let prev_type = select_container_primitive(value.expect_bv_type());
        let target_type = select_container_primitive(self.0);
        if !prev_type.eq(&target_type) {
            ctx.fn_builder.ins().uextend(target_type, *value)
        } else {
            *value
        }
    }

    pub(super) fn truncate_to_fit(&self, value: TaggedValue, ctx: &mut CodeGenContext) -> Value {
        debug_assert!(self.0 <= value.expect_bv_type());
        let prev_type = select_container_primitive(value.expect_bv_type());
        let target_type = select_container_primitive(self.0);
        if !prev_type.eq(&target_type) {
            ctx.fn_builder.ins().ireduce(target_type, *value)
        } else {
            *value
        }
    }

    fn overflow_guard(&self, value: Value, ctx: &mut CodeGenContext) -> Value {
        self.mask(value, self.0, ctx)
    }

    fn mask(&self, value: Value, width: WidthInt, ctx: &mut CodeGenContext) -> Value {
        if width < 64 {
            ctx.fn_builder
                .ins()
                .band_imm(value, ((u64::MAX) >> (64 - width)) as i64)
        } else {
            value
        }
    }

    fn cmp(&self, lhs: Value, rhs: Value, condcode: IntCC, ctx: &mut CodeGenContext) -> Value {
        ctx.fn_builder.ins().icmp(condcode, lhs, rhs)
    }
}

impl BVCodeGenVTable for BVWord {
    fn symbol(&self, arg: ExprRef, ctx: &mut CodeGenContext) -> Value {
        let value = ctx.load_input_state(arg);
        // TODO: currently bv symbol is always stored as `i64`
        self.truncate_to_fit(TaggedValue::tag_bv(*value, 64), ctx)
    }

    fn literal(&self, value: BitVecValueRef, ctx: &mut CodeGenContext) -> Value {
        ctx.fn_builder.ins().iconst(
            select_container_primitive(self.0),
            value.to_u64().unwrap() as i64,
        )
    }

    fn add(&self, lhs: TaggedValue, rhs: TaggedValue, ctx: &mut CodeGenContext) -> Value {
        self.overflow_guard(ctx.fn_builder.ins().iadd(*lhs, *rhs), ctx)
    }
    fn sub(&self, lhs: TaggedValue, rhs: TaggedValue, ctx: &mut CodeGenContext) -> Value {
        self.overflow_guard(ctx.fn_builder.ins().isub(*lhs, *rhs), ctx)
    }
    fn mul(&self, lhs: TaggedValue, rhs: TaggedValue, ctx: &mut CodeGenContext) -> Value {
        self.overflow_guard(ctx.fn_builder.ins().imul(*lhs, *rhs), ctx)
    }

    fn and(&self, lhs: TaggedValue, rhs: TaggedValue, ctx: &mut CodeGenContext) -> Value {
        ctx.fn_builder.ins().band(*lhs, *rhs)
    }
    fn or(&self, lhs: TaggedValue, rhs: TaggedValue, ctx: &mut CodeGenContext) -> Value {
        ctx.fn_builder.ins().bor(*lhs, *rhs)
    }
    fn xor(&self, lhs: TaggedValue, rhs: TaggedValue, ctx: &mut CodeGenContext) -> Value {
        ctx.fn_builder.ins().bxor(*lhs, *rhs)
    }

    fn not(&self, arg: TaggedValue, ctx: &mut CodeGenContext) -> Value {
        self.overflow_guard(ctx.fn_builder.ins().bnot(*arg), ctx)
    }
    fn negate(&self, arg: TaggedValue, ctx: &mut CodeGenContext) -> Value {
        let flipped = ctx.fn_builder.ins().bnot(*arg);
        self.overflow_guard(ctx.fn_builder.ins().iadd_imm(flipped, 1), ctx)
    }

    fn zero_extend(&self, arg: TaggedValue, _by: WidthInt, ctx: &mut CodeGenContext) -> Value {
        self.extend_to_fit(arg, ctx)
    }
    fn sign_extend(&self, arg: TaggedValue, _by: WidthInt, ctx: &mut CodeGenContext) -> Value {
        let mut ret = self.extend_to_fit(arg, ctx);
        let num_leading_zeros =
            select_container_primitive(self.0).bytes() * 8 - arg.expect_bv_type();
        if num_leading_zeros != 0 {
            let shifted = ctx.fn_builder.ins().ishl_imm(ret, num_leading_zeros as i64);
            ret = ctx
                .fn_builder
                .ins()
                .sshr_imm(shifted, num_leading_zeros as i64);
        }
        self.overflow_guard(ret, ctx)
    }

    fn shift_right(&self, arg0: TaggedValue, arg1: TaggedValue, ctx: &mut CodeGenContext) -> Value {
        assert!(!arg1.requires_bv_delegation());
        self.truncate_to_fit(
            TaggedValue::tag_bv(
                ctx.fn_builder.ins().ushr(*arg0, *arg1),
                arg0.expect_bv_type(),
            ),
            ctx,
        )
    }
    fn arithmetic_shift_right(
        &self,
        arg0: TaggedValue,
        arg1: TaggedValue,
        ctx: &mut CodeGenContext,
    ) -> Value {
        assert!(!arg1.requires_bv_delegation());
        self.truncate_to_fit(
            TaggedValue::tag_bv(
                ctx.fn_builder.ins().sshr(*arg0, *arg1),
                arg0.expect_bv_type(),
            ),
            ctx,
        )
    }
    fn shift_left(&self, arg0: TaggedValue, arg1: TaggedValue, ctx: &mut CodeGenContext) -> Value {
        assert!(!arg1.requires_bv_delegation());
        let arg0 = self.extend_to_fit(arg0, ctx);
        self.overflow_guard(ctx.fn_builder.ins().ishl(arg0, *arg1), ctx)
    }

    fn equal(&self, lhs: TaggedValue, rhs: TaggedValue, ctx: &mut CodeGenContext) -> Value {
        if lhs.requires_bv_delegation() {
            invoke_bv_extern_binary_function("equal", [lhs, rhs], ctx).unwrap()
        } else {
            self.cmp(*lhs, *rhs, IntCC::Equal, ctx)
        }
    }
    fn gt(&self, lhs: TaggedValue, rhs: TaggedValue, ctx: &mut CodeGenContext) -> Value {
        if lhs.requires_bv_delegation() {
            invoke_bv_extern_binary_function("gt", [lhs, rhs], ctx).unwrap()
        } else {
            self.cmp(*lhs, *rhs, IntCC::UnsignedGreaterThan, ctx)
        }
    }
    fn ge(&self, lhs: TaggedValue, rhs: TaggedValue, ctx: &mut CodeGenContext) -> Value {
        if lhs.requires_bv_delegation() {
            invoke_bv_extern_binary_function("ge", [lhs, rhs], ctx).unwrap()
        } else {
            self.cmp(*lhs, *rhs, IntCC::UnsignedGreaterThanOrEqual, ctx)
        }
    }
    fn gt_signed(&self, lhs: TaggedValue, rhs: TaggedValue, ctx: &mut CodeGenContext) -> Value {
        if lhs.requires_bv_delegation() {
            invoke_bv_extern_binary_function("gt_signed", [lhs, rhs], ctx).unwrap()
        } else {
            self.cmp(*lhs, *rhs, IntCC::SignedGreaterThan, ctx)
        }
    }
    fn ge_signed(&self, lhs: TaggedValue, rhs: TaggedValue, ctx: &mut CodeGenContext) -> Value {
        if lhs.requires_bv_delegation() {
            invoke_bv_extern_binary_function("ge_signed", [lhs, rhs], ctx).unwrap()
        } else {
            self.cmp(*lhs, *rhs, IntCC::SignedGreaterThanOrEqual, ctx)
        }
    }

    fn concat(&self, hi: TaggedValue, lo: TaggedValue, ctx: &mut CodeGenContext) -> Value {
        let lo_width = lo.expect_bv_type();
        let (hi, lo) = (self.extend_to_fit(hi, ctx), self.extend_to_fit(lo, ctx));
        let hi = ctx.fn_builder.ins().ishl_imm(hi, lo_width as i64);
        ctx.fn_builder.ins().bor(hi, lo)
    }

    fn slice(
        &self,
        value: TaggedValue,
        hi: WidthInt,
        lo: WidthInt,
        ctx: &mut CodeGenContext,
    ) -> Value {
        if value.requires_bv_delegation() {
            #[cfg(feature = "aot-clif")]
            {
                if let Some(stack_slot_addr) = aot::slice_with_dst_words_allocator(
                    value,
                    hi,
                    lo,
                    |width, ctx| {
                        assert!(width <= super::THIN_BV_MAX_WIDTH);
                        let stack_slot =
                            ctx.fn_builder
                                .func
                                .create_sized_stack_slot(StackSlotData::new(
                                    StackSlotKind::ExplicitSlot,
                                    size_of::<baa::Word>() as u32,
                                    3,
                                ));
                        ctx.fn_builder.ins().stack_addr(ctx.int, stack_slot, 0)
                    },
                    ctx,
                ) {
                    let ret = ctx.fn_builder.ins().load(
                        ctx.int,
                        codegen::ir::MemFlags::trusted(),
                        stack_slot_addr,
                        0,
                    );
                    return self.truncate_to_fit(TaggedValue::tag_bv(ret, 64), ctx);
                }
            }
            let hi = iconst!(ctx, hi);
            let lo = iconst!(ctx, lo);
            let value_width = iconst!(ctx, value.expect_bv_type());

            // extern `slice` fn always returns i64 type
            let ret = invoke_bv_extern_function(
                ctx.runtime_lib.bv_ops["slice"],
                &[*value, value_width, hi, lo],
                ctx,
            )
            .unwrap();
            self.truncate_to_fit(TaggedValue::tag_bv(ret, 64), ctx)
        } else {
            let shifted = self.truncate_to_fit(
                TaggedValue::tag_bv(
                    ctx.fn_builder.ins().ushr_imm(*value, lo as i64),
                    value.expect_bv_type(),
                ),
                ctx,
            );
            self.mask(shifted, hi - lo + 1, ctx)
        }
    }
    fn implies(&self, lhs: TaggedValue, rhs: TaggedValue, ctx: &mut CodeGenContext) -> Value {
        let lhs = ctx.fn_builder.ins().bnot(*lhs);
        let ret = ctx.fn_builder.ins().bor(lhs, *rhs);
        self.overflow_guard(ret, ctx)
    }
}

fn invoke_bv_extern_function(
    func: FuncRef,
    args: &[Value],
    ctx: &mut CodeGenContext,
) -> Option<Value> {
    let call = ctx.fn_builder.ins().call(func, args);
    ctx.fn_builder.inst_results(call).first().copied()
}

fn invoke_bv_extern_binary_function(
    symbol: impl AsRef<str>,
    args: [TaggedValue; 2],
    ctx: &mut CodeGenContext,
) -> Option<Value> {
    let [lhs, rhs] = args;
    debug_assert_eq!(lhs.expect_bv_type(), rhs.expect_bv_type());
    invoke_bv_extern_function(
        ctx.runtime_lib.bv_ops[symbol.as_ref()],
        &[*lhs, *rhs, iconst!(ctx, lhs.expect_bv_type())],
        ctx,
    )
}

fn invoke_bv_extern_binary_in_place_function(
    symbol: impl AsRef<str>,
    args: [TaggedValue; 3],
    ctx: &mut CodeGenContext,
) -> Option<Value> {
    let [dst, lhs, rhs] = args;
    debug_assert_eq!(lhs.expect_bv_type(), rhs.expect_bv_type());
    debug_assert_eq!(dst.expect_bv_type(), lhs.expect_bv_type());
    invoke_bv_extern_function(
        ctx.runtime_lib.bv_ops[symbol.as_ref()],
        &[*dst, *lhs, *rhs, iconst!(ctx, dst.expect_bv_type())],
        ctx,
    )
}

/// Returns reserved bv cache slot.
fn reserve_bv_slot_and_then(
    width: WidthInt,
    ctx: &mut CodeGenContext,
    op: impl FnOnce(TaggedValue, &mut CodeGenContext),
) -> Value {
    let dst_slot = ctx.reserve_intermediate_bv_cache_slot(width);
    let dst = ctx.resource_ptr_at_slot(dst_slot);
    op(dst, ctx);
    *dst_slot
}

impl BVIndirect {
    pub(super) fn new(width: WidthInt) -> Self {
        Self(width)
    }

    #[inline]
    fn with_dst(
        &self,
        ctx: &mut CodeGenContext,
        op: impl FnOnce(TaggedValue, &mut CodeGenContext),
    ) -> Value {
        reserve_bv_slot_and_then(self.0, ctx, op)
    }
}

impl BVCodeGenVTable for BVIndirect {
    fn symbol(&self, arg: ExprRef, ctx: &mut CodeGenContext) -> Value {
        self.with_dst(ctx, |dst, ctx| {
            let value = ctx.load_input_state(arg);
            ctx.copy_from_bv(dst, value);
        })
    }

    fn literal(&self, value: BitVecValueRef, ctx: &mut CodeGenContext) -> Value {
        self.with_dst(ctx, |dst, ctx| {
            let owned_bv_literal = value.words().to_vec().into_boxed_slice();
            let ptr = owned_bv_literal.as_ref() as *const [baa::Word] as *const baa::Word;
            ctx.compiler.constant.bv_data.push(owned_bv_literal);
            let src = TaggedValue {
                value: iconst!(ctx, ptr),
                data_type: expr::Type::BV(self.0),
            };
            ctx.copy_from_bv(dst, src);
        })
    }

    fn add(&self, lhs: TaggedValue, rhs: TaggedValue, ctx: &mut CodeGenContext) -> Value {
        self.with_dst(ctx, |dst, ctx| {
            invoke_bv_extern_binary_in_place_function("add", [dst, lhs, rhs], ctx);
        })
    }

    fn sub(&self, lhs: TaggedValue, rhs: TaggedValue, ctx: &mut CodeGenContext) -> Value {
        self.with_dst(ctx, |dst, ctx| {
            invoke_bv_extern_binary_in_place_function("sub", [dst, lhs, rhs], ctx);
        })
    }
    fn mul(&self, lhs: TaggedValue, rhs: TaggedValue, ctx: &mut CodeGenContext) -> Value {
        self.with_dst(ctx, |dst, ctx| {
            invoke_bv_extern_binary_in_place_function("mul", [dst, lhs, rhs], ctx);
        })
    }

    fn and(&self, lhs: TaggedValue, rhs: TaggedValue, ctx: &mut CodeGenContext) -> Value {
        self.with_dst(ctx, |dst, ctx| {
            invoke_bv_extern_binary_in_place_function("and", [dst, lhs, rhs], ctx);
        })
    }
    fn or(&self, lhs: TaggedValue, rhs: TaggedValue, ctx: &mut CodeGenContext) -> Value {
        self.with_dst(ctx, |dst, ctx| {
            invoke_bv_extern_binary_in_place_function("or", [dst, lhs, rhs], ctx);
        })
    }
    fn xor(&self, lhs: TaggedValue, rhs: TaggedValue, ctx: &mut CodeGenContext) -> Value {
        self.with_dst(ctx, |dst, ctx| {
            invoke_bv_extern_binary_in_place_function("xor", [dst, lhs, rhs], ctx);
        })
    }

    fn not(&self, arg: TaggedValue, ctx: &mut CodeGenContext) -> Value {
        self.with_dst(ctx, |dst, ctx| {
            invoke_bv_extern_function(
                ctx.runtime_lib.bv_ops["not"],
                &[*dst, *arg, iconst!(ctx, arg.expect_bv_type())],
                ctx,
            );
        })
    }

    fn negate(&self, arg: TaggedValue, ctx: &mut CodeGenContext) -> Value {
        self.with_dst(ctx, |dst, ctx| {
            invoke_bv_extern_function(
                ctx.runtime_lib.bv_ops["negate"],
                &[*dst, *arg, iconst!(ctx, arg.expect_bv_type())],
                ctx,
            );
        })
    }

    fn zero_extend(&self, arg: TaggedValue, by: WidthInt, ctx: &mut CodeGenContext) -> Value {
        self.with_dst(ctx, |dst, ctx| {
            let arg = if arg.expect_bv_type() <= super::THIN_BV_MAX_WIDTH {
                BVWord(64).extend_to_fit(arg, ctx)
            } else {
                *arg
            };
            let original_width = iconst!(ctx, self.0 - by);
            let by = iconst!(ctx, by);
            invoke_bv_extern_function(
                ctx.runtime_lib.bv_ops["zero_extend"],
                &[*dst, arg, original_width, by],
                ctx,
            );
        })
    }

    fn sign_extend(&self, arg: TaggedValue, by: WidthInt, ctx: &mut CodeGenContext) -> Value {
        self.with_dst(ctx, |dst, ctx| {
            let arg = if arg.expect_bv_type() <= super::THIN_BV_MAX_WIDTH {
                BVWord(64).extend_to_fit(arg, ctx)
            } else {
                *arg
            };
            let original_width = iconst!(ctx, self.0 - by);
            let by = iconst!(ctx, by);
            invoke_bv_extern_function(
                ctx.runtime_lib.bv_ops["sign_extend"],
                &[*dst, arg, original_width, by],
                ctx,
            );
        })
    }

    fn shift_right(&self, arg0: TaggedValue, arg1: TaggedValue, ctx: &mut CodeGenContext) -> Value {
        self.with_dst(ctx, |dst, ctx| {
            let shift_data_width = iconst!(ctx, arg1.expect_bv_type());
            let data_width = iconst!(ctx, arg0.expect_bv_type());
            invoke_bv_extern_function(
                ctx.runtime_lib.bv_ops["shift_right"],
                &[*dst, *arg0, data_width, *arg1, shift_data_width],
                ctx,
            );
        })
    }

    fn arithmetic_shift_right(
        &self,
        arg0: TaggedValue,
        arg1: TaggedValue,
        ctx: &mut CodeGenContext,
    ) -> Value {
        self.with_dst(ctx, |dst, ctx| {
            let shift_data_width = iconst!(ctx, arg1.expect_bv_type());
            let data_width = iconst!(ctx, arg0.expect_bv_type());
            invoke_bv_extern_function(
                ctx.runtime_lib.bv_ops["arithmetic_shift_right"],
                &[*dst, *arg0, data_width, *arg1, shift_data_width],
                ctx,
            );
        })
    }

    fn shift_left(&self, arg0: TaggedValue, arg1: TaggedValue, ctx: &mut CodeGenContext) -> Value {
        self.with_dst(ctx, |dst, ctx| {
            let shift_data_width = iconst!(ctx, arg1.expect_bv_type());
            let data_width = iconst!(ctx, arg0.expect_bv_type());
            invoke_bv_extern_function(
                ctx.runtime_lib.bv_ops["shift_left"],
                &[*dst, *arg0, data_width, *arg1, shift_data_width],
                ctx,
            );
        })
    }

    fn equal(&self, _lhs: TaggedValue, _rhs: TaggedValue, _ctx: &mut CodeGenContext) -> Value {
        unreachable!()
    }
    fn gt(&self, _lhs: TaggedValue, _rhs: TaggedValue, _ctx: &mut CodeGenContext) -> Value {
        unreachable!()
    }
    fn ge(&self, _lhs: TaggedValue, _rhs: TaggedValue, _ctx: &mut CodeGenContext) -> Value {
        unreachable!()
    }
    fn gt_signed(&self, _lhs: TaggedValue, _rhs: TaggedValue, _ctx: &mut CodeGenContext) -> Value {
        unreachable!()
    }
    fn ge_signed(&self, _lhs: TaggedValue, _rhs: TaggedValue, _ctx: &mut CodeGenContext) -> Value {
        unreachable!()
    }
    fn implies(&self, _lhs: TaggedValue, _rhs: TaggedValue, _ctx: &mut CodeGenContext) -> Value {
        unreachable!()
    }

    fn concat(&self, mut hi: TaggedValue, mut lo: TaggedValue, ctx: &mut CodeGenContext) -> Value {
        self.with_dst(ctx, |dst, ctx| {
            // extern `concat` function expects i64 type
            if !hi.requires_bv_delegation() {
                hi.value = BVWord(64).extend_to_fit(hi, ctx);
            }
            if !lo.requires_bv_delegation() {
                lo.value = BVWord(64).extend_to_fit(lo, ctx);
            }
            let (hi_width, lo_width) = (
                iconst!(ctx, hi.expect_bv_type()),
                iconst!(ctx, lo.expect_bv_type()),
            );
            invoke_bv_extern_function(
                ctx.runtime_lib.bv_ops["concat"],
                &[*dst, *hi, *lo, hi_width, lo_width],
                ctx,
            );
        })
    }

    fn slice(
        &self,
        value: TaggedValue,
        hi: WidthInt,
        lo: WidthInt,
        ctx: &mut CodeGenContext,
    ) -> Value {
        self.with_dst(ctx, |dst, ctx| {
            let (hi, lo) = (iconst!(ctx, hi), iconst!(ctx, lo));
            let value_width = iconst!(ctx, value.expect_bv_type());
            invoke_bv_extern_function(
                ctx.runtime_lib.bv_ops["slice_with_output_buffer"],
                &[*dst, *value, value_width, hi, lo],
                ctx,
            );
        })
    }
}

#[cfg(feature = "aot-clif")]
pub(super) use aot::BVIndirectAOT;

#[cfg(feature = "aot-clif")]
mod aot {
    use super::*;
    pub struct BVIndirectAOT {
        width: WidthInt,
        fallback: BVIndirect,
    }

    impl BVIndirectAOT {
        pub fn new(width: WidthInt) -> Self {
            Self {
                width,
                fallback: BVIndirect::new(width),
            }
        }
    }

    pub fn slice_with_dst_words_allocator<A>(
        src: TaggedValue,
        hi: WidthInt,
        lo: WidthInt,
        allocator: A,
        ctx: &mut CodeGenContext,
    ) -> Option<Value>
    where
        A: FnOnce(WidthInt, &mut CodeGenContext) -> Value,
    {
        let aot_slice = ctx.aot_func_ref("slice")?;
        let dst_width = hi - lo + 1;
        let dst_words = allocator(dst_width, ctx);
        let dst_len = iconst!(ctx, dst_width.div_ceil(baa::Word::BITS));
        let src_len = iconst!(ctx, src.bv_num_words());
        let (hi, lo) = (iconst!(ctx, hi), iconst!(ctx, lo));
        invoke_bv_extern_function(aot_slice, &[dst_words, dst_len, *src, src_len, hi, lo], ctx);
        Some(dst_words)
    }

    /// Store `value` to a fresh stack slot.
    /// Returns the starting address of stack slot.
    fn move_to_stack_slot(value: TaggedValue, ctx: &mut CodeGenContext) -> Value {
        debug_assert!(!value.requires_bv_delegation());
        let stack_slot = ctx
            .fn_builder
            .func
            .create_sized_stack_slot(StackSlotData::new(
                StackSlotKind::ExplicitSlot,
                size_of::<baa::Word>() as u32,
                3,
            ));
        let value = BVWord(baa::Word::BITS).extend_to_fit(value, ctx);
        ctx.fn_builder.ins().stack_store(value, stack_slot, 0);
        ctx.fn_builder.ins().stack_addr(types::I64, stack_slot, 0)
    }

    /// Returns the starting address and length of the underlying words buffer of bitvector.
    /// This might involve stack allocation if `value` is not backed by a `baa::BitVec`
    fn words_slice_raw_parts(value: TaggedValue, ctx: &mut CodeGenContext) -> (Value, Value) {
        let address = if value.requires_bv_delegation() {
            *value
        } else {
            move_to_stack_slot(value, ctx)
        };
        let len = iconst!(ctx, value.bv_num_words());
        (address, len)
    }

    impl BVCodeGenVTable for BVIndirectAOT {
        /// External `slice` function prototype:
        /// ```ignore
        /// fn slice(
        ///     dst: *mut Word, dst_len: usize,
        ///     src: *const Word, src_len: usize,
        ///     hi: usize, lo: usize,
        /// )
        /// ```
        fn slice(
            &self,
            value: TaggedValue,
            hi: WidthInt,
            lo: WidthInt,
            ctx: &mut CodeGenContext,
        ) -> Value {
            let mut dst_slot = None;
            slice_with_dst_words_allocator(
                value,
                hi,
                lo,
                |width, ctx| {
                    debug_assert_eq!(width, self.width);
                    let reserved_slot = ctx.reserve_intermediate_bv_cache_slot(width);
                    let dst = ctx.resource_ptr_at_slot(reserved_slot);
                    dst_slot = Some(*reserved_slot);
                    words_slice_raw_parts(dst, ctx).0
                },
                ctx,
            );
            dst_slot.unwrap_or_else(|| self.fallback.slice(value, hi, lo, ctx))
        }

        /// External `concat` function prototype:
        /// ```ignore
        /// fn concat(
        ///     dst: *mut Word, dst_len: usize,
        ///     msb: *const Word, msb_len: usize,
        ///     lsb: *const Word, lsb_len: usize,
        ///     lsb_width: usize,
        /// )
        /// ```
        fn concat(&self, hi: TaggedValue, lo: TaggedValue, ctx: &mut CodeGenContext) -> Value {
            let Some(aot_concat) = ctx.aot_func_ref("concat") else {
                return self.fallback.concat(hi, lo, ctx);
            };
            let (hi_words, hi_len) = words_slice_raw_parts(hi, ctx);
            let (lo_words, lo_len) = words_slice_raw_parts(lo, ctx);
            let lsb_width = iconst!(ctx, lo.expect_bv_type());
            reserve_bv_slot_and_then(self.width, ctx, |dst, ctx| {
                let (dst_words, dst_len) = words_slice_raw_parts(dst, ctx);
                invoke_bv_extern_function(
                    aot_concat,
                    &[
                        dst_words, dst_len, hi_words, hi_len, lo_words, lo_len, lsb_width,
                    ],
                    ctx,
                );
            })
        }

        delegate::delegate! {
            to self.fallback {
                fn symbol(&self, expr: ExprRef, ctx: &mut CodeGenContext) -> Value;
                fn literal(&self, value: BitVecValueRef, ctx: &mut CodeGenContext) -> Value;
                fn add(&self, lhs: TaggedValue, rhs: TaggedValue, ctx: &mut CodeGenContext) -> Value;
                fn sub(&self, lhs: TaggedValue, rhs: TaggedValue, ctx: &mut CodeGenContext) -> Value;
                fn mul(&self, lhs: TaggedValue, rhs: TaggedValue, ctx: &mut CodeGenContext) -> Value;
                fn and(&self, lhs: TaggedValue, rhs: TaggedValue, ctx: &mut CodeGenContext) -> Value;
                fn or(&self, lhs: TaggedValue, rhs: TaggedValue, ctx: &mut CodeGenContext) -> Value;
                fn xor(&self, lhs: TaggedValue, rhs: TaggedValue, ctx: &mut CodeGenContext) -> Value;
                fn not(&self, arg: TaggedValue, ctx: &mut CodeGenContext) -> Value;
                fn negate(&self, arg: TaggedValue, ctx: &mut CodeGenContext) -> Value;
                fn zero_extend(&self, arg: TaggedValue, by: WidthInt, ctx: &mut CodeGenContext) -> Value;
                fn sign_extend(&self, arg: TaggedValue, by: WidthInt, ctx: &mut CodeGenContext) -> Value;

                fn shift_right(&self, arg0: TaggedValue, arg1: TaggedValue, ctx: &mut CodeGenContext) -> Value;
                fn arithmetic_shift_right(
                    &self,
                    arg0: TaggedValue,
                    arg1: TaggedValue,
                    ctx: &mut CodeGenContext,
                ) -> Value;
                fn shift_left(&self, arg0: TaggedValue, arg1: TaggedValue, ctx: &mut CodeGenContext) -> Value;

                fn equal(&self, lhs: TaggedValue, rhs: TaggedValue, ctx: &mut CodeGenContext) -> Value;
                fn gt(&self, lhs: TaggedValue, rhs: TaggedValue, ctx: &mut CodeGenContext) -> Value;
                fn ge(&self, lhs: TaggedValue, rhs: TaggedValue, ctx: &mut CodeGenContext) -> Value;
                fn gt_signed(&self, lhs: TaggedValue, rhs: TaggedValue, ctx: &mut CodeGenContext) -> Value;
                fn ge_signed(&self, lhs: TaggedValue, rhs: TaggedValue, ctx: &mut CodeGenContext) -> Value;
                fn implies(&self, lhs: TaggedValue, rhs: TaggedValue, ctx: &mut CodeGenContext) -> Value;
            }
        }
    }
}
