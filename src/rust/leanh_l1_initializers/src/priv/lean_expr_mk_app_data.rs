use leanh_l1::r#priv::lean_uint64_mix_hash::lean_uint64_mix_hash;

use crate::r#priv::expr_bvar_range_data::expr_bvar_range_data;

const EXPR_DEPTH_SHIFT: u32 = 32;
const EXPR_DEPTH_MASK: u64 = 0xFF;
const EXPR_FLAGS_MASK: u64 = 0x0F_u64 << 40;
const EXPR_RANGE_SHIFT: u32 = 44;

#[inline]
pub unsafe fn lean_expr_mk_app_data(fn_data: u64, arg_data: u64) -> u64 {
    let mut depth = ((fn_data >> EXPR_DEPTH_SHIFT) & EXPR_DEPTH_MASK)
        .max((arg_data >> EXPR_DEPTH_SHIFT) & EXPR_DEPTH_MASK)
        + 1;
    if depth > EXPR_DEPTH_MASK {
        depth = EXPR_DEPTH_MASK;
    }
    let range = expr_bvar_range_data(fn_data).max(expr_bvar_range_data(arg_data));
    let hash = lean_uint64_mix_hash(fn_data, arg_data) as u64;
    let flags = (fn_data | arg_data) & EXPR_FLAGS_MASK;
    flags | hash | (depth << EXPR_DEPTH_SHIFT) | (range << EXPR_RANGE_SHIFT)
}
