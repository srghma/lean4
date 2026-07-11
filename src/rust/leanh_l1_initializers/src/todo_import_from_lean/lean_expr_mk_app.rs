use leanh_l1::{
    datatypes::LeanObject,
    emitted::{
        lean_alloc_ctor::lean_alloc_ctor, lean_ctor_get_uint64::lean_ctor_get_uint64,
        lean_ctor_set::lean_ctor_set, lean_ctor_set_uint64::lean_ctor_set_uint64,
    },
    r#priv::lean_uint64_mix_hash::lean_uint64_mix_hash,
};

use crate::todo_import_from_lean::lean_expr_mk_const::EXPR_DATA_OFFSET;

const EXPR_APP_TAG: u32 = 5;
const EXPR_APP_FIELDS: u32 = 2;
const EXPR_APP_SCALAR_SIZE: u32 = core::mem::size_of::<u64>() as u32;
const EXPR_FLAGS_MASK: u64 = 0x0F_u64 << 40;
const EXPR_DEPTH_SHIFT: u32 = 32;
const EXPR_DEPTH_MASK: u64 = 0xFF;
const EXPR_RANGE_SHIFT: u32 = 44;

#[inline]
unsafe fn lean_expr_data(expr: *const LeanObject) -> u64 {
    lean_ctor_get_uint64(expr, EXPR_DATA_OFFSET as u32)
}

#[inline]
unsafe fn lean_expr_mk_app_data(fn_data: u64, arg_data: u64) -> u64 {
    let mut depth = ((fn_data >> EXPR_DEPTH_SHIFT) & EXPR_DEPTH_MASK)
        .max((arg_data >> EXPR_DEPTH_SHIFT) & EXPR_DEPTH_MASK)
        + 1;
    if depth > EXPR_DEPTH_MASK {
        depth = EXPR_DEPTH_MASK;
    }
    let range = (fn_data >> EXPR_RANGE_SHIFT).max(arg_data >> EXPR_RANGE_SHIFT);
    let hash = lean_uint64_mix_hash(fn_data, arg_data) as u64;
    let flags = (fn_data | arg_data) & EXPR_FLAGS_MASK;
    flags | hash | (depth << EXPR_DEPTH_SHIFT) | (range << EXPR_RANGE_SHIFT)
}

pub unsafe fn lean_expr_mk_app(
    fn_expr: *mut LeanObject,
    arg_expr: *mut LeanObject,
) -> *mut LeanObject {
    let data = lean_expr_mk_app_data(lean_expr_data(fn_expr), lean_expr_data(arg_expr));
    let expr = lean_alloc_ctor(EXPR_APP_TAG, EXPR_APP_FIELDS, EXPR_APP_SCALAR_SIZE);
    lean_ctor_set(expr, 0, fn_expr);
    lean_ctor_set(expr, 1, arg_expr);
    lean_ctor_set_uint64(expr, EXPR_DATA_OFFSET, data);
    expr
}
