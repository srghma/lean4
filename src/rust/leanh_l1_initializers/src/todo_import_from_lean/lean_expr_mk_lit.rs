use leanh_l1::{
    datatypes::LeanObject,
    emitted::{
        lean_alloc_ctor::lean_alloc_ctor, lean_ctor_get::lean_ctor_get,
        lean_ctor_set::lean_ctor_set, lean_ctor_set_uint64::lean_ctor_set_uint64,
        lean_unbox::lean_unbox,
    },
};

use crate::r#priv::lean_expr_mk_data::lean_expr_mk_data;
use crate::todo_import_from_lean::lean_expr_mk_const::EXPR_DATA_OFFSET;

const EXPR_LIT_TAG: u32 = 9;
const EXPR_LIT_FIELDS: u32 = 1;
const EXPR_LIT_SCALAR_SIZE: u32 = core::mem::size_of::<u64>() as u32;
const EXPR_LIT_HASH_SEED: u64 = 3;

#[inline]
pub unsafe fn lean_expr_mk_lit(lit: *mut LeanObject) -> *mut LeanObject {
    let value = lean_unbox(lean_ctor_get(lit, 0)) as u64;
    let hash =
        leanh_l1::r#priv::lean_uint64_mix_hash::lean_uint64_mix_hash(EXPR_LIT_HASH_SEED, value);
    let data = lean_expr_mk_data(
        hash,
        leanh_l1::emitted::lean_unsigned_to_nat::lean_unsigned_to_nat(0),
        0,
        false,
        false,
        false,
        false,
    );
    let expr = lean_alloc_ctor(EXPR_LIT_TAG, EXPR_LIT_FIELDS, EXPR_LIT_SCALAR_SIZE);
    lean_ctor_set(expr, 0, lit);
    lean_ctor_set_uint64(expr, EXPR_DATA_OFFSET, data);
    expr
}
