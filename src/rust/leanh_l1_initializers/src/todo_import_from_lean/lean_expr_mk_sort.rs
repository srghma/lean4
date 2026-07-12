use leanh_l1::{
    datatypes::LeanObject,
    emitted::{
        lean_alloc_ctor::lean_alloc_ctor, lean_ctor_set::lean_ctor_set,
        lean_ctor_set_uint64::lean_ctor_set_uint64,
    },
};

use crate::r#priv::lean_expr_mk_data::lean_expr_mk_data;
use crate::todo_import_from_lean::lean_expr_tag::LeanExprTag;
use crate::todo_import_from_lean::{
    lean_level_has_mvar::lean_level_has_mvar, lean_level_has_param::lean_level_has_param,
    lean_level_hash::lean_level_hash,
};

const EXPR_SORT_FIELDS: u32 = 1;
const EXPR_SORT_SCALAR_SIZE: u32 = core::mem::size_of::<u64>() as u32;
const EXPR_SORT_HASH_SEED: u64 = 11;

#[inline]
pub unsafe fn lean_expr_mk_sort(level: *mut LeanObject) -> *mut LeanObject {
    let hash = leanh_l1::r#priv::lean_uint64_mix_hash::lean_uint64_mix_hash(
        EXPR_SORT_HASH_SEED,
        lean_level_hash(level) as u64,
    );
    let data = lean_expr_mk_data(
        hash,
        leanh_l1::emitted::lean_unsigned_to_nat::lean_unsigned_to_nat(0),
        0,
        false,
        false,
        lean_level_has_mvar(level),
        lean_level_has_param(level),
    );
    let expr = lean_alloc_ctor(
        LeanExprTag::Sort as u32,
        EXPR_SORT_FIELDS,
        EXPR_SORT_SCALAR_SIZE,
    );
    lean_ctor_set(expr, 0, level);
    lean_ctor_set_uint64(expr, core::mem::size_of::<*mut LeanObject>(), data);
    expr
}
