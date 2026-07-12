use leanh_l1::{
    datatypes::LeanObject,
    emitted::{
        lean_alloc_ctor::lean_alloc_ctor, lean_ctor_set::lean_ctor_set,
        lean_ctor_set_uint64::lean_ctor_set_uint64, lean_unbox::lean_unbox,
        lean_unsigned_to_nat::lean_unsigned_to_nat,
    },
    runtime_object_nat_int::lean_nat_add,
};

use crate::r#priv::lean_expr_mk_data::lean_expr_mk_data;
use crate::todo_import_from_lean::lean_expr_tag::LeanExprTag;

const EXPR_BVAR_FIELDS: u32 = 1;
const EXPR_BVAR_SCALAR_SIZE: u32 = core::mem::size_of::<u64>() as u32;
const EXPR_BVAR_HASH_SEED: u64 = 7;

#[inline]
pub unsafe fn lean_expr_mk_bvar(idx: *mut LeanObject) -> *mut LeanObject {
    let idx_hash = lean_unbox(idx) as u64;
    let hash =
        leanh_l1::r#priv::lean_uint64_mix_hash::lean_uint64_mix_hash(EXPR_BVAR_HASH_SEED, idx_hash);
    let data = lean_expr_mk_data(
        hash,
        lean_nat_add(idx, lean_unsigned_to_nat(1)),
        0,
        false,
        false,
        false,
        false,
    );
    let expr = lean_alloc_ctor(
        LeanExprTag::BVar as u32,
        EXPR_BVAR_FIELDS,
        EXPR_BVAR_SCALAR_SIZE,
    );
    lean_ctor_set(expr, 0, idx);
    lean_ctor_set_uint64(expr, core::mem::size_of::<*mut LeanObject>(), data);
    expr
}
