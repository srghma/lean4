use leanh_l1::{
    datatypes::LeanObject,
    emitted::{
        lean_alloc_ctor::lean_alloc_ctor, lean_ctor_set::lean_ctor_set,
        lean_ctor_set_uint64::lean_ctor_set_uint64,
    },
};

use crate::r#priv::lean_expr_mk_data::lean_expr_mk_data;

const EXPR_FVAR_TAG: u32 = 1;
const EXPR_FVAR_FIELDS: u32 = 1;
const EXPR_FVAR_SCALAR_SIZE: u32 = core::mem::size_of::<u64>() as u32;
const EXPR_FVAR_HASH_SEED: u64 = 13;

#[inline]
pub unsafe fn lean_expr_mk_fvar(fvar_id: *mut LeanObject) -> *mut LeanObject {
    let hash = leanh_l1::r#priv::lean_uint64_mix_hash::lean_uint64_mix_hash(
        EXPR_FVAR_HASH_SEED,
        leanh_l1::emitted::lean_ctor_get_uint64::lean_ctor_get_uint64(
            fvar_id,
            (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
        ),
    );
    let data = lean_expr_mk_data(
        hash,
        leanh_l1::emitted::lean_unsigned_to_nat::lean_unsigned_to_nat(0),
        0,
        true,
        false,
        false,
        false,
    );
    let expr = lean_alloc_ctor(EXPR_FVAR_TAG, EXPR_FVAR_FIELDS, EXPR_FVAR_SCALAR_SIZE);
    lean_ctor_set(expr, 0, fvar_id);
    lean_ctor_set_uint64(expr, core::mem::size_of::<*mut LeanObject>(), data);
    expr
}
