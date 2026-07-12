use leanh_l1::{
    datatypes::LeanObject,
    emitted::{
        lean_alloc_ctor::lean_alloc_ctor, lean_ctor_set::lean_ctor_set,
        lean_ctor_set_uint64::lean_ctor_set_uint64,
    },
};

use crate::r#priv::lean_expr_mk_data::lean_expr_mk_data;
use crate::todo_import_from_lean::expr_data::expr_data;
use crate::todo_import_from_lean::lean_expr_mk_const::EXPR_DATA_OFFSET;

const EXPR_MDATA_TAG: u32 = 10;
const EXPR_MDATA_FIELDS: u32 = 2;
const EXPR_MDATA_SCALAR_SIZE: u32 = core::mem::size_of::<u64>() as u32;

#[inline]
pub unsafe fn lean_expr_mk_mdata(data: *mut LeanObject, expr: *mut LeanObject) -> *mut LeanObject {
    let child = expr_data(expr);
    let approx_depth = (((child >> 32) as u8).saturating_add(1)) as u32;
    let hash = leanh_l1::r#priv::lean_uint64_mix_hash::lean_uint64_mix_hash(10, child);
    let packed = lean_expr_mk_data(
        hash,
        leanh_l1::emitted::lean_unsigned_to_nat::lean_unsigned_to_nat(0),
        approx_depth,
        ((child >> 40) & 1) != 0,
        ((child >> 41) & 1) != 0,
        ((child >> 42) & 1) != 0,
        ((child >> 43) & 1) != 0,
    );
    let result = lean_alloc_ctor(EXPR_MDATA_TAG, EXPR_MDATA_FIELDS, EXPR_MDATA_SCALAR_SIZE);
    lean_ctor_set(result, 0, data);
    lean_ctor_set(result, 1, expr);
    lean_ctor_set_uint64(result, EXPR_DATA_OFFSET, packed);
    result
}
