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
use crate::todo_import_from_lean::lean_expr_tag::LeanExprTag;

const EXPR_PROJ_FIELDS: u32 = 3;
const EXPR_PROJ_SCALAR_SIZE: u32 = core::mem::size_of::<u64>() as u32;
const EXPR_PROJ_DATA_OFFSET: usize = EXPR_DATA_OFFSET + core::mem::size_of::<*mut LeanObject>();

#[inline]
pub unsafe fn lean_expr_mk_proj(
    type_name: *mut LeanObject,
    idx: *mut LeanObject,
    struct_: *mut LeanObject,
) -> *mut LeanObject {
    let child = expr_data(struct_);
    let approx_depth = (((child >> 32) as u8).saturating_add(1)) as u32;
    let hash = leanh_l1::r#priv::lean_uint64_mix_hash::lean_uint64_mix_hash(
        leanh_l1::emitted::lean_ctor_get_uint64::lean_ctor_get_uint64(
            type_name,
            (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
        ),
        leanh_l1::r#priv::lean_uint64_mix_hash::lean_uint64_mix_hash(
            leanh_l1::emitted::lean_unbox::lean_unbox(idx) as u64,
            child,
        ),
    );
    let packed = lean_expr_mk_data(
        hash,
        leanh_l1::emitted::lean_unsigned_to_nat::lean_unsigned_to_nat(0),
        approx_depth,
        ((child >> 40) & 1) != 0,
        ((child >> 41) & 1) != 0,
        ((child >> 42) & 1) != 0,
        ((child >> 43) & 1) != 0,
    );
    let result = lean_alloc_ctor(
        LeanExprTag::Proj as u32,
        EXPR_PROJ_FIELDS,
        EXPR_PROJ_SCALAR_SIZE,
    );
    lean_ctor_set(result, 0, type_name);
    lean_ctor_set(result, 1, idx);
    lean_ctor_set(result, 2, struct_);
    lean_ctor_set_uint64(result, EXPR_PROJ_DATA_OFFSET, packed);
    result
}
