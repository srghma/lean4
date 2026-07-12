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

const EXPR_LET_NONDEP_OFFSET: usize =
    core::mem::size_of::<*mut LeanObject>() * 4 + core::mem::size_of::<u64>();
const EXPR_LET_DATA_OFFSET: usize = EXPR_DATA_OFFSET * 2;

const EXPR_LET_FIELDS: u32 = 4;
const EXPR_LET_SCALAR_SIZE: u32 = core::mem::size_of::<u64>() as u32;

#[inline]
pub unsafe fn lean_expr_mk_let(
    n: *mut LeanObject,
    t: *mut LeanObject,
    v: *mut LeanObject,
    b: *mut LeanObject,
    nondep: bool,
) -> *mut LeanObject {
    let data_expr = expr_data(b);
    let approx_depth = ((data_expr >> 32) as u8).saturating_add(1) as u32;
    let hash = leanh_l1::r#priv::lean_uint64_mix_hash::lean_uint64_mix_hash(
        8,
        leanh_l1::r#priv::lean_uint64_mix_hash::lean_uint64_mix_hash(
            leanh_l1::emitted::lean_ctor_get_uint64::lean_ctor_get_uint64(
                n,
                (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
            ),
            leanh_l1::r#priv::lean_uint64_mix_hash::lean_uint64_mix_hash(
                data_expr,
                leanh_l1::r#priv::lean_uint64_mix_hash::lean_uint64_mix_hash(
                    expr_data(t),
                    expr_data(v),
                ),
            ),
        ),
    );
    let data = lean_expr_mk_data(
        hash,
        leanh_l1::emitted::lean_unsigned_to_nat::lean_unsigned_to_nat(0),
        approx_depth,
        false,
        false,
        ((data_expr >> 42) & 1) != 0,
        ((data_expr >> 43) & 1) != 0,
    );
    let expr = lean_alloc_ctor(
        LeanExprTag::Let as u32,
        EXPR_LET_FIELDS,
        EXPR_LET_SCALAR_SIZE,
    );
    lean_ctor_set(expr, 0, n);
    lean_ctor_set(expr, 1, t);
    lean_ctor_set(expr, 2, v);
    lean_ctor_set(expr, 3, b);
    leanh_l1::emitted::lean_ctor_set_uint8::lean_ctor_set_uint8(
        expr,
        EXPR_LET_NONDEP_OFFSET as u32,
        nondep as u8,
    );
    lean_ctor_set_uint64(expr, EXPR_LET_DATA_OFFSET, data);
    expr
}
