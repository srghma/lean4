use leanh_l1::{
    datatypes::LeanObject,
    emitted::{
        lean_alloc_ctor::lean_alloc_ctor, lean_box::lean_box, lean_ctor_get::lean_ctor_get,
        lean_ctor_set::lean_ctor_set, lean_ctor_set_uint64::lean_ctor_set_uint64,
        lean_is_scalar::lean_is_scalar,
    },
    r#priv::lean_uint64_mix_hash::lean_uint64_mix_hash,
};

pub use crate::todo_import_from_lean::lean_level_depth::lean_level_depth;
pub use crate::todo_import_from_lean::lean_level_has_mvar::level_has_mvar;
pub use crate::todo_import_from_lean::lean_level_has_param::level_has_param;
pub use crate::todo_import_from_lean::lean_level_hash::level_hash;
pub use crate::todo_import_from_lean::level_data::level_data;

const EXPR_CONST_TAG: u32 = 4;
const EXPR_CONST_FIELDS: u32 = 2;
const EXPR_CONST_SCALAR_SIZE: u32 = core::mem::size_of::<u64>() as u32;
const EXPR_CONST_HASH_SEED: u64 = 5;
const EXPR_LEVELS_HASH_SEED: u64 = 7;
const NAME_HASH_OFFSET: usize = core::mem::size_of::<*mut LeanObject>() * 2;
pub const EXPR_DATA_OFFSET: usize = core::mem::size_of::<*mut LeanObject>() * 2;

#[inline]
unsafe fn lean_expr_mk_data(
    hash: u64,
    bvar_range: *mut LeanObject,
    mut approx_depth: u32,
    has_fvar: bool,
    has_expr_mvar: bool,
    has_level_mvar: bool,
    has_level_param: bool,
) -> u64 {
    if approx_depth > 255 {
        approx_depth = 255;
    }
    debug_assert!(lean_is_scalar(bvar_range));
    let range = ((bvar_range as usize) >> 1) as u64;
    (hash as u32 as u64)
        | ((approx_depth as u64) << 32)
        | ((has_fvar as u64) << 40)
        | ((has_expr_mvar as u64) << 41)
        | ((has_level_mvar as u64) << 42)
        | ((has_level_param as u64) << 43)
        | (range << 44)
}

#[inline]
unsafe fn fold_levels_hash(mut levels: *const LeanObject) -> u64 {
    let mut hash = EXPR_LEVELS_HASH_SEED;
    while !lean_is_scalar(levels) {
        hash = lean_uint64_mix_hash(hash, level_hash(lean_ctor_get(levels, 0)) as u64);
        levels = lean_ctor_get(levels, 1);
    }
    hash
}

#[inline]
unsafe fn any_level_mvar(mut levels: *const LeanObject) -> bool {
    while !lean_is_scalar(levels) {
        if level_has_mvar(lean_ctor_get(levels, 0)) {
            return true;
        }
        levels = lean_ctor_get(levels, 1);
    }
    false
}

#[inline]
unsafe fn any_level_param(mut levels: *const LeanObject) -> bool {
    while !lean_is_scalar(levels) {
        if level_has_param(lean_ctor_get(levels, 0)) {
            return true;
        }
        levels = lean_ctor_get(levels, 1);
    }
    false
}

#[inline]
unsafe fn name_hash(name: *const LeanObject) -> u64 {
    debug_assert!(!lean_is_scalar(name));
    leanh_l1::emitted::lean_ctor_get_uint64::lean_ctor_get_uint64(
        name,
        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
    )
}

pub unsafe fn lean_expr_mk_const(
    name: *mut LeanObject,
    levels: *mut LeanObject,
) -> *mut LeanObject {
    let hash = lean_uint64_mix_hash(
        EXPR_CONST_HASH_SEED,
        lean_uint64_mix_hash(name_hash(name), fold_levels_hash(levels)),
    );
    let data = lean_expr_mk_data(
        hash,
        lean_box(0),
        0,
        false,
        false,
        any_level_mvar(levels),
        any_level_param(levels),
    );

    let expr = lean_alloc_ctor(EXPR_CONST_TAG, EXPR_CONST_FIELDS, EXPR_CONST_SCALAR_SIZE);
    lean_ctor_set(expr, 0, name);
    lean_ctor_set(expr, 1, levels);
    lean_ctor_set_uint64(expr, EXPR_DATA_OFFSET as usize, data);
    expr
}
