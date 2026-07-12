use leanh_l1::{
    datatypes::LeanObject,
    emitted::{lean_is_scalar::lean_is_scalar, lean_unbox::lean_unbox},
    runtime_object_panic::lean_internal_panic_out_of_memory::lean_internal_panic,
};

const EXPR_APPROX_DEPTH_SHIFT: u32 = 32;
const EXPR_HAS_FVAR_SHIFT: u32 = 40;
const EXPR_HAS_EXPR_MVAR_SHIFT: u32 = 41;
const EXPR_HAS_LEVEL_MVAR_SHIFT: u32 = 42;
const EXPR_HAS_LEVEL_PARAM_SHIFT: u32 = 43;
pub const EXPR_BVAR_RANGE_SHIFT: u32 = 44;

pub unsafe fn lean_expr_mk_data(
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
    if !lean_is_scalar(bvar_range) {
        lean_internal_panic("too many bound variables");
    }
    let range = lean_unbox(bvar_range) as usize;
    if range > 1_048_575 {
        lean_internal_panic("too many bound variables");
    }
    let h = hash as u32 as u64;
    let r = range as u64;
    h | ((approx_depth as u64) << EXPR_APPROX_DEPTH_SHIFT)
        | ((has_fvar as u64) << EXPR_HAS_FVAR_SHIFT)
        | ((has_expr_mvar as u64) << EXPR_HAS_EXPR_MVAR_SHIFT)
        | ((has_level_mvar as u64) << EXPR_HAS_LEVEL_MVAR_SHIFT)
        | ((has_level_param as u64) << EXPR_HAS_LEVEL_PARAM_SHIFT)
        | (r << EXPR_BVAR_RANGE_SHIFT)
}
