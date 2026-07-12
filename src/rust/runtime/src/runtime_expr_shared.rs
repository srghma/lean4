use crate::datatypes::LeanObject;
use crate::{lean_ctor_get_uint8, lean_ctor_get_uint64};
use core::ffi::c_int;
pub use leanh_l1_initializers::todo_import_from_lean::lean_expr_mk_const::level_data;

// Expression kind tags shared by kernel/expr, kernel/abstract, print, etc.
pub const EXPR_BVAR: u8 = 0;
pub const EXPR_FVAR: u8 = 1;
pub const EXPR_MVAR: u8 = 2;
pub const EXPR_SORT: u8 = 3;
pub const EXPR_CONST: u8 = 4;
pub const EXPR_APP: u8 = 5;
pub const EXPR_LAMBDA: u8 = 6;
pub const EXPR_PI: u8 = 7;
pub const EXPR_LET: u8 = 8;
pub const EXPR_LIT: u8 = 9;
pub const EXPR_MDATA: u8 = 10;
pub const EXPR_PROJ: u8 = 11;

// Level kind tags shared by level helpers.
pub const LEVEL_SUCC: u8 = 1;
pub const LEVEL_MAX: u8 = 2;
pub const LEVEL_IMAX: u8 = 3;
pub const LEVEL_PARAM: u8 = 4;
pub const LEVEL_MVAR: u8 = 5;

// BinderInfo values stored in Lambda/Pi scalar area.
pub const BI_DEFAULT: u8 = 0;
pub const BI_IMPLICIT: u8 = 1;
pub const BI_STRICT_IMPLICIT: u8 = 2;
pub const BI_INST_IMPLICIT: u8 = 3;

// DataValue tags used by printing and ordering.
pub const DV_BOOL: u8 = 1;
pub const DV_NAME: u8 = 2;
pub const DV_NAT: u8 = 3;
pub const DV_STRING: u8 = 4;

// Except constructor tags and packed data-word masks.
pub const EXCEPT_ERROR_TAG: u32 = 0;
pub const EXCEPT_OK_TAG: u32 = 1;
pub const LEVEL_DATA_HAS_MVAR: u64 = 1 << 32;
pub const LEVEL_DATA_HAS_PARAM_BIT: u64 = 1u64 << 33;
pub const LEVEL_DATA_DEPTH_SHIFT: u32 = 40;
pub const EXPR_DATA_HAS_LEVEL_PARAM_BIT: u64 = 1u64 << 43;

// Socket address string buffer sizes shared by net helpers.
pub const INET_ADDRSTRLEN: usize = 16;
pub const INET6_ADDRSTRLEN: usize = 46;

// Object/file-layout constants shared by module/compact/process helpers.
pub const PTR_SIZE: usize = core::mem::size_of::<usize>();
pub const OLEAN_HEADER_SIZE: usize = 88;
pub const OLEAN_MARKER: &[u8; 5] = b"olean";
pub const OLEAN_VERSION_V2: u8 = 2;
pub const OLEAN_VERSION_V3: u8 = 3;
pub const OLEAN_FLAGS_GMP: u8 = 0b1;
pub const LEAN_MP_LIMB_SIZE: usize = 8;
pub const LEAN_MPZ_MP_D_OFFSET: usize = 16;
pub const LEAN_MPZ_MP_SIZE_OFFSET: usize = 12;
pub const LEAN_TASK_STATE_FINISHED: u8 = 2;
pub const UV_EALREADY: c_int = -3003;

#[derive(Clone, Debug)]
pub struct LibInfo {
    pub base_addr: usize,
    pub id: std::string::String,
}

/// Round `d` up to the next multiple of PTR_SIZE.
#[inline(always)]
pub fn align_up_ptr(d: usize) -> usize {
    let rem = d % PTR_SIZE;
    if rem != 0 { d + PTR_SIZE - rem } else { d }
}

// Expr.Data helpers.
#[inline(always)]
pub unsafe fn expr_data(e: *const LeanObject) -> u64 {
    let num_objs = (*e).other as usize;
    lean_ctor_get_uint64(e, num_objs * core::mem::size_of::<*mut LeanObject>())
}

/// bvarRange = bits [63:44] of Expr.Data.
#[inline(always)]
pub unsafe fn expr_bvar_range_data(data: u64) -> u64 {
    data >> EXPR_BVAR_RANGE_SHIFT
}

/// bvarRange = bits [63:44] of Expr.Data.
#[inline(always)]
pub unsafe fn expr_bvar_range(e: *const LeanObject) -> u64 {
    expr_bvar_range_data(expr_data(e))
}

/// BinderInfo byte for Lambda/Pi.
#[inline(always)]
pub unsafe fn expr_binder_info_raw(e: *const LeanObject) -> u8 {
    let num_objs = (*e).other as usize;
    lean_ctor_get_uint8(e, num_objs * 8 + 8)
}

/// nondep byte for Let.
#[inline(always)]
pub unsafe fn expr_let_nondep(e: *const LeanObject) -> bool {
    lean_ctor_get_uint8(e, 4 * 8 + 8) != 0
}
