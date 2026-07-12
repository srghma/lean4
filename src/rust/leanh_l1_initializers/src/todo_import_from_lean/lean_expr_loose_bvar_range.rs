use leanh_l1::datatypes::LeanObject;

use crate::todo_import_from_lean::expr_data::expr_data;

const EXPR_BVAR_RANGE_SHIFT: u32 = 44;

#[inline]
pub unsafe fn lean_expr_loose_bvar_range(e: *const LeanObject) -> u32 {
    (expr_data(e) >> EXPR_BVAR_RANGE_SHIFT) as u32
}
