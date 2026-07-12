use leanh_l1::datatypes::LeanObject;

use crate::todo_import_from_lean::expr_data::expr_data;

const EXPR_HAS_EXPR_MVAR_SHIFT: u32 = 41;

#[inline]
pub unsafe fn lean_expr_has_expr_mvar(e: *const LeanObject) -> bool {
    ((expr_data(e) >> EXPR_HAS_EXPR_MVAR_SHIFT) & 1) != 0
}
