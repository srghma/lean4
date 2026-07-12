use leanh_l1::datatypes::LeanObject;

use crate::todo_import_from_lean::expr_data::expr_data;

const EXPR_HAS_LEVEL_PARAM_SHIFT: u32 = 43;

#[inline]
pub unsafe fn lean_expr_has_level_param(e: *const LeanObject) -> bool {
    ((expr_data(e) >> EXPR_HAS_LEVEL_PARAM_SHIFT) & 1) != 0
}
