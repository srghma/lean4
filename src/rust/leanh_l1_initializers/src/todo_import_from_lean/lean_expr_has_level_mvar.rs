use leanh_l1::datatypes::LeanObject;

use crate::todo_import_from_lean::expr_data::expr_data;

const EXPR_HAS_LEVEL_MVAR_SHIFT: u32 = 42;

#[inline]
pub unsafe fn lean_expr_has_level_mvar(e: *const LeanObject) -> bool {
    ((expr_data(e) >> EXPR_HAS_LEVEL_MVAR_SHIFT) & 1) != 0
}
