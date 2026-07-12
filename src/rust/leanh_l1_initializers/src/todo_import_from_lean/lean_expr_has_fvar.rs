use leanh_l1::datatypes::LeanObject;

use crate::todo_import_from_lean::expr_data::expr_data;

const EXPR_HAS_FVAR_SHIFT: u32 = 40;

#[inline]
pub unsafe fn lean_expr_has_fvar(e: *const LeanObject) -> bool {
    ((expr_data(e) >> EXPR_HAS_FVAR_SHIFT) & 1) != 0
}
