use leanh_l1::datatypes::LeanObject;

use crate::todo_import_from_lean::{
    lean_expr_has_expr_mvar::lean_expr_has_expr_mvar,
    lean_expr_has_level_mvar::lean_expr_has_level_mvar,
};

#[inline]
pub unsafe fn lean_expr_has_mvar(e: *const LeanObject) -> bool {
    lean_expr_has_expr_mvar(e) || lean_expr_has_level_mvar(e)
}
