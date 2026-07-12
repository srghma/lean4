use leanh_l1::datatypes::LeanObject;

use crate::todo_import_from_lean::expr_data::expr_data;

#[inline]
pub unsafe fn lean_expr_hash(e: *const LeanObject) -> u64 {
    expr_data(e) as u32 as u64
}
