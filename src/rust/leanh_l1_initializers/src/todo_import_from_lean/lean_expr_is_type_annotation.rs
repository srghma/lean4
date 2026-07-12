use leanh_l1::datatypes::LeanObject;

#[inline]
pub unsafe fn lean_expr_is_type_annotation(e: *const LeanObject) -> bool {
    crate::todo_import_from_lean::lean_expr_is_opt_param::lean_expr_is_opt_param(e)
        || crate::todo_import_from_lean::lean_expr_is_auto_param::lean_expr_is_auto_param(e)
        || crate::todo_import_from_lean::lean_is_out_param::lean_is_out_param(e)
        || crate::todo_import_from_lean::lean_expr_is_semi_out_param::lean_expr_is_semi_out_param(e)
}
