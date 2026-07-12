use leanh_l1::datatypes::LeanObject;

#[inline]
pub unsafe fn lean_expr_consume_type_annotations(mut e: *mut LeanObject) -> *mut LeanObject {
    loop {
        if crate::todo_import_from_lean::lean_expr_is_opt_param::lean_expr_is_opt_param(e)
            || crate::todo_import_from_lean::lean_expr_is_auto_param::lean_expr_is_auto_param(e)
        {
            let app = leanh_l1::emitted::lean_ctor_get::lean_ctor_get(e, 1);
            leanh_l1::emitted::lean_dec_ref::lean_dec_ref(e);
            e = app;
            continue;
        }
        if crate::todo_import_from_lean::lean_is_out_param::lean_is_out_param(e)
            || crate::todo_import_from_lean::lean_expr_is_semi_out_param::lean_expr_is_semi_out_param(e)
        {
            let fn_ = leanh_l1::emitted::lean_ctor_get::lean_ctor_get(e, 0);
            let app = leanh_l1::emitted::lean_ctor_get::lean_ctor_get(fn_, 1);
            leanh_l1::emitted::lean_dec_ref::lean_dec_ref(fn_);
            leanh_l1::emitted::lean_dec_ref::lean_dec_ref(e);
            e = app;
            continue;
        }
        return e;
    }
}
