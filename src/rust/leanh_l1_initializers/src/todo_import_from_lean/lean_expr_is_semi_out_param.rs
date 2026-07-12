use leanh_l1::datatypes::LeanObject;

use crate::kernel_type_checker::lean_name_eq::lean_name_eq;
use crate::todo_import_from_lean::expr_annotation_names::semi_out_param_name;

#[inline]
pub unsafe fn lean_expr_is_semi_out_param(e: *const LeanObject) -> bool {
    if leanh_l1::emitted::lean_obj_tag::lean_obj_tag(e) != 5 {
        return false;
    }
    let fn_ = leanh_l1::emitted::lean_ctor_get::lean_ctor_get(e, 0);
    if leanh_l1::emitted::lean_obj_tag::lean_obj_tag(fn_) != 4 {
        return false;
    }
    let name = leanh_l1::emitted::lean_ctor_get::lean_ctor_get(fn_, 0);
    lean_name_eq(name, semi_out_param_name())
}
