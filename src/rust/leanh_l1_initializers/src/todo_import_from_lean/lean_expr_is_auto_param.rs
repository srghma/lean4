use leanh_l1::datatypes::LeanObject;

use crate::kernel_type_checker::lean_name_eq::lean_name_eq;
use crate::todo_import_from_lean::expr_annotation_names::auto_param_name;
use crate::todo_import_from_lean::lean_expr_tag::LeanExprTag;

#[inline]
pub unsafe fn lean_expr_is_auto_param(e: *const LeanObject) -> bool {
    if LeanExprTag::from_u8(leanh_l1::emitted::lean_obj_tag::lean_obj_tag(e)) != LeanExprTag::App {
        return false;
    }
    let fn_ = leanh_l1::emitted::lean_ctor_get::lean_ctor_get(e, 0);
    if LeanExprTag::from_u8(leanh_l1::emitted::lean_obj_tag::lean_obj_tag(fn_)) != LeanExprTag::App
    {
        return false;
    }
    let head = leanh_l1::emitted::lean_ctor_get::lean_ctor_get(fn_, 0);
    if LeanExprTag::from_u8(leanh_l1::emitted::lean_obj_tag::lean_obj_tag(head))
        != LeanExprTag::Const
    {
        return false;
    }
    let name = leanh_l1::emitted::lean_ctor_get::lean_ctor_get(head, 0);
    lean_name_eq(name, auto_param_name())
}
