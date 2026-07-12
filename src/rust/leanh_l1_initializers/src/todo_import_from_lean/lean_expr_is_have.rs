use crate::todo_import_from_lean::lean_expr_tag::LeanExprTag;
use leanh_l1::{
    datatypes::LeanObject,
    emitted::{lean_ctor_get_uint8::lean_ctor_get_uint8, lean_obj_tag::lean_obj_tag},
};

#[inline]
pub unsafe fn lean_expr_is_have(e: *const LeanObject) -> bool {
    if LeanExprTag::from_u8(lean_obj_tag(e)) == LeanExprTag::Let {
        lean_ctor_get_uint8(e, (core::mem::size_of::<*mut LeanObject>() * 4 + 8) as u32) != 0
    } else {
        false
    }
}
