use leanh_l1::{
    datatypes::LeanObject,
    emitted::{lean_ctor_get_uint8::lean_ctor_get_uint8, lean_obj_tag::lean_obj_tag},
};

#[inline]
pub unsafe fn lean_expr_is_have(e: *const LeanObject) -> bool {
    if lean_obj_tag(e) == 8 {
        lean_ctor_get_uint8(e, (core::mem::size_of::<*mut LeanObject>() * 4 + 8) as u32) != 0
    } else {
        false
    }
}
