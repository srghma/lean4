use leanh_l1::{
    datatypes::LeanObject,
    emitted::{lean_ctor_get_uint8::lean_ctor_get_uint8, lean_obj_tag::lean_obj_tag},
};

#[inline]
pub unsafe fn lean_expr_binder_info(e: *const LeanObject) -> u8 {
    match lean_obj_tag(e) {
        6 | 7 => lean_ctor_get_uint8(e, (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32),
        _ => 0,
    }
}
