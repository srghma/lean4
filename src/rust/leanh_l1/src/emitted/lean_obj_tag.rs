use crate::{datatypes::LeanObject, r#priv::lean_ptr_tag::lean_ptr_tag};

#[inline]
pub unsafe fn lean_obj_tag(obj: *const LeanObject) -> u8 {
    // unsafe {
    //     if lean_is_scalar(obj) {
    //         lean_unbox(obj) as u8
    //     } else {
    lean_ptr_tag(obj)
    //     }
    // }
}
