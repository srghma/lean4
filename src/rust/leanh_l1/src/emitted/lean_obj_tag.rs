use crate::{datatypes::LeanObject, r#priv::lean_ptr_tag::lean_ptr_tag};

#[inline]
pub unsafe fn lean_obj_tag(obj: *mut LeanObject) -> u8 {
    // unsafe {
    //     if lean_is_scalar_bool(obj) {
    //         lean_unbox(obj) as u8
    //     } else {
    lean_ptr_tag(obj)
    //     }
    // }
}
