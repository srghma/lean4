use crate::{datatypes::{LeanObject, LeanObjectTag}, r#priv::lean_ptr_tag::lean_ptr_tag};

#[inline]
pub unsafe fn lean_obj_tag(obj: *const LeanObject) -> LeanObjectTag {
    // unsafe {
    //     if lean_is_scalar(obj) {
    //         lean_unbox(obj) as u8
    //     } else {
    lean_ptr_tag(obj)
    //     }
    // }
}
