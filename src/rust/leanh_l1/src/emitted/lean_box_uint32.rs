use crate::{datatypes::LeanObject, emitted::lean_box::lean_box};

#[inline]
pub unsafe fn lean_box_uint32(value: u32) -> *mut LeanObject {
    unsafe { lean_box(value as usize) }
}
