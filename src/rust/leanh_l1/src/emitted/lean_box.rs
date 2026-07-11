use crate::datatypes::LeanObject;

#[inline]
pub unsafe fn lean_box(value: usize) -> *mut LeanObject {
    ((value << 1) | 1) as *mut LeanObject
}
