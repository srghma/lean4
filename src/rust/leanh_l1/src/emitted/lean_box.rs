use crate::datatypes::{LeanObject, Size};

#[inline]
pub unsafe fn lean_box(value: Size) -> *mut LeanObject {
    ((value << 1) | 1) as *mut LeanObject
}
