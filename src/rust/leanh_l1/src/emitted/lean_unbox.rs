use crate::datatypes::{LeanObject, Size};

#[inline]
pub unsafe fn lean_unbox(obj: *const LeanObject) -> usize {
    (obj as Size) >> 1
}
