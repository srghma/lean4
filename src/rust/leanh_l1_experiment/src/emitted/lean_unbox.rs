use crate::datatypes::LeanObject;

#[inline]
pub unsafe fn lean_unbox(obj: *const LeanObject) -> usize {
    (obj as usize) >> 1
}
