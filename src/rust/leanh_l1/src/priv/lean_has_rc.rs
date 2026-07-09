use crate::datatypes::LeanObject;

#[inline(always)]
pub unsafe fn lean_has_rc(o: *const LeanObject) -> bool {
    unsafe { (*o).rc != 0 }
}
