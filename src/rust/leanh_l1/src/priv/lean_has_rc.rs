use crate::datatypes::LeanObject;

#[inline(always)]
pub unsafe fn lean_has_rc(o: *mut LeanObject) -> bool {
    unsafe { (*o).rc != 0 }
}
