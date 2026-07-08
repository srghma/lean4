use crate::{datatypes::LeanObject, lean_inc_ref_n::lean_inc_ref_n};

#[inline]
pub fn lean_inc_ref(obj: *mut LeanObject) {
    unsafe { lean_inc_ref_n(obj, 1) };
}
