use crate::{datatypes::LeanObject, emitted::lean_inc_ref_n::lean_inc_ref_n};

#[inline]
pub unsafe fn lean_inc_ref(obj: *const LeanObject) {
    unsafe { lean_inc_ref_n(obj, 1) };
}
