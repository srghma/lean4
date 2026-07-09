use crate::{
    datatypes::LeanObject, emitted::lean_inc_ref::lean_inc_ref,
    emitted::lean_is_scalar::lean_is_scalar,
};

#[inline]
pub unsafe fn lean_inc(obj: *const LeanObject) {
    if !lean_is_scalar(obj) {
        unsafe { lean_inc_ref(obj) };
    }
}
