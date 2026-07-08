use crate::{
    datatypes::LeanObject, lean_dec_ref::lean_dec_ref, lean_is_scalar::lean_is_scalar_bool,
};

#[inline]
pub unsafe fn lean_dec(obj: *mut LeanObject) {
    unsafe {
        if !lean_is_scalar_bool(obj) {
            lean_dec_ref(obj);
        }
    }
}
