use crate::{
    datatypes::LeanObject, emitted::lean_dec_ref::lean_dec_ref,
    emitted::lean_is_scalar::lean_is_scalar,
};

#[inline]
pub unsafe fn lean_dec(obj: *mut LeanObject) {
    unsafe {
        if !lean_is_scalar(obj) {
            lean_dec_ref(obj);
        }
    }
}
