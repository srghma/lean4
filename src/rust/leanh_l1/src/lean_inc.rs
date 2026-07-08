use crate::{
    datatypes::LeanObject, lean_inc_ref::lean_inc_ref, lean_is_scalar::lean_is_scalar_bool,
};

#[inline]
pub fn lean_inc(obj: *mut LeanObject) {
    if !lean_is_scalar_bool(obj) {
        lean_inc_ref(obj);
    }
}
