use crate::{
    datatypes::LeanObject, emitted::lean_is_scalar::lean_is_scalar_bool,
    r#priv::lean_free_object::lean_free_object,
};

// Mirrors origin-master-src/include/lean/lean.h:507-511 (`lean_del_object`).
#[inline]
pub unsafe fn lean_del_object(obj: *mut LeanObject) {
    if !lean_is_scalar_bool(obj) {
        lean_free_object(obj);
    }
}
