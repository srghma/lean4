use leanh_l1::{
    datatypes::LeanObject, emitted::lean_is_exclusive::lean_is_exclusive,
    r#priv::lean_sarray_capacity::lean_sarray_capacity,
};

use crate::r#priv::lean_copy_sarray::lean_copy_sarray;

pub unsafe fn lean_sarray_ensure_exclusive(a: *mut LeanObject) -> *mut LeanObject {
    if lean_is_exclusive(a) {
        a
    } else {
        lean_copy_sarray(a, lean_sarray_capacity(a))
    }
}
