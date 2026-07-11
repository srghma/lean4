use leanh_l1::{datatypes::LeanObject, r#priv::lean_sarray_capacity::lean_sarray_capacity};

use crate::r#priv::lean_copy_sarray::lean_copy_sarray;

pub unsafe fn lean_sarray_ensure_capacity(
    a: *mut LeanObject,
    min_cap: usize,
    exact: bool,
) -> *mut LeanObject {
    let cap = lean_sarray_capacity(a);
    if min_cap <= cap {
        a
    } else {
        lean_copy_sarray(a, if exact { min_cap } else { min_cap * 2 })
    }
}
