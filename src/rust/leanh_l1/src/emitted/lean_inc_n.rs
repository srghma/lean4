use crate::{
    datatypes::LeanObject,
    emitted::{lean_inc_ref_n::lean_inc_ref_n, lean_is_scalar::lean_is_scalar},
};

// Mirrors origin-master-src/include/lean/lean.h:582 (`lean_inc_n`).
#[inline]
pub unsafe fn lean_inc_n(obj: *const LeanObject, n: usize) {
    if !lean_is_scalar(obj) {
        lean_inc_ref_n(obj, n);
    }
}
