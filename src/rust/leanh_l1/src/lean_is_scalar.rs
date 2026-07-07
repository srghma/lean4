use crate::datatypes::{LeanObject, Size};

#[inline]
pub fn lean_is_scalar(obj: *mut LeanObject) -> u8 {
    ((obj as Size & 1) == 1) as u8
}

// Private implementation helpers for the hardcoded EmitRust surface.
// NOT IN EmitRust; here because it is used in `lean_alloc_closure`, `lean_apply_m`, `lean_ctor_release`, `lean_dec`, and 14 more EmitRust functions.
#[inline]
pub fn lean_is_scalar_bool(obj: *mut LeanObject) -> bool {
    // same as
    // (obj as Size) & 1 == 1
    lean_is_scalar(obj) != 0 // same as `== 1`
}
