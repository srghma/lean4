use crate::datatypes::{LeanObject, Size};

// Private implementation helpers for the hardcoded EmitRust surface.
// NOT IN EmitRust; here because it is used in `lean_alloc_closure`, `lean_apply_m`, `lean_ctor_release`, `lean_dec`, and 14 more EmitRust functions.

#[inline]
pub fn lean_is_scalar(obj: *const LeanObject) -> bool {
    (obj as Size & 1) == 1
}
