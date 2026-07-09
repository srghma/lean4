use crate::datatypes::{LeanArrayObject, LeanObject};

// NOT IN EmitRust; here because it is used in `lean_alloc_closure`, `lean_apply_m`, `lean_ctor_release`, `lean_dec`, and 4 more EmitRust functions.
#[inline]
pub unsafe fn lean_array_size(obj: *const LeanObject) -> usize {
    let array = obj as *const LeanArrayObject<0>;
    (*array).m_size
}
