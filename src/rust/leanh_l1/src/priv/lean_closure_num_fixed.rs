use crate::{datatypes::LeanObject, r#priv::lean_to_closure::lean_to_closure};

// NOT IN EmitRust; here because it is used in `lean_alloc_closure`, `lean_apply_m`, `lean_closure_set`, `lean_ctor_release`, and 6 more EmitRust functions.
#[inline]
pub unsafe fn lean_closure_num_fixed(obj: *const LeanObject) -> usize {
    unsafe { (*lean_to_closure(obj)).m_num_fixed as usize }
}
