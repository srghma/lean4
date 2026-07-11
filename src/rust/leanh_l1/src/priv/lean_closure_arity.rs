use crate::{datatypes::LeanObject, r#priv::lean_to_closure::lean_to_closure};

#[inline]
pub unsafe fn lean_closure_arity(obj: *const LeanObject) -> u32 {
    (*lean_to_closure(obj)).m_arity as u32
}
