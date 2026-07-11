use crate::{datatypes::LeanObject, r#priv::lean_to_array::lean_to_array};

#[inline]
pub unsafe fn lean_array_capacity(obj: *const LeanObject) -> usize {
    unsafe { (*lean_to_array(obj)).m_capacity }
}
