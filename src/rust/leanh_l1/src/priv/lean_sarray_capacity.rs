use crate::{datatypes::LeanObject, r#priv::lean_to_sarray::lean_to_sarray};

#[inline]
pub unsafe fn lean_sarray_capacity(obj: *const LeanObject) -> usize {
    unsafe { (*lean_to_sarray(obj)).m_capacity }
}
