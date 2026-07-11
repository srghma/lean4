use crate::{datatypes::LeanObject, r#priv::lean_to_string::lean_to_string};

#[inline]
pub unsafe fn lean_string_capacity(obj: *const LeanObject) -> usize {
    unsafe { (*lean_to_string(obj)).m_capacity }
}
