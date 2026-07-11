use crate::{datatypes::LeanObject, r#priv::lean_to_string::lean_to_string};

pub unsafe fn lean_string_size(obj: *const LeanObject) -> usize {
    unsafe { (*lean_to_string(obj)).m_size }
}
