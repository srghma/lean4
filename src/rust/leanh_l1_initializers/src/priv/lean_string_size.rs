use leanh_l1::{datatypes::LeanObject, r#priv::lean_to_string::lean_to_string};

pub unsafe fn lean_string_size(obj: *const LeanObject) -> usize {
    (*lean_to_string(obj)).m_size
}
