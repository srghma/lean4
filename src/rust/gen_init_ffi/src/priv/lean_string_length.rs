use leanh_l1::{
    datatypes::LeanObject,
    r#priv::lean_to_string::lean_to_string,
};

#[inline]
pub unsafe fn lean_string_length(obj: *const LeanObject) -> usize {
    unsafe { (*lean_to_string(obj)).m_length }
}
