use leanh_l1::{
    datatypes::LeanObject,
    r#priv::lean_to_sarray::lean_to_sarray,
};

#[inline]
pub unsafe fn lean_sarray_size(obj: *const LeanObject) -> usize {
    unsafe { (*lean_to_sarray(obj)).m_size }
}
