use crate::{datatypes::LeanObject, r#priv::lean_is_sarray::lean_is_sarray};

#[inline]
pub unsafe fn lean_sarray_elem_size(obj: *const LeanObject) -> usize {
    assert!(unsafe { lean_is_sarray(obj) });
    unsafe { (*obj).other as usize }
}
