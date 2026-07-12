use leanh_l1::{
    datatypes::{LeanObject, LeanScalarArray},
    r#priv::{lean_sarray_elem_size::lean_sarray_elem_size, lean_to_sarray::lean_to_sarray},
};

#[inline]
pub unsafe fn lean_sarray_byte_size(obj: *const LeanObject) -> usize {
    let obj = lean_to_sarray(obj);
    core::mem::size_of::<LeanScalarArray<0>>()
        + lean_sarray_elem_size(obj as *const LeanObject) * unsafe { (*obj).m_capacity }
}
