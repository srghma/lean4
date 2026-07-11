use leanh_l1::{
    datatypes::{LeanObject, LeanScalarArray},
    emitted::lean_is_exclusive::lean_is_exclusive,
    r#priv::{lean_sarray_capacity::lean_sarray_capacity, lean_to_sarray::lean_to_sarray},
};

#[inline]
pub unsafe fn lean_sarray_set_size(obj: *mut LeanObject, size: usize) {
    debug_assert!(lean_is_exclusive(obj));
    debug_assert!(size <= lean_sarray_capacity(obj));
    unsafe {
        (*(lean_to_sarray(obj) as *mut LeanScalarArray<0>)).m_size = size;
    }
}
