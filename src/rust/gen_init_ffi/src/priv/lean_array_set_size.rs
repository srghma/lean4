use leanh_l1::{
    datatypes::{LeanArrayObject, LeanObject},
    emitted::lean_is_exclusive::lean_is_exclusive,
    r#priv::{lean_array_capacity::lean_array_capacity, lean_to_array::lean_to_array},
};

#[inline]
pub unsafe fn lean_array_set_size(obj: *mut LeanObject, size: usize) {
    debug_assert!(lean_is_exclusive(obj));
    debug_assert!(size <= lean_array_capacity(obj));
    unsafe {
        (*(lean_to_array(obj) as *mut LeanArrayObject<0>)).m_size = size;
    }
}
