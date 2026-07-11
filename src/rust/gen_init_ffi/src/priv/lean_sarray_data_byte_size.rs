use leanh_l1::{
    datatypes::{LeanObject, LeanScalarArray},
    r#priv::lean_sarray_elem_size::lean_sarray_elem_size,
};

use crate::ffi::common::lean_sarray_size::lean_sarray_size;

#[inline]
pub unsafe fn lean_sarray_data_byte_size(obj: *const LeanObject) -> usize {
    unsafe {
        core::mem::size_of::<LeanScalarArray<0>>()
            + lean_sarray_elem_size(obj) * lean_sarray_size(obj)
    }
}
