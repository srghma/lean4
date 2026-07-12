use std::ffi::c_uint;

use leanh_l1::datatypes::LeanScalarArray;

pub fn lean_alloc_sarray_would_overflow(elem_size: c_uint, capacity: usize) -> bool {
    match (elem_size as usize).checked_mul(capacity) {
        None => true,
        Some(bytes) => core::mem::size_of::<LeanScalarArray<0>>()
            .checked_add(bytes)
            .is_none(),
    }
}
