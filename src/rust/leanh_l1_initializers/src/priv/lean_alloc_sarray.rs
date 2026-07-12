use std::ffi::c_uint;

use leanh_l1::{
    datatypes::{LeanObject, LeanScalarArray, LEAN_SCALAR_ARRAY_TAG},
    r#priv::lean_alloc_object::lean_alloc_object,
};

pub unsafe fn lean_alloc_sarray(
    elem_size: c_uint,
    size: usize,
    capacity: usize,
) -> *mut LeanObject {
    let byte_size = core::mem::size_of::<LeanScalarArray<0>>()
        .checked_add(
            (elem_size as usize)
                .checked_mul(capacity)
                .expect("sarray allocation overflow"),
        )
        .expect("sarray allocation overflow");
    let obj = lean_alloc_object(byte_size) as *mut LeanScalarArray<0>;
    (*obj).m_header.rc = 1;
    (*obj).m_header.cs_size = 0;
    (*obj).m_header.other = elem_size as u8;
    (*obj).m_header.tag = LEAN_SCALAR_ARRAY_TAG;
    (*obj).m_size = size;
    (*obj).m_capacity = capacity;
    obj as *mut LeanObject
}
