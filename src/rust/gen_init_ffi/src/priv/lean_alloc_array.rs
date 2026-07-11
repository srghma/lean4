use leanh_l1::datatypes::{
    LeanExternalObject, LeanObject, LeanScalarArray, LeanStringObject, Size,
};
use std::ffi::c_void;

// appended by move_rust_fn_to_gen_init_ffi.ts from ../lean4-rust/src/rust/lean_runtime/src/lib.rs:428-446

pub(crate) unsafe fn lean_alloc_array(size: usize, capacity: usize) -> *mut LeanObject {
    const LEAN_ARRAY_TAG: u8 = 246;
    let byte_size = core::mem::size_of::<LeanArrayObject>()
        .checked_add(
            core::mem::size_of::<*mut LeanObject>()
                .checked_mul(capacity)
                .expect("array allocation overflow"),
        )
        .expect("array allocation overflow");
    let obj = lean_alloc_object(byte_size) as *mut LeanArrayObject;
    (*obj).header.rc = 1;
    (*obj).header.cs_size = 0;
    (*obj).header.other = 0;
    (*obj).header.tag = LEAN_ARRAY_TAG;
    (*obj).size = size;
    (*obj).capacity = capacity;
    obj as *mut LeanObject
}

// appended by move_rust_fn_to_gen_init_ffi.ts from src/rust/runtime/src/base.rs:118-135

pub(crate) unsafe fn lean_alloc_array(size: usize, capacity: usize) -> *mut LeanObject {
    let byte_size = core::mem::size_of::<LeanArrayObject<0>>()
        .checked_add(
            core::mem::size_of::<*mut LeanObject>()
                .checked_mul(capacity)
                .expect("array allocation overflow"),
        )
        .expect("array allocation overflow");
    let obj = lean_alloc_object(byte_size) as *mut LeanArrayObject<0>;
    (*obj).m_header.rc = 1;
    (*obj).m_header.cs_size = 0;
    (*obj).m_header.other = 0;
    (*obj).m_header.tag = LEAN_ARRAY_TAG;
    (*obj).m_size = size;
    (*obj).m_capacity = capacity;
    obj as *mut LeanObject
}
