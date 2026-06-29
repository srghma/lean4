use runtime::leanh_extra::*;
// Generated stub file for Lean FFI imports
// Source: src/Init/Data/ByteArray/Basic.lean

pub unsafe fn lean_sarray_dec_eq(a: *mut LeanObject, b: *mut LeanObject) -> u8 {
    let a_ref = unsafe { &*(a as *mut LeanScalarArray<0>) };
    let b_ref = unsafe { &*(b as *mut LeanScalarArray<0>) };
    if a_ref.m_size != b_ref.m_size {
        return 0;
    }
    unsafe {
        (core::slice::from_raw_parts(a_ref.m_data.as_ptr(), a_ref.m_size)
            == core::slice::from_raw_parts(b_ref.m_data.as_ptr(), b_ref.m_size)) as u8
    }
}

// moved lean_sarray_size to ffi/common/lean_sarray_size__01__6b901b56.rs
// original source: Init/Data/ByteArray/Basic.rs:17-19

pub unsafe fn lean_byte_array_uget(array: *mut LeanObject, idx: usize) -> u8 {
    unsafe {
        (*(array as *mut LeanScalarArray<0>))
            .m_data
            .as_ptr()
            .add(idx)
            .read()
    }
}

pub unsafe fn lean_byte_array_get(array: *mut LeanObject, idx: *mut LeanObject) -> u8 {
    unsafe { lean_byte_array_uget(array, lean_unbox(idx)) }
}

pub unsafe fn lean_byte_array_fget(array: *mut LeanObject, idx: *mut LeanObject) -> u8 {
    unsafe { lean_byte_array_uget(array, lean_unbox(idx)) }
}

pub fn lean_byte_array_set(_: *mut LeanObject, _: *mut LeanObject, _: u8) -> *mut LeanObject {
    todo!("Stub for lean_byte_array_set");
}

pub fn lean_byte_array_fset(_: *mut LeanObject, _: *mut LeanObject, _: u8) -> *mut LeanObject {
    todo!("Stub for lean_byte_array_fset");
}

pub fn lean_byte_array_uset(_: *mut LeanObject, _: usize, _: u8) -> *mut LeanObject {
    todo!("Stub for lean_byte_array_uset");
}

pub fn lean_byte_array_hash(_: *mut LeanObject) -> u64 {
    todo!("Stub for lean_byte_array_hash");
}

pub fn lean_byte_array_copy_slice(
    _: *mut LeanObject,
    _: *mut LeanObject,
    _: *mut LeanObject,
    _: *mut LeanObject,
    _: *mut LeanObject,
    _: u8,
) -> *mut LeanObject {
    todo!("Stub for lean_byte_array_copy_slice");
}
