use runtime::leanh_extra::*;
// Generated stub file for Lean FFI imports
// Source: src/Init/Data/String/Basic.lean

pub fn lean_string_validate_utf8(_: *mut LeanObject) -> u8 {
    1
}

pub unsafe fn lean_string_data(s: *mut LeanObject) -> *mut LeanObject {
    unsafe { (*(s as *mut LeanStringObject<0>)).m_data.as_mut_ptr() as *mut LeanObject }
}

pub unsafe fn lean_string_dec_lt(a: *mut LeanObject, b: *mut LeanObject) -> u8 {
    unsafe {
        let a_ref = &*(a as *mut LeanStringObject<0>);
        let b_ref = &*(b as *mut LeanStringObject<0>);
        let a_size = a_ref.m_size.saturating_sub(1);
        let b_size = b_ref.m_size.saturating_sub(1);
        (core::slice::from_raw_parts(a_ref.m_data.as_ptr(), a_size)
            < core::slice::from_raw_parts(b_ref.m_data.as_ptr(), b_size)) as u8
    }
}

pub unsafe fn lean_string_is_valid_pos(s: *mut LeanObject, pos: *mut LeanObject) -> u8 {
    let pos = unsafe { lean_unbox(pos) };
    let size = unsafe { (*(s as *mut LeanStringObject<0>)).m_size.saturating_sub(1) };
    (pos <= size) as u8
}

// moved lean_string_utf8_extract to ffi/common/lean_string_utf8_extract__01__6a944aaa.rs
// original source: Init/Data/String/Basic.rs:30-45

pub unsafe fn lean_string_utf8_get_fast(s: *mut LeanObject, pos: *mut LeanObject) -> u32 {
    let pos = unsafe { lean_unbox(pos) };
    unsafe {
        (*(s as *mut LeanStringObject<0>))
            .m_data
            .as_ptr()
            .add(pos)
            .read() as u32
    }
}

pub unsafe fn lean_string_utf8_next_fast(
    _: *mut LeanObject,
    pos: *mut LeanObject,
) -> *mut LeanObject {
    unsafe { lean_box(lean_unbox(pos) + 1) }
}

// moved lean_string_utf8_get to ffi/common/lean_string_utf8_get__01__c0890e0e.rs
// original source: Init/Data/String/Basic.rs:51-53

pub unsafe fn lean_string_utf8_get_opt(
    s: *mut LeanObject,
    pos: *mut LeanObject,
) -> *mut LeanObject {
    unsafe { lean_box(lean_string_utf8_get_fast(s, pos) as usize) }
}

pub unsafe fn lean_string_utf8_get_bang(s: *mut LeanObject, pos: *mut LeanObject) -> u32 {
    unsafe { lean_string_utf8_get_fast(s, pos) }
}

// moved lean_string_utf8_next to ffi/common/lean_string_utf8_next__01__32c449db.rs
// original source: Init/Data/String/Basic.rs:65-67

pub unsafe fn lean_string_utf8_prev(_: *mut LeanObject, pos: *mut LeanObject) -> *mut LeanObject {
    unsafe { lean_box(lean_unbox(pos).saturating_sub(1)) }
}

// moved lean_string_utf8_at_end to ffi/common/lean_string_utf8_at_end__01__d435a2c6.rs
// original source: Init/Data/String/Basic.rs:88-92
