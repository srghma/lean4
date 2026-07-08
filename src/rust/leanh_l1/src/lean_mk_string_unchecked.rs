// from runtime_object_string
use std::ffi::c_char;

use crate::{
    datatypes::{LEAN_STRING_TAG, LeanObject, LeanStringObject},
    r#priv::lean_alloc_object::lean_alloc_object,
};

// ════════════════════════════════════════════════════════════════════════════
// String constructors
// ════════════════════════════════════════════════════════════════════════════

// NOT IN EmitRust; here because it is used in `lean_mk_string`, `lean_mk_string_unchecked`.
pub(crate) unsafe fn lean_alloc_string(
    size: usize,
    capacity: usize,
    len: usize,
) -> *mut LeanObject {
    let byte_size = core::mem::size_of::<LeanStringObject<0>>()
        .checked_add(capacity)
        .expect("string allocation overflow");
    let obj = lean_alloc_object(byte_size) as *mut LeanStringObject<0>;
    (*obj).m_header.rc = 1;
    (*obj).m_header.cs_size = 0;
    (*obj).m_header.other = 0;
    (*obj).m_header.tag = LEAN_STRING_TAG;
    (*obj).m_size = size;
    (*obj).m_capacity = capacity;
    (*obj).m_length = len;
    obj as *mut LeanObject
}

// ── string buffer helpers ───────────────────────────────────────────────────

#[inline]
unsafe fn w_string_cstr(o: *mut LeanObject) -> *mut c_char {
    (o as *mut u8).add(size_of::<LeanStringObject<0>>()) as *mut c_char
}
pub unsafe fn lean_mk_string_unchecked(s: *const c_char, sz: usize, len: usize) -> *mut LeanObject {
    let rsz = sz + 1;
    let r = lean_alloc_string(rsz, rsz, len);
    core::ptr::copy_nonoverlapping(s, w_string_cstr(r), sz);
    *w_string_cstr(r).add(sz) = 0;
    r
}
