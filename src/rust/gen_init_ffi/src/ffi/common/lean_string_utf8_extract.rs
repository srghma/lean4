// Generated duplicate-function bucket
// source: Init/Data/String/Basic.rs:30-45
// exact-text variant: no

use std::ffi::CStr;

use leanh_l1::datatypes::LeanObject;
use leanh_l1::emitted::lean_is_scalar::lean_is_scalar;
use leanh_l1::emitted::{
    lean_mk_string_unchecked::lean_mk_string_unchecked, lean_unbox::lean_unbox,
};
use leanh_l1::r#priv::lean_string_cstr::lean_string_cstr;
use leanh_l1::r#priv::lean_string_size::lean_string_size;

use crate::r#priv::is_utf8_first_byte::is_utf8_first_byte;
use crate::r#priv::lean_mk_string_from_bytes_unchecked::lean_mk_string_from_bytes_unchecked;

static EMPTY_BYTES: &[u8; 1] = b"\0";
static EMPTY_CSTR: &CStr = unsafe { CStr::from_bytes_with_nul_unchecked(EMPTY_BYTES) };

pub unsafe fn lean_string_utf8_extract(
    s: *mut LeanObject,
    b0: *mut LeanObject,
    e0: *mut LeanObject,
) -> *mut LeanObject {
    let empty = || lean_mk_string_unchecked(EMPTY_CSTR.as_ptr(), 0, 0);
    if !lean_is_scalar(b0) || !lean_is_scalar(e0) {
        return s;
    }
    let b = lean_unbox(b0);
    let mut e = lean_unbox(e0);
    let str = lean_string_cstr(s) as *const u8;
    let sz = lean_string_size(s) - 1;
    if b >= e || b >= sz {
        return empty();
    }
    if !is_utf8_first_byte(*str.add(b)) {
        return empty();
    }
    if e > sz {
        e = sz;
    }
    if e < sz && !is_utf8_first_byte(*str.add(e)) {
        e = sz;
    }
    let new_sz = e - b;
    lean_mk_string_from_bytes_unchecked(lean_string_cstr(s).add(b), new_sz)
}
