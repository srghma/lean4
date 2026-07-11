use std::ffi::c_char;

use crate::{
    datatypes::LeanObject,
    emitted::lean_mk_string_unchecked::lean_mk_string_unchecked,
    r#priv::{
        lean_mk_string_lossy_recover::lean_mk_string_lossy_recover,
        lean_validate_utf8::lean_validate_utf8,
    },
};

pub unsafe fn lean_mk_string_from_bytes(s: *const c_char, sz: usize) -> *mut LeanObject {
    let mut pos: usize = 0;
    let mut i: usize = 0;
    if lean_validate_utf8(s as *const u8, sz, &mut pos, &mut i) {
        // is_utf8 in lean
        lean_mk_string_unchecked(s, pos, i)
    } else {
        lean_mk_string_lossy_recover(s, sz, pos, i)
    }
}
