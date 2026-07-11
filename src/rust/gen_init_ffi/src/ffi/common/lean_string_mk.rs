// Generated duplicate-function bucket
// source: Init/Prelude.rs:279-282
// exact-text variant: no

use std::ffi::c_char;

use leanh_l1::{
    datatypes::LeanObject,
    emitted::{
        lean_ctor_get::lean_ctor_get, lean_dec::lean_dec,
        lean_mk_string_unchecked::lean_mk_string_unchecked, lean_unbox_uint32::lean_unbox_uint32,
    },
};

use crate::{
    ffi::Init::Prelude::lean_is_scalar,
    r#priv::lean_runtime_push_unicode_scalar::lean_runtime_push_unicode_scalar,
};

#[inline]
pub unsafe fn lean_string_mk(chars: *mut LeanObject) -> *mut LeanObject {
    let mut buf: Vec<u8> = Vec::new();
    let mut o = chars;
    let mut len: usize = 0;
    while !lean_is_scalar(o) {
        let cp = lean_unbox_uint32(lean_ctor_get(o, 0));
        let start = buf.len();
        buf.resize(start + 4, 0);
        let consumed =
            lean_runtime_push_unicode_scalar(buf.as_mut_ptr().add(start) as *mut c_char, cp)
                as usize;
        buf.truncate(start + consumed);
        o = lean_ctor_get(o, 1);
        len += 1;
    }
    lean_dec(chars);
    lean_mk_string_unchecked(buf.as_ptr() as *const c_char, buf.len(), len)
}
