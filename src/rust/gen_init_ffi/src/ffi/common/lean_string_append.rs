// Generated duplicate-function bucket
// source: Init/Data/String/Bootstrap.rs:33-35
// source: Init/Data/String/Defs.rs:9-11
// exact-text variant: yes

use leanh_l1::datatypes::{LeanObject, LeanStringObject};
use leanh_l1::emitted::lean_dec_ref::lean_dec_ref;
use leanh_l1::emitted::lean_is_exclusive::lean_is_exclusive;
use leanh_l1::emitted::lean_mk_string_unchecked::{lean_alloc_string, w_string_cstr};
use leanh_l1::r#priv::lean_string_cstr::lean_string_cstr;
use leanh_l1::r#priv::lean_string_size::lean_string_size;

use super::lean_string_length::lean_string_length;
use crate::r#priv::mk_capacity::mk_capacity;
use crate::r#priv::string_ensure_capacity::string_ensure_capacity;

pub unsafe fn lean_string_append(s1: *mut LeanObject, s2: *mut LeanObject) -> *mut LeanObject {
    let sz1 = lean_string_size(s1);
    let sz2 = lean_string_size(s2);
    let len1 = lean_string_length(s1);
    let len2 = lean_string_length(s2);
    let new_len = len1 + len2;
    let new_sz = sz1 + sz2 - 1;
    let r;
    if !lean_is_exclusive(s1) {
        r = lean_alloc_string(new_sz, mk_capacity(new_sz), new_len);
        core::ptr::copy_nonoverlapping(lean_string_cstr(s1), w_string_cstr(r), sz1 - 1);
        lean_dec_ref(s1);
    } else {
        debug_assert!(s1 != s2);
        r = string_ensure_capacity(s1, sz2 - 1);
    }
    core::ptr::copy_nonoverlapping(lean_string_cstr(s2), w_string_cstr(r).add(sz1 - 1), sz2 - 1);
    (*(r as *mut LeanStringObject<0>)).m_size = new_sz;
    (*(r as *mut LeanStringObject<0>)).m_length = new_len;
    *w_string_cstr(r).add(new_sz - 1) = 0;
    r
}
