use leanh_l1::{
    datatypes::LeanObject,
    emitted::{
        lean_is_exclusive::lean_is_exclusive,
        lean_mk_string_unchecked::{lean_alloc_string, w_string_cstr},
    },
    r#priv::{
        lean_free_object::lean_free_object, lean_string_cstr::lean_string_cstr,
        lean_string_size::lean_string_size,
    },
};

use crate::{
    ffi::common::lean_string_length::lean_string_length,
    r#priv::lean_string_capacity::lean_string_capacity,
};

pub(crate) unsafe fn string_ensure_capacity(o: *mut LeanObject, extra: usize) -> *mut LeanObject {
    debug_assert!(lean_is_exclusive(o));
    let sz = lean_string_size(o);
    let cap = lean_string_capacity(o);
    if sz + extra > cap {
        let new_o = lean_alloc_string(sz, cap + sz + extra, lean_string_length(o));
        core::ptr::copy_nonoverlapping(lean_string_cstr(o), w_string_cstr(new_o), sz);
        lean_free_object(o);
        new_o
    } else {
        o
    }
}
