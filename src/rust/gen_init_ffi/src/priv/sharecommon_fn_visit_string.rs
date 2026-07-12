use leanh_l1::{
    datatypes::LeanObject,
    emitted::lean_alloc_string::lean_alloc_string,
    r#priv::{lean_string_cstr::lean_string_cstr, lean_string_size::lean_string_size},
};

use crate::r#priv::{
    lean_string_length::lean_string_length, sharecommon_data::ShareCommonFn,
    sharecommon_fn_save::sharecommon_fn_save,
};

// appended by move_rust_fn_to_gen_init_ffi.ts from src/rust/runtime/src/runtime_sharecommon.rs:75-84

pub(crate) unsafe fn sharecommon_fn_visit_string(this: &mut ShareCommonFn, a: *mut LeanObject) {
    let sz = lean_string_size(a);
    let len = lean_string_length(a);
    let new_a = lean_alloc_string(sz, sz, len);
    let dest = lean_string_cstr(new_a).cast_mut();
    let src = lean_string_cstr(a);
    libc::memcpy(dest.cast(), src.cast(), sz);
    sharecommon_fn_save(this, a, new_a);
}
