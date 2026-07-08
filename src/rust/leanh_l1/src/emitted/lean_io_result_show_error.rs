use std::ffi::CStr;

use crate::{
    datatypes::LeanObject,
    emitted::{
        lean_ctor_get::lean_ctor_get, lean_dec::lean_dec, lean_inc::lean_inc,
        lean_io_result_is_error::lean_io_result_is_error,
    },
    r#priv::lean_string_cstr::lean_string_cstr,
    todo_import_from_lean::io_error::lean_io_error_to_string,
};

// Mirrors origin-master-src/runtime/io.cpp:61-67 (`lean_io_result_show_error`).
pub unsafe fn lean_io_result_show_error(r: *mut LeanObject) {
    debug_assert!(lean_io_result_is_error(r));
    let err = lean_ctor_get(r, 0);
    lean_inc(err);
    let msg = lean_io_error_to_string(err);
    let text = CStr::from_ptr(lean_string_cstr(msg));
    eprintln!("uncaught exception: {}", text.to_string_lossy());
    lean_dec(msg);
}
