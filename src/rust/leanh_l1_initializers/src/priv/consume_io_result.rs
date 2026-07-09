use leanh_l1::{
    datatypes::LeanObject,
    emitted::{lean_dec::lean_dec, lean_inc::lean_inc, lean_io_result_is_ok::lean_io_result_is_ok},
    r#priv::lean_string_cstr::lean_string_cstr,
    todo_import_from_lean::io_error::lean_io_error_to_string,
};

use crate::r#priv::lean_io_result_get_error::lean_io_result_get_error;

pub(crate) unsafe fn consume_io_result(result: *mut LeanObject) {
    if lean_io_result_is_ok(result) {
        lean_dec(result);
    } else {
        let err = lean_io_result_get_error(result);
        lean_inc(err);
        lean_dec(result);
        let msg = lean_io_error_to_string(err);
        let text = core::ffi::CStr::from_ptr(lean_string_cstr(msg));

        let prefix = b"IO Error in lean_initialize: ";
        libc::write(2, prefix.as_ptr().cast(), prefix.len());
        let bytes = text.to_bytes();
        libc::write(2, bytes.as_ptr().cast(), bytes.len());
        libc::write(2, b"\n".as_ptr().cast(), 1);
    }
}
