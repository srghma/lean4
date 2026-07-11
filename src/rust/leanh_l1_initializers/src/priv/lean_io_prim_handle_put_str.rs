use leanh_l1::{
    datatypes::LeanObject,
    emitted::{lean_box::lean_box, lean_io_result_mk_ok::lean_io_result_mk_ok},
    r#priv::{lean_string_cstr::lean_string_cstr, lean_string_size::lean_string_size},
};

use crate::{
    r#priv::{
        lean_io_result_mk_error::lean_io_result_mk_error, lean_runtime_errno::lean_runtime_errno,
        lean_runtime_get_external_data::lean_runtime_get_external_data,
    },
    runtime_io_error::lean_decode_io_error::lean_decode_io_error,
};

pub unsafe fn lean_io_prim_handle_put_str(
    h: *const LeanObject,
    s: *const LeanObject,
) -> *mut LeanObject {
    let fp = lean_runtime_get_external_data(h).cast::<libc::FILE>();
    let n = lean_string_size(s) - 1;
    let m = libc::fwrite(lean_string_cstr(s).cast::<core::ffi::c_void>(), 1, n, fp);
    if m == n {
        lean_io_result_mk_ok(lean_box(0))
    } else {
        lean_io_result_mk_error(lean_decode_io_error(
            lean_runtime_errno(),
            core::ptr::null_mut(),
        ))
    }
}
