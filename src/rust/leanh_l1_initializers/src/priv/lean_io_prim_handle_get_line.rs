use std::ffi::c_char;

use leanh_l1::{
    datatypes::LeanObject, emitted::lean_io_result_mk_ok::lean_io_result_mk_ok,
    r#priv::lean_mk_string_from_bytes::lean_mk_string_from_bytes,
};

use crate::{
    r#priv::{
        lean_io_result_mk_error::lean_io_result_mk_error, lean_runtime_errno::lean_runtime_errno,
        lean_runtime_get_external_data::lean_runtime_get_external_data,
    },
    runtime_io_error::lean_decode_io_error::lean_decode_io_error,
};

pub unsafe fn lean_io_prim_handle_get_line(h: *const LeanObject) -> *mut LeanObject {
    let fp = lean_runtime_get_external_data(h).cast::<libc::FILE>();
    let mut result = Vec::<u8>::new();
    unsafe {
        loop {
            let c = libc::fgetc(fp);
            if c == libc::EOF {
                break;
            }
            result.push(c as u8);
            if c == b'\n' as i32 {
                break;
            }
        }
    }

    if libc::ferror(fp) != 0 {
        lean_io_result_mk_error(lean_decode_io_error(
            lean_runtime_errno(),
            core::ptr::null_mut(),
        ))
    } else {
        if libc::feof(fp) != 0 {
            libc::clearerr(fp);
        }
        let s = lean_mk_string_from_bytes(result.as_ptr() as *const c_char, result.len());
        lean_io_result_mk_ok(s)
    }
}
