// appended by move_rust_fn_to_leanh_l1_initializers.ts from ../lean4-rust/src/rust/lean_runtime/src/lib.rs:609-621

use leanh_l1::{
    datatypes::LeanObject,
    emitted::{lean_box::lean_box, lean_io_result_mk_ok::lean_io_result_mk_ok},
};

use crate::{
    r#priv::{
        lean_io_result_mk_error::lean_io_result_mk_error, lean_runtime_errno::lean_runtime_errno,
        lean_runtime_get_external_data::lean_runtime_get_external_data,
    },
    runtime_io_error::lean_decode_io_error::lean_decode_io_error,
};

pub unsafe fn lean_io_prim_handle_flush(h: *mut LeanObject) -> *mut LeanObject {
    let fp = lean_runtime_get_external_data(h).cast::<libc::FILE>();
    if libc::fflush(fp) == 0 {
        lean_io_result_mk_ok(lean_box(0))
    } else {
        lean_io_result_mk_error(lean_decode_io_error(
            lean_runtime_errno(),
            core::ptr::null_mut(),
        ))
    }
}
