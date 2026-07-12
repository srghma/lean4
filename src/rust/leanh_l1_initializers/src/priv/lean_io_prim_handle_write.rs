use leanh_l1::{
    datatypes::LeanObject,
    emitted::{lean_box::lean_box, lean_io_result_mk_ok::lean_io_result_mk_ok},
};

use crate::{
    r#priv::{
        lean_errno::lean_errno, lean_get_external_data::lean_get_external_data,
        lean_io_result_mk_error::lean_io_result_mk_error, lean_sarray_cptr::lean_sarray_cptr,
        lean_sarray_size::lean_sarray_size,
    },
    runtime_io_error::lean_decode_io_error::lean_decode_io_error,
};

pub unsafe fn lean_io_prim_handle_write(
    h: *const LeanObject,
    buf: *const LeanObject,
) -> *mut LeanObject {
    let fp = lean_get_external_data(h).cast::<libc::FILE>();
    let n = lean_sarray_size(buf);
    let m = libc::fwrite(lean_sarray_cptr(buf).cast(), 1, n, fp);
    if m == n {
        lean_io_result_mk_ok(lean_box(0))
    } else {
        lean_io_result_mk_error(lean_decode_io_error(lean_errno(), core::ptr::null_mut()))
    }
}
