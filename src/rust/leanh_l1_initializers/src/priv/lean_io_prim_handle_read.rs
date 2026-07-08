use leanh_l1::{
    datatypes::{LeanObject, Size},
    emitted::{lean_dec::lean_dec, lean_io_result_mk_ok::lean_io_result_mk_ok},
};

use crate::{
    r#priv::{
        lean_alloc_sarray::lean_alloc_sarray,
        lean_alloc_sarray_would_overflow::lean_alloc_sarray_would_overflow,
        lean_io_result_mk_error::lean_io_result_mk_error, lean_runtime_errno::lean_runtime_errno,
        lean_runtime_get_external_data::lean_runtime_get_external_data,
        lean_sarray_cptr::lean_sarray_cptr, lean_sarray_set_size::lean_sarray_set_size,
    },
    runtime_io_error::lean_decode_io_error::lean_decode_io_error,
};

pub unsafe fn lean_io_prim_handle_read(h: *mut LeanObject, nbytes: Size) -> *mut LeanObject {
    let fp = lean_runtime_get_external_data(h).cast::<libc::FILE>();
    if lean_alloc_sarray_would_overflow(1, nbytes) {
        return lean_io_result_mk_error(lean_decode_io_error(libc::ENOMEM, core::ptr::null_mut()));
    }

    let res = lean_alloc_sarray(1, 0, nbytes);
    if nbytes == 0 {
        return lean_io_result_mk_ok(res);
    }

    let n = libc::fread(
        lean_sarray_cptr(res) as *mut core::ffi::c_void,
        1,
        nbytes,
        fp,
    );
    if n > 0 {
        lean_sarray_set_size(res, n);
        lean_io_result_mk_ok(res)
    } else if libc::feof(fp) != 0 {
        libc::clearerr(fp);
        lean_sarray_set_size(res, n);
        lean_io_result_mk_ok(res)
    } else {
        lean_dec(res);
        lean_io_result_mk_error(lean_decode_io_error(
            lean_runtime_errno(),
            core::ptr::null_mut(),
        ))
    }
}
