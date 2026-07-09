use std::ffi::c_int;

use leanh_l1::{
    datatypes::LeanObject,
    emitted::{lean_inc::lean_inc, lean_mk_string::lean_mk_string},
};
use libuv_sys2::uv_strerror;

use crate::{
    runtime_io_error::{consts::*, lean_decode_io_error::with_optional_file},
    todo_import_from_lean::{
        lean_mk_io_error_already_exists::lean_mk_io_error_already_exists,
        lean_mk_io_error_already_exists_file::lean_mk_io_error_already_exists_file,
        lean_mk_io_error_hardware_fault::lean_mk_io_error_hardware_fault,
        lean_mk_io_error_illegal_operation::lean_mk_io_error_illegal_operation,
        lean_mk_io_error_inappropriate_type::lean_mk_io_error_inappropriate_type,
        lean_mk_io_error_inappropriate_type_file::lean_mk_io_error_inappropriate_type_file,
        lean_mk_io_error_interrupted::lean_mk_io_error_interrupted,
        lean_mk_io_error_invalid_argument::lean_mk_io_error_invalid_argument,
        lean_mk_io_error_invalid_argument_file::lean_mk_io_error_invalid_argument_file,
        lean_mk_io_error_no_file_or_directory::lean_mk_io_error_no_file_or_directory,
        lean_mk_io_error_no_such_thing::lean_mk_io_error_no_such_thing,
        lean_mk_io_error_no_such_thing_file::lean_mk_io_error_no_such_thing_file,
        lean_mk_io_error_other_error::lean_mk_io_error_other_error,
        lean_mk_io_error_permission_denied::lean_mk_io_error_permission_denied,
        lean_mk_io_error_permission_denied_file::lean_mk_io_error_permission_denied_file,
        lean_mk_io_error_protocol_error::lean_mk_io_error_protocol_error,
        lean_mk_io_error_resource_busy::lean_mk_io_error_resource_busy,
        lean_mk_io_error_resource_exhausted::lean_mk_io_error_resource_exhausted,
        lean_mk_io_error_resource_exhausted_file::lean_mk_io_error_resource_exhausted_file,
        lean_mk_io_error_resource_vanished::lean_mk_io_error_resource_vanished,
        lean_mk_io_error_time_expired::lean_mk_io_error_time_expired,
        lean_mk_io_error_unsatisfied_constraints::lean_mk_io_error_unsatisfied_constraints,
        lean_mk_io_error_unsupported_operation::lean_mk_io_error_unsupported_operation,
    },
};

unsafe fn mk_uv_details(errnum: c_int) -> *mut LeanObject {
    lean_mk_string(uv_strerror(errnum))
}
pub unsafe fn lean_decode_uv_error(errnum: c_int, fname: *mut LeanObject) -> *mut LeanObject {
    let details = mk_uv_details(errnum);
    match errnum {
        UV_EINTR => {
            lean_inc(fname);
            lean_mk_io_error_interrupted(fname, errnum as u32, details)
        }
        UV_ELOOP | UV_ENAMETOOLONG | UV_EDESTADDRREQ | UV_EBADF | UV_EINVAL | UV_EILSEQ
        | UV_ENOTCONN | UV_ENOTSOCK => with_optional_file(
            fname,
            errnum,
            details,
            lean_mk_io_error_invalid_argument,
            lean_mk_io_error_invalid_argument_file,
        ),
        UV_ENOENT => {
            lean_inc(fname);
            lean_mk_io_error_no_file_or_directory(fname, errnum as u32, details)
        }
        UV_EACCES | UV_EROFS | UV_ECONNABORTED | UV_EFBIG | UV_EPERM => with_optional_file(
            fname,
            errnum,
            details,
            lean_mk_io_error_permission_denied,
            lean_mk_io_error_permission_denied_file,
        ),
        UV_EMFILE | UV_ENFILE | UV_ENOSPC | UV_E2BIG | UV_EAGAIN | UV_EMLINK | UV_EMSGSIZE
        | UV_ENOBUFS | UV_ENOMEM => with_optional_file(
            fname,
            errnum,
            details,
            lean_mk_io_error_resource_exhausted,
            lean_mk_io_error_resource_exhausted_file,
        ),
        UV_EISDIR | UV_ENOTDIR => with_optional_file(
            fname,
            errnum,
            details,
            lean_mk_io_error_inappropriate_type,
            lean_mk_io_error_inappropriate_type_file,
        ),
        UV_ENXIO | UV_EHOSTUNREACH | UV_ENETUNREACH | UV_ECONNREFUSED | UV_ENODATA | UV_ESRCH => {
            with_optional_file(
                fname,
                errnum,
                details,
                lean_mk_io_error_no_such_thing,
                lean_mk_io_error_no_such_thing_file,
            )
        }
        UV_EEXIST | UV_EISCONN => with_optional_file(
            fname,
            errnum,
            details,
            lean_mk_io_error_already_exists,
            lean_mk_io_error_already_exists_file,
        ),
        UV_EIO => lean_mk_io_error_hardware_fault(errnum as u32, details),
        UV_ENOTEMPTY => lean_mk_io_error_unsatisfied_constraints(errnum as u32, details),
        UV_ENOTTY => lean_mk_io_error_illegal_operation(errnum as u32, details),
        UV_ECONNRESET | UV_ENETDOWN | UV_EPIPE => {
            lean_mk_io_error_resource_vanished(errnum as u32, details)
        }
        UV_EPROTO | UV_EPROTONOSUPPORT | UV_EPROTOTYPE => {
            lean_mk_io_error_protocol_error(errnum as u32, details)
        }
        UV_ETIMEDOUT => lean_mk_io_error_time_expired(errnum as u32, details),
        UV_EADDRINUSE | UV_EBUSY | UV_ETXTBSY => {
            lean_mk_io_error_resource_busy(errnum as u32, details)
        }
        UV_EADDRNOTAVAIL | UV_EAFNOSUPPORT | UV_ENODEV | UV_ENOPROTOOPT | UV_ENOSYS
        | UV_ENOTSUP | UV_ERANGE | UV_ESPIPE | UV_EXDEV => {
            lean_mk_io_error_unsupported_operation(errnum as u32, details)
        }
        _ => lean_mk_io_error_other_error(errnum as u32, details),
    }
}
