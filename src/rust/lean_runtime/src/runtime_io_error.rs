/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

mod runtime_io_error_impl {
    use super::*;

    extern "C" {
        fn lean_mk_io_error_already_exists(errnum: u32, details: *mut LeanObject) -> *mut LeanObject;
        fn lean_mk_io_error_already_exists_file(
            name: *mut LeanObject,
            errnum: u32,
            details: *mut LeanObject,
        ) -> *mut LeanObject;
        fn lean_mk_io_error_hardware_fault(errnum: u32, details: *mut LeanObject) -> *mut LeanObject;
        fn lean_mk_io_error_illegal_operation(errnum: u32, details: *mut LeanObject) -> *mut LeanObject;
        fn lean_mk_io_error_inappropriate_type(errnum: u32, details: *mut LeanObject) -> *mut LeanObject;
        fn lean_mk_io_error_inappropriate_type_file(
            name: *mut LeanObject,
            errnum: u32,
            details: *mut LeanObject,
        ) -> *mut LeanObject;
        fn lean_mk_io_error_interrupted(
            name: *mut LeanObject,
            errnum: u32,
            details: *mut LeanObject,
        ) -> *mut LeanObject;
        fn lean_mk_io_error_no_file_or_directory(
            name: *mut LeanObject,
            errnum: u32,
            details: *mut LeanObject,
        ) -> *mut LeanObject;
        fn lean_mk_io_error_no_such_thing(errnum: u32, details: *mut LeanObject) -> *mut LeanObject;
        fn lean_mk_io_error_no_such_thing_file(
            name: *mut LeanObject,
            errnum: u32,
            details: *mut LeanObject,
        ) -> *mut LeanObject;
        fn lean_mk_io_error_other_error(errnum: u32, details: *mut LeanObject) -> *mut LeanObject;
        fn lean_mk_io_error_permission_denied(errnum: u32, details: *mut LeanObject) -> *mut LeanObject;
        fn lean_mk_io_error_permission_denied_file(
            name: *mut LeanObject,
            errnum: u32,
            details: *mut LeanObject,
        ) -> *mut LeanObject;
        fn lean_mk_io_error_protocol_error(errnum: u32, details: *mut LeanObject) -> *mut LeanObject;
        fn lean_mk_io_error_resource_busy(errnum: u32, details: *mut LeanObject) -> *mut LeanObject;
        fn lean_mk_io_error_resource_exhausted(errnum: u32, details: *mut LeanObject) -> *mut LeanObject;
        fn lean_mk_io_error_resource_exhausted_file(
            name: *mut LeanObject,
            errnum: u32,
            details: *mut LeanObject,
        ) -> *mut LeanObject;
        fn lean_mk_io_error_resource_vanished(errnum: u32, details: *mut LeanObject) -> *mut LeanObject;
        fn lean_mk_io_error_time_expired(errnum: u32, details: *mut LeanObject) -> *mut LeanObject;
        fn lean_mk_io_error_unsatisfied_constraints(errnum: u32, details: *mut LeanObject) -> *mut LeanObject;
        fn lean_mk_io_error_unsupported_operation(errnum: u32, details: *mut LeanObject) -> *mut LeanObject;
    }

    unsafe fn mk_details(errnum: c_int) -> *mut LeanObject {
        lean_mk_string(libc::strerror(errnum))
    }

    unsafe fn with_optional_file(
        fname: *mut LeanObject,
        errnum: c_int,
        details: *mut LeanObject,
        plain: unsafe extern "C" fn(u32, *mut LeanObject) -> *mut LeanObject,
        file: unsafe extern "C" fn(*mut LeanObject, u32, *mut LeanObject) -> *mut LeanObject,
    ) -> *mut LeanObject {
        if fname.is_null() {
            plain(errnum as u32, details)
        } else {
            lean_inc(fname);
            file(fname, errnum as u32, details)
        }
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_decode_io_error(errnum: c_int, fname: *mut LeanObject) -> *mut LeanObject {
        let details = mk_details(errnum);
        match errnum {
            libc::EINTR => {
                lean_inc(fname);
                lean_mk_io_error_interrupted(fname, errnum as u32, details)
            }
            libc::ELOOP | libc::ENAMETOOLONG | libc::EDESTADDRREQ
            | libc::EBADF | libc::EDOM | libc::EINVAL | libc::EILSEQ
            | libc::ENOEXEC | libc::ENOSTR | libc::ENOTCONN | libc::ENOTSOCK => {
                with_optional_file(
                    fname,
                    errnum,
                    details,
                    lean_mk_io_error_invalid_argument,
                    lean_mk_io_error_invalid_argument_file,
                )
            }
            libc::ENOENT => {
                lean_inc(fname);
                lean_mk_io_error_no_file_or_directory(fname, errnum as u32, details)
            }
            libc::EACCES | libc::EROFS | libc::ECONNABORTED | libc::EFBIG | libc::EPERM => {
                with_optional_file(
                    fname,
                    errnum,
                    details,
                    lean_mk_io_error_permission_denied,
                    lean_mk_io_error_permission_denied_file,
                )
            }
            libc::EMFILE | libc::ENFILE | libc::ENOSPC | libc::E2BIG | libc::EAGAIN
            | libc::EMLINK | libc::EMSGSIZE | libc::ENOBUFS | libc::ENOLCK | libc::ENOMEM
            | libc::ENOSR => {
                with_optional_file(
                    fname,
                    errnum,
                    details,
                    lean_mk_io_error_resource_exhausted,
                    lean_mk_io_error_resource_exhausted_file,
                )
            }
            libc::EISDIR | libc::EBADMSG | libc::ENOTDIR => {
                with_optional_file(
                    fname,
                    errnum,
                    details,
                    lean_mk_io_error_inappropriate_type,
                    lean_mk_io_error_inappropriate_type_file,
                )
            }
            libc::ENXIO | libc::EHOSTUNREACH | libc::ENETUNREACH | libc::ECHILD
            | libc::ECONNREFUSED | libc::ENODATA | libc::ENOMSG | libc::ESRCH => {
                with_optional_file(
                    fname,
                    errnum,
                    details,
                    lean_mk_io_error_no_such_thing,
                    lean_mk_io_error_no_such_thing_file,
                )
            }
            libc::EEXIST | libc::EINPROGRESS | libc::EISCONN => {
                with_optional_file(
                    fname,
                    errnum,
                    details,
                    lean_mk_io_error_already_exists,
                    lean_mk_io_error_already_exists_file,
                )
            }
            libc::EIO => lean_mk_io_error_hardware_fault(errnum as u32, details),
            libc::ENOTEMPTY => lean_mk_io_error_unsatisfied_constraints(errnum as u32, details),
            libc::ENOTTY => lean_mk_io_error_illegal_operation(errnum as u32, details),
            libc::ECONNRESET | libc::EIDRM | libc::ENETDOWN | libc::ENETRESET
            | libc::ENOLINK | libc::EPIPE => {
                lean_mk_io_error_resource_vanished(errnum as u32, details)
            }
            libc::EPROTO | libc::EPROTONOSUPPORT | libc::EPROTOTYPE => {
                lean_mk_io_error_protocol_error(errnum as u32, details)
            }
            libc::ETIME | libc::ETIMEDOUT => lean_mk_io_error_time_expired(errnum as u32, details),
            libc::EADDRINUSE | libc::EBUSY | libc::EDEADLK | libc::ETXTBSY => {
                lean_mk_io_error_resource_busy(errnum as u32, details)
            }
            libc::EADDRNOTAVAIL | libc::EAFNOSUPPORT | libc::ENODEV | libc::ENOPROTOOPT
            | libc::ENOSYS | libc::EOPNOTSUPP | libc::ERANGE | libc::ESPIPE | libc::EXDEV => {
                lean_mk_io_error_unsupported_operation(errnum as u32, details)
            }
            libc::EFAULT | _ => lean_mk_io_error_other_error(errnum as u32, details),
        }
    }
}
