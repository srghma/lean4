/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

mod runtime_io_error_impl {
    use crate::base::{c_char, c_int, lean_inc, lean_mk_string, LeanObject};
    use libuv_sys2::uv_strerror;

    const UV_E2BIG: c_int = -libc::E2BIG;
    const UV_EACCES: c_int = -libc::EACCES;
    const UV_EADDRINUSE: c_int = -libc::EADDRINUSE;
    const UV_EADDRNOTAVAIL: c_int = -libc::EADDRNOTAVAIL;
    const UV_EAFNOSUPPORT: c_int = -libc::EAFNOSUPPORT;
    const UV_EAGAIN: c_int = -libc::EAGAIN;
    const UV_EBADF: c_int = -libc::EBADF;
    const UV_EBUSY: c_int = -libc::EBUSY;
    const UV_ECONNABORTED: c_int = -libc::ECONNABORTED;
    const UV_ECONNREFUSED: c_int = -libc::ECONNREFUSED;
    const UV_ECONNRESET: c_int = -libc::ECONNRESET;
    const UV_EDESTADDRREQ: c_int = -libc::EDESTADDRREQ;
    const UV_EEXIST: c_int = -libc::EEXIST;
    const UV_EFAULT: c_int = -libc::EFAULT;
    const UV_EFBIG: c_int = -libc::EFBIG;
    const UV_EHOSTUNREACH: c_int = -libc::EHOSTUNREACH;
    const UV_EILSEQ: c_int = -libc::EILSEQ;
    const UV_EINTR: c_int = -libc::EINTR;
    const UV_EINVAL: c_int = -libc::EINVAL;
    const UV_EIO: c_int = -libc::EIO;
    const UV_EISCONN: c_int = -libc::EISCONN;
    const UV_EISDIR: c_int = -libc::EISDIR;
    const UV_ELOOP: c_int = -libc::ELOOP;
    const UV_EMFILE: c_int = -libc::EMFILE;
    const UV_EMLINK: c_int = -libc::EMLINK;
    const UV_EMSGSIZE: c_int = -libc::EMSGSIZE;
    const UV_ENAMETOOLONG: c_int = -libc::ENAMETOOLONG;
    const UV_ENETDOWN: c_int = -libc::ENETDOWN;
    const UV_ENETUNREACH: c_int = -libc::ENETUNREACH;
    const UV_ENFILE: c_int = -libc::ENFILE;
    const UV_ENOBUFS: c_int = -libc::ENOBUFS;
    const UV_ENODATA: c_int = -libc::ENODATA;
    const UV_ENODEV: c_int = -libc::ENODEV;
    const UV_ENOENT: c_int = -libc::ENOENT;
    const UV_ENOMEM: c_int = -libc::ENOMEM;
    const UV_ENOPROTOOPT: c_int = -libc::ENOPROTOOPT;
    const UV_ENOSPC: c_int = -libc::ENOSPC;
    const UV_ENOSYS: c_int = -libc::ENOSYS;
    const UV_ENOTCONN: c_int = -libc::ENOTCONN;
    const UV_ENOTDIR: c_int = -libc::ENOTDIR;
    const UV_ENOTEMPTY: c_int = -libc::ENOTEMPTY;
    const UV_ENOTSOCK: c_int = -libc::ENOTSOCK;
    const UV_ENOTSUP: c_int = -libc::ENOTSUP;
    const UV_ENOTTY: c_int = -libc::ENOTTY;
    const UV_ENXIO: c_int = -libc::ENXIO;
    const UV_EPERM: c_int = -libc::EPERM;
    const UV_EPIPE: c_int = -libc::EPIPE;
    const UV_EPROTO: c_int = -libc::EPROTO;
    const UV_EPROTONOSUPPORT: c_int = -libc::EPROTONOSUPPORT;
    const UV_EPROTOTYPE: c_int = -libc::EPROTOTYPE;
    const UV_ERANGE: c_int = -libc::ERANGE;
    const UV_EROFS: c_int = -libc::EROFS;
    const UV_ESPIPE: c_int = -libc::ESPIPE;
    const UV_ESRCH: c_int = -libc::ESRCH;
    const UV_ETIMEDOUT: c_int = -libc::ETIMEDOUT;
    const UV_ETXTBSY: c_int = -libc::ETXTBSY;
    const UV_EXDEV: c_int = -libc::EXDEV;

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
            UV_ENXIO | UV_EHOSTUNREACH | UV_ENETUNREACH | UV_ECONNREFUSED | UV_ENODATA
            | UV_ESRCH => with_optional_file(
                fname,
                errnum,
                details,
                lean_mk_io_error_no_such_thing,
                lean_mk_io_error_no_such_thing_file,
            ),
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
            UV_EFAULT | _ => lean_mk_io_error_other_error(errnum as u32, details),
        }
    }
}
