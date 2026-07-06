/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

mod runtime_io_handle_impl {
    use crate::*;

    unsafe fn io_get_handle(hfile: *mut LeanObject) -> *mut libc::FILE {
        (*(hfile as *mut LeanExternalObject)).data.cast()
    }

    pub unsafe fn lean_io_prim_handle_lock(h: *mut LeanObject, exclusive: u8) -> *mut LeanObject {
        let fp = io_get_handle(h);
        let op = if exclusive != 0 {
            libc::LOCK_EX
        } else {
            libc::LOCK_SH
        };
        if libc::flock(libc::fileno(fp), op) == 0 {
            lean_io_result_mk_ok(lean_box(0))
        } else {
            lean_io_result_mk_error(lean_decode_io_error(
                super::lean_runtime_errno(),
                core::ptr::null_mut(),
            ))
        }
    }

    pub unsafe fn lean_io_prim_handle_try_lock(
        h: *mut LeanObject,
        exclusive: u8,
    ) -> *mut LeanObject {
        let fp = io_get_handle(h);
        let op = if exclusive != 0 {
            libc::LOCK_EX
        } else {
            libc::LOCK_SH
        };
        if libc::flock(libc::fileno(fp), op | libc::LOCK_NB) == 0 {
            lean_io_result_mk_ok(lean_box(1))
        } else if super::lean_runtime_errno() == libc::EWOULDBLOCK {
            lean_io_result_mk_ok(lean_box(0))
        } else {
            lean_io_result_mk_error(lean_decode_io_error(
                super::lean_runtime_errno(),
                core::ptr::null_mut(),
            ))
        }
    }

    pub unsafe fn lean_io_prim_handle_unlock(h: *mut LeanObject) -> *mut LeanObject {
        let fp = io_get_handle(h);
        if libc::flock(libc::fileno(fp), libc::LOCK_UN) == 0 {
            lean_io_result_mk_ok(lean_box(0))
        } else {
            lean_io_result_mk_error(lean_decode_io_error(
                super::lean_runtime_errno(),
                core::ptr::null_mut(),
            ))
        }
    }
}
