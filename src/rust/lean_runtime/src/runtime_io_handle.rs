/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

mod runtime_io_handle_impl {
    use super::*;

    unsafe fn io_get_handle(hfile: *mut LeanObject) -> *mut libc::FILE {
        (*(hfile as *mut LeanExternalObject)).data.cast()
    }

    #[cfg(not(target_os = "windows"))]
    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_io_prim_handle_lock(h: *mut LeanObject, exclusive: u8) -> *mut LeanObject {
        let fp = io_get_handle(h);
        let op = if exclusive != 0 { libc::LOCK_EX } else { libc::LOCK_SH };
        if libc::flock(libc::fileno(fp), op) == 0 {
            lean_io_result_mk_ok(lean_box(0))
        } else {
            lean_io_result_mk_error(lean_decode_io_error(super::lean_runtime_errno(), core::ptr::null_mut()))
        }
    }

    #[cfg(not(target_os = "windows"))]
    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_io_prim_handle_try_lock(h: *mut LeanObject, exclusive: u8) -> *mut LeanObject {
        let fp = io_get_handle(h);
        let op = if exclusive != 0 { libc::LOCK_EX } else { libc::LOCK_SH };
        if libc::flock(libc::fileno(fp), op | libc::LOCK_NB) == 0 {
            lean_io_result_mk_ok(lean_box(1))
        } else if super::lean_runtime_errno() == libc::EWOULDBLOCK {
            lean_io_result_mk_ok(lean_box(0))
        } else {
            lean_io_result_mk_error(lean_decode_io_error(super::lean_runtime_errno(), core::ptr::null_mut()))
        }
    }

    #[cfg(not(target_os = "windows"))]
    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_io_prim_handle_unlock(h: *mut LeanObject) -> *mut LeanObject {
        let fp = io_get_handle(h);
        if libc::flock(libc::fileno(fp), libc::LOCK_UN) == 0 {
            lean_io_result_mk_ok(lean_box(0))
        } else {
            lean_io_result_mk_error(lean_decode_io_error(super::lean_runtime_errno(), core::ptr::null_mut()))
        }
    }

    #[cfg(target_os = "windows")]
    mod windows {
        use super::*;

        type Bool = i32;
        type Dword = u32;
        type Handle = *mut core::ffi::c_void;

        #[repr(C)]
        struct Overlapped {
            internal: usize,
            internal_high: usize,
            offset: Dword,
            offset_high: Dword,
            event: Handle,
        }

        extern "system" {
            fn LockFileEx(
                file: Handle,
                flags: Dword,
                reserved: Dword,
                low_bytes_to_lock: Dword,
                high_bytes_to_lock: Dword,
                overlapped: *mut Overlapped,
            ) -> Bool;
            fn UnlockFileEx(
                file: Handle,
                reserved: Dword,
                low_bytes_to_unlock: Dword,
                high_bytes_to_unlock: Dword,
                overlapped: *mut Overlapped,
            ) -> Bool;
            fn GetLastError() -> Dword;
            fn _fileno(file: *mut libc::FILE) -> i32;
            fn _get_osfhandle(fd: i32) -> isize;
        }

        const LOCKFILE_EXCLUSIVE_LOCK: Dword = 0x00000002;
        const LOCKFILE_FAIL_IMMEDIATELY: Dword = 0x00000001;
        const ERROR_LOCK_VIOLATION: Dword = 33;
        const ERROR_NOT_LOCKED: Dword = 158;
        const MAXDWORD: Dword = u32::MAX;

        unsafe fn win_handle(fp: *mut libc::FILE) -> Handle {
            _get_osfhandle(_fileno(fp)) as Handle
        }

        unsafe fn last_error_result() -> *mut LeanObject {
            let mut buf = [0u8; 16];
            let mut n = GetLastError();
            let mut i = buf.len();
            if n == 0 {
                i -= 1;
                buf[i] = b'0';
            } else {
                while n != 0 {
                    i -= 1;
                    buf[i] = b'0' + (n % 10) as u8;
                    n /= 10;
                }
            }
            let msg = super::super::lean_mk_string_from_bytes(buf[i..].as_ptr().cast(), buf.len() - i);
            lean_io_result_mk_error(lean_mk_io_user_error(msg))
        }

        #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
        pub unsafe extern "C" fn lean_io_prim_handle_lock(h: *mut LeanObject, exclusive: u8) -> *mut LeanObject {
            let mut overlapped = Overlapped {
                internal: 0,
                internal_high: 0,
                offset: 0,
                offset_high: 0,
                event: core::ptr::null_mut(),
            };
            let flags = if exclusive != 0 { LOCKFILE_EXCLUSIVE_LOCK } else { 0 };
            if LockFileEx(win_handle(super::io_get_handle(h)), flags, 0, MAXDWORD, MAXDWORD, &mut overlapped) != 0 {
                lean_io_result_mk_ok(lean_box(0))
            } else {
                last_error_result()
            }
        }

        #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
        pub unsafe extern "C" fn lean_io_prim_handle_try_lock(h: *mut LeanObject, exclusive: u8) -> *mut LeanObject {
            let mut overlapped = Overlapped {
                internal: 0,
                internal_high: 0,
                offset: 0,
                offset_high: 0,
                event: core::ptr::null_mut(),
            };
            let mut flags = LOCKFILE_FAIL_IMMEDIATELY;
            if exclusive != 0 {
                flags |= LOCKFILE_EXCLUSIVE_LOCK;
            }
            if LockFileEx(win_handle(super::io_get_handle(h)), flags, 0, MAXDWORD, MAXDWORD, &mut overlapped) != 0 {
                lean_io_result_mk_ok(lean_box(1))
            } else if GetLastError() == ERROR_LOCK_VIOLATION {
                lean_io_result_mk_ok(lean_box(0))
            } else {
                last_error_result()
            }
        }

        #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
        pub unsafe extern "C" fn lean_io_prim_handle_unlock(h: *mut LeanObject) -> *mut LeanObject {
            let mut overlapped = Overlapped {
                internal: 0,
                internal_high: 0,
                offset: 0,
                offset_high: 0,
                event: core::ptr::null_mut(),
            };
            if UnlockFileEx(win_handle(super::io_get_handle(h)), 0, MAXDWORD, MAXDWORD, &mut overlapped) != 0 {
                lean_io_result_mk_ok(lean_box(0))
            } else if GetLastError() == ERROR_NOT_LOCKED {
                lean_io_result_mk_ok(lean_box(0))
            } else {
                last_error_result()
            }
        }
    }
}
