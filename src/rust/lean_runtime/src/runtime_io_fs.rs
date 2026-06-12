/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

mod runtime_io_fs_impl {
    use super::*;
    use core::ffi::c_char;

    extern "C" {
        fn lean_mk_io_user_error(msg: *mut LeanObject) -> *mut LeanObject;
    }

    unsafe fn check_no_nuls(s: *mut LeanObject) -> Result<*const c_char, *mut LeanObject> {
        let cstr = super::lean_string_cstr(s);
        let len = super::lean_string_size(s);
        if libc::strlen(cstr) != len - 1 {
            Err(mk_embedded_nul_error(s))
        } else {
            Ok(cstr)
        }
    }

    unsafe fn io_error_from_str(msg: *const c_char) -> *mut LeanObject {
        lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(msg)))
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_chmod(filename: *mut LeanObject, mode: u32) -> *mut LeanObject {
        let fname = match check_no_nuls(filename) {
            Ok(s) => s,
            Err(e) => return e,
        };
        if libc::chmod(fname, mode as libc::mode_t) == 0 {
            lean_io_result_mk_ok(lean_box(0))
        } else {
            lean_io_result_mk_error(lean_decode_io_error(super::lean_runtime_errno(), filename))
        }
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_io_create_dir(p: *mut LeanObject) -> *mut LeanObject {
        let str_ = match check_no_nuls(p) {
            Ok(s) => s,
            Err(e) => return e,
        };
        #[cfg(target_os = "windows")]
        let ret = libc::mkdir(str_);
        #[cfg(not(target_os = "windows"))]
        let ret = libc::mkdir(str_, 0o777);
        if ret == 0 {
            lean_io_result_mk_ok(lean_box(0))
        } else {
            lean_io_result_mk_error(lean_decode_io_error(super::lean_runtime_errno(), p))
        }
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_io_remove_dir(p: *mut LeanObject) -> *mut LeanObject {
        let str_ = match check_no_nuls(p) {
            Ok(s) => s,
            Err(e) => return e,
        };
        if libc::rmdir(str_) == 0 {
            lean_io_result_mk_ok(lean_box(0))
        } else {
            lean_io_result_mk_error(lean_decode_io_error(super::lean_runtime_errno(), p))
        }
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_io_current_dir() -> *mut LeanObject {
        let mut buffer = [0u8; libc::PATH_MAX as usize];
        let cwd = libc::getcwd(buffer.as_mut_ptr().cast::<c_char>(), buffer.len());
        if !cwd.is_null() {
            lean_io_result_mk_ok(lean_mk_string(cwd))
        } else {
            io_error_from_str(c"failed to retrieve current working directory".as_ptr())
        }
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_io_app_path() -> *mut LeanObject {
        #[cfg(target_os = "windows")]
        {
            use core::ffi::c_void;
            extern "C" {
                fn GetModuleHandleA(module_name: *const c_char) -> *mut c_void;
                fn GetModuleFileNameA(h_module: *mut c_void, lp_filename: *mut c_char, n_size: u32) -> u32;
            }
            let mut path = [0u8; 32768usize]; // MAX_PATH
            let h = GetModuleHandleA(core::ptr::null());
            let n = GetModuleFileNameA(h, path.as_mut_ptr().cast(), path.len() as u32);
            if n == 0 {
                return io_error_from_str(c"failed to locate application".as_ptr());
            }
            // lowercase drive letter
            if n >= 2 && path[1] == b':' {
                path[0] = path[0].to_ascii_lowercase();
            }
            lean_io_result_mk_ok(lean_mk_string(path.as_ptr().cast()))
        }
        #[cfg(target_os = "macos")]
        {
            extern "C" {
                fn _NSGetExecutablePath(buf: *mut c_char, bufsize: *mut u32) -> core::ffi::c_int;
            }
            let mut buf1 = [0u8; libc::PATH_MAX as usize];
            let mut buf2 = [0u8; libc::PATH_MAX as usize];
            let mut bufsize = libc::PATH_MAX as u32;
            if _NSGetExecutablePath(buf1.as_mut_ptr().cast(), &mut bufsize) != 0 {
                return io_error_from_str(c"failed to locate application".as_ptr());
            }
            let resolved = libc::realpath(buf1.as_ptr().cast(), buf2.as_mut_ptr().cast());
            if resolved.is_null() {
                return io_error_from_str(c"failed to resolve symbolic links when locating application".as_ptr());
            }
            lean_io_result_mk_ok(lean_mk_string(buf2.as_ptr().cast()))
        }
        #[cfg(target_os = "emscripten")]
        {
            io_error_from_str(c"no Lean executable file exists in WASM outside of Node.js".as_ptr())
        }
        #[cfg(not(any(target_os = "windows", target_os = "macos", target_os = "emscripten")))]
        {
            // Linux and other Unix-like systems
            let mut dest = [0u8; libc::PATH_MAX as usize];
            let pid = libc::getpid();
            let mut path_buf = [0u8; 64];
            libc::snprintf(
                path_buf.as_mut_ptr().cast(),
                path_buf.len(),
                c"/proc/%d/exe".as_ptr(),
                pid as core::ffi::c_int,
            );
            let n = libc::readlink(
                path_buf.as_ptr().cast(),
                dest.as_mut_ptr().cast(),
                libc::PATH_MAX as usize - 1,
            );
            if n == -1 {
                io_error_from_str(c"failed to locate application".as_ptr())
            } else {
                lean_io_result_mk_ok(lean_mk_string(dest.as_ptr().cast()))
            }
        }
    }
}
