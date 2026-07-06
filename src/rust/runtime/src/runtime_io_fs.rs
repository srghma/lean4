/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

mod runtime_io_fs_impl {
    use super::*;
    use core::ffi::c_char;
    use std::ffi::{CStr, CString};

    extern "C" {
        fn lean_mk_io_user_error(msg: *mut LeanObject) -> *mut LeanObject;
        fn io_wrap_handle(hfile: *mut libc::FILE) -> *mut LeanObject;
        fn lean_mk_io_error_no_file_or_directory(
            fname: *mut LeanObject,
            errnum: u32,
            details: *mut LeanObject,
        ) -> *mut LeanObject;
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

    unsafe fn mk_file_not_found_error(fname: *mut LeanObject) -> *mut LeanObject {
        lean_inc(fname);
        let details = lean_mk_string(c"".as_ptr());
        lean_io_result_mk_error(lean_mk_io_error_no_file_or_directory(
            fname,
            libc::ENOENT as u32,
            details,
        ))
    }

    unsafe fn rename_error_detail(from: *const c_char, to: *const c_char) -> *mut LeanObject {
        let from = CStr::from_ptr(from).to_string_lossy();
        let to = CStr::from_ptr(to).to_string_lossy();
        let detail = CString::new(format!("{from} and/or {to}")).unwrap();
        lean_mk_string(detail.as_ptr())
    }

    unsafe fn ctor_set(obj: *mut LeanObject, index: u32, value: *mut LeanObject) {
        lean_runtime_ctor_set(obj, index, value);
    }

    unsafe fn ctor_set_uint32(obj: *mut LeanObject, offset: usize, value: u32) {
        (obj.add(1) as *mut u8)
            .add(offset)
            .cast::<u32>()
            .write(value);
    }

    unsafe fn system_time_to_obj(sec: i64, nsec: u32) -> *mut LeanObject {
        let o = lean_runtime_alloc_ctor(0, 1, core::mem::size_of::<u32>() as u32);
        ctor_set(o, 0, super::lean_int64_to_int_rust(sec));
        ctor_set_uint32(o, core::mem::size_of::<*mut LeanObject>(), nsec);
        o
    }

    #[cfg(any(target_os = "linux", target_os = "android"))]
    unsafe fn stat_timespecs(st: &libc::stat) -> ((i64, u32), (i64, u32)) {
        (
            (st.st_atime as i64, st.st_atime_nsec as u32),
            (st.st_mtime as i64, st.st_mtime_nsec as u32),
        )
    }

    #[cfg(any(target_os = "macos", target_os = "ios"))]
    unsafe fn stat_timespecs(st: &libc::stat) -> ((i64, u32), (i64, u32)) {
        (
            (
                st.st_atimespec.tv_sec as i64,
                st.st_atimespec.tv_nsec as u32,
            ),
            (
                st.st_mtimespec.tv_sec as i64,
                st.st_mtimespec.tv_nsec as u32,
            ),
        )
    }

    #[cfg(not(any(
        target_os = "linux",
        target_os = "android",
        target_os = "macos",
        target_os = "ios"
    )))]
    unsafe fn stat_timespecs(st: &libc::stat) -> ((i64, u32), (i64, u32)) {
        ((st.st_atime as i64, 0), (st.st_mtime as i64, 0))
    }

    unsafe fn metadata_core(st: &libc::stat) -> *mut LeanObject {
        let ((atime_sec, atime_nsec), (mtime_sec, mtime_nsec)) = stat_timespecs(st);
        let mdata = lean_runtime_alloc_ctor(
            0,
            2,
            (2 * core::mem::size_of::<u64>() + core::mem::size_of::<u8>()) as u32,
        );
        ctor_set(mdata, 0, system_time_to_obj(atime_sec, atime_nsec));
        ctor_set(mdata, 1, system_time_to_obj(mtime_sec, mtime_nsec));

        let ptr_size = core::mem::size_of::<*mut LeanObject>();
        lean_ctor_set_uint64(mdata, 2 * ptr_size, st.st_size as u64);
        lean_ctor_set_uint64(
            mdata,
            2 * ptr_size + core::mem::size_of::<u64>(),
            st.st_nlink as u64,
        );

        let mode = st.st_mode as libc::mode_t;
        let file_type = if mode & libc::S_IFMT == libc::S_IFDIR {
            0
        } else if mode & libc::S_IFMT == libc::S_IFREG {
            1
        } else if cfg!(not(target_os = "windows")) && mode & libc::S_IFMT == libc::S_IFLNK {
            2
        } else {
            3
        };
        lean_ctor_set_uint8(
            mdata,
            2 * ptr_size + 2 * core::mem::size_of::<u64>(),
            file_type,
        );
        lean_io_result_mk_ok(mdata)
    }

    unsafe fn tmpdir_template() -> Option<CString> {
        #[cfg(unix)]
        {
            use std::os::unix::ffi::OsStrExt;

            let mut bytes = std::env::temp_dir().as_os_str().as_bytes().to_vec();
            if bytes.is_empty() {
                return None;
            }
            if *bytes.last().unwrap() != b'/' {
                bytes.push(b'/');
            }
            bytes.extend_from_slice(b"tmp.XXXXXXXX");
            CString::new(bytes).ok()
        }
        #[cfg(not(unix))]
        {
            let mut path = std::env::temp_dir().to_string_lossy().into_owned();
            if path.is_empty() {
                return None;
            }
            if !path.ends_with('\\') && !path.ends_with('/') {
                path.push(std::path::MAIN_SEPARATOR);
            }
            path.push_str("tmp.XXXXXXXX");
            CString::new(path).ok()
        }
    }

    pub unsafe fn lean_chmod(filename: *mut LeanObject, mode: u32) -> *mut LeanObject {
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

    pub unsafe fn lean_io_create_dir(p: *mut LeanObject) -> *mut LeanObject {
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

    pub unsafe fn lean_io_remove_dir(p: *mut LeanObject) -> *mut LeanObject {
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

    pub unsafe fn lean_io_rename(from: *mut LeanObject, to: *mut LeanObject) -> *mut LeanObject {
        let from_str = match check_no_nuls(from) {
            Ok(s) => s,
            Err(e) => return e,
        };
        let to_str = match check_no_nuls(to) {
            Ok(s) => s,
            Err(e) => return e,
        };
        #[cfg(target_os = "windows")]
        let ok = {
            extern "system" {
                fn MoveFileExA(
                    existing_file_name: *const c_char,
                    new_file_name: *const c_char,
                    flags: u32,
                ) -> core::ffi::c_int;
            }
            const MOVEFILE_REPLACE_EXISTING: u32 = 0x1;
            MoveFileExA(from_str, to_str, MOVEFILE_REPLACE_EXISTING) != 0
        };
        #[cfg(not(target_os = "windows"))]
        let ok = libc::rename(from_str, to_str) == 0;

        if ok {
            lean_io_result_mk_ok(lean_box(0))
        } else {
            let details = rename_error_detail(from_str, to_str);
            lean_io_result_mk_error(lean_decode_io_error(super::lean_runtime_errno(), details))
        }
    }

    pub unsafe fn lean_io_hard_link(
        orig: *mut LeanObject,
        link: *mut LeanObject,
    ) -> *mut LeanObject {
        let orig_str = match check_no_nuls(orig) {
            Ok(s) => s,
            Err(e) => return e,
        };
        let link_str = match check_no_nuls(link) {
            Ok(s) => s,
            Err(e) => return e,
        };
        #[cfg(target_os = "windows")]
        let ret = {
            extern "system" {
                fn CreateHardLinkA(
                    file_name: *const c_char,
                    existing_file_name: *const c_char,
                    security_attributes: *mut core::ffi::c_void,
                ) -> core::ffi::c_int;
            }
            if CreateHardLinkA(link_str, orig_str, core::ptr::null_mut()) != 0 {
                0
            } else {
                -1
            }
        };
        #[cfg(not(target_os = "windows"))]
        let ret = libc::link(orig_str, link_str);

        if ret == 0 {
            lean_io_result_mk_ok(lean_box(0))
        } else {
            lean_io_result_mk_error(lean_decode_io_error(super::lean_runtime_errno(), orig))
        }
    }

    pub unsafe fn lean_io_remove_file(filename: *mut LeanObject) -> *mut LeanObject {
        let fname = match check_no_nuls(filename) {
            Ok(s) => s,
            Err(e) => return e,
        };
        #[cfg(target_os = "windows")]
        let ret = libc::remove(fname);
        #[cfg(not(target_os = "windows"))]
        let ret = libc::unlink(fname);

        if ret == 0 {
            lean_io_result_mk_ok(lean_box(0))
        } else {
            lean_io_result_mk_error(lean_decode_io_error(super::lean_runtime_errno(), filename))
        }
    }

    pub unsafe fn lean_io_realpath(filename: *mut LeanObject) -> *mut LeanObject {
        let fname = match check_no_nuls(filename) {
            Ok(s) => s,
            Err(e) => {
                lean_dec(filename);
                return e;
            }
        };

        #[cfg(target_os = "windows")]
        let result = {
            use std::path::Path;

            match CStr::from_ptr(fname)
                .to_str()
                .ok()
                .and_then(|path| std::fs::canonicalize(Path::new(path)).ok())
            {
                Some(path) => {
                    let mut path = path.to_string_lossy().into_owned();
                    if path.len() >= 2 && path.as_bytes()[1] == b':' {
                        let drive = path[..1].to_ascii_lowercase();
                        path.replace_range(..1, &drive);
                    }
                    let path = CString::new(path).unwrap();
                    lean_io_result_mk_ok(lean_mk_string(path.as_ptr()))
                }
                None => mk_file_not_found_error(filename),
            }
        };

        #[cfg(not(target_os = "windows"))]
        let result = {
            let mut buffer = [0u8; libc::PATH_MAX as usize];
            let resolved = libc::realpath(fname, buffer.as_mut_ptr().cast());
            if resolved.is_null() {
                mk_file_not_found_error(filename)
            } else {
                lean_io_result_mk_ok(lean_mk_string(buffer.as_ptr().cast()))
            }
        };

        lean_dec(filename);
        result
    }

    pub unsafe fn lean_io_read_dir(dirname: *mut LeanObject) -> *mut LeanObject {
        let dirname_ptr = match check_no_nuls(dirname) {
            Ok(s) => s,
            Err(e) => return e,
        };
        let dir = libc::opendir(dirname_ptr);
        if dir.is_null() {
            return lean_io_result_mk_error(lean_decode_io_error(
                super::lean_runtime_errno(),
                dirname,
            ));
        }

        let mut arr = lean_alloc_array(0, 0);
        loop {
            let entry = libc::readdir(dir);
            if entry.is_null() {
                break;
            }

            let name = (*entry).d_name.as_ptr();
            if libc::strcmp(name, c".".as_ptr()) == 0 || libc::strcmp(name, c"..".as_ptr()) == 0 {
                continue;
            }

            let lentry = lean_runtime_alloc_ctor(0, 2, 0);
            lean_inc(dirname);
            ctor_set(lentry, 0, dirname);
            ctor_set(lentry, 1, lean_mk_string(name));
            arr = lean_array_push(arr, lentry);
        }

        assert!(libc::closedir(dir) == 0);
        lean_io_result_mk_ok(arr)
    }

    pub unsafe fn lean_io_metadata(filename: *mut LeanObject) -> *mut LeanObject {
        let fname = match check_no_nuls(filename) {
            Ok(s) => s,
            Err(e) => return e,
        };
        let mut st = core::mem::MaybeUninit::<libc::stat>::uninit();
        if libc::stat(fname, st.as_mut_ptr()) == 0 {
            metadata_core(&st.assume_init())
        } else {
            lean_io_result_mk_error(lean_decode_io_error(super::lean_runtime_errno(), filename))
        }
    }

    pub unsafe fn lean_io_symlink_metadata(filename: *mut LeanObject) -> *mut LeanObject {
        let fname = match check_no_nuls(filename) {
            Ok(s) => s,
            Err(e) => return e,
        };
        let mut st = core::mem::MaybeUninit::<libc::stat>::uninit();
        #[cfg(target_os = "windows")]
        let ret = libc::stat(fname, st.as_mut_ptr());
        #[cfg(not(target_os = "windows"))]
        let ret = libc::lstat(fname, st.as_mut_ptr());
        if ret == 0 {
            metadata_core(&st.assume_init())
        } else {
            lean_io_result_mk_error(lean_decode_io_error(super::lean_runtime_errno(), filename))
        }
    }

    pub unsafe fn lean_io_create_tempdir(_w: *mut LeanObject) -> *mut LeanObject {
        let template = match tmpdir_template() {
            Some(template) => template,
            None => {
                return lean_io_result_mk_error(lean_decode_io_error(
                    libc::ENOENT,
                    lean_mk_string(c"".as_ptr()),
                ));
            }
        };
        let mut bytes = template.into_bytes_with_nul();
        let path = libc::mkdtemp(bytes.as_mut_ptr().cast());
        if path.is_null() {
            lean_io_result_mk_error(lean_decode_io_error(
                super::lean_runtime_errno(),
                core::ptr::null_mut(),
            ))
        } else {
            lean_io_result_mk_ok(lean_mk_string(path))
        }
    }

    pub unsafe fn lean_io_create_tempfile(_w: *mut LeanObject) -> *mut LeanObject {
        let template = match tmpdir_template() {
            Some(template) => template,
            None => {
                return lean_io_result_mk_error(lean_decode_io_error(
                    libc::ENOENT,
                    lean_mk_string(c"".as_ptr()),
                ));
            }
        };
        let mut bytes = template.into_bytes_with_nul();
        let fd = libc::mkstemp(bytes.as_mut_ptr().cast());
        if fd == -1 {
            return lean_io_result_mk_error(lean_decode_io_error(
                super::lean_runtime_errno(),
                core::ptr::null_mut(),
            ));
        }
        let handle = libc::fdopen(fd, c"r+".as_ptr());
        if handle.is_null() {
            let err = super::lean_runtime_errno();
            libc::close(fd);
            return lean_io_result_mk_error(lean_decode_io_error(err, core::ptr::null_mut()));
        }
        let pair = lean_runtime_alloc_ctor(0, 2, 0);
        ctor_set(pair, 0, io_wrap_handle(handle));
        ctor_set(pair, 1, lean_mk_string(bytes.as_ptr().cast()));
        lean_io_result_mk_ok(pair)
    }

    pub unsafe fn lean_io_get_random_bytes(nbytes: usize) -> *mut LeanObject {
        if nbytes == 0 {
            return lean_io_result_mk_ok(lean_alloc_sarray(1, 0, 0));
        }
        if lean_alloc_sarray_would_overflow(1, nbytes) {
            return lean_io_result_mk_error(lean_decode_io_error(
                libc::ENOMEM,
                core::ptr::null_mut(),
            ));
        }

        let res = lean_alloc_sarray(1, 0, nbytes);
        let mut remain = nbytes;
        let mut dst = lean_sarray_cptr(res).cast_mut();

        #[cfg(not(target_os = "windows"))]
        {
            let random_path = c"/dev/urandom";
            let fd = libc::open(random_path.as_ptr(), libc::O_RDONLY | libc::O_CLOEXEC);
            if fd < 0 {
                lean_dec(res);
                let fname = lean_mk_string(random_path.as_ptr());
                return lean_io_result_mk_error(lean_decode_io_error(
                    super::lean_runtime_errno(),
                    fname,
                ));
            }

            while remain > 0 {
                #[cfg(target_os = "emscripten")]
                let read_size = remain.min(65536);
                #[cfg(not(target_os = "emscripten"))]
                let read_size = remain;

                let nread = libc::read(fd, dst.cast(), read_size);
                if nread < 0 {
                    if super::lean_runtime_errno() != libc::EINTR {
                        let err = super::lean_runtime_errno();
                        libc::close(fd);
                        lean_dec(res);
                        return lean_io_result_mk_error(lean_decode_io_error(
                            err,
                            core::ptr::null_mut(),
                        ));
                    }
                } else {
                    remain -= nread as usize;
                    dst = dst.add(nread as usize);
                }
            }
            libc::close(fd);
        }

        #[cfg(target_os = "windows")]
        {
            extern "system" {
                fn BCryptGenRandom(
                    algorithm: *mut core::ffi::c_void,
                    buffer: *mut u8,
                    count: u32,
                    flags: u32,
                ) -> i32;
            }
            const BCRYPT_USE_SYSTEM_PREFERRED_RNG: u32 = 0x00000002;

            while remain > 0 {
                let read_size = remain.min(u32::MAX as usize);
                let status = BCryptGenRandom(
                    core::ptr::null_mut(),
                    dst,
                    read_size as u32,
                    BCRYPT_USE_SYSTEM_PREFERRED_RNG,
                );
                if status < 0 {
                    lean_dec(res);
                    return io_error_from_str(c"BCryptGenRandom failed".as_ptr());
                }
                remain -= read_size;
                dst = dst.add(read_size);
            }
        }

        lean_sarray_set_size(res, nbytes);
        lean_io_result_mk_ok(res)
    }

    pub unsafe fn lean_io_current_dir() -> *mut LeanObject {
        let mut buffer = [0u8; libc::PATH_MAX as usize];
        let cwd = libc::getcwd(buffer.as_mut_ptr().cast::<c_char>(), buffer.len());
        if !cwd.is_null() {
            lean_io_result_mk_ok(lean_mk_string(cwd))
        } else {
            io_error_from_str(c"failed to retrieve current working directory".as_ptr())
        }
    }

    pub unsafe fn lean_io_app_path() -> *mut LeanObject {
        #[cfg(target_os = "windows")]
        {
            use core::ffi::c_void;
            extern "C" {
                fn GetModuleHandleA(module_name: *const c_char) -> *mut c_void;
                fn GetModuleFileNameA(
                    h_module: *mut c_void,
                    lp_filename: *mut c_char,
                    n_size: u32,
                ) -> u32;
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
                return io_error_from_str(
                    c"failed to resolve symbolic links when locating application".as_ptr(),
                );
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
