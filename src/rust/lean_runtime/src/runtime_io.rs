// runtime_io.rs — port of runtime/io.cpp
//
// Platform-specific sections use cfg() guards.
// Functions that call into C++ object_ref/option_ref templates delegate to
// io_shims.cpp thin wrappers.
//
// Integration:
//   - add `include!("runtime_io.rs");` in lib.rs
//   - add io_shims.cpp to RUNTIME_OBJS in CMakeLists.txt
//   - remove io.cpp from RUNTIME_OBJS (or guard its lean_*-prefixed
//     extern "C" LEAN_EXPORT functions with #ifndef LEAN_RUST_IO)

mod runtime_io_impl {
    use super::*;
    use core::ffi::{c_char, c_int, c_uint, c_void};
    use core::ptr::{null, null_mut};
    #[cfg(not(target_os = "windows"))]
    use core::ptr;

    // -----------------------------------------------------------------------
    // C++ shims from io_shims.cpp
    // -----------------------------------------------------------------------
    extern "C" {
        // object_ref thread-local stream accessors
        #[link_name = "stdin"]
        static mut libc_stdin: *mut c_void;
        #[link_name = "stdout"]
        static mut libc_stdout: *mut c_void;
        #[link_name = "stderr"]
        static mut libc_stderr: *mut c_void;

        // io_wrap_handle / io_handle_external_class registration
        fn lean_io_wrap_handle_c(fp: *mut c_void) -> *mut LeanObject;
        fn lean_io_get_handle_c(hfile: *mut LeanObject) -> *mut libc_FILE;

        // io errors
        fn lean_decode_io_error_c(errnum: c_int, fname: *mut LeanObject) -> *mut LeanObject;
        fn lean_decode_uv_error_c(errnum: c_int, fname: *mut LeanObject) -> *mut LeanObject;
        fn lean_mk_embedded_nul_error_c(str: *mut LeanObject) -> *mut LeanObject;

        // stream_of_handle (Lean function implemented in Lean)
        fn lean_stream_of_handle(h: *mut LeanObject) -> *mut LeanObject;

        // option_ref helpers
        fn lean_io_option_get_or_block_c(o_opt: *mut LeanObject) -> *mut LeanObject;

        // task helpers (already in runtime_task.rs / object_shims.cpp)
        fn lean_io_as_task_core(act: *mut LeanObject, prio: usize) -> *mut LeanObject;
        fn lean_io_map_task_core(
            f: *mut LeanObject,
            t: *mut LeanObject,
            prio: usize,
            sync: u8,
        ) -> *mut LeanObject;
        fn lean_io_bind_task_core(
            t: *mut LeanObject,
            f: *mut LeanObject,
            prio: usize,
            sync: u8,
        ) -> *mut LeanObject;

        // uv stat
        #[link_name = "lean_io_shim_uv_stat"]
        fn lean_io_shim_uv_stat_cxx(
            path: *const c_char,
            out: *mut UvStatBuf,
        ) -> c_int;
        #[link_name = "lean_io_shim_uv_lstat"]
        fn lean_io_shim_uv_lstat_cxx(
            path: *const c_char,
            out: *mut UvStatBuf,
        ) -> c_int;
        #[link_name = "lean_io_shim_uv_link"]
        fn lean_io_shim_uv_link_cxx(
            orig: *const c_char,
            link: *const c_char,
        ) -> c_int;
        #[link_name = "lean_io_shim_uv_unlink"]
        fn lean_io_shim_uv_unlink_cxx(path: *const c_char) -> c_int;
        fn lean_io_shim_uv_strerror(errnum: c_int) -> *const c_char;
        #[link_name = "lean_io_shim_uv_os_tmpdir"]
        fn lean_io_shim_uv_os_tmpdir_cxx(buf: *mut c_char, sz: *mut usize) -> c_int;
        #[link_name = "lean_io_shim_uv_fs_mkstemp"]
        fn lean_io_shim_uv_fs_mkstemp_cxx(
            pattern: *const c_char,
            out_fd: *mut c_int,
            out_path: *mut c_char,
            path_cap: usize,
        ) -> c_int;
        #[link_name = "lean_io_shim_uv_fs_mkdtemp"]
        fn lean_io_shim_uv_fs_mkdtemp_cxx(
            pattern: *const c_char,
            out_path: *mut c_char,
            path_cap: usize,
        ) -> c_int;
    }

    // Opaque FILE type for FFI
    #[repr(C)]
    pub struct libc_FILE {
        _opaque: [u8; 0],
    }

    // Minimal uv_timespec / uv_stat mirror — must match libuv ABI
    #[repr(C)]
    pub struct UvTimespec {
        pub tv_sec: i64,
        pub tv_nsec: u32,
    }

    #[repr(C)]
    pub struct UvStatBuf {
        pub st_dev: u64,
        pub st_mode: u64,
        pub st_nlink: u64,
        pub st_uid: u64,
        pub st_gid: u64,
        pub st_rdev: u64,
        pub st_ino: u64,
        pub st_size: u64,
        pub st_blksize: u64,
        pub st_blocks: u64,
        pub st_flags: u64,
        pub st_gen: u64,
        pub st_atim: UvTimespec,
        pub st_mtim: UvTimespec,
        pub st_ctim: UvTimespec,
        pub st_birthtim: UvTimespec,
    }

    // Platform stat mode bits
    const S_IFMT:  u64 = 0o170000;
    const S_IFDIR: u64 = 0o040000;
    const S_IFREG: u64 = 0o100000;
    #[cfg(not(target_os = "windows"))]
    const S_IFLNK: u64 = 0o120000;

    // -----------------------------------------------------------------------
    // Helper: check string for embedded NUL
    // -----------------------------------------------------------------------
    unsafe fn string_has_embedded_nul(s: *const LeanObject) -> bool {
        let cstr = lean_string_cstr(s as *mut LeanObject);
        let lean_sz = lean_string_size(s as *mut LeanObject); // includes trailing NUL
        libc_strlen(cstr) != lean_sz - 1
    }

    extern "C" {
        fn libc_strlen(s: *const c_char) -> usize;
        fn libc_strerror(errnum: c_int) -> *const c_char;
        fn libc_fclose(fp: *mut libc_FILE) -> c_int;
        fn libc_fflush(fp: *mut libc_FILE) -> c_int;
        fn libc_fseek(fp: *mut libc_FILE, off: i64, whence: c_int) -> c_int;
        fn libc_fread(buf: *mut u8, sz: usize, n: usize, fp: *mut libc_FILE) -> usize;
        fn libc_fwrite(buf: *const u8, sz: usize, n: usize, fp: *mut libc_FILE) -> usize;
        fn libc_feof(fp: *mut libc_FILE) -> c_int;
        fn libc_ferror(fp: *mut libc_FILE) -> c_int;
        fn libc_clearerr(fp: *mut libc_FILE);
        fn libc_isatty(fd: c_int) -> c_int;
        fn libc_fileno(fp: *mut libc_FILE) -> c_int;
        fn libc_ftruncate(fd: c_int, len: i64) -> c_int;
        fn libc_ftello(fp: *mut libc_FILE) -> i64;
        fn libc_getcwd(buf: *mut c_char, sz: usize) -> *mut c_char;
        fn libc_open(path: *const c_char, flags: c_int, mode: c_int) -> c_int;
        fn libc_fdopen(fd: c_int, mode: *const c_char) -> *mut libc_FILE;
        fn libc_mkdir(path: *const c_char, mode: c_int) -> c_int;
        fn libc_rmdir(path: *const c_char) -> c_int;
        fn libc_rename(from: *const c_char, to: *const c_char) -> c_int;
        fn libc_fdopen_r(fd: c_int) -> *mut libc_FILE; // shim for fdopen("r+")
        fn libc_chmod(path: *const c_char, mode: c_uint) -> c_int;
        fn libc_flock(fd: c_int, op: c_int) -> c_int;
        fn libc_getc_unlocked(fp: *mut libc_FILE) -> c_int;
        fn libc_flockfile(fp: *mut libc_FILE);
        fn libc_funlockfile(fp: *mut libc_FILE);
        fn libc_realpath(path: *const c_char, out: *mut c_char) -> *mut c_char;
        fn libc_getpid() -> i32;
        fn libc_readlink(path: *const c_char, buf: *mut c_char, bufsz: usize) -> isize;
        fn libc_read_urandom(buf: *mut u8, n: usize) -> isize;
        fn libc_fdopen_with_mode(fd: c_int, mode: *const c_char) -> *mut libc_FILE;
        fn libc_opendir(path: *const c_char) -> *mut c_void;
        fn libc_readdir(dp: *mut c_void) -> *mut DirentC;
        fn libc_closedir(dp: *mut c_void) -> c_int;
    }

    // -- Additional C symbols needed by this module (C++ inlines given symbols in shims) --
    extern "C" {
        fn lean_mk_string(s: *const c_char) -> *mut LeanObject;
        fn lean_mk_ascii_string_unchecked(s: *const c_char) -> *mut LeanObject;
        fn lean_mk_io_user_error(msg: *mut LeanObject) -> *mut LeanObject;
        fn lean_mk_io_error_already_exists(w: *mut LeanObject) -> *mut LeanObject;
        fn lean_io_result_mk_ok(a: *mut LeanObject) -> *mut LeanObject;
        fn lean_io_result_mk_error(e: *mut LeanObject) -> *mut LeanObject;
        fn lean_io_error_to_string(e: *mut LeanObject) -> *mut LeanObject;
        fn lean_mk_io_user_error_from_message(s: *const c_char) -> *mut LeanObject;
        fn lean_set_st_header(o: *mut LeanObject, tag: u8, other: u8);
        /// lean_mk_string_from_bytes_unchecked — defined in runtime_object_string_impl with #[no_mangle]
        fn lean_mk_string_from_bytes_unchecked(s: *const c_char, len: usize) -> *mut LeanObject;
        fn lean_alloc_array(size: usize, capacity: usize) -> *mut LeanObject;
        fn lean_int64_to_int(n: i64) -> *mut LeanObject;
        fn lean_io_eprintln(msg: *mut LeanObject) -> *mut LeanObject;
        fn lean_alloc_sarray_would_overflow_c(elem_size: usize, size: usize) -> bool;
    }

    // lean_ctor_set / lean_ctor_set_uint32 — Rust implementations (mirrors lean.h inlines)
    #[inline(always)]
    unsafe fn lean_ctor_set(obj: *mut LeanObject, idx: usize, val: *mut LeanObject) {
        (obj.add(1) as *mut *mut LeanObject).add(idx).write(val);
    }
    #[inline(always)]
    unsafe fn lean_ctor_set_uint32(obj: *mut LeanObject, offset: usize, value: u32) {
        (obj.add(1) as *mut u8).add(offset).cast::<u32>().write(value);
    }
    #[inline(always)]
    unsafe fn lean_alloc_ctor_local(tag: c_uint, num_objs: c_uint, scalar_sz: c_uint) -> *mut LeanObject {
        extern "C" { fn lean_runtime_alloc_ctor(tag: c_uint, num_objs: c_uint, scalar_size: c_uint) -> *mut LeanObject; }
        lean_runtime_alloc_ctor(tag, num_objs, scalar_sz)
    }
    // Convenience alias inside this module
    #[inline(always)]
    unsafe fn lean_alloc_ctor(tag: c_uint, num_objs: c_uint, scalar_sz: c_uint) -> *mut LeanObject {
        lean_alloc_ctor_local(tag, num_objs, scalar_sz)
    }
    /// LEAN_REF_TAG (253) — tag used for Ref objects
    const LEAN_REF_TAG_IO: u8 = 253;

    #[repr(C)]
    struct DirentC {
        d_ino: u64,
        d_off: i64,
        d_reclen: u16,
        d_type: u8,
        d_name: [c_char; 256],
    }

    // -----------------------------------------------------------------------
    // io_result helpers (already in lean.h inline, replicated for clarity)
    // -----------------------------------------------------------------------
    #[inline(always)]
    unsafe fn io_result_mk_ok(a: *mut LeanObject) -> *mut LeanObject {
        lean_io_result_mk_ok(a)
    }
    #[inline(always)]
    unsafe fn io_result_mk_error_obj(e: *mut LeanObject) -> *mut LeanObject {
        lean_io_result_mk_error(e)
    }
    unsafe fn ensure_io_shim_init() {
        if IO_SHIM_INIT.swap(true, Ordering::AcqRel) {
            return;
        }
        libc::write(2, b"io: wrap stdin\n".as_ptr().cast(), 15);
        IO_SHIM_STDIN = lean_io_wrap_handle_c(libc_stdin);
        libc::write(2, b"io: wrap stdout\n".as_ptr().cast(), 16);
        IO_SHIM_STDOUT = lean_io_wrap_handle_c(libc_stdout);
        libc::write(2, b"io: wrap stderr\n".as_ptr().cast(), 16);
        IO_SHIM_STDERR = lean_io_wrap_handle_c(libc_stderr);
        libc::write(2, b"io: persist stdin\n".as_ptr().cast(), 18);
        mark_io_handle_persistent(IO_SHIM_STDIN);
        libc::write(2, b"io: persist stdout\n".as_ptr().cast(), 19);
        mark_io_handle_persistent(IO_SHIM_STDOUT);
        libc::write(2, b"io: persist stderr\n".as_ptr().cast(), 19);
        mark_io_handle_persistent(IO_SHIM_STDERR);
        libc::write(2, b"io: done\n".as_ptr().cast(), 9);
    }
    unsafe fn mark_io_handle_persistent(h: *mut LeanObject) {
        if !lean_is_scalar(h) {
            (*h).m_rc = 0;
        }
    }
    unsafe fn decode_io_error(errnum: c_int, fname: *mut LeanObject) -> *mut LeanObject {
        lean_decode_io_error_c(errnum, fname)
    }
    unsafe fn decode_uv_error(errnum: c_int, fname: *mut LeanObject) -> *mut LeanObject {
        lean_decode_uv_error_c(errnum, fname)
    }

    // -----------------------------------------------------------------------
    // lean_io_result_show_error
    // -----------------------------------------------------------------------
    #[no_mangle]
    pub unsafe extern "C" fn lean_io_result_show_error(r: *mut LeanObject) {
        let err = lean_io_result_get_error(r);
        lean_inc(err);
        let s = lean_io_error_to_string(err);
        let cstr = lean_string_cstr(s);
        // write "uncaught exception: <msg>\n" to stderr
        extern "C" { fn fputs(s: *const c_char, fp: *mut libc_FILE) -> c_int; }
        fputs(b"uncaught exception: \0".as_ptr() as *const c_char, libc_stderr as *mut libc_FILE);
        fputs(cstr, libc_stderr as *mut libc_FILE);
        fputs(b"\n\0".as_ptr() as *const c_char, libc_stderr as *mut libc_FILE);
        lean_dec(s);
    }

    // -----------------------------------------------------------------------
    // lean_decode_io_error / lean_decode_uv_error — delegate to C++ shim
    // (the shim builds the Lean ADT; it's pure C++ template dispatch)
    // -----------------------------------------------------------------------
    #[no_mangle]
    pub unsafe extern "C" fn lean_decode_io_error(
        errnum: c_int,
        fname: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_decode_io_error_c(errnum, fname)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_decode_uv_error(
        errnum: c_int,
        fname: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_decode_uv_error_c(errnum, fname)
    }

    // -----------------------------------------------------------------------
    // mk_embedded_nul_error
    // -----------------------------------------------------------------------
    unsafe fn mk_embedded_nul_error(s: *mut LeanObject) -> *mut LeanObject {
        lean_mk_embedded_nul_error_c(s)
    }

    // -----------------------------------------------------------------------
    // lean_get_stdin / lean_get_stdout / lean_get_stderr
    // -----------------------------------------------------------------------
    #[no_mangle]
    pub unsafe extern "C" fn lean_get_stdin() -> *mut LeanObject {
        ensure_io_shim_init();
        lean_inc(IO_SHIM_STDIN);
        IO_SHIM_STDIN
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_get_stdout() -> *mut LeanObject {
        ensure_io_shim_init();
        lean_inc(IO_SHIM_STDOUT);
        IO_SHIM_STDOUT
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_get_stderr() -> *mut LeanObject {
        ensure_io_shim_init();
        lean_inc(IO_SHIM_STDERR);
        IO_SHIM_STDERR
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_get_set_stdin(h: *mut LeanObject) -> *mut LeanObject {
        IO_SHIM_STDIN = h;
        mark_io_handle_persistent(h);
        lean_box(0)
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_get_set_stdout(h: *mut LeanObject) -> *mut LeanObject {
        IO_SHIM_STDOUT = h;
        mark_io_handle_persistent(h);
        lean_box(0)
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_get_set_stderr(h: *mut LeanObject) -> *mut LeanObject {
        IO_SHIM_STDERR = h;
        mark_io_handle_persistent(h);
        lean_box(0)
    }

    // -----------------------------------------------------------------------
    // lean_chmod
    // -----------------------------------------------------------------------
    #[no_mangle]
    pub unsafe extern "C" fn lean_chmod(filename: *mut LeanObject, mode: u32) -> *mut LeanObject {
        let fname = lean_string_cstr(filename);
        if string_has_embedded_nul(filename) {
            return mk_embedded_nul_error(filename);
        }
        if libc_chmod(fname, mode) == 0 {
            io_result_mk_ok(lean_box(0))
        } else {
            extern "C" { fn lean_errno() -> c_int; }
            lean_inc(filename);
            io_result_mk_error_obj(decode_io_error(lean_errno(), filename))
        }
    }

    // -----------------------------------------------------------------------
    // lean_io_prim_handle_mk
    // -----------------------------------------------------------------------
    #[no_mangle]
    pub unsafe extern "C" fn lean_io_prim_handle_mk(
        filename: *mut LeanObject,
        mode: u8,
    ) -> *mut LeanObject {
        extern "C" { fn lean_errno() -> c_int; }
        if string_has_embedded_nul(filename) {
            return mk_embedded_nul_error(filename);
        }
        let fname = lean_string_cstr(filename);

        // Build open flags
        let mut flags: c_int = 0;
        #[cfg(target_os = "windows")]
        { flags |= 0x8000 /* O_BINARY */; flags |= 0x0080 /* O_NOINHERIT */; }
        #[cfg(not(target_os = "windows"))]
        { flags |= 0x80000 /* O_CLOEXEC */; }

        flags |= match mode {
            0 => 0,          // O_RDONLY
            1 => 0x201 | 0x200, // O_WRONLY | O_CREAT | O_TRUNC — shim resolves platform values
            2 => 0x201 | 0x200 | 0x800, // writeNew adds O_EXCL
            3 => 2,          // O_RDWR
            4 => 0x401 | 0x200, // O_WRONLY | O_CREAT | O_APPEND
            _ => 0,
        };
        let fd = libc_open(fname, flags, 0o666);
        if fd == -1 {
            return io_result_mk_error_obj(decode_io_error(lean_errno(), filename));
        }
        let fp_mode = match mode {
            0 => b"r\0".as_ptr() as *const c_char,
            1 | 2 => b"w\0".as_ptr() as *const c_char,
            3 => b"r+\0".as_ptr() as *const c_char,
            4 => b"a\0".as_ptr() as *const c_char,
            _ => b"r\0".as_ptr() as *const c_char,
        };
        let fp = libc_fdopen(fd, fp_mode);
        if fp.is_null() {
            return io_result_mk_error_obj(decode_io_error(lean_errno(), filename));
        }
        io_result_mk_ok(lean_io_wrap_handle_c(fp as *mut c_void))
    }

    // -----------------------------------------------------------------------
    // Handle.isTty / isEof / flush / rewind / truncate
    // -----------------------------------------------------------------------
    #[no_mangle]
    pub unsafe extern "C" fn lean_io_prim_handle_is_tty(h: *mut LeanObject) -> u8 {
        let fp = lean_io_get_handle_c(h);
        let fd = libc_fileno(fp);
        libc_isatty(fd) as u8
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_io_prim_handle_is_eof(h: *mut LeanObject) -> u8 {
        let fp = lean_io_get_handle_c(h);
        (libc_feof(fp) != 0) as u8
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_io_prim_handle_flush(h: *mut LeanObject) -> *mut LeanObject {
        extern "C" { fn lean_errno() -> c_int; }
        let fp = lean_io_get_handle_c(h);
        if libc_fflush(fp) == 0 {
            io_result_mk_ok(lean_box(0))
        } else {
            io_result_mk_error_obj(decode_io_error(lean_errno(), null_mut()))
        }
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_io_prim_handle_rewind(h: *mut LeanObject) -> *mut LeanObject {
        extern "C" { fn lean_errno() -> c_int; }
        let fp = lean_io_get_handle_c(h);
        if libc_fseek(fp, 0, 0 /* SEEK_SET */) == 0 {
            io_result_mk_ok(lean_box(0))
        } else {
            io_result_mk_error_obj(decode_io_error(lean_errno(), null_mut()))
        }
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_io_prim_handle_truncate(h: *mut LeanObject) -> *mut LeanObject {
        extern "C" { fn lean_errno() -> c_int; }
        let fp = lean_io_get_handle_c(h);
        let fd = libc_fileno(fp);
        let pos = libc_ftello(fp);
        if libc_ftruncate(fd, pos) == 0 {
            io_result_mk_ok(lean_box(0))
        } else {
            io_result_mk_error_obj(decode_io_error(lean_errno(), null_mut()))
        }
    }

    // -----------------------------------------------------------------------
    // Handle.read
    // -----------------------------------------------------------------------
    #[no_mangle]
    pub unsafe extern "C" fn lean_io_prim_handle_read(
        h: *mut LeanObject,
        nbytes: usize,
    ) -> *mut LeanObject {
        extern "C" { fn lean_errno() -> c_int; }
        let fp = lean_io_get_handle_c(h);
        if lean_alloc_sarray_would_overflow_c(1, nbytes) {
            return io_result_mk_error_obj(decode_io_error(12 /* ENOMEM */, null_mut()));
        }
        let res = lean_alloc_sarray(1, 0, nbytes);
        if nbytes == 0 {
            return io_result_mk_ok(res);
        }
        let n = libc_fread(lean_sarray_cptr(res) as *mut u8, 1, nbytes, fp);
        if n > 0 {
            lean_sarray_set_size(res, n);
            io_result_mk_ok(res)
        } else if libc_feof(fp) != 0 {
            libc_clearerr(fp);
            lean_sarray_set_size(res, 0);
            io_result_mk_ok(res)
        } else {
            lean_dec_ref(res);
            io_result_mk_error_obj(decode_io_error(lean_errno(), null_mut()))
        }
    }

    // -----------------------------------------------------------------------
    // Handle.write
    // -----------------------------------------------------------------------
    #[no_mangle]
    pub unsafe extern "C" fn lean_io_prim_handle_write(
        h: *mut LeanObject,
        buf: *mut LeanObject,
    ) -> *mut LeanObject {
        extern "C" { fn lean_errno() -> c_int; }
        let fp = lean_io_get_handle_c(h);
        let n = lean_sarray_size(buf);
        let m = libc_fwrite(lean_sarray_cptr(buf), 1, n, fp);
        if m == n {
            io_result_mk_ok(lean_box(0))
        } else {
            io_result_mk_error_obj(decode_io_error(lean_errno(), null_mut()))
        }
    }

    // -----------------------------------------------------------------------
    // Handle.getLine
    // -----------------------------------------------------------------------
    #[no_mangle]
    pub unsafe extern "C" fn lean_io_prim_handle_get_line(h: *mut LeanObject) -> *mut LeanObject {
        extern "C" { fn lean_errno() -> c_int; }
        let fp = lean_io_get_handle_c(h);
        let mut buf: Vec<u8> = Vec::new();
        libc_flockfile(fp);
        loop {
            let c = libc_getc_unlocked(fp);
            if c == -1 /* EOF */ { break; }
            buf.push(c as u8);
            if c == b'\n' as c_int { break; }
        }
        libc_funlockfile(fp);
        if libc_ferror(fp) != 0 {
            return io_result_mk_error_obj(decode_io_error(lean_errno(), null_mut()));
        }
        if libc_feof(fp) != 0 {
            libc_clearerr(fp);
        }
        let s = lean_mk_string_from_bytes_unchecked(buf.as_ptr() as *const c_char, buf.len());
        io_result_mk_ok(s)
    }

    // -----------------------------------------------------------------------
    // Handle.putStr
    // -----------------------------------------------------------------------
    #[no_mangle]
    pub unsafe extern "C" fn lean_io_prim_handle_put_str(
        h: *mut LeanObject,
        s: *mut LeanObject,
    ) -> *mut LeanObject {
        extern "C" { fn lean_errno() -> c_int; }
        let fp = lean_io_get_handle_c(h);
        let n = lean_string_size(s) - 1;
        let m = libc_fwrite(lean_string_cstr(s) as *const u8, 1, n, fp);
        if m == n {
            io_result_mk_ok(lean_box(0))
        } else {
            io_result_mk_error_obj(decode_io_error(lean_errno(), null_mut()))
        }
    }

    // -----------------------------------------------------------------------
    #[no_mangle]
    pub unsafe extern "C" fn lean_io_prim_handle_lock(h: *mut LeanObject, x: u8) -> *mut LeanObject {
        extern "C" { fn lean_errno() -> c_int; }
        let fp = lean_io_get_handle_c(h);
        if libc_flock(libc_fileno(fp), if x != 0 { libc::LOCK_EX } else { libc::LOCK_SH }) == 0 {
            io_result_mk_ok(lean_box(0))
        } else {
            io_result_mk_error_obj(decode_io_error(lean_errno(), null_mut()))
        }
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_io_prim_handle_try_lock(h: *mut LeanObject, x: u8) -> *mut LeanObject {
        extern "C" { fn lean_errno() -> c_int; }
        let fp = lean_io_get_handle_c(h);
        if libc_flock(libc_fileno(fp), (if x != 0 { libc::LOCK_EX } else { libc::LOCK_SH }) | libc::LOCK_NB) == 0 {
            io_result_mk_ok(lean_box(1))
        } else if lean_errno() == libc::EWOULDBLOCK {
            io_result_mk_ok(lean_box(0))
        } else {
            io_result_mk_error_obj(decode_io_error(lean_errno(), null_mut()))
        }
    }
    #[no_mangle]
    pub unsafe extern "C" fn lean_io_prim_handle_unlock(h: *mut LeanObject) -> *mut LeanObject {
        extern "C" { fn lean_errno() -> c_int; }
        let fp = lean_io_get_handle_c(h);
        if libc_flock(libc_fileno(fp), libc::LOCK_UN) == 0 {
            io_result_mk_ok(lean_box(0))
        } else {
            io_result_mk_error_obj(decode_io_error(lean_errno(), null_mut()))
        }
    }

    // -----------------------------------------------------------------------
    // lean_io_get_random_bytes
    // -----------------------------------------------------------------------
    #[no_mangle]
    pub unsafe extern "C" fn lean_io_get_random_bytes(nbytes: usize) -> *mut LeanObject {
        extern "C" { fn lean_errno() -> c_int; }
        if nbytes == 0 {
            return io_result_mk_ok(lean_alloc_sarray(1, 0, 0));
        }
        if lean_alloc_sarray_would_overflow_c(1, nbytes) {
            return io_result_mk_error_obj(decode_io_error(12 /* ENOMEM */, null_mut()));
        }
        let res = lean_alloc_sarray(1, 0, nbytes);
        let dst = lean_sarray_cptr(res);
        let mut remain = nbytes;
        let mut offset = 0usize;
        while remain > 0 {
            #[cfg(target_os = "windows")]
            {
                extern "C" {
                    fn lean_io_shim_bcrypt_random(buf: *mut u8, n: usize) -> c_int;
                }
                let r = lean_io_shim_bcrypt_random(dst.add(offset), remain);
                if r != 0 {
                    lean_dec_ref(res);
                    return io_result_mk_error_obj(lean_mk_io_user_error(
                        lean_mk_ascii_string_unchecked(b"BCryptGenRandom failed\0".as_ptr() as *const c_char),
                    ));
                }
                remain = 0;
            }
            #[cfg(not(target_os = "windows"))]
            {
                let read_sz = if cfg!(target_arch = "wasm32") {
                    remain.min(65536)
                } else {
                    remain
                };
                let nread = libc_read_urandom(dst.add(offset) as *mut u8, read_sz);
                if nread < 0 {
                    if lean_errno() != 4 /* EINTR */ {
                        lean_dec_ref(res);
                        return io_result_mk_error_obj(decode_io_error(lean_errno(), null_mut()));
                    }
                } else {
                    remain -= nread as usize;
                    offset += nread as usize;
                }
            }
        }
        lean_sarray_set_size(res, nbytes);
        io_result_mk_ok(res)
    }

    // -----------------------------------------------------------------------
    // lean_io_realpath
    // -----------------------------------------------------------------------
    #[no_mangle]
    pub unsafe extern "C" fn lean_io_realpath(filename: *mut LeanObject) -> *mut LeanObject {
        extern "C" {
            fn lean_errno() -> c_int;
            fn libc_realpath(path: *const c_char, out: *mut c_char) -> *mut c_char;
        }
        if string_has_embedded_nul(filename) {
            let r = mk_embedded_nul_error(filename);
            lean_dec(filename);
            return r;
        }
        let fname = lean_string_cstr(filename);
        let mut buffer = [0u8; PATH_MAX];
        let result = libc_realpath(fname, buffer.as_mut_ptr() as *mut c_char);
        let out = if result.is_null() {
            io_result_mk_error_obj(decode_io_error(lean_errno(), null_mut()))
        } else {
            io_result_mk_ok(lean_mk_string(buffer.as_ptr() as *const c_char))
        };
        lean_dec(filename);
        out
    }

    // -----------------------------------------------------------------------
    // lean_io_read_dir
    // -----------------------------------------------------------------------
    #[no_mangle]
    pub unsafe extern "C" fn lean_io_read_dir(dirname: *mut LeanObject) -> *mut LeanObject {
        extern "C" { fn lean_errno() -> c_int; }
        if string_has_embedded_nul(dirname) {
            return mk_embedded_nul_error(dirname);
        }
        let dirname_ptr = lean_string_cstr(dirname);
        let arr = lean_alloc_array(0, 0);
        let dp = libc_opendir(dirname_ptr);
        if dp.is_null() {
            return io_result_mk_error_obj(decode_io_error(lean_errno(), dirname));
        }
        let dot = b".\0".as_ptr() as *const c_char;
        let dotdot = b"..\0".as_ptr() as *const c_char;
        let mut arr = arr;
        loop {
            let entry = libc_readdir(dp);
            if entry.is_null() { break; }
            // strcmp
            extern "C" { fn strcmp(a: *const c_char, b: *const c_char) -> c_int; }
            if strcmp((*entry).d_name.as_ptr(), dot) == 0
                || strcmp((*entry).d_name.as_ptr(), dotdot) == 0
            {
                continue;
            }
            let lentry = lean_alloc_ctor(0, 2, 0);
            lean_inc(dirname);
            lean_ctor_set(lentry, 0, dirname);
            lean_ctor_set(lentry, 1, lean_mk_string((*entry).d_name.as_ptr()));
            arr = lean_array_push(arr, lentry);
        }
        libc_closedir(dp);
        io_result_mk_ok(arr)
    }

    // -----------------------------------------------------------------------
    // lean_io_metadata / lean_io_symlink_metadata
    // -----------------------------------------------------------------------
    unsafe fn timespec_to_obj(ts: &UvTimespec) -> *mut LeanObject {
        let o = lean_alloc_ctor(0, 1, 4 /* sizeof(uint32) */);
        lean_ctor_set(o, 0, lean_int64_to_int(ts.tv_sec));
        lean_ctor_set_uint32(o, core::mem::size_of::<*mut LeanObject>(), ts.tv_nsec);
        o
    }

    unsafe fn metadata_core(st: &UvStatBuf) -> *mut LeanObject {
        let mdata = lean_alloc_ctor(0, 2, 2 * 8 + 1 /* uint64 * 2 + uint8 */);
        lean_ctor_set(mdata, 0, timespec_to_obj(&st.st_atim));
        lean_ctor_set(mdata, 1, timespec_to_obj(&st.st_mtim));
        let ptr_sz = core::mem::size_of::<*mut LeanObject>();
        lean_ctor_set_uint64(mdata, 2 * ptr_sz, st.st_size);
        lean_ctor_set_uint64(mdata, 2 * ptr_sz + 8, st.st_nlink);
        let ftype: u8 = if st.st_mode & S_IFMT == S_IFDIR { 0 }
            else if st.st_mode & S_IFMT == S_IFREG { 1 }
            else {
                #[cfg(not(target_os = "windows"))]
                if st.st_mode & S_IFMT == S_IFLNK { 2 } else { 3 }
                #[cfg(target_os = "windows")]
                3
            };
        lean_ctor_set_uint8(mdata, 2 * ptr_sz + 16, ftype);
        io_result_mk_ok(mdata)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_io_metadata(filename: *mut LeanObject) -> *mut LeanObject {
        if string_has_embedded_nul(filename) {
            return mk_embedded_nul_error(filename);
        }
        let mut st = core::mem::zeroed::<UvStatBuf>();
        let ret = lean_io_shim_uv_stat_cxx(lean_string_cstr(filename), &mut st);
        if ret < 0 {
            io_result_mk_error_obj(decode_uv_error(ret, filename))
        } else {
            metadata_core(&st)
        }
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_io_symlink_metadata(filename: *mut LeanObject) -> *mut LeanObject {
        #[cfg(target_os = "windows")]
        { return lean_io_metadata(filename); }
        #[cfg(not(target_os = "windows"))]
        {
            if string_has_embedded_nul(filename) {
                return mk_embedded_nul_error(filename);
            }
            let mut st = core::mem::zeroed::<UvStatBuf>();
            let ret = lean_io_shim_uv_lstat_cxx(lean_string_cstr(filename), &mut st);
            if ret < 0 {
                io_result_mk_error_obj(decode_uv_error(ret, filename))
            } else {
                metadata_core(&st)
            }
        }
    }

    // -----------------------------------------------------------------------
    // lean_io_create_dir / lean_io_remove_dir / lean_io_rename / lean_io_hard_link
    // -----------------------------------------------------------------------
    #[no_mangle]
    pub unsafe extern "C" fn lean_io_create_dir(p: *mut LeanObject) -> *mut LeanObject {
        extern "C" { fn lean_errno() -> c_int; }
        if string_has_embedded_nul(p) { return mk_embedded_nul_error(p); }
        let str = lean_string_cstr(p);
        if libc_mkdir(str, 0o777) == 0 {
            io_result_mk_ok(lean_box(0))
        } else {
            io_result_mk_error_obj(decode_io_error(lean_errno(), p))
        }
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_io_remove_dir(p: *mut LeanObject) -> *mut LeanObject {
        extern "C" { fn lean_errno() -> c_int; }
        if string_has_embedded_nul(p) { return mk_embedded_nul_error(p); }
        let str = lean_string_cstr(p);
        if libc_rmdir(str) == 0 {
            io_result_mk_ok(lean_box(0))
        } else {
            io_result_mk_error_obj(decode_io_error(lean_errno(), p))
        }
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_io_rename(
        from: *mut LeanObject,
        to: *mut LeanObject,
    ) -> *mut LeanObject {
        extern "C" {
            fn lean_errno() -> c_int;
            fn libc_rename(from: *const c_char, to: *const c_char) -> c_int;
        }
        if string_has_embedded_nul(from) { return mk_embedded_nul_error(from); }
        if string_has_embedded_nul(to) { return mk_embedded_nul_error(to); }
        let from_c = lean_string_cstr(from);
        let to_c = lean_string_cstr(to);
        if libc_rename(from_c, to_c) == 0 {
            io_result_mk_ok(lean_box(0))
        } else {
            io_result_mk_error_obj(decode_io_error(lean_errno(), from))
        }
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_io_hard_link(
        orig: *mut LeanObject,
        link: *mut LeanObject,
    ) -> *mut LeanObject {
        if string_has_embedded_nul(orig) { return mk_embedded_nul_error(orig); }
        if string_has_embedded_nul(link) { return mk_embedded_nul_error(link); }
        let ret = lean_io_shim_uv_link_cxx(lean_string_cstr(orig), lean_string_cstr(link));
        if ret < 0 {
            io_result_mk_error_obj(decode_uv_error(ret, orig))
        } else {
            io_result_mk_ok(lean_box(0))
        }
    }

    // -----------------------------------------------------------------------
    // lean_io_remove_file
    // -----------------------------------------------------------------------
    #[no_mangle]
    pub unsafe extern "C" fn lean_io_remove_file(filename: *mut LeanObject) -> *mut LeanObject {
        if string_has_embedded_nul(filename) { return mk_embedded_nul_error(filename); }
        let ret = lean_io_shim_uv_unlink_cxx(lean_string_cstr(filename));
        if ret < 0 {
            io_result_mk_error_obj(decode_uv_error(ret, filename))
        } else {
            io_result_mk_ok(lean_box(0))
        }
    }

    // -----------------------------------------------------------------------
    // lean_io_create_tempfile / lean_io_create_tempdir
    // -----------------------------------------------------------------------
    const PATH_MAX: usize = 4096;

    #[no_mangle]
    pub unsafe extern "C" fn lean_io_create_tempfile(_w: *mut LeanObject) -> *mut LeanObject {
        let mut base = [0u8; PATH_MAX];
        let mut base_len = PATH_MAX;
        let ret = lean_io_shim_uv_os_tmpdir_cxx(base.as_mut_ptr() as *mut c_char, &mut base_len);
        if ret < 0 {
            return io_result_mk_error_obj(decode_uv_error(ret, null_mut()));
        }
        if base_len == 0 {
            return io_result_mk_error_obj(decode_uv_error(-4058 /* UV_ENOENT */, lean_mk_ascii_string_unchecked(b"\0".as_ptr() as *const c_char)));
        }
        // Ensure trailing separator
        #[cfg(target_os = "windows")]
        let sep = b'\\';
        #[cfg(not(target_os = "windows"))]
        let sep = b'/';
        if base[base_len - 1] != sep {
            base[base_len] = sep;
            base_len += 1;
        }
        let pattern = b"tmp.XXXXXXXX\0";
        let pat_len = pattern.len() - 1;
        base[base_len..base_len + pat_len].copy_from_slice(&pattern[..pat_len]);
        base[base_len + pat_len] = 0;

        let mut fd: c_int = -1;
        let mut out_path = [0u8; PATH_MAX];
        let ret = lean_io_shim_uv_fs_mkstemp_cxx(
            base.as_ptr() as *const c_char,
            &mut fd,
            out_path.as_mut_ptr() as *mut c_char,
            PATH_MAX,
        );
        if ret < 0 {
            return io_result_mk_error_obj(decode_uv_error(ret, null_mut()));
        }
        // fdopen for read+write
        let fp = libc_fdopen_with_mode(fd, b"r+\0".as_ptr() as *const c_char);
        let handle = lean_io_wrap_handle_c(fp as *mut c_void);
        let path_str = lean_mk_string(out_path.as_ptr() as *const c_char);
        // Return pair (handle, path)
        let pair = lean_alloc_ctor(0, 2, 0);
        lean_ctor_set(pair, 0, handle);
        lean_ctor_set(pair, 1, path_str);
        lean_io_result_mk_ok(pair)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_io_create_tempdir(_w: *mut LeanObject) -> *mut LeanObject {
        let mut base = [0u8; PATH_MAX];
        let mut base_len = PATH_MAX;
        let ret = lean_io_shim_uv_os_tmpdir_cxx(base.as_mut_ptr() as *mut c_char, &mut base_len);
        if ret < 0 {
            return io_result_mk_error_obj(decode_uv_error(ret, null_mut()));
        }
        if base_len == 0 {
            return io_result_mk_error_obj(decode_uv_error(-4058 /* UV_ENOENT */, lean_mk_ascii_string_unchecked(b"\0".as_ptr() as *const c_char)));
        }
        #[cfg(target_os = "windows")]
        let sep = b'\\';
        #[cfg(not(target_os = "windows"))]
        let sep = b'/';
        if base[base_len - 1] != sep {
            base[base_len] = sep;
            base_len += 1;
        }
        let pattern = b"tmp.XXXXXXXX\0";
        let pat_len = pattern.len() - 1;
        base[base_len..base_len + pat_len].copy_from_slice(&pattern[..pat_len]);
        base[base_len + pat_len] = 0;

        let mut out_path = [0u8; PATH_MAX];
        let ret = lean_io_shim_uv_fs_mkdtemp_cxx(
            base.as_ptr() as *const c_char,
            out_path.as_mut_ptr() as *mut c_char,
            PATH_MAX,
        );
        if ret < 0 {
            return io_result_mk_error_obj(decode_uv_error(ret, null_mut()));
        }
        lean_io_result_mk_ok(lean_mk_string(out_path.as_ptr() as *const c_char))
    }

    // -----------------------------------------------------------------------
    // lean_io_app_path / lean_io_current_dir
    // -----------------------------------------------------------------------
    #[no_mangle]
    pub unsafe extern "C" fn lean_io_app_path() -> *mut LeanObject {
        extern "C" { fn lean_errno() -> c_int; }
        #[cfg(target_os = "windows")]
        {
            extern "C" {
                fn GetModuleHandleW(name: *const u16) -> *mut c_void;
                fn GetModuleFileNameW(module: *mut c_void, buf: *mut u16, size: u32) -> u32;
            }
            let module = GetModuleHandleW(null());
            let mut buf = [0u16; PATH_MAX];
            let n = GetModuleFileNameW(module, buf.as_mut_ptr(), PATH_MAX as u32);
            if n == 0 {
                return io_result_mk_error_obj(lean_mk_io_user_error(lean_mk_ascii_string_unchecked(
                    b"failed to locate application\0".as_ptr() as *const c_char,
                )));
            }
            let mut path = String::from_utf16_lossy(&buf[..n as usize]);
            if path.len() >= 2 && path.as_bytes()[1] == b':' {
                let mut bytes = path.into_bytes();
                bytes[0] = bytes[0].to_ascii_lowercase();
                let cpath = std::ffi::CString::new(bytes).unwrap();
                return io_result_mk_ok(lean_mk_string(cpath.as_ptr()));
            }
            let cpath = std::ffi::CString::new(path).unwrap();
            return io_result_mk_ok(lean_mk_string(cpath.as_ptr()));
        }
        #[cfg(target_os = "macos")]
        {
            extern "C" {
                fn _NSGetExecutablePath(buf: *mut c_char, size: *mut u32) -> c_int;
                fn libc_realpath(path: *const c_char, out: *mut c_char) -> *mut c_char;
            }
            let mut buf1 = [0u8; PATH_MAX];
            let mut buf2 = [0u8; PATH_MAX];
            let mut size = PATH_MAX as u32;
            if _NSGetExecutablePath(buf1.as_mut_ptr() as *mut c_char, &mut size) != 0 {
                return io_result_mk_error_obj(lean_mk_io_user_error(lean_mk_ascii_string_unchecked(
                    b"failed to locate application\0".as_ptr() as *const c_char,
                )));
            }
            if libc_realpath(buf1.as_ptr() as *const c_char, buf2.as_mut_ptr() as *mut c_char).is_null() {
                return io_result_mk_error_obj(lean_mk_io_user_error(lean_mk_ascii_string_unchecked(
                    b"failed to resolve symbolic links when locating application\0".as_ptr() as *const c_char,
                )));
            }
            return io_result_mk_ok(lean_mk_string(buf2.as_ptr() as *const c_char));
        }
        #[cfg(all(not(target_os = "windows"), not(target_os = "macos")))]
        {
            let path = format!("/proc/{}/exe", libc_getpid());
            let cpath = std::ffi::CString::new(path).unwrap();
            let mut dest = [0u8; PATH_MAX];
            if libc_readlink(cpath.as_ptr(), dest.as_mut_ptr() as *mut c_char, PATH_MAX - 1) == -1 {
                return io_result_mk_error_obj(lean_mk_io_user_error(lean_mk_ascii_string_unchecked(
                    b"failed to locate application\0".as_ptr() as *const c_char,
                )));
            }
            return io_result_mk_ok(lean_mk_string(dest.as_ptr() as *const c_char));
        }
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_io_current_dir() -> *mut LeanObject {
        let mut buf = [0u8; PATH_MAX];
        let cwd = libc_getcwd(buf.as_mut_ptr() as *mut c_char, PATH_MAX);
        if !cwd.is_null() {
            io_result_mk_ok(lean_mk_string(cwd))
        } else {
            io_result_mk_error_obj(lean_mk_io_user_error(lean_mk_ascii_string_unchecked(
                b"failed to retrieve current working directory\0".as_ptr() as *const c_char,
            )))
        }
    }

    // -----------------------------------------------------------------------
    // ST ref primitives
    // -----------------------------------------------------------------------
    #[no_mangle]
    pub unsafe extern "C" fn lean_st_mk_ref(a: *mut LeanObject) -> *mut LeanObject {
        extern "C" { fn lean_alloc_small_object(sz: usize) -> *mut LeanObject; }
        // lean_ref_object = { lean_object header; lean_object* m_value }
        let o = lean_alloc_small_object(core::mem::size_of::<LeanRefObject>());
        lean_set_st_header(o, LEAN_REF_TAG_IO, 0);
        (*(o as *mut LeanRefObject)).m_value = a;
        o
    }

    #[repr(C)]
    struct LeanRefObject {
        header: LeanObject,
        m_value: *mut LeanObject,
    }

    #[inline(always)]
    unsafe fn ref_maybe_mt(rf: *const LeanObject) -> bool {
        lean_is_mt(rf) || lean_is_persistent(rf)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_st_ref_get(rf: *mut LeanObject) -> *mut LeanObject {
        if ref_maybe_mt(rf) {
            extern "C" { fn lean_io_ref_get_mt_cxx(rf: *mut LeanObject) -> *mut LeanObject; }
            lean_io_ref_get_mt_cxx(rf)
        } else {
            let val = (*(rf as *mut LeanRefObject)).m_value;
            lean_inc(val);
            val
        }
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_st_ref_take(rf: *mut LeanObject) -> *mut LeanObject {
        if ref_maybe_mt(rf) {
            extern "C" { fn lean_io_ref_take_mt_cxx(rf: *mut LeanObject) -> *mut LeanObject; }
            lean_io_ref_take_mt_cxx(rf)
        } else {
            let val = (*(rf as *mut LeanRefObject)).m_value;
            (*(rf as *mut LeanRefObject)).m_value = null_mut();
            val
        }
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_st_ref_set(rf: *mut LeanObject, a: *mut LeanObject) -> *mut LeanObject {
        if ref_maybe_mt(rf) {
            lean_mark_mt(a);
            extern "C" { fn lean_io_ref_set_mt_cxx(rf: *mut LeanObject, a: *mut LeanObject); }
            lean_io_ref_set_mt_cxx(rf, a);
        } else {
            let old = (*(rf as *mut LeanRefObject)).m_value;
            if !old.is_null() { lean_dec(old); }
            (*(rf as *mut LeanRefObject)).m_value = a;
        }
        lean_box(0)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_st_ref_swap(rf: *mut LeanObject, a: *mut LeanObject) -> *mut LeanObject {
        if ref_maybe_mt(rf) {
            lean_mark_mt(a);
            extern "C" { fn lean_io_ref_swap_mt_cxx(rf: *mut LeanObject, a: *mut LeanObject) -> *mut LeanObject; }
            lean_io_ref_swap_mt_cxx(rf, a)
        } else {
            let old = (*(rf as *mut LeanRefObject)).m_value;
            if old.is_null() { lean_internal_panic(b"null reference read\0".as_ptr() as *const c_char); }
            (*(rf as *mut LeanRefObject)).m_value = a;
            old
        }
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_st_ref_ptr_eq(ref1: *mut LeanObject, ref2: *mut LeanObject) -> u8 {
        (lean_to_ref(ref1) == lean_to_ref(ref2)) as u8
    }

    // -----------------------------------------------------------------------
    // Task / IO task combinators
    // -----------------------------------------------------------------------
    #[no_mangle]
    pub unsafe extern "C" fn lean_io_as_task(act: *mut LeanObject, prio: *mut LeanObject) -> *mut LeanObject {
        lean_io_as_task_core(act, lean_unbox(prio))
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_io_map_task(
        f: *mut LeanObject,
        t: *mut LeanObject,
        prio: *mut LeanObject,
        sync: u8,
    ) -> *mut LeanObject {
        lean_io_map_task_core(f, t, lean_unbox(prio), sync)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_io_bind_task(
        t: *mut LeanObject,
        f: *mut LeanObject,
        prio: *mut LeanObject,
        sync: u8,
    ) -> *mut LeanObject {
        lean_io_bind_task_core(t, f, lean_unbox(prio), sync)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_io_check_canceled() -> u8 {
        lean_io_check_canceled_core() as u8
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_io_cancel(t: *mut LeanObject) -> *mut LeanObject {
        lean_io_cancel_core(t);
        lean_box(0)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_io_get_task_state(t: *mut LeanObject) -> u8 {
        lean_io_get_task_state_core(t)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_io_wait(t: *mut LeanObject) -> *mut LeanObject {
        lean_task_get_own(t)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_io_wait_any(task_list: *mut LeanObject) -> *mut LeanObject {
        let t = lean_io_wait_any_core(task_list);
        let v = lean_task_get(t);
        lean_inc(v);
        v
    }

    // -----------------------------------------------------------------------
    // lean_io_exit / lean_io_force_exit
    // -----------------------------------------------------------------------
    #[no_mangle]
    pub unsafe extern "C" fn lean_io_exit(code: u8) -> *mut LeanObject {
        extern "C" { fn exit(code: c_int) -> !; }
        exit(code as c_int)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_io_force_exit(code: u8) -> *mut LeanObject {
        std::process::exit(code as i32)
    }

    // -----------------------------------------------------------------------
    // lean_runtime_mark_multi_threaded / lean_runtime_mark_persistent
    // -----------------------------------------------------------------------
    #[no_mangle]
    pub unsafe extern "C" fn lean_runtime_mark_multi_threaded(a: *mut LeanObject) -> *mut LeanObject {
        lean_mark_mt(a);
        a
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_runtime_mark_persistent(a: *mut LeanObject) -> *mut LeanObject {
        if runtime_trace_enabled("LEAN_TRACE_MARK_PERSISTENT") {
            eprintln!("lean_runtime_mark_persistent arg={:p}", a);
        }
        lean_mark_persistent(a);
        a
    }

    // -----------------------------------------------------------------------
    // lean_runtime_forget
    // -----------------------------------------------------------------------
    #[no_mangle]
    pub unsafe extern "C" fn lean_runtime_forget(o: *mut LeanObject) -> *mut LeanObject {
        // Under LSAN, suppress leak report. Shim handles the ASan call if needed.
        extern "C" {
            #[cfg(feature = "lsan")]
            fn __lsan_ignore_object(o: *const c_void);
        }
        #[cfg(feature = "lsan")]
        __lsan_ignore_object(o as *const c_void);
        lean_box(0)
    }

    // -----------------------------------------------------------------------
    // lean_option_get_or_block
    // -----------------------------------------------------------------------
    #[no_mangle]
    pub unsafe extern "C" fn lean_option_get_or_block(o_opt: *mut LeanObject) -> *mut LeanObject {
        lean_io_option_get_or_block_c(o_opt)
    }

    // -----------------------------------------------------------------------
    // lean_windows_get_next_transition / lean_get_windows_local_timezone_id_at
    // (Windows-only; non-Windows stubs return an error)
    // -----------------------------------------------------------------------
    extern "C" {
        #[link_name = "lean_io_shim_windows_get_next_transition"]
        fn lean_io_shim_windows_get_next_transition_cxx(
            tz: *mut LeanObject,
            tm: u64,
            default_time: u8,
        ) -> *mut LeanObject;
        #[link_name = "lean_io_shim_get_windows_local_timezone_id_at"]
        fn lean_io_shim_get_windows_local_timezone_id_at_cxx(tm: u64) -> *mut LeanObject;
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_windows_get_next_transition(
        timezone_str: *mut LeanObject,
        tm_obj: u64,
        default_time: u8,
    ) -> *mut LeanObject {
        lean_io_shim_windows_get_next_transition_cxx(timezone_str, tm_obj, default_time)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_get_windows_local_timezone_id_at(tm: u64) -> *mut LeanObject {
        lean_io_shim_get_windows_local_timezone_id_at_cxx(tm)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_io_ref_get_mt(rf: *mut LeanObject) -> *mut LeanObject {
        let val = (*(rf as *mut LeanRefObject)).m_value;
        lean_inc(val);
        val
    }

    #[export_name = "lean_io_ref_get_mt_cxx"]
    pub unsafe extern "C" fn lean_io_ref_get_mt_cxx_export(
        rf: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_io_ref_get_mt(rf)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_io_ref_take_mt(rf: *mut LeanObject) -> *mut LeanObject {
        let val = (*(rf as *mut LeanRefObject)).m_value;
        (*(rf as *mut LeanRefObject)).m_value = null_mut();
        val
    }

    #[export_name = "lean_io_ref_take_mt_cxx"]
    pub unsafe extern "C" fn lean_io_ref_take_mt_cxx_export(
        rf: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_io_ref_take_mt(rf)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_io_ref_set_mt(rf: *mut LeanObject, a: *mut LeanObject) {
        let old = (*(rf as *mut LeanRefObject)).m_value;
        if !old.is_null() {
            lean_dec(old);
        }
        (*(rf as *mut LeanRefObject)).m_value = a;
    }

    #[export_name = "lean_io_ref_set_mt_cxx"]
    pub unsafe extern "C" fn lean_io_ref_set_mt_cxx_export(
        rf: *mut LeanObject,
        a: *mut LeanObject,
    ) {
        lean_io_ref_set_mt(rf, a)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_io_ref_swap_mt(
        rf: *mut LeanObject,
        a: *mut LeanObject,
    ) -> *mut LeanObject {
        let old = (*(rf as *mut LeanRefObject)).m_value;
        (*(rf as *mut LeanRefObject)).m_value = a;
        old
    }

    #[export_name = "lean_io_ref_swap_mt_cxx"]
    pub unsafe extern "C" fn lean_io_ref_swap_mt_cxx_export(
        rf: *mut LeanObject,
        a: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_io_ref_swap_mt(rf, a)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_io_shim_uv_stat(
        path: *const c_char,
        out: *mut UvStatBuf,
    ) -> c_int {
        let mut st = core::mem::MaybeUninit::<libc::stat>::uninit();
        if libc::stat(path, st.as_mut_ptr()) != 0 {
            return -(*libc::__errno_location());
        }
        let st = st.assume_init();
        (*out).st_dev = st.st_dev as u64;
        (*out).st_mode = st.st_mode as u64;
        (*out).st_nlink = st.st_nlink as u64;
        (*out).st_uid = st.st_uid as u64;
        (*out).st_gid = st.st_gid as u64;
        (*out).st_rdev = st.st_rdev as u64;
        (*out).st_ino = st.st_ino as u64;
        (*out).st_size = st.st_size as u64;
        (*out).st_blksize = st.st_blksize as u64;
        (*out).st_blocks = st.st_blocks as u64;
        (*out).st_flags = 0;
        (*out).st_gen = 0;
        (*out).st_atim = UvTimespec { tv_sec: st.st_atime, tv_nsec: 0 };
        (*out).st_mtim = UvTimespec { tv_sec: st.st_mtime, tv_nsec: 0 };
        (*out).st_ctim = UvTimespec { tv_sec: st.st_ctime, tv_nsec: 0 };
        (*out).st_birthtim = UvTimespec { tv_sec: 0, tv_nsec: 0 };
        0
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_io_shim_uv_lstat(
        path: *const c_char,
        out: *mut UvStatBuf,
    ) -> c_int {
        let mut st = core::mem::MaybeUninit::<libc::stat>::uninit();
        if libc::lstat(path, st.as_mut_ptr()) != 0 {
            return -(*libc::__errno_location());
        }
        let st = st.assume_init();
        (*out).st_dev = st.st_dev as u64;
        (*out).st_mode = st.st_mode as u64;
        (*out).st_nlink = st.st_nlink as u64;
        (*out).st_uid = st.st_uid as u64;
        (*out).st_gid = st.st_gid as u64;
        (*out).st_rdev = st.st_rdev as u64;
        (*out).st_ino = st.st_ino as u64;
        (*out).st_size = st.st_size as u64;
        (*out).st_blksize = st.st_blksize as u64;
        (*out).st_blocks = st.st_blocks as u64;
        (*out).st_flags = 0;
        (*out).st_gen = 0;
        (*out).st_atim = UvTimespec { tv_sec: st.st_atime, tv_nsec: 0 };
        (*out).st_mtim = UvTimespec { tv_sec: st.st_mtime, tv_nsec: 0 };
        (*out).st_ctim = UvTimespec { tv_sec: st.st_ctime, tv_nsec: 0 };
        (*out).st_birthtim = UvTimespec { tv_sec: 0, tv_nsec: 0 };
        0
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_io_shim_uv_link(
        orig: *const c_char,
        link: *const c_char,
    ) -> c_int {
        if libc::link(orig, link) == 0 {
            0
        } else {
            -(*libc::__errno_location())
        }
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_io_shim_uv_unlink(path: *const c_char) -> c_int {
        if libc::unlink(path) == 0 {
            0
        } else {
            -(*libc::__errno_location())
        }
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_io_shim_uv_os_tmpdir(
        buf: *mut c_char,
        sz: *mut usize,
    ) -> c_int {
        let tmp = std::env::temp_dir();
        #[cfg(unix)]
        let bytes = std::os::unix::ffi::OsStrExt::as_bytes(tmp.as_os_str());
        #[cfg(not(unix))]
        let bytes = {
            let tmp = tmp.to_string_lossy();
            tmp.as_bytes()
        };
        if bytes.len() >= *sz {
            return -(*libc::__errno_location());
        }
        core::ptr::copy_nonoverlapping(bytes.as_ptr(), buf as *mut u8, bytes.len());
        *buf.add(bytes.len()) = 0;
        *sz = bytes.len();
        0
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_io_shim_uv_fs_mkstemp(
        pattern: *const c_char,
        out_fd: *mut c_int,
        out_path: *mut c_char,
        path_cap: usize,
    ) -> c_int {
        let c_pattern = core::ffi::CStr::from_ptr(pattern);
        let mut path = c_pattern.to_bytes_with_nul().to_vec();
        if path.len() > path_cap {
            return -(*libc::__errno_location());
        }
        let fd = libc::mkstemp(path.as_mut_ptr() as *mut c_char);
        if fd < 0 {
            return -(*libc::__errno_location());
        }
        *out_fd = fd;
        core::ptr::copy_nonoverlapping(path.as_ptr(), out_path as *mut u8, path.len());
        0
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_io_shim_uv_fs_mkdtemp(
        pattern: *const c_char,
        out_path: *mut c_char,
        path_cap: usize,
    ) -> c_int {
        let c_pattern = core::ffi::CStr::from_ptr(pattern);
        let mut path = c_pattern.to_bytes_with_nul().to_vec();
        if path.len() > path_cap {
            return -(*libc::__errno_location());
        }
        let out = libc::mkdtemp(path.as_mut_ptr() as *mut c_char);
        if out.is_null() {
            return -(*libc::__errno_location());
        }
        core::ptr::copy_nonoverlapping(path.as_ptr(), out_path as *mut u8, path.len());
        0
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_io_shim_windows_get_next_transition(
        _tz: *mut LeanObject,
        _tm: u64,
        _default_time: u8,
    ) -> *mut LeanObject {
        lean_box(0)
    }

    #[no_mangle]
    pub unsafe extern "C" fn lean_io_shim_get_windows_local_timezone_id_at(
        _tm: u64,
    ) -> *mut LeanObject {
        lean_box(0)
    }

    #[export_name = "libc_strlen"]
    pub unsafe extern "C" fn libc_strlen_export(s: *const c_char) -> usize {
        libc::strlen(s)
    }

    #[export_name = "libc_strerror"]
    pub unsafe extern "C" fn libc_strerror_export(errnum: c_int) -> *const c_char {
        libc::strerror(errnum)
    }

    #[export_name = "libc_fclose"]
    pub unsafe extern "C" fn libc_fclose_export(fp: *mut libc_FILE) -> c_int {
        libc::fclose(fp as *mut libc::FILE)
    }

    #[export_name = "libc_fflush"]
    pub unsafe extern "C" fn libc_fflush_export(fp: *mut libc_FILE) -> c_int {
        libc::fflush(fp as *mut libc::FILE)
    }

    #[export_name = "libc_fseek"]
    pub unsafe extern "C" fn libc_fseek_export(fp: *mut libc_FILE, off: i64, whence: c_int) -> c_int {
        libc::fseek(fp as *mut libc::FILE, off, whence)
    }

    #[export_name = "libc_fread"]
    pub unsafe extern "C" fn libc_fread_export(
        buf: *mut u8,
        sz: usize,
        n: usize,
        fp: *mut libc_FILE,
    ) -> usize {
        libc::fread(buf as *mut c_void, sz, n, fp as *mut libc::FILE)
    }

    #[export_name = "libc_fwrite"]
    pub unsafe extern "C" fn libc_fwrite_export(
        buf: *const u8,
        sz: usize,
        n: usize,
        fp: *mut libc_FILE,
    ) -> usize {
        libc::fwrite(buf as *const c_void, sz, n, fp as *mut libc::FILE)
    }

    #[export_name = "libc_feof"]
    pub unsafe extern "C" fn libc_feof_export(fp: *mut libc_FILE) -> c_int {
        libc::feof(fp as *mut libc::FILE)
    }

    #[export_name = "libc_ferror"]
    pub unsafe extern "C" fn libc_ferror_export(fp: *mut libc_FILE) -> c_int {
        libc::ferror(fp as *mut libc::FILE)
    }

    #[export_name = "libc_clearerr"]
    pub unsafe extern "C" fn libc_clearerr_export(fp: *mut libc_FILE) {
        libc::clearerr(fp as *mut libc::FILE)
    }

    #[export_name = "libc_isatty"]
    pub unsafe extern "C" fn libc_isatty_export(fd: c_int) -> c_int {
        libc::isatty(fd)
    }

    #[export_name = "libc_fileno"]
    pub unsafe extern "C" fn libc_fileno_export(fp: *mut libc_FILE) -> c_int {
        libc::fileno(fp as *mut libc::FILE)
    }

    #[export_name = "libc_ftruncate"]
    pub unsafe extern "C" fn libc_ftruncate_export(fd: c_int, len: i64) -> c_int {
        libc::ftruncate(fd, len)
    }

    #[export_name = "libc_ftello"]
    pub unsafe extern "C" fn libc_ftello_export(fp: *mut libc_FILE) -> i64 {
        libc::ftello(fp as *mut libc::FILE)
    }

    #[export_name = "libc_getcwd"]
    pub unsafe extern "C" fn libc_getcwd_export(buf: *mut c_char, sz: usize) -> *mut c_char {
        libc::getcwd(buf, sz)
    }

    #[export_name = "libc_open"]
    pub unsafe extern "C" fn libc_open_export(path: *const c_char, flags: c_int, mode: c_int) -> c_int {
        libc::open(path, flags, mode)
    }

    #[export_name = "libc_fdopen"]
    pub unsafe extern "C" fn libc_fdopen_export(fd: c_int, mode: *const c_char) -> *mut libc_FILE {
        libc::fdopen(fd, mode) as *mut libc_FILE
    }

    #[export_name = "libc_mkdir"]
    pub unsafe extern "C" fn libc_mkdir_export(path: *const c_char, mode: c_int) -> c_int {
        libc::mkdir(path, mode as libc::mode_t)
    }

    #[export_name = "libc_rmdir"]
    pub unsafe extern "C" fn libc_rmdir_export(path: *const c_char) -> c_int {
        libc::rmdir(path)
    }

    #[export_name = "libc_rename"]
    pub unsafe extern "C" fn libc_rename_export(from: *const c_char, to: *const c_char) -> c_int {
        libc::rename(from, to)
    }

    #[export_name = "libc_fdopen_r"]
    pub unsafe extern "C" fn libc_fdopen_r_export(fd: c_int) -> *mut libc_FILE {
        libc::fdopen(fd, b"r+\0".as_ptr() as *const c_char) as *mut libc_FILE
    }

    #[export_name = "libc_chmod"]
    pub unsafe extern "C" fn libc_chmod_export(path: *const c_char, mode: c_uint) -> c_int {
        libc::chmod(path, mode as libc::mode_t)
    }

    #[export_name = "libc_flock"]
    pub unsafe extern "C" fn libc_flock_export(fd: c_int, op: c_int) -> c_int {
        libc::flock(fd, op)
    }

    #[export_name = "libc_getc_unlocked"]
    pub unsafe extern "C" fn libc_getc_unlocked_export(fp: *mut libc_FILE) -> c_int {
        extern "C" {
            fn getc_unlocked(fp: *mut libc::FILE) -> c_int;
        }
        getc_unlocked(fp as *mut libc::FILE)
    }

    #[export_name = "libc_flockfile"]
    pub unsafe extern "C" fn libc_flockfile_export(fp: *mut libc_FILE) {
        extern "C" {
            fn flockfile(fp: *mut libc::FILE);
        }
        flockfile(fp as *mut libc::FILE)
    }

    #[export_name = "libc_funlockfile"]
    pub unsafe extern "C" fn libc_funlockfile_export(fp: *mut libc_FILE) {
        extern "C" {
            fn funlockfile(fp: *mut libc::FILE);
        }
        funlockfile(fp as *mut libc::FILE)
    }

    #[export_name = "libc_realpath"]
    pub unsafe extern "C" fn libc_realpath_export(path: *const c_char, out: *mut c_char) -> *mut c_char {
        libc::realpath(path, out)
    }

    #[export_name = "libc_getpid"]
    pub unsafe extern "C" fn libc_getpid_export() -> i32 {
        libc::getpid()
    }

    #[export_name = "libc_readlink"]
    pub unsafe extern "C" fn libc_readlink_export(path: *const c_char, buf: *mut c_char, bufsz: usize) -> isize {
        libc::readlink(path, buf, bufsz)
    }

    #[export_name = "libc_read_urandom"]
    pub unsafe extern "C" fn libc_read_urandom_export(buf: *mut u8, n: usize) -> isize {
        let fd = libc::open(c"/dev/urandom".as_ptr(), libc::O_RDONLY);
        if fd < 0 {
            return -1;
        }
        let read = libc::read(fd, buf as *mut c_void, n);
        libc::close(fd);
        read
    }

    #[export_name = "libc_fdopen_with_mode"]
    pub unsafe extern "C" fn libc_fdopen_with_mode_export(fd: c_int, mode: *const c_char) -> *mut libc_FILE {
        libc::fdopen(fd, mode) as *mut libc_FILE
    }

    #[export_name = "libc_opendir"]
    pub unsafe extern "C" fn libc_opendir_export(path: *const c_char) -> *mut c_void {
        libc::opendir(path) as *mut c_void
    }

    #[export_name = "libc_readdir"]
    pub unsafe extern "C" fn libc_readdir_export(dp: *mut c_void) -> *mut DirentC {
        libc::readdir(dp as *mut libc::DIR) as *mut DirentC
    }

    #[export_name = "libc_closedir"]
    pub unsafe extern "C" fn libc_closedir_export(dp: *mut c_void) -> c_int {
        libc::closedir(dp as *mut libc::DIR)
    }

    // -----------------------------------------------------------------------
    // initialize_io / finalize_io
    // -----------------------------------------------------------------------
    #[export_name = "_ZN4lean13initialize_ioEv"]
    pub unsafe fn initialize_io() {
        ensure_io_shim_init();
    }

    #[export_name = "_ZN4lean11finalize_ioEv"]
    pub unsafe fn finalize_io() {}

    // -----------------------------------------------------------------------
    // Module init pair (called from the main initialize_runtime / finalize)
    // -----------------------------------------------------------------------
    // Wrapped as #[no_mangle] so C++ can call lean::initialize_io() indirectly.
    // The lean:: namespace mangling is handled via the existing C++ shim:
    //   extern "C" void lean_initialize_io() { lean::initialize_io(); }
} // mod runtime_io_impl

// Re-export initialize_io / finalize_io for the runtime init sequence
pub(crate) use runtime_io_impl::{initialize_io as initialize_io_module,
                                   finalize_io as finalize_io_module};
