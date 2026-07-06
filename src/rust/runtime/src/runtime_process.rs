/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Port of src/runtime/process.cpp to Rust.
Supports Unix (Linux + macOS). On Windows the C++ file is still compiled.
*/

// NOTE: This file is include!()-ed from lib.rs so all helpers defined there
// are in scope: lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set_uint8,
// lean_array_get, lean_array_size, lean_string_cstr, lean_box,
// lean_is_scalar, lean_inc, lean_dec, lean_runtime_alloc_ctor,
// lean_runtime_ctor_set, lean_io_result_mk_ok, lean_io_result_mk_error,
// lean_mk_string, lean_decode_io_error, lean_mk_io_user_error, etc.

mod runtime_process_impl {
    use crate::*;
    use crate::runtime_io_stream::io_wrap_handle;
    use core::ffi::c_int;
    use core::ptr::null_mut;

    // ─── additional externals needed for this module ──────────────────────────

    unsafe extern "C" {
        fn lean_mk_string_from_bytes(s: *const c_char, n: Size) -> *mut LeanObject;
    }

    // lean_box_uint32 is a static inline in lean.h; implement it directly in Rust
    // On 64-bit systems (our target), UInt32 is boxed as a tagged scalar: lean_box(v)
    unsafe fn lean_box_uint32_rust(v: u32) -> *mut LeanObject {
        lean_box(v as usize)
    }

    // ─── helpers ──────────────────────────────────────────────────────────────

    unsafe fn io_result_ok(a: *mut LeanObject) -> *mut LeanObject {
        lean_io_result_mk_ok(a)
    }

    unsafe fn io_result_err_errno(errnum: c_int) -> *mut LeanObject {
        lean_io_result_mk_error(lean_decode_io_error(errnum, null_mut()))
    }

    // lean_ctor_get_uint32 is not in lib.rs – define locally
    unsafe fn lean_ctor_get_uint32(obj: *mut LeanObject, byte_offset: usize) -> u32 {
        // duplicate in undefined at line 46 (🔁)
        (obj.add(1) as *mut u8)
            .add(byte_offset)
            .cast::<u32>()
            .read_unaligned()
    }

    unsafe fn lean_ctor_set_uint32(obj: *mut LeanObject, byte_offset: usize, v: u32) {
        // duplicate in undefined at line 53 (🔁)
        (obj.add(1) as *mut u8)
            .add(byte_offset)
            .cast::<u32>()
            .write_unaligned(v);
    }

    // lean_ctor_set (set object field) is not in lib.rs – define locally
    unsafe fn lean_ctor_set(obj: *mut LeanObject, idx: usize, val: *mut LeanObject) {
        // duplicate in undefined at line 61 (🔁)
        (obj.add(1) as *mut *mut LeanObject).add(idx).write(val);
    }

    // Lean constructor allocation forwarding to lean_runtime_alloc_ctor
    unsafe fn lean_alloc_ctor(tag: u32, num_objs: usize, scalar_size: usize) -> *mut LeanObject {
        // duplicate in undefined at line 66 (🔁)
        lean_runtime_alloc_ctor(tag as c_uint, num_objs as c_uint, scalar_size as c_uint)
    }

    // Option helpers
    unsafe fn mk_option_none() -> *mut LeanObject {
        lean_box(0)
    }
    unsafe fn mk_option_some(v: *mut LeanObject) -> *mut LeanObject {
        let r = lean_alloc_ctor(1, 1, 0);
        lean_runtime_ctor_set(r, 0, v);
        r
    }

    // ─── layout constants for IO.Process.Child ───────────────────────────────
    // The child struct:
    //   3 object fields: stdin, stdout, stderr
    //   then scalars:    u32 pid   (offset = 3 * sizeof(*))
    //                    u8  setsid (offset = 3 * sizeof(*) + 4)
    const PTR_SIZE: usize = core::mem::size_of::<*mut LeanObject>();
    const CHILD_PID_OFFSET: usize = 3 * PTR_SIZE;
    const CHILD_SETSID_OFFSET: usize = 3 * PTR_SIZE + 4; // after u32

    // ─── stdio configuration ──────────────────────────────────────────────────

    #[derive(PartialEq, Copy, Clone)]
    enum StdioMode {
        Piped = 0,
        Inherit = 1,
        Null = 2,
    }

    impl StdioMode {
        fn from_u8(v: u8) -> Self {
            match v {
                0 => StdioMode::Piped,
                1 => StdioMode::Inherit,
                _ => StdioMode::Null,
            }
        }
    }

    struct OwnedPipe {
        read_fd: c_int,
        write_fd: c_int,
    }

    fn setup_stdio(mode: StdioMode) -> Result<Option<OwnedPipe>, c_int> {
        match mode {
            StdioMode::Inherit | StdioMode::Null => Ok(None),
            StdioMode::Piped => {
                let mut fds = [0i32; 2];
                let ret = unsafe {
                    #[cfg(target_os = "macos")]
                    {
                        let r = libc::pipe(fds.as_mut_ptr());
                        if r == 0 {
                            libc::fcntl(fds[0], libc::F_SETFD, libc::FD_CLOEXEC);
                            libc::fcntl(fds[1], libc::F_SETFD, libc::FD_CLOEXEC);
                        }
                        r
                    }
                    #[cfg(not(target_os = "macos"))]
                    {
                        libc::pipe2(fds.as_mut_ptr(), libc::O_CLOEXEC)
                    }
                };
                if ret == -1 {
                    Err(unsafe { *libc::__errno_location() })
                } else {
                    Ok(Some(OwnedPipe {
                        read_fd: fds[0],
                        write_fd: fds[1],
                    }))
                }
            }
        }
    }

    // ─── lean_io_process_get_current_dir ─────────────────────────────────────

    #[cfg(unix)]
    pub unsafe fn lean_io_process_get_current_dir() -> *mut LeanObject {
        let mut buf = [0u8; libc::PATH_MAX as usize];
        let ret = libc::getcwd(buf.as_mut_ptr().cast(), buf.len());
        if !ret.is_null() {
            let len = libc::strlen(ret);
            let s = lean_mk_string_from_bytes(ret, len);
            io_result_ok(s)
        } else {
            io_result_err_errno(*libc::__errno_location())
        }
    }

    // ─── lean_io_process_set_current_dir ─────────────────────────────────────

    #[cfg(unix)]
    pub unsafe fn lean_io_process_set_current_dir(path: *mut LeanObject) -> *mut LeanObject {
        if libc::chdir(lean_string_cstr(path)) == 0 {
            io_result_ok(lean_box(0))
        } else {
            lean_io_result_mk_error(lean_decode_io_error(*libc::__errno_location(), path))
        }
    }

    // ─── lean_io_process_get_pid ──────────────────────────────────────────────

    #[cfg(unix)]
    pub unsafe fn lean_io_process_get_pid() -> u32 {
        libc::getpid() as u32
    }

    // ─── lean_io_get_tid ──────────────────────────────────────────────────────

    #[cfg(unix)]
    pub unsafe fn lean_io_get_tid() -> u64 {
        #[cfg(target_os = "macos")]
        {
            let mut tid: u64 = 0;
            libc::pthread_threadid_np(core::ptr::null_mut(), &mut tid);
            tid
        }
        #[cfg(all(target_os = "linux"))]
        {
            // SYS_gettid is available since Linux 2.4.11
            libc::syscall(libc::SYS_gettid) as u64
        }
        #[cfg(not(any(target_os = "macos", target_os = "linux")))]
        {
            0u64
        }
    }

    // ─── lean_io_process_child_wait ───────────────────────────────────────────

    #[cfg(unix)]
    pub unsafe fn lean_io_process_child_wait(
        _world: *mut LeanObject,
        child: *mut LeanObject,
    ) -> *mut LeanObject {
        let pid = lean_ctor_get_uint32(child, CHILD_PID_OFFSET) as libc::pid_t;
        let mut status: c_int = 0;
        if libc::waitpid(pid, &mut status, 0) == -1 {
            return io_result_err_errno(*libc::__errno_location());
        }
        let exit_code = if libc::WIFEXITED(status) {
            libc::WEXITSTATUS(status) as u32
        } else {
            // WIFSIGNALED – bash convention: 128 + signal
            128 + libc::WTERMSIG(status) as u32
        };
        io_result_ok(lean_box_uint32_rust(exit_code))
    }

    // ─── lean_io_process_child_try_wait ──────────────────────────────────────

    #[cfg(unix)]
    pub unsafe fn lean_io_process_child_try_wait(
        _world: *mut LeanObject,
        child: *mut LeanObject,
    ) -> *mut LeanObject {
        let pid = lean_ctor_get_uint32(child, CHILD_PID_OFFSET) as libc::pid_t;
        let mut status: c_int = 0;
        let ret = libc::waitpid(pid, &mut status, libc::WNOHANG);
        if ret == -1 {
            io_result_err_errno(*libc::__errno_location())
        } else if ret == 0 {
            io_result_ok(mk_option_none())
        } else {
            let exit_code = if libc::WIFEXITED(status) {
                libc::WEXITSTATUS(status) as u32
            } else {
                128 + libc::WTERMSIG(status) as u32
            };
            io_result_ok(mk_option_some(lean_box_uint32_rust(exit_code)))
        }
    }

    // ─── lean_io_process_child_kill ───────────────────────────────────────────

    #[cfg(unix)]
    pub unsafe fn lean_io_process_child_kill(
        _world: *mut LeanObject,
        child: *mut LeanObject,
    ) -> *mut LeanObject {
        let pid = lean_ctor_get_uint32(child, CHILD_PID_OFFSET) as libc::pid_t;
        let do_setsid = lean_ctor_get_uint8(child, CHILD_SETSID_OFFSET) != 0;
        let ret = if do_setsid {
            libc::killpg(pid, libc::SIGKILL)
        } else {
            libc::kill(pid, libc::SIGKILL)
        };
        if ret == -1 {
            io_result_err_errno(*libc::__errno_location())
        } else {
            io_result_ok(lean_box(0))
        }
    }

    // ─── lean_io_process_child_pid ────────────────────────────────────────────

    #[cfg(unix)]
    pub unsafe fn lean_io_process_child_pid(
        _world: *mut LeanObject,
        child: *mut LeanObject,
    ) -> u32 {
        lean_ctor_get_uint32(child, CHILD_PID_OFFSET)
    }

    // ─── lean_io_process_child_take_stdin ────────────────────────────────────
    // Returns (IO.Result (stdin_handle, new_child)):
    //   The original child had (stdin, stdout, stderr) + pid + setsid.
    //   We return the stdin handle and a new child without stdin (it becomes box(0)).
    // The new child (child2) omits the setsid flag: scalar_size = sizeof(u32) only.

    #[cfg(unix)]
    pub unsafe fn lean_io_process_child_take_stdin(
        _world: *mut LeanObject,
        lchild: *mut LeanObject,
    ) -> *mut LeanObject {
        let pid = lean_ctor_get_uint32(lchild, CHILD_PID_OFFSET);

        // Build child2 = constructor{ stdin=box(0), stdout, stderr } + scalar u32 pid
        let stdout = lean_ctor_get(lchild, 1);
        let stderr = lean_ctor_get(lchild, 2);
        lean_inc(stdout);
        lean_inc(stderr);

        let child2 = lean_alloc_ctor(0, 3, core::mem::size_of::<u32>());
        lean_ctor_set(child2, 0, lean_box(0));
        lean_ctor_set(child2, 1, stdout);
        lean_ctor_set(child2, 2, stderr);
        lean_ctor_set_uint32(child2, 3 * PTR_SIZE, pid);

        // Extract stdin from original child
        let stdin_obj = lean_ctor_get(lchild, 0);
        lean_inc(stdin_obj);

        // Build pair: constructor{ stdin_obj, child2 }
        let pair = lean_alloc_ctor(0, 2, 0);
        lean_ctor_set(pair, 0, stdin_obj);
        lean_ctor_set(pair, 1, child2);

        lean_dec(lchild);

        io_result_ok(pair)
    }

    // ─── spawn helper ─────────────────────────────────────────────────────────

    #[cfg(unix)]
    unsafe fn spawn(
        proc_name: *const c_char,
        lean_args: *mut LeanObject, // Array String
        stdin_mode: StdioMode,
        stdout_mode: StdioMode,
        stderr_mode: StdioMode,
        cwd_opt: *mut LeanObject, // Option String
        env_arr: *mut LeanObject, // Array (String × Option String)
        inherit_env: bool,
        do_setsid: bool,
    ) -> *mut LeanObject {
        let stdin_pipe = match setup_stdio(stdin_mode) {
            Ok(p) => p,
            Err(e) => return io_result_err_errno(e),
        };
        let stdout_pipe = match setup_stdio(stdout_mode) {
            Ok(p) => p,
            Err(e) => return io_result_err_errno(e),
        };
        let stderr_pipe = match setup_stdio(stderr_mode) {
            Ok(p) => p,
            Err(e) => return io_result_err_errno(e),
        };

        // Build argv via strdup (must not allocate between fork and exec for ASAN)
        let args_size = lean_array_size(lean_args);
        let mut pargs: Vec<*mut libc::c_char> = Vec::with_capacity(args_size + 2);
        pargs.push(libc::strdup(proc_name));
        for i in 0..args_size {
            let arg = lean_array_get(lean_args, i);
            pargs.push(libc::strdup(lean_string_cstr(arg)));
        }
        pargs.push(null_mut());

        let pid = libc::fork();

        if pid == 0 {
            // ── child process ─────────────────────────────────────────────────

            if !inherit_env {
                #[cfg(target_os = "macos")]
                {
                    // On macOS, environ is a global pointer
                    unsafe extern "C" {
                        static mut environ: *mut *mut libc::c_char;
                    }
                    environ = null_mut();
                }
                #[cfg(not(target_os = "macos"))]
                {
                    unsafe {
                        libc::clearenv();
                    }
                }
            }

            // Apply env entries: Array (String × Option String)
            let env_size = lean_array_size(env_arr);
            for i in 0..env_size {
                let entry = lean_array_get(env_arr, i);
                // Pair: field 0 = key String, field 1 = Option String
                let key = lean_ctor_get(entry, 0);
                let val_opt = lean_ctor_get(entry, 1);
                if lean_is_scalar(val_opt) || lean_obj_tag(val_opt) == 0 {
                    // None (tag 0 as scalar box(0))
                    libc::unsetenv(lean_string_cstr(key));
                } else {
                    // Some(val): tag 1, field 0 = the string
                    let val = lean_ctor_get(val_opt, 0);
                    libc::setenv(lean_string_cstr(key), lean_string_cstr(val), 1);
                }
            }

            // stdin redirection
            if let Some(ref p) = stdin_pipe {
                libc::dup2(p.read_fd, libc::STDIN_FILENO);
                libc::close(p.write_fd);
            } else if stdin_mode == StdioMode::Null {
                let fd = libc::open(b"/dev/null\0".as_ptr().cast(), libc::O_RDONLY);
                libc::dup2(fd, libc::STDIN_FILENO);
            }

            // stdout redirection
            if let Some(ref p) = stdout_pipe {
                libc::dup2(p.write_fd, libc::STDOUT_FILENO);
                libc::close(p.read_fd);
            } else if stdout_mode == StdioMode::Null {
                let fd = libc::open(b"/dev/null\0".as_ptr().cast(), libc::O_WRONLY);
                libc::dup2(fd, libc::STDOUT_FILENO);
            }

            // stderr redirection
            if let Some(ref p) = stderr_pipe {
                libc::dup2(p.write_fd, libc::STDERR_FILENO);
                libc::close(p.read_fd);
            } else if stderr_mode == StdioMode::Null {
                let fd = libc::open(b"/dev/null\0".as_ptr().cast(), libc::O_WRONLY);
                libc::dup2(fd, libc::STDERR_FILENO);
            }

            // chdir if cwd is Some
            // Option String: None = scalar box(0), Some(s) = non-scalar, tag 1
            if !lean_is_scalar(cwd_opt) && lean_obj_tag(cwd_opt) == 1 {
                let cwd_str = lean_ctor_get(cwd_opt, 0);
                if libc::chdir(lean_string_cstr(cwd_str)) < 0 {
                    let msg = b"could not change directory\n\0";
                    libc::write(libc::STDERR_FILENO, msg.as_ptr().cast(), msg.len() - 1);
                    libc::_exit(-1);
                }
            }

            if do_setsid {
                libc::setsid();
            }

            libc::execvp(pargs[0], pargs.as_ptr() as *const *const libc::c_char);

            let msg = b"could not execute external process\n\0";
            libc::write(libc::STDERR_FILENO, msg.as_ptr().cast(), msg.len() - 1);
            libc::_exit(-1);
        }

        // Parent: free argv strings
        for p in &pargs {
            if !p.is_null() {
                libc::free(*p as *mut _);
            }
        }

        if pid == -1 {
            return io_result_err_errno(*libc::__errno_location());
        }

        // ── parent: set up handles and build child Lean object ────────────────

        let mut parent_stdin: *mut LeanObject = lean_box(0);
        let mut parent_stdout: *mut LeanObject = lean_box(0);
        let mut parent_stderr: *mut LeanObject = lean_box(0);

        if let Some(p) = stdin_pipe {
            libc::close(p.read_fd);
            parent_stdin = io_wrap_handle(libc::fdopen(p.write_fd, c"w".as_ptr()));
        }
        if let Some(p) = stdout_pipe {
            libc::close(p.write_fd);
            parent_stdout = io_wrap_handle(libc::fdopen(p.read_fd, c"r".as_ptr()));
        }
        if let Some(p) = stderr_pipe {
            libc::close(p.write_fd);
            parent_stderr = io_wrap_handle(libc::fdopen(p.read_fd, c"r".as_ptr()));
        }

        // Child constructor: 3 object fields + u32 pid + u8 setsid
        let scalar_size = core::mem::size_of::<u32>() + core::mem::size_of::<u8>();
        let child = lean_alloc_ctor(0, 3, scalar_size);
        lean_ctor_set(child, 0, parent_stdin);
        lean_ctor_set(child, 1, parent_stdout);
        lean_ctor_set(child, 2, parent_stderr);
        lean_ctor_set_uint32(child, CHILD_PID_OFFSET, pid as u32);
        lean_ctor_set_uint8(child, CHILD_SETSID_OFFSET, do_setsid as u8);

        io_result_ok(child)
    }

    // ─── lean_io_process_spawn ────────────────────────────────────────────────
    // The Lean-side arguments are packed in a single constructor:
    //   obj[0]: stdio_cfg  (constructor with 3 u8 scalars: stdin_mode, stdout_mode, stderr_mode)
    //   obj[1]: proc_name  (String)
    //   obj[2]: args       (Array String)
    //   obj[3]: cwd        (Option String)
    //   obj[4]: env        (Array (String × Option String))
    //   scalar[5*PTR_SIZE + 0]: inherit_env (u8)
    //   scalar[5*PTR_SIZE + 1]: do_setsid   (u8)

    #[cfg(unix)]
    pub unsafe fn lean_io_process_spawn(args_: *mut LeanObject) -> *mut LeanObject {
        let stdio_cfg = lean_ctor_get(args_, 0);
        // stdio_cfg has 0 object fields; scalars start at base+sizeof(header)
        let stdin_mode = StdioMode::from_u8(lean_ctor_get_uint8(stdio_cfg, 0));
        let stdout_mode = StdioMode::from_u8(lean_ctor_get_uint8(stdio_cfg, 1));
        let stderr_mode = StdioMode::from_u8(lean_ctor_get_uint8(stdio_cfg, 2));

        // flush stdout when stdin is inherited (mirrors C++ code)
        if stdin_mode == StdioMode::Inherit {
            use std::io::Write;
            let _ = std::io::stdout().flush();
        }

        let proc_name_obj = lean_ctor_get(args_, 1);
        let lean_args = lean_ctor_get(args_, 2);
        let cwd_opt = lean_ctor_get(args_, 3);
        let env_arr = lean_ctor_get(args_, 4);
        let inherit_env = lean_ctor_get_uint8(args_, 5 * PTR_SIZE) != 0;
        let do_setsid = lean_ctor_get_uint8(args_, 5 * PTR_SIZE + 1) != 0;

        let result = spawn(
            lean_string_cstr(proc_name_obj),
            lean_args,
            stdin_mode,
            stdout_mode,
            stderr_mode,
            cwd_opt,
            env_arr,
            inherit_env,
            do_setsid,
        );

        lean_dec(args_);
        result
    }

    // ─── initialize / finalize ────────────────────────────────────────────────
    pub fn initialize_process() {}
    pub fn finalize_process() {}
}

pub use runtime_process_impl::*;
