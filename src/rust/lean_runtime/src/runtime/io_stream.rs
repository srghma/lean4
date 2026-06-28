/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

use crate::leanh::*;
use core::ffi::{c_char, c_int, c_long, c_uchar, c_uint, c_void, CStr};
use core::ptr;
use core::sync::atomic::{AtomicBool, AtomicI32, AtomicPtr, AtomicU32, Ordering};
use crate::runtime::*;

pub(crate) mod runtime_io_stream_impl {
    use super::*;
    use core::cell::Cell;

    static mut IO_HANDLE_EXTERNAL_CLASS: *mut LeanExternalClass = ptr::null_mut();
    static mut STREAM_STDIN: *mut LeanObject = ptr::null_mut();
    static mut STREAM_STDOUT: *mut LeanObject = ptr::null_mut();
    static mut STREAM_STDERR: *mut LeanObject = ptr::null_mut();

    extern "C" {
        static mut stdin: *mut libc::FILE;
        static mut stdout: *mut libc::FILE;
        static mut stderr: *mut libc::FILE;

        fn lean_stream_of_handle(h: *mut LeanObject) -> *mut LeanObject;
        fn signal(signum: libc::c_int, handler: usize) -> usize;
    }

    struct ThreadStream {
        value: Cell<*mut LeanObject>,
    }

    impl ThreadStream {
        const fn new() -> Self {
            Self {
                value: Cell::new(ptr::null_mut()),
            }
        }

        unsafe fn get(&self, default: *mut LeanObject) -> *mut LeanObject {
            let value = self.value.get();
            if value.is_null() {
                self.value.set(default);
                default
            } else {
                value
            }
        }

        unsafe fn set(&self, default: *mut LeanObject, value: *mut LeanObject) -> *mut LeanObject {
            let old = self.get(default);
            self.value.set(value);
            old
        }
    }

    impl Drop for ThreadStream {
        fn drop(&mut self) {
            let value = self.value.get();
            if !value.is_null() {
                unsafe { lean_dec(value) };
            }
        }
    }

    thread_local! {
        static CURRENT_STDIN: ThreadStream = const { ThreadStream::new() };
        static CURRENT_STDOUT: ThreadStream = const { ThreadStream::new() };
        static CURRENT_STDERR: ThreadStream = const { ThreadStream::new() };
    }

    unsafe fn io_handle_finalizer(handle: *mut c_void) {
        libc::fclose(handle.cast());
    }

    unsafe fn io_handle_foreach(_: *mut c_void, _: *mut LeanObject) {}

    pub unsafe fn io_wrap_handle(hfile: *mut libc::FILE) -> *mut LeanObject {
        lean_runtime_alloc_external(IO_HANDLE_EXTERNAL_CLASS, hfile.cast())
    }

    #[inline]
    pub(crate) unsafe fn lean_get_stdin() -> *mut LeanObject {
        CURRENT_STDIN.with(|stream| {
            let value = stream.get(STREAM_STDIN);
            lean_inc(value);
            value
        })
    }

    #[inline]
    pub(crate) unsafe fn lean_get_stdout() -> *mut LeanObject {
        CURRENT_STDOUT.with(|stream| {
            let value = stream.get(STREAM_STDOUT);
            lean_inc(value);
            value
        })
    }

    #[inline]
    pub(crate) unsafe fn lean_get_stderr() -> *mut LeanObject {
        CURRENT_STDERR.with(|stream| {
            let value = stream.get(STREAM_STDERR);
            lean_inc(value);
            value
        })
    }

    #[inline]
    pub(crate) unsafe fn lean_get_set_stdin(handle: *mut LeanObject) -> *mut LeanObject {
        CURRENT_STDIN.with(|stream| stream.set(STREAM_STDIN, handle))
    }

    #[inline]
    pub(crate) unsafe fn lean_get_set_stdout(handle: *mut LeanObject) -> *mut LeanObject {
        CURRENT_STDOUT.with(|stream| stream.set(STREAM_STDOUT, handle))
    }

    #[inline]
    pub(crate) unsafe fn lean_get_set_stderr(handle: *mut LeanObject) -> *mut LeanObject {
        CURRENT_STDERR.with(|stream| stream.set(STREAM_STDERR, handle))
    }

    pub unsafe fn initialize_io() {
        IO_HANDLE_EXTERNAL_CLASS =
            lean_register_external_class(Some(io_handle_finalizer), Some(io_handle_foreach));

        STREAM_STDOUT = lean_stream_of_handle(io_wrap_handle(stdout));
        lean_mark_persistent(STREAM_STDOUT);
        STREAM_STDERR = lean_stream_of_handle(io_wrap_handle(stderr));
        lean_mark_persistent(STREAM_STDERR);
        STREAM_STDIN = lean_stream_of_handle(io_wrap_handle(stdin));
        lean_mark_persistent(STREAM_STDIN);

        #[cfg(all(unix, not(target_os = "emscripten")))]
        {
            const SIGPIPE: libc::c_int = 13;
            const SIG_IGN: usize = 1;
            const SIG_ERR: usize = usize::MAX;
            assert_ne!(signal(SIGPIPE, SIG_IGN), SIG_ERR);
        }
    }

}
