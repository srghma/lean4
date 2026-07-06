/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

mod runtime_io_stream_impl {
    use crate::*;
    use core::ffi::{CStr, c_char, c_int, c_long, c_uchar, c_uint, c_void};
    use core::cell::Cell;
    use libc_stdhandle::{stderr as libc_stderr, stdin as libc_stdin, stdout as libc_stdout};

    unsafe extern "C" {
        fn lean_stream_of_handle(h: *mut LeanObject) -> *mut LeanObject;
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

    pub unsafe fn lean_get_stdin() -> *mut LeanObject {
        CURRENT_STDIN.with(|stream| {
            let value = stream.get(STREAM_STDIN);
            lean_inc(value);
            value
        })
    }

    pub unsafe fn lean_get_stdout() -> *mut LeanObject {
        CURRENT_STDOUT.with(|stream| {
            let value = stream.get(STREAM_STDOUT);
            lean_inc(value);
            value
        })
    }

    pub unsafe fn lean_get_stderr() -> *mut LeanObject {
        CURRENT_STDERR.with(|stream| {
            let value = stream.get(STREAM_STDERR);
            lean_inc(value);
            value
        })
    }

    pub unsafe fn lean_get_set_stdin(handle: *mut LeanObject) -> *mut LeanObject {
        CURRENT_STDIN.with(|stream| stream.set(STREAM_STDIN, handle))
    }

    pub unsafe fn lean_get_set_stdout(handle: *mut LeanObject) -> *mut LeanObject {
        CURRENT_STDOUT.with(|stream| stream.set(STREAM_STDOUT, handle))
    }

    pub unsafe fn lean_get_set_stderr(handle: *mut LeanObject) -> *mut LeanObject {
        CURRENT_STDERR.with(|stream| stream.set(STREAM_STDERR, handle))
    }
    pub fn finalize_io() {}
}

#[allow(unused_imports)]
pub(crate) use runtime_io_stream_impl::io_wrap_handle;
