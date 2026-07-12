use core::ffi::c_void;
use core::ptr;
use libc_stdhandle::{stderr as libc_stderr, stdin as libc_stdin, stdout as libc_stdout};

use leanh_l1::{
    datatypes::{LeanExternalClass, LeanObject},
    emitted::lean_mark_persistent::lean_mark_persistent,
};

use crate::{
    r#priv::{
        lean_alloc_external::lean_alloc_external,
        lean_register_external_class::lean_register_external_class,
    },
    todo_import_from_lean::lean_stream_of_handle::lean_stream_of_handle,
};

static mut IO_HANDLE_EXTERNAL_CLASS: *mut LeanExternalClass = ptr::null_mut();
static mut STREAM_STDIN: *mut LeanObject = ptr::null_mut();
static mut STREAM_STDOUT: *mut LeanObject = ptr::null_mut();
static mut STREAM_STDERR: *mut LeanObject = ptr::null_mut();

unsafe fn io_handle_finalizer(handle: *mut c_void) {
    libc::fclose(handle.cast());
}

pub unsafe fn io_wrap_handle(hfile: *mut libc::FILE) -> *mut LeanObject {
    lean_alloc_external(IO_HANDLE_EXTERNAL_CLASS, hfile.cast())
}

pub unsafe fn initialize_io() {
    IO_HANDLE_EXTERNAL_CLASS = lean_register_external_class(Some(io_handle_finalizer), None);

    STREAM_STDOUT = lean_stream_of_handle(io_wrap_handle(libc_stdout()));
    lean_mark_persistent(STREAM_STDOUT);
    STREAM_STDERR = lean_stream_of_handle(io_wrap_handle(libc_stderr()));
    lean_mark_persistent(STREAM_STDERR);
    STREAM_STDIN = lean_stream_of_handle(io_wrap_handle(libc_stdin()));
    lean_mark_persistent(STREAM_STDIN);

    #[cfg(unix)]
    {
        const SIGPIPE: libc::c_int = 13;
        assert_ne!(libc::signal(SIGPIPE, libc::SIG_IGN), libc::SIG_ERR);
    }
}
