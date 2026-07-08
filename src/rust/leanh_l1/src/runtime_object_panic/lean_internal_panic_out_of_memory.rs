use core::ffi::{CStr, c_char};
use std::io::Write;
use std::sync::OnceLock;

#[inline]
pub unsafe fn cstr_lossy(msg: *const c_char) -> String {
    unsafe {
        if msg.is_null() {
            String::new()
        } else {
            CStr::from_ptr(msg).to_string_lossy().into_owned()
        }
    }
}

#[inline]
fn c_char_ptr(bytes: &'static [u8]) -> *const c_char {
    bytes.as_ptr().cast()
}

#[inline]
pub fn abort_on_panic() {
    if should_abort_on_panic() {
        std::process::abort();
    }
}

#[inline]
pub fn should_abort_on_panic() -> bool {
    static SHOULD_ABORT_ON_PANIC: OnceLock<bool> = OnceLock::new();
    *SHOULD_ABORT_ON_PANIC.get_or_init(|| std::env::var_os("LEAN_ABORT_ON_PANIC").is_some())
}

#[inline]
pub unsafe fn lean_internal_panic(msg: *const c_char) -> ! {
    unsafe {
        let line = cstr_lossy(msg);
        let _ = writeln!(std::io::stderr(), "INTERNAL PANIC: {line}");
        abort_on_panic();
        std::process::exit(1);
    }
}

#[inline]
pub unsafe fn lean_internal_panic_out_of_memory() -> ! {
    unsafe { lean_internal_panic(c_char_ptr(b"out of memory\0")) }
}
