use core::ffi::c_char;
use core::sync::atomic::{AtomicBool, Ordering};

use crate::r#priv::print_backtrace::print_backtrace;
use crate::runtime_object_panic::lean_internal_panic_out_of_memory::{abort_on_panic, cstr_lossy};
use crate::runtime_object_panic::panic_eprintln::panic_eprintln;

pub static G_EXIT_ON_PANIC: AtomicBool = AtomicBool::new(false);
pub static G_PANIC_MESSAGES: AtomicBool = AtomicBool::new(true);

unsafe fn lean_panic_impl(msg: &[u8], force_stderr: bool) {
    if G_PANIC_MESSAGES.load(Ordering::Relaxed) {
        panic_eprintln(msg, force_stderr);

        let skip = std::env::var("LEAN_BACKTRACE")
            .map(|value| value == "0")
            .unwrap_or(false);
        if !skip {
            panic_eprintln(b"backtrace:", force_stderr);
            print_backtrace(force_stderr);
        }
    }

    abort_on_panic();
    if G_EXIT_ON_PANIC.load(Ordering::Relaxed) {
        std::process::exit(1);
    }
}

pub unsafe fn lean_panic(msg: *const c_char, force_stderr: bool) {
    let line = cstr_lossy(msg);
    lean_panic_impl(line.as_bytes(), force_stderr);
}
