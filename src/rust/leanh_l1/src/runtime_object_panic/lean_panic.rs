use core::sync::atomic::{AtomicBool, Ordering};
use std::sync::OnceLock;

use crate::r#priv::print_backtrace::print_backtrace;
use crate::runtime_object_panic::lean_internal_panic_out_of_memory::abort_on_panic;
use crate::runtime_object_panic::panic_eprintln::panic_eprintln;

pub static G_EXIT_ON_PANIC: AtomicBool = AtomicBool::new(false);
pub static G_PANIC_MESSAGES: AtomicBool = AtomicBool::new(true);

static LEAN_BACKTRACE_DISABLED: OnceLock<bool> = OnceLock::new();
pub fn lean_panic_impl(msg: &[u8], force_stderr: bool) {
    if G_PANIC_MESSAGES.load(Ordering::Relaxed) {
        panic_eprintln(msg, force_stderr);

        let skip = *LEAN_BACKTRACE_DISABLED.get_or_init(|| {
            std::env::var("LEAN_BACKTRACE")
                .map(|value| value == "0")
                .unwrap_or(false)
        });
        if !skip {
            panic_eprintln(b"backtrace:", force_stderr);
            unsafe { print_backtrace(force_stderr) };
        }
    }

    abort_on_panic();
    if G_EXIT_ON_PANIC.load(Ordering::Relaxed) {
        std::process::exit(1);
    }
}

pub unsafe fn lean_panic(msg: impl AsRef<str>, force_stderr: bool) {
    lean_panic_impl(msg.as_ref().as_bytes(), force_stderr);
}
