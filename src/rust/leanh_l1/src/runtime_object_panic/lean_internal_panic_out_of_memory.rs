use std::io::Write;
use std::sync::OnceLock;

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
pub unsafe fn lean_internal_panic(msg: impl AsRef<str>) -> ! {
    let _ = writeln!(std::io::stderr(), "INTERNAL PANIC: {}", msg.as_ref());
    abort_on_panic();
    std::process::exit(1);
}

#[inline]
pub unsafe fn lean_internal_panic_out_of_memory() -> ! {
    unsafe { lean_internal_panic("out of memory") }
}
