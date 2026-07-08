use crate::emitted::lean_dec::lean_dec;
use crate::r#priv::lean_mk_string_from_bytes::lean_mk_string_from_bytes;
use crate::runtime_object_panic::lean_internal_panic_out_of_memory::should_abort_on_panic;
use crate::runtime_object_panic::lean_panic::G_EXIT_ON_PANIC;
use crate::todo_import_from_lean::lean_io_eprintln::lean_io_eprintln;
use core::sync::atomic::Ordering;
use std::io::Write;

pub fn panic_eprintln(line: &[u8], force_stderr: bool) {
    if force_stderr || G_EXIT_ON_PANIC.load(Ordering::Relaxed) || should_abort_on_panic() {
        let mut stderr = std::io::stderr();
        let _ = stderr.write_all(line);
        let _ = stderr.write_all(b"\n");
    } else {
        unsafe {
            let s = lean_mk_string_from_bytes(line.as_ptr().cast(), line.len());
            let r = lean_io_eprintln(s);
            lean_dec(r);
        }
    }
}
