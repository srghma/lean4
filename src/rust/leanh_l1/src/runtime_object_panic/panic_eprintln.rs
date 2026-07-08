use crate::datatypes::LeanObject;
use crate::lean_box::lean_box;
use crate::lean_dec::lean_dec;
use crate::r#priv::lean_mk_string_from_bytes::lean_mk_string_from_bytes;
use crate::r#priv::lean_string_cstr::lean_string_cstr;
use crate::r#priv::lean_string_size::lean_string_size;
use crate::runtime_object_panic::lean_internal_panic_out_of_memory::should_abort_on_panic;
use crate::runtime_object_panic::lean_panic::G_EXIT_ON_PANIC;
use core::sync::atomic::Ordering;
use std::io::Write;

pub unsafe fn lean_io_eprintln(v_s_9609_: *mut LeanObject) -> *mut LeanObject {
    // [lean-audit] Rust should import from Lean ([export]): Function is found in rust code, but is defined in rust (defined) (🛠️) | Lean: src/Init/System/IO.lean:1298
    let mut stderr = std::io::stderr();
    let size = lean_string_size(v_s_9609_).saturating_sub(1);
    let bytes = core::slice::from_raw_parts(lean_string_cstr(v_s_9609_).cast::<u8>(), size);
    let _ = stderr.write_all(bytes);
    let _ = stderr.write_all(b"\n");
    lean_box(0)
}

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
