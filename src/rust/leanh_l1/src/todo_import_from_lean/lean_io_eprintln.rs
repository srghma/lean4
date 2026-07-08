use crate::datatypes::LeanObject;
use crate::emitted::lean_box::lean_box;
use crate::r#priv::lean_string_cstr::lean_string_cstr;
use crate::r#priv::lean_string_size::lean_string_size;
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
