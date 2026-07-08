use core::ffi::c_char;
use libloading::os::unix::Library as UnixLibrary;

use crate::datatypes::LeanObject;
use crate::emitted::lean_dec::lean_dec;
use crate::emitted::lean_mk_string::lean_mk_string;
use crate::r#priv::lean_string_cstr::lean_string_cstr;
use crate::runtime_object_panic::lean_internal_panic_out_of_memory::cstr_lossy;

type DemangleBacktraceLine = unsafe fn(*mut LeanObject) -> *mut LeanObject;

pub unsafe fn demangle_backtrace_line(symbol: *const c_char) -> Option<String> {
    let lib = UnixLibrary::this();
    let Ok(demangle) = (unsafe { lib.get::<DemangleBacktraceLine>(c"lean_demangle_bt_line_cstr") })
    // [lean-audit] Rust should import from Lean ([export]): Function is referenced via dynamic string lookup (dynamic) (🔍) | Lean: src/Lean/Compiler/NameDemangling.lean:335
    else {
        return None;
    };
    let line = lean_mk_string(symbol);
    let result = unsafe { (*demangle)(line) };
    let result_str = lean_string_cstr(result);
    let demangled = if !result_str.is_null() && *result_str != 0 {
        Some(cstr_lossy(result_str))
    } else {
        None
    };
    lean_dec(result);
    demangled
}
