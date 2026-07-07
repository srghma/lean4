use core::ffi::{CStr, c_char, c_int, c_long, c_uchar, c_uint, c_void};
use core::ptr;
use core::sync::atomic::{AtomicBool, Ordering};
use libloading::os::unix::Library as UnixLibrary;
use std::io::Write;
use std::sync::OnceLock;

pub unsafe fn lean_io_eprintln(mut v_s_9609_: *mut LeanObject) -> *mut LeanObject { // [lean-audit] Rust should import from Lean ([export]): Function is found in rust code, but is defined in rust (defined) (🛠️) | Lean: src/Init/System/IO.lean:1298
    // use gen_init::gen::Init::System::IO::{lean_io_eprintln};
    todo!("asdfasd")
}

use crate::datatypes::LeanObject;
use crate::in_emit_rust::{lean_dec, lean_mk_string};
use crate::runtime_object_string::lean_mk_string_from_bytes;


static G_EXIT_ON_PANIC: AtomicBool = AtomicBool::new(false);
static G_PANIC_MESSAGES: AtomicBool = AtomicBool::new(true);

fn panic_eprintln(line: &[u8], force_stderr: bool) {
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

type DemangleBacktraceLine = unsafe fn(*mut LeanObject) -> *mut LeanObject;

pub unsafe fn lean_string_cstr(obj: *mut LeanObject) -> *const c_char {
    (obj as *const u8).add(32) as *const c_char
}

unsafe fn demangle_backtrace_line(symbol: *const c_char) -> Option<String> {
    let lib = UnixLibrary::this();
    let Ok(demangle) = (unsafe { lib.get::<DemangleBacktraceLine>(c"lean_demangle_bt_line_cstr") }) // [lean-audit] Rust should import from Lean ([export]): Function is referenced via dynamic string lookup (dynamic) (🔍) | Lean: src/Lean/Compiler/NameDemangling.lean:335
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
pub unsafe fn print_backtrace(force_stderr: bool) {
    const MAX_FRAMES: usize = 100;
    let mut buf = [ptr::null_mut::<c_void>(); MAX_FRAMES];
    let nptrs = libc::backtrace(buf.as_mut_ptr(), MAX_FRAMES as c_int);
    if nptrs <= 0 {
        return;
    }
    let symbols = libc::backtrace_symbols(buf.as_ptr(), nptrs);
    if symbols.is_null() {
        return;
    }
    for i in 0..nptrs as usize {
        let symbol = *symbols.add(i);
        if !symbol.is_null() {
            if std::env::var_os("LEAN_BACKTRACE_RAW").is_none() {
                if let Some(line) = demangle_backtrace_line(symbol) {
                    panic_eprintln(line.as_bytes(), force_stderr);
                    continue;
                }
            }
            let line = cstr_lossy(symbol);
            panic_eprintln(line.as_bytes(), force_stderr);
        }
    }
    libc::free(symbols.cast());
    if nptrs as usize == MAX_FRAMES {
        panic_eprintln(b"...", force_stderr);
    }
}

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
