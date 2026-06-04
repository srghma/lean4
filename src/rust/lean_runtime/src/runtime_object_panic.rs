/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

// Port of the panic / sorry / object-sizing section of src/runtime/object.cpp.
// Coverage:
//   lean_internal_panic{,_out_of_memory,_unreachable,_rc_overflow,_overflow}
//   lean_set_{exit_on,}_panic{,_messages}
//   lean_internal_set_exit_on_panic
//   lean_panic, lean_panic_fn, lean_panic_fn_borrowed
//   lean_sorry
//   lean_object_byte_size, lean_object_data_byte_size
//   lean_dbg_stack_trace
//   initialize_object (partial — globals only; array/ext-class init is in runtime_object_array.rs)
//   finalize_object   (partial)


use std::io::Write;

// ─── Globals ─────────────────────────────────────────────────────────────────

static G_EXIT_ON_PANIC: AtomicBool = AtomicBool::new(false);
static G_PANIC_MESSAGES: AtomicBool = AtomicBool::new(true);

// ─── Platform backtrace ───────────────────────────────────────────────────────

// When the Lean demangler is linked in it overrides this stub (mirrors the C++
// `__attribute__((weak))` declaration).
extern "C" {
    fn lean_demangle_bt_line_cstr(s: *mut LeanObject) -> *mut LeanObject;
}

#[cfg(any(target_os = "linux", target_os = "macos"))]
mod backtrace_impl {
    use super::*;
    use core::ffi::c_void;

    extern "C" {
        fn backtrace(buffer: *mut *mut c_void, size: c_int) -> c_int;
        fn backtrace_symbols(buffer: *const *mut c_void, size: c_int) -> *mut *mut c_char;
        fn free(ptr: *mut c_void);
    }

    pub(super) unsafe fn print_backtrace(force_stderr: bool) {
        const MAX_FRAMES: usize = 100;
        let mut buf = [core::ptr::null_mut::<c_void>(); MAX_FRAMES];
        let nptrs = backtrace(buf.as_mut_ptr(), MAX_FRAMES as c_int);
        if nptrs <= 0 {
            panic_eprintln("(backtrace() returned no frames)", force_stderr);
            return;
        }
        let symbols = backtrace_symbols(buf.as_ptr(), nptrs);
        if symbols.is_null() {
            panic_eprintln("(backtrace_symbols failed)", force_stderr);
            return;
        }

        let raw = std::env::var("LEAN_BACKTRACE_RAW").is_ok();
        for i in 0..nptrs as usize {
            let sym_ptr = *symbols.add(i);
            if sym_ptr.is_null() {
                continue;
            }
            if !raw {
                // Try the Lean demangler first.
                let sym_str = lean_mk_string(sym_ptr);
                let result = lean_demangle_bt_line_cstr(sym_str);
                let result_cstr = lean_string_cstr(result);
                if !result_cstr.is_null() && *result_cstr != 0 {
                    let s = std::ffi::CStr::from_ptr(result_cstr).to_string_lossy();
                    panic_eprintln(s.as_ref(), force_stderr);
                    lean_dec(result);
                    continue;
                }
                lean_dec(result);
            }
            let s = std::ffi::CStr::from_ptr(sym_ptr).to_string_lossy();
            panic_eprintln(s.as_ref(), force_stderr);
        }
        // `backtrace_symbols` says the outer array must be freed but NOT each string.
        free(symbols as *mut c_void);

        if nptrs as usize == MAX_FRAMES {
            panic_eprintln("...", force_stderr);
        }
    }
}

#[cfg(not(any(target_os = "linux", target_os = "macos")))]
mod backtrace_impl {
    pub(super) unsafe fn print_backtrace(force_stderr: bool) {
        super::panic_eprintln("(stack trace unavailable)", force_stderr);
    }
}

// ─── Internal helpers ─────────────────────────────────────────────────────────

fn should_abort_on_panic() -> bool {
    std::env::var("LEAN_ABORT_ON_PANIC").is_ok()
}

fn abort_on_panic() {
    if should_abort_on_panic() {
        std::process::abort();
    }
}

// Write `line` to either the Lean IO stderr channel or directly to the OS
// stderr stream (when we are about to kill the process or the Lean IO layer
// isn't safe to call into).
fn panic_eprintln(line: &str, force_stderr: bool) {
    if force_stderr || G_EXIT_ON_PANIC.load(Ordering::Relaxed) || should_abort_on_panic() {
        let _ = writeln!(std::io::stderr(), "{line}");
    } else {
        // Route through the Lean IO buffer so output ordering is preserved.
        unsafe {
            let s = lean_mk_string(
                std::ffi::CString::new(line)
                    .unwrap_or_default()
                    .as_ptr(),
            );
            let r = lean_io_eprintln(s);
            lean_dec(r);
        }
    }
}

unsafe fn lean_panic_impl(msg: &str, force_stderr: bool) {
    if G_PANIC_MESSAGES.load(Ordering::Relaxed) {
        panic_eprintln(msg, force_stderr);

        #[cfg(any(target_os = "linux", target_os = "macos"))]
        {
            // Backtrace is printed unless LEAN_BACKTRACE=0.
            let skip = std::env::var("LEAN_BACKTRACE")
                .map(|v| v == "0")
                .unwrap_or(false);
            if !skip {
                panic_eprintln("backtrace:", force_stderr);
                backtrace_impl::print_backtrace(force_stderr);
            }
        }
    }

    abort_on_panic();
    if G_EXIT_ON_PANIC.load(Ordering::Relaxed) {
        std::process::exit(1);
    }
}

// ─── Exported C symbols ───────────────────────────────────────────────────────

#[no_mangle]
pub unsafe extern "C" fn lean_internal_panic(msg: *const c_char) -> ! {
    let s = std::ffi::CStr::from_ptr(msg).to_string_lossy();
    let _ = writeln!(std::io::stderr(), "INTERNAL PANIC: {s}");
    abort_on_panic();
    std::process::exit(1);
}

#[no_mangle]
pub extern "C" fn lean_internal_panic_out_of_memory() -> ! {
    unsafe { lean_internal_panic(c"out of memory".as_ptr()) }
}

#[no_mangle]
pub extern "C" fn lean_internal_panic_unreachable() -> ! {
    unsafe { lean_internal_panic(c"unreachable code has been reached".as_ptr()) }
}

#[no_mangle]
pub extern "C" fn lean_internal_panic_rc_overflow() -> ! {
    unsafe { lean_internal_panic(c"reference counter overflowed".as_ptr()) }
}

#[no_mangle]
pub extern "C" fn lean_internal_panic_overflow() -> ! {
    unsafe { lean_internal_panic(c"integer overflow in runtime computation".as_ptr()) }
}

#[no_mangle]
pub extern "C" fn lean_set_exit_on_panic(flag: bool) {
    G_EXIT_ON_PANIC.store(flag, Ordering::Relaxed);
}

/// `setExitOnPanic (exit : Bool) : BaseIO Unit`
#[no_mangle]
pub unsafe extern "C" fn lean_internal_set_exit_on_panic(exit: u8) -> *mut LeanObject {
    G_EXIT_ON_PANIC.store(exit != 0, Ordering::Relaxed);
    lean_box(0)
}

#[no_mangle]
pub extern "C" fn lean_set_panic_messages(flag: bool) {
    G_PANIC_MESSAGES.store(flag, Ordering::Relaxed);
}

#[no_mangle]
pub unsafe extern "C" fn lean_panic(msg: *const c_char) {
    let s = std::ffi::CStr::from_ptr(msg).to_string_lossy();
    lean_panic_impl(s.as_ref(), false);
}

/// Called from Lean-generated code. Consumes `msg`, returns `default_val`.
#[no_mangle]
pub unsafe extern "C" fn lean_panic_fn(
    default_val: *mut LeanObject,
    msg: *mut LeanObject,
) -> *mut LeanObject {
    // lean_string_size includes the null terminator; subtract 1 for the content.
    let sz = lean_string_size(msg).saturating_sub(1);
    let ptr = lean_string_cstr(msg);
    let s = if sz > 0 && !ptr.is_null() {
        let bytes = core::slice::from_raw_parts(ptr as *const u8, sz);
        String::from_utf8_lossy(bytes).into_owned()
    } else {
        String::new()
    };
    lean_panic_impl(s.as_str(), false);
    lean_dec(msg);
    default_val
}

/// Borrowed variant: increments `default_val` before forwarding.
#[no_mangle]
pub unsafe extern "C" fn lean_panic_fn_borrowed(
    default_val: *mut LeanObject,
    msg: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(default_val);
    lean_panic_fn(default_val, msg)
}

#[no_mangle]
pub unsafe extern "C" fn lean_sorry(_: u8) -> *mut LeanObject {
    lean_internal_panic(c"executed 'sorry'".as_ptr())
}

// ─── Object sizing ────────────────────────────────────────────────────────────

// Object tag constants (must match lean.h).
const LEAN_ARRAY: u8 = 246;
const LEAN_SCALAR_ARRAY: u8 = 248;
const LEAN_STRING: u8 = 249;
const LEAN_CLOSURE: u8 = 250;



#[no_mangle]
pub unsafe extern "C" fn lean_object_byte_size(o: *mut LeanObject) -> usize {
    let cs_sz = (*o).m_cs_sz;
    let tag = lean_ptr_tag(o);
    if cs_sz == 0 {
        match tag {
            LEAN_ARRAY        => lean_array_byte_size(o),
            LEAN_SCALAR_ARRAY => lean_sarray_byte_size(o),
            LEAN_STRING       => lean_string_byte_size(o),
            LEAN_CLOSURE      => lean_closure_byte_size(o),
            _                 => lean_small_object_size(o),
        }
    } else {
        match tag {
            LEAN_ARRAY        => lean_array_byte_size(o),
            LEAN_SCALAR_ARRAY => lean_sarray_byte_size(o),
            LEAN_STRING       => lean_string_byte_size(o),
            LEAN_CLOSURE      => lean_closure_byte_size(o),
            _                 => cs_sz as usize,
        }
    }
}

#[no_mangle]
pub unsafe extern "C" fn lean_object_data_byte_size(o: *mut LeanObject) -> usize {
    let cs_sz = (*o).m_cs_sz;
    let tag = lean_ptr_tag(o);
    if cs_sz == 0 {
        match tag {
            LEAN_ARRAY        => lean_array_data_byte_size(o),
            LEAN_SCALAR_ARRAY => lean_sarray_data_byte_size(o),
            LEAN_STRING       => lean_string_data_byte_size(o),
            LEAN_CLOSURE      => lean_closure_data_byte_size(o),
            _                 => lean_small_object_size(o),
        }
    } else {
        match tag {
            LEAN_ARRAY        => lean_array_data_byte_size(o),
            LEAN_SCALAR_ARRAY => lean_sarray_data_byte_size(o),
            LEAN_STRING       => lean_string_data_byte_size(o),
            LEAN_CLOSURE      => lean_closure_data_byte_size(o),
            _                 => cs_sz as usize,
        }
    }
}

// ─── Debug stack trace ────────────────────────────────────────────────────────

#[no_mangle]
pub unsafe extern "C" fn lean_dbg_stack_trace(fn_obj: *mut LeanObject) -> *mut LeanObject {
    backtrace_impl::print_backtrace(false);
    lean_apply_1(fn_obj, lean_box(0))
}

// ─── Module init/finalize (panic-globals portion) ────────────────────────────
// The array empty sentinel and external-class registry live in
// runtime_object_array.rs; this file only resets the panic flags.

#[export_name = "_ZN4lean17initialize_objectEv"]
pub(crate) fn initialize_object_panic_export() {
    initialize_object_panic();
}

#[export_name = "_ZN4lean15finalize_objectEv"]
pub(crate) fn finalize_object_panic_export() {
    finalize_object_panic();
}

pub(crate) fn initialize_object_panic() {
    G_EXIT_ON_PANIC.store(false, Ordering::Relaxed);
    G_PANIC_MESSAGES.store(true, Ordering::Relaxed);
}

pub(crate) fn finalize_object_panic() {
    // Nothing to release — atomics have no heap allocation.
}
