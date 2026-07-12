/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

mod runtime_debug_impl {
    use crate::*;
    use core::ffi::{c_char, c_int, c_long, c_uchar, c_uint, c_void, CStr};
    use std::collections::HashSet;
    use std::ffi::CStr;
    use std::io::{self, Read, Write};
    use std::process;
    use std::sync::{Mutex, OnceLock};

    static HAS_VIOLATIONS: AtomicBool = AtomicBool::new(false);
    static ASSERTIONS_ENABLED: AtomicBool = AtomicBool::new(true);
    static DEBUG_DIALOG: AtomicBool = AtomicBool::new(true);
    static ENABLED_DEBUG_TAGS: OnceLock<Mutex<HashSet<String>>> = OnceLock::new();

    fn debug_tags() -> &'static Mutex<HashSet<String>> {
        ENABLED_DEBUG_TAGS.get_or_init(|| Mutex::new(HashSet::new()))
    }

    fn write_stderr(text: &str) {
        let _ = io::stderr().write_all(text.as_bytes());
        let _ = io::stderr().flush();
    }
    pub fn initialize_debug() {
        // Debug tags are initialized lazily.
    }
    pub fn finalize_debug() {
        if let Some(tags) = ENABLED_DEBUG_TAGS.get() {
            tags.lock().unwrap().clear();
        }
    }
    pub fn has_violations() -> bool {
        HAS_VIOLATIONS.load(Ordering::Relaxed)
    }
    pub fn enable_assertions(enabled: bool) {
        ASSERTIONS_ENABLED.store(enabled, Ordering::Relaxed);
    }
    pub fn assertions_enabled() -> bool {
        ASSERTIONS_ENABLED.load(Ordering::Relaxed)
    }
    pub unsafe fn notify_assertion_violation(
        file_name: *const c_char,
        line: c_int,
        condition: *const c_char,
    ) {
        write_stderr("LEAN ASSERTION VIOLATION\n");
        write_stderr(&format!("File: {}\n", cstr_to_string(file_name)));
        write_stderr(&format!("Line: {line}\n"));
        write_stderr(&format!("{}\n", cstr_to_string(condition)));
    }
    pub unsafe fn enable_debug(tag: *const c_char) {
        debug_tags().lock().unwrap().insert(cstr_to_string(tag));
    }

    pub unsafe fn lean_internal_enable_debug(tag: *mut LeanObject) -> *mut LeanObject {
        enable_debug(lean_string_cstr(tag));
        lean_box(0)
    }
    pub unsafe fn disable_debug(tag: *const c_char) {
        if let Some(tags) = ENABLED_DEBUG_TAGS.get() {
            tags.lock().unwrap().remove(&cstr_to_string(tag));
        }
    }
    pub unsafe fn is_debug_enabled(tag: *const c_char) -> bool {
        if let Some(tags) = ENABLED_DEBUG_TAGS.get() {
            tags.lock().unwrap().contains(&cstr_to_string(tag))
        } else {
            false
        }
    }
    pub fn enable_debug_dialog(enabled: bool) {
        DEBUG_DIALOG.store(enabled, Ordering::Relaxed);
    }
    pub fn debuggable_exit() -> ! {
        process::abort();
    }
    pub fn invoke_debugger() {
        HAS_VIOLATIONS.store(true, Ordering::Relaxed);
        if !DEBUG_DIALOG.load(Ordering::Relaxed) {
            debuggable_exit();
        }
        loop {
            write_stderr("(C)ontinue, (A)bort/exit, (S)top/trap\n");
            let mut byte = [0u8; 1];
            match io::stdin().read_exact(&mut byte) {
                Ok(()) => match byte[0] {
                    b'C' | b'c' => return,
                    b'A' | b'a' | b'S' | b's' => debuggable_exit(),
                    _ => write_stderr("INVALID COMMAND\n"),
                },
                Err(_) => debuggable_exit(),
            }
        }
    }

    pub unsafe fn lean_notify_assert(
        file_name: *const c_char,
        line: c_int,
        condition: *const c_char,
    ) {
        notify_assertion_violation(file_name, line, condition);
        invoke_debugger();
    }
}

pub use runtime_debug_impl::*;

unsafe fn io_eprintln_checked(msg: *mut LeanObject) {
    let result = lean_io_eprintln(msg);
    debug_assert!(lean_io_result_is_ok(result));
    lean_dec(result);
}

unsafe fn lean_is_shared_obj(obj: *const LeanObject) -> bool {
    !lean_is_scalar(obj) && (*obj).rc > 1
}

pub unsafe fn lean_closure_max_args(_: *mut LeanObject) -> *mut LeanObject {
    lean_box(16)
}

pub unsafe fn lean_max_small_nat(_: *mut LeanObject) -> *mut LeanObject {
    lean_box(usize::MAX >> 1)
}

pub unsafe fn lean_dbg_trace(msg: *mut LeanObject, action: *mut LeanObject) -> *mut LeanObject {
    io_eprintln_checked(msg);
    lean_apply_1(action, lean_box(0))
}

pub unsafe fn lean_dbg_sleep(ms: u32, action: *mut LeanObject) -> *mut LeanObject {
    std::thread::sleep(std::time::Duration::from_millis(ms as u64));
    lean_apply_1(action, lean_box(0))
}

pub unsafe fn lean_dbg_trace_if_shared(
    msg: *mut LeanObject,
    value: *mut LeanObject,
) -> *mut LeanObject {
    if lean_is_shared_obj(value) {
        let suffix = CStr::from_ptr(lean_string_cstr(msg)).to_string_lossy();
        let text = std::ffi::CString::new(format!("shared RC {suffix}"))
            .expect("debug trace message has embedded NUL");
        io_eprintln_checked(lean_mk_string(text.as_ptr()));
    }
    value
}
