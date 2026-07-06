/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

// Port of the panic, sorry, and stack trace helpers from src/runtime/object.cpp.

mod runtime_object_panic_impl {
    use super::*;
    use std::io::Write;

    static G_EXIT_ON_PANIC: AtomicBool = AtomicBool::new(false);
    static G_PANIC_MESSAGES: AtomicBool = AtomicBool::new(true);

    extern "C" {
        fn lean_io_eprintln(msg: *mut LeanObject) -> *mut LeanObject;
    }

    #[inline]
    fn c_char_ptr(bytes: &'static [u8]) -> *const c_char {
        bytes.as_ptr().cast()
    }

    unsafe fn cstr_lossy(msg: *const c_char) -> String {
        if msg.is_null() {
            String::new()
        } else {
            CStr::from_ptr(msg).to_string_lossy().into_owned()
        }
    }

    #[cfg(any(target_os = "linux", target_os = "macos"))]
    mod backtrace_impl {
        use super::*;

        extern "C" {
            fn backtrace(buffer: *mut *mut c_void, size: c_int) -> c_int;
            fn backtrace_symbols(buffer: *const *mut c_void, size: c_int) -> *mut *mut c_char;
            fn free(ptr: *mut c_void);
        }

        type DemangleBacktraceLine = unsafe fn(*mut LeanObject) -> *mut LeanObject;

        unsafe fn demangle_backtrace_line(symbol: *const c_char) -> Option<String> {
            let proc = libc::dlsym(
                libc::RTLD_DEFAULT,
                c_char_ptr(b"lean_demangle_bt_line_cstr\0"),
            );
            if proc.is_null() {
                return None;
            }
            let demangle: DemangleBacktraceLine = core::mem::transmute(proc);
            let line = lean_mk_string(symbol);
            let result = demangle(line);
            let result_str = lean_string_cstr(result);
            let demangled = if !result_str.is_null() && *result_str != 0 {
                Some(cstr_lossy(result_str))
            } else {
                None
            };
            lean_dec(result);
            demangled
        }

        pub(super) unsafe fn print_backtrace(force_stderr: bool) {
            const MAX_FRAMES: usize = 100;
            let mut buf = [ptr::null_mut::<c_void>(); MAX_FRAMES];
            let nptrs = backtrace(buf.as_mut_ptr(), MAX_FRAMES as c_int);
            if nptrs <= 0 {
                return;
            }
            let symbols = backtrace_symbols(buf.as_ptr(), nptrs);
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
            free(symbols.cast());
            if nptrs as usize == MAX_FRAMES {
                panic_eprintln(b"...", force_stderr);
            }
        }
    }

    #[cfg(not(any(target_os = "linux", target_os = "macos")))]
    mod backtrace_impl {
        pub(super) unsafe fn print_backtrace(force_stderr: bool) {
            super::panic_eprintln(b"(stack trace unavailable)", force_stderr);
        }
    }

    fn should_abort_on_panic() -> bool {
        #[cfg(target_os = "emscripten")]
        {
            false
        }
        #[cfg(not(target_os = "emscripten"))]
        {
            std::env::var_os("LEAN_ABORT_ON_PANIC").is_some()
        }
    }

    fn abort_on_panic() {
        if should_abort_on_panic() {
            std::process::abort();
        }
    }

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

    unsafe fn lean_panic_impl(msg: &[u8], force_stderr: bool) {
        if G_PANIC_MESSAGES.load(Ordering::Relaxed) {
            panic_eprintln(msg, force_stderr);

            #[cfg(any(target_os = "linux", target_os = "macos"))]
            {
                let skip = std::env::var("LEAN_BACKTRACE")
                    .map(|value| value == "0")
                    .unwrap_or(false);
                if !skip {
                    panic_eprintln(b"backtrace:", force_stderr);
                    backtrace_impl::print_backtrace(force_stderr);
                }
            }

            #[cfg(not(any(target_os = "linux", target_os = "macos")))]
            {
                panic_eprintln(b"backtrace:", force_stderr);
                backtrace_impl::print_backtrace(force_stderr);
            }
        }

        abort_on_panic();
        if G_EXIT_ON_PANIC.load(Ordering::Relaxed) {
            std::process::exit(1);
        }
    }

    pub unsafe fn lean_internal_panic(msg: *const c_char) -> ! {
        let line = cstr_lossy(msg);
        let _ = writeln!(std::io::stderr(), "INTERNAL PANIC: {line}");
        abort_on_panic();
        std::process::exit(1);
    }

    pub unsafe fn lean_internal_panic_out_of_memory() -> ! {
        lean_internal_panic(c_char_ptr(b"out of memory\0"))
    }

    pub unsafe fn lean_internal_panic_unreachable() -> ! {
        lean_internal_panic(c_char_ptr(b"unreachable code has been reached\0"))
    }

    pub unsafe fn lean_internal_panic_rc_overflow() -> ! {
        lean_internal_panic(c_char_ptr(b"reference counter overflowed\0"))
    }

    pub unsafe fn lean_internal_panic_overflow() -> ! {
        lean_internal_panic(c_char_ptr(b"integer overflow in runtime computation\0"))
    }

    pub extern "C" fn lean_set_exit_on_panic(flag: bool) {
        G_EXIT_ON_PANIC.store(flag, Ordering::Relaxed);
    }

    pub unsafe fn lean_internal_set_exit_on_panic(exit: u8) -> *mut LeanObject {
        G_EXIT_ON_PANIC.store(exit != 0, Ordering::Relaxed);
        lean_box(0)
    }

    pub extern "C" fn lean_set_panic_messages(flag: bool) {
        G_PANIC_MESSAGES.store(flag, Ordering::Relaxed);
    }

    pub unsafe fn lean_panic(msg: *const c_char, force_stderr: bool) {
        let line = cstr_lossy(msg);
        lean_panic_impl(line.as_bytes(), force_stderr);
    }

    pub unsafe fn lean_panic_fn(
        default_val: *mut LeanObject,
        msg: *mut LeanObject,
    ) -> *mut LeanObject {
        let size = lean_string_size(msg).saturating_sub(1);
        let bytes = core::slice::from_raw_parts(lean_string_cstr(msg).cast::<u8>(), size);
        lean_panic_impl(bytes, false);
        lean_dec(msg);
        default_val
    }

    pub unsafe fn lean_panic_fn_borrowed(
        default_val: *mut LeanObject,
        msg: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_inc(default_val);
        lean_panic_fn(default_val, msg)
    }

    pub unsafe fn lean_sorry(_: u8) -> *mut LeanObject {
        lean_internal_panic(c_char_ptr(b"executed 'sorry'\0"))
    }

    pub unsafe fn lean_dbg_stack_trace(fn_obj: *mut LeanObject) -> *mut LeanObject {
        backtrace_impl::print_backtrace(false);
        lean_apply_1(fn_obj, lean_box(0))
    }
}
