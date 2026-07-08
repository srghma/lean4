use std::{
    ffi::{c_int, c_void},
    ptr,
};

use crate::{r#priv::demangle_backtrace_line::demangle_backtrace_line, runtime_object_panic::{
    lean_internal_panic_out_of_memory::cstr_lossy, panic_eprintln::panic_eprintln,
}};

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
            if std::env::var_os("LEAN_BACKTRACE_RAW").is_none()
                && let Some(line) = demangle_backtrace_line(symbol) {
                    panic_eprintln(line.as_bytes(), force_stderr);
                    continue;
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
