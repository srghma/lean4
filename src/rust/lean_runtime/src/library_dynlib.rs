/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

use crate::*;

static mut DYNLIB_EXTERNAL_CLASS: *mut LeanExternalClass = ptr::null_mut();
static mut DYNLIB_SYMBOL_EXTERNAL_CLASS: *mut LeanExternalClass = ptr::null_mut();

#[cfg(unix)]
extern "C" {
    fn dlopen(path: *const c_char, flags: i32) -> *mut c_void;
    fn dlclose(handle: *mut c_void) -> i32;
    fn dlsym(handle: *mut c_void, name: *const c_char) -> *mut c_void;
    fn dlerror() -> *const c_char;
}

#[cfg(windows)]
extern "system" {
    fn LoadLibraryA(path: *const c_char) -> *mut c_void;
    fn FreeLibrary(handle: *mut c_void) -> i32;
    fn GetProcAddress(handle: *mut c_void, name: *const c_char) -> *mut c_void;
}

unsafe fn dynlib_finalizer(handle: *mut c_void) {
    #[cfg(unix)]
    {
        dlclose(handle);
    }
    #[cfg(windows)]
    {
        FreeLibrary(handle);
    }
}

unsafe fn noop_external_finalizer(_: *mut c_void) {}
unsafe fn noop_external_foreach(_: *mut c_void, _: *mut LeanObject) {}

unsafe fn dynlib_error(prefix: &str, detail: *const c_char) -> *mut LeanObject {
    let detail = if detail.is_null() {
        "unknown error".into()
    } else {
        core::ffi::CStr::from_ptr(detail).to_string_lossy()
    };
    let message = std::ffi::CString::new(format!("{prefix}{detail}"))
        .expect("dynamic loader error has no NUL");
    lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(message.as_ptr())))
}

pub fn initialize_dynlib() {
    unsafe {
        DYNLIB_EXTERNAL_CLASS =
            lean_register_external_class(Some(dynlib_finalizer), Some(noop_external_foreach));
        DYNLIB_SYMBOL_EXTERNAL_CLASS = lean_register_external_class(
            Some(noop_external_finalizer),
            Some(noop_external_foreach),
        );
    }
}

#[inline]
pub(crate) unsafe fn lean_dynlib_load(path: *mut LeanObject) -> *mut LeanObject {
    #[cfg(unix)]
    {
        const RTLD_LAZY: i32 = 1;
        #[cfg(any(target_os = "macos", target_os = "ios"))]
        const RTLD_GLOBAL: i32 = 0x8;
        #[cfg(not(any(target_os = "macos", target_os = "ios")))]
        const RTLD_GLOBAL: i32 = 0x100;

        let handle = dlopen(lean_string_cstr(path), RTLD_LAZY | RTLD_GLOBAL);
        if handle.is_null() {
            return dynlib_error("error loading library, ", dlerror());
        }
        lean_io_result_mk_ok(lean_runtime_alloc_external(DYNLIB_EXTERNAL_CLASS, handle))
    }
    #[cfg(windows)]
    {
        let handle = LoadLibraryA(lean_string_cstr(path));
        if handle.is_null() {
            return dynlib_error("error loading library, ", ptr::null());
        }
        lean_io_result_mk_ok(lean_runtime_alloc_external(DYNLIB_EXTERNAL_CLASS, handle))
    }
}

#[inline]
pub(crate) unsafe fn lean_dynlib_get(
    dynlib: *mut LeanObject,
    name: *mut LeanObject,
) -> *mut LeanObject {
    #[cfg(unix)]
    let symbol = {
        dlerror();
        let symbol = dlsym(
            lean_runtime_get_external_data(dynlib),
            lean_string_cstr(name),
        );
        if !dlerror().is_null() {
            return lean_box(0);
        }
        symbol
    };
    #[cfg(windows)]
    let symbol = {
        let symbol = GetProcAddress(
            lean_runtime_get_external_data(dynlib),
            lean_string_cstr(name),
        );
        if symbol.is_null() {
            return lean_box(0);
        }
        symbol
    };

    let symbol = lean_runtime_alloc_external(DYNLIB_SYMBOL_EXTERNAL_CLASS, symbol);
    let mut fields = [symbol];
    lean_runtime_mk_cnstr(1, 1, fields.as_mut_ptr(), 0)
}

#[inline]
pub(crate) unsafe fn lean_dynlib_symbol_run_as_init(
    _: *mut LeanObject,
    symbol: *mut LeanObject,
) -> *mut LeanObject {
    let symbol = lean_runtime_get_external_data(symbol);
    let initialize: unsafe extern "C" fn(u8) -> *mut LeanObject = core::mem::transmute(symbol);
    initialize(1)
}
