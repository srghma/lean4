#[cfg(all(lean_has_address_sanitizer, unix))]
use std::ffi::c_void;

#[cfg(all(lean_has_address_sanitizer, unix))]
use libloading::os::unix::Library as UnixLibrary;

#[cfg(lean_has_address_sanitizer)]
use crate::datatypes::LeanObject;

#[cfg(all(lean_has_address_sanitizer, unix))]
unsafe fn ignore_lsan_object(ptr: *mut c_void) {
    let lib = UnixLibrary::this();
    if let Ok(ignore) = unsafe { lib.get::<unsafe fn(*mut c_void)>(c"__lsan_ignore_object") } {
        unsafe { (*ignore)(ptr) };
    }
}

#[cfg(lean_has_address_sanitizer)]
#[inline(always)]
pub unsafe fn lsan_ignore(o: *mut LeanObject) {
    ignore_lsan_object(o as *mut c_void);
}

#[cfg(not(lean_has_address_sanitizer))]
#[inline(always)]
pub unsafe fn lsan_ignore(_o: *mut LeanObject) {}
