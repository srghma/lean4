use crate::r#priv::lean_register_external_class::lean_register_external_class;
use leanh_l1::datatypes::LeanExternalClass;
use libloading::Library;
use std::ffi::c_void;
use std::ptr;

// #[cfg(unix)]
// use libloading::os::unix::{Library as UnixLibrary, RTLD_GLOBAL, RTLD_LAZY};
// #[cfg(unix)]
// use std::os::unix::ffi::OsStrExt;

static mut DYNLIB_EXTERNAL_CLASS: *mut LeanExternalClass = ptr::null_mut();
static mut DYNLIB_SYMBOL_EXTERNAL_CLASS: *mut LeanExternalClass = ptr::null_mut();

pub struct DynLibHandle {
    pub lib: Library,
}

unsafe fn dynlib_finalizer(handle: *mut c_void) {
    drop(Box::from_raw(handle as *mut DynLibHandle));
}

pub fn initialize_dynlib() {
    unsafe {
        DYNLIB_EXTERNAL_CLASS = lean_register_external_class(Some(dynlib_finalizer), None);
        DYNLIB_SYMBOL_EXTERNAL_CLASS = lean_register_external_class(None, None);
    }
}
