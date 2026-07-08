use std::ffi::c_int;
use std::ffi::c_void;
use std::mem;
use std::ptr;
use std::sync::atomic::{AtomicPtr, Ordering};




pub fn finalize_stack_overflow() {
    let guard = MAIN_STACK_GUARD.swap(ptr::null_mut(), Ordering::Relaxed);
    if !guard.is_null() {
        unsafe {
            stack_guard_dtor(guard);
            drop(Box::from_raw(guard));
        }
    }
}
