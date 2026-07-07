use core::ffi::c_void;
use core::ptr;
use core::sync::atomic::{AtomicI32, AtomicPtr};
use gmp_mpfr_sys::gmp::mpz_t;
use std::cell::Cell;

thread_local! {
    pub static G_TO_FREE: Cell<*mut LeanObject> = const { Cell::new(ptr::null_mut()) };
}
