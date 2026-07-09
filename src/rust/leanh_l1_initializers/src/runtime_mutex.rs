use core::ffi::c_void;
use std::ptr;
use std::sync::{Condvar, Mutex};
use std::thread::ThreadId;

use leanh_l1::datatypes::LeanExternalClass;

use crate::r#priv::lean_register_external_class::lean_register_external_class;

static mut BASEMUTEX_EXTERNAL_CLASS: *mut LeanExternalClass = ptr::null_mut();
static mut CONDVAR_EXTERNAL_CLASS: *mut LeanExternalClass = ptr::null_mut();
static mut BASERECMUTEX_EXTERNAL_CLASS: *mut LeanExternalClass = ptr::null_mut();
static mut BASESHAREDMUTEX_EXTERNAL_CLASS: *mut LeanExternalClass = ptr::null_mut();

pub struct BaseMutex {
    pub locked: Mutex<bool>,
    pub changed: Condvar,
}

pub struct RuntimeCondvar {
    pub condvar: Condvar,
}

pub struct RecState {
    pub owner: Option<ThreadId>,
    pub depth: usize,
}

pub struct BaseRecMutex {
    pub state: Mutex<RecState>,
    pub changed: Condvar,
}

pub struct SharedState {
    pub readers: usize,
    pub writer: bool,
}

pub struct BaseSharedMutex {
    pub state: Mutex<SharedState>,
    pub changed: Condvar,
}

unsafe fn basemutex_finalizer(data: *mut c_void) {
    drop(Box::from_raw(data.cast::<BaseMutex>()));
}

unsafe fn condvar_finalizer(data: *mut c_void) {
    drop(Box::from_raw(data.cast::<RuntimeCondvar>()));
}

unsafe fn baserecmutex_finalizer(data: *mut c_void) {
    drop(Box::from_raw(data.cast::<BaseRecMutex>()));
}

unsafe fn basesharedmutex_finalizer(data: *mut c_void) {
    drop(Box::from_raw(data.cast::<BaseSharedMutex>()));
}

pub fn initialize_mutex() {
    unsafe {
        BASEMUTEX_EXTERNAL_CLASS = lean_register_external_class(Some(basemutex_finalizer), None);
        CONDVAR_EXTERNAL_CLASS = lean_register_external_class(Some(condvar_finalizer), None);
        BASERECMUTEX_EXTERNAL_CLASS =
            lean_register_external_class(Some(baserecmutex_finalizer), None);
        BASESHAREDMUTEX_EXTERNAL_CLASS =
            lean_register_external_class(Some(basesharedmutex_finalizer), None);
    }
}
