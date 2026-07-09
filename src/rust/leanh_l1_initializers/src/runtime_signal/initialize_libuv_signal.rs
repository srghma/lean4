use crate::runtime_event_loop::event_loop::GLOBAL_EV;
use crate::runtime_event_loop::event_loop_lock::event_loop_lock;
use crate::runtime_event_loop::event_loop_unlock::event_loop_unlock;
use core::ffi::{c_int, c_void};
use core::ptr::{addr_of_mut, null_mut};
use leanh_l1::datatypes::{LeanExternalClass, LeanObject};
use leanh_l1::emitted::lean_dec::lean_dec;
use leanh_l1::emitted::lean_inc::lean_inc;
use leanh_l1::runtime_apply::lean_apply_1;
use libuv_sys2::{uv_close, uv_handle_t, uv_signal_t};

use crate::r#priv::lean_register_external_class::lean_register_external_class;

static mut UV_SIGNAL_EXTERNAL_CLASS: *mut LeanExternalClass = null_mut();

#[repr(C)]
struct LeanUvSignalObject {
    uv_signal: *mut uv_signal_t,
    promise: *mut LeanObject,
    signum: c_int,
    repeating: bool,
    state: c_int,
}

unsafe fn signal_foreach(obj: *mut c_void, f: *mut LeanObject) {
    let signal = obj.cast::<LeanUvSignalObject>();
    if !(*signal).promise.is_null() {
        lean_inc(f);
        lean_apply_1(f, (*signal).promise);
    }
}

unsafe extern "C" fn close_free_handle(handle: *mut uv_handle_t) {
    libc::free(handle.cast());
}

pub unsafe fn lean_uv_signal_finalizer(ptr: *mut c_void) {
    let signal = ptr.cast::<LeanUvSignalObject>();

    if !(*signal).promise.is_null() {
        lean_dec((*signal).promise);
    }

    event_loop_lock(addr_of_mut!(GLOBAL_EV));
    uv_close(
        (*signal).uv_signal.cast::<uv_handle_t>(),
        Some(close_free_handle),
    );
    event_loop_unlock(addr_of_mut!(GLOBAL_EV));

    libc::free(signal.cast());
}

pub unsafe fn initialize_libuv_signal() {
    UV_SIGNAL_EXTERNAL_CLASS =
        lean_register_external_class(Some(lean_uv_signal_finalizer), Some(signal_foreach));
}
