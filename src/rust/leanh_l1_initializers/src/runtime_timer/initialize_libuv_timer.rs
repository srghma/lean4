use leanh_l1::datatypes::{LeanExternalClass, LeanObject};
use leanh_l1::emitted::{lean_dec::lean_dec, lean_inc::lean_inc};
use leanh_l1::runtime_apply::lean_apply_1;
use std::{ffi::c_void, ptr::null_mut};

use crate::r#priv::lean_register_external_class::lean_register_external_class;

use crate::runtime_event_loop::{
    event_loop::GLOBAL_EV, event_loop_lock::event_loop_lock, event_loop_unlock::event_loop_unlock,
};
use core::ffi::c_int;
use core::ptr::addr_of_mut;
use libuv_sys2::{uv_close, uv_handle_t, uv_timer_t};

#[repr(C)]
struct LeanUvTimerObject {
    uv_timer: *mut uv_timer_t,
    promise: *mut LeanObject,
    timeout: u64,
    repeating: bool,
    state: c_int,
}

static mut UV_TIMER_EXTERNAL_CLASS: *mut LeanExternalClass = null_mut();

unsafe fn timer_foreach(obj: *mut c_void, f: *mut LeanObject) {
    let timer = obj.cast::<LeanUvTimerObject>();
    if !(*timer).promise.is_null() {
        lean_inc(f);
        lean_apply_1(f, (*timer).promise);
    }
}

#[inline]
unsafe extern "C" fn close_free_handle(handle: *mut uv_handle_t) {
    libc::free(handle.cast());
}

pub unsafe fn lean_uv_timer_finalizer(ptr: *mut c_void) {
    let timer = ptr.cast::<LeanUvTimerObject>();

    if !(*timer).promise.is_null() {
        lean_dec((*timer).promise);
    }

    event_loop_lock(addr_of_mut!(GLOBAL_EV));
    uv_close(
        (*timer).uv_timer.cast::<uv_handle_t>(),
        Some(close_free_handle),
    );
    event_loop_unlock(addr_of_mut!(GLOBAL_EV));

    libc::free(timer.cast());
}

pub unsafe fn initialize_libuv_timer() {
    UV_TIMER_EXTERNAL_CLASS =
        lean_register_external_class(Some(lean_uv_timer_finalizer), Some(timer_foreach));
}
