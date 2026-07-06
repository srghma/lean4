use crate::base::lean_register_external_class;
use crate::datatypes::LeanExternalClass;
use crate::in_emit_rust::{lean_dec, lean_inc};
use crate::runtime_apply::lean_apply_1;
use crate::{datatypes::LeanObject, runtime_event_loop::GLOBAL_EV};
use core::ffi::{CStr, c_char, c_int, c_long, c_uchar, c_uint, c_void};
use core::ptr::{addr_of_mut, null_mut};
use libuv_sys2::{
    uv_close, uv_loop_t, uv_timer_init as uv_timer_init_sys, uv_timer_start as uv_timer_start_sys,
    uv_timer_stop as uv_timer_stop_sys,
};

#[repr(C)]
pub struct UvHandle {
    pub data: *mut c_void,
    pub loop_: *mut c_void,
    pub rest: [u8; 80],
}

#[repr(C, align(8))]
pub struct UvTimer {
    handle: UvHandle,
    rest: [u8; 56],
}

#[repr(C)]
struct LeanUvTimerObject {
    uv_timer: *mut UvTimer,
    promise: *mut LeanObject,
    timeout: u64,
    repeating: bool,
    state: c_int,
}

static mut UV_TIMER_EXTERNAL_CLASS: *mut LeanExternalClass = null_mut();

pub unsafe fn lean_uv_timer_finalizer(ptr: *mut c_void) {
    let timer = ptr.cast::<LeanUvTimerObject>();

    if !(*timer).promise.is_null() {
        lean_dec((*timer).promise);
    }

    event_loop_lock(addr_of_mut!(GLOBAL_EV));
    uv_close(
        (*timer).uv_timer.cast::<UvHandle>(),
        Some(close_free_handle),
    );
    event_loop_unlock(addr_of_mut!(GLOBAL_EV));

    libc::free(timer.cast());
}

unsafe fn timer_foreach(obj: *mut c_void, f: *mut LeanObject) {
    let timer = obj.cast::<LeanUvTimerObject>();
    if !(*timer).promise.is_null() {
        lean_inc(f);
        lean_apply_1(f, (*timer).promise);
    }
}

pub unsafe fn initialize_libuv_timer() {
    UV_TIMER_EXTERNAL_CLASS =
        lean_register_external_class(Some(lean_uv_timer_finalizer), Some(timer_foreach));
}
