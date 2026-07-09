use leanh_l1::runtime_object_panic::lean_internal_panic_out_of_memory::lean_internal_panic;
use std::{ptr, sync::atomic::Ordering};

use core::ffi::{CStr, c_int};
use libuv_sys2::{
    uv_async_init, uv_async_t, uv_cond_init, uv_default_loop, uv_mutex_init_recursive, uv_stop,
    uv_strerror,
};

use crate::runtime_event_loop::event_loop::{EventLoop, GLOBAL_EV};
unsafe extern "C" fn async_callback(handle: *mut uv_async_t) {
    uv_stop((*handle).loop_);
}

unsafe fn check_uv(result: c_int, msg: &'static [u8]) {
    if result != 0 {
        let err = CStr::from_ptr(uv_strerror(result)).to_string_lossy();
        let text = std::ffi::CString::new(format!(
            "{}: {err}",
            CStr::from_bytes_with_nul(msg).unwrap().to_string_lossy()
        ))
        .expect("libuv error message has no NUL");
        lean_internal_panic(text.as_ptr());
    }
}

pub unsafe fn event_loop_init(event_loop: *mut EventLoop) {
    (*event_loop).loop_ = uv_default_loop();
    check_uv(
        uv_mutex_init_recursive(ptr::addr_of_mut!((*event_loop).mutex)),
        b"Failed to initialize mutex\0",
    );
    check_uv(
        uv_cond_init(ptr::addr_of_mut!((*event_loop).cond_var)),
        b"Failed to initialize condition variable\0",
    );
    check_uv(
        uv_async_init(
            (*event_loop).loop_,
            ptr::addr_of_mut!((*event_loop).async_),
            Some(async_callback),
        ),
        b"Failed to initialize async\0",
    );
    (*event_loop).n_waiters.store(0, Ordering::Relaxed);
}

pub unsafe fn initialize_libuv_loop() {
    event_loop_init(ptr::addr_of_mut!(GLOBAL_EV));
}
