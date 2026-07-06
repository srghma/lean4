use core::ffi::{CStr, c_char, c_int, c_long, c_uchar, c_uint, c_void};
use core::ptr;
use core::ptr::null_mut;
use core::sync::atomic::{AtomicI32, Ordering};
use libuv_sys2::{
    uv_async_init as uv_async_init_sys, uv_async_send as uv_async_send_sys,
    uv_cond_init as uv_cond_init_sys, uv_cond_signal as uv_cond_signal_sys,
    uv_cond_wait as uv_cond_wait_sys, uv_default_loop as uv_default_loop_sys,
    uv_loop_alive as uv_loop_alive_sys, uv_loop_configure as uv_loop_configure_sys, uv_loop_t,
    uv_mutex_init_recursive as uv_mutex_init_recursive_sys, uv_mutex_lock as uv_mutex_lock_sys,
    uv_mutex_trylock as uv_mutex_trylock_sys, uv_mutex_unlock as uv_mutex_unlock_sys,
    uv_run as uv_run_sys, uv_stop as uv_stop_sys, uv_strerror,
};

#[repr(C, align(8))]
struct UvMutex {
    storage: [u8; 40],
}

#[repr(C, align(8))]
struct UvCond {
    storage: [u8; 48],
}

#[repr(C)]
struct UvHandlePrefix {
    data: *mut c_void,
    loop_: *mut uv_loop_t,
}

#[repr(C, align(8))]
struct UvAsync {
    prefix: UvHandlePrefix,
    rest: [u8; 112],
}

#[repr(C)]
pub struct EventLoop {
    pub loop_: *mut uv_loop_t,
    mutex: UvMutex,
    cond_var: UvCond,
    async_: UvAsync,
    n_waiters: AtomicI32,
}

pub static mut GLOBAL_EV: EventLoop = EventLoop {
    loop_: null_mut(),
    mutex: UvMutex { storage: [0; 40] },
    cond_var: UvCond { storage: [0; 48] },
    async_: UvAsync {
        prefix: UvHandlePrefix {
            data: null_mut(),
            loop_: null_mut(),
        },
        rest: [0; 112],
    },
    n_waiters: AtomicI32::new(0),
};

pub unsafe fn event_loop_lock(event_loop: *mut EventLoop) {
    if uv_mutex_trylock(ptr::addr_of_mut!((*event_loop).mutex)) != 0 {
        (*event_loop).n_waiters.fetch_add(1, Ordering::SeqCst);
        event_loop_interrupt(event_loop);
        uv_mutex_lock(ptr::addr_of_mut!((*event_loop).mutex));
        (*event_loop).n_waiters.fetch_sub(1, Ordering::SeqCst);
    }
}
