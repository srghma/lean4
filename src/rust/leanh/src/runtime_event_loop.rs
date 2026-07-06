use core::ffi::{CStr, c_char, c_int, c_long, c_uchar, c_uint, c_void};
use core::ptr;
use core::ptr::null_mut;
use core::sync::atomic::{AtomicI32, Ordering};
use libuv_sys2::{
    uv_async_init, uv_async_send, uv_async_t, uv_cond_init, uv_cond_signal, uv_cond_t,
    uv_cond_wait, uv_default_loop, uv_loop_alive, uv_loop_configure, uv_loop_t,
    uv_mutex_init_recursive, uv_mutex_lock, uv_mutex_t, uv_mutex_trylock, uv_mutex_unlock,
    uv_run as uv_run_sys, uv_stop as uv_stop_sys, uv_strerror,
};

#[repr(C)]
pub struct EventLoop {
    pub loop_: *mut uv_loop_t,
    mutex: uv_mutex_t,
    cond_var: uv_cond_t,
    async_: uv_async_t,
    n_waiters: AtomicI32,
}

pub static mut GLOBAL_EV: EventLoop = EventLoop {
    loop_: null_mut(),
    mutex: unsafe { core::mem::zeroed() },
    cond_var: unsafe { core::mem::zeroed() },
    async_: unsafe { core::mem::zeroed() },
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

pub unsafe fn event_loop_interrupt(event_loop: *mut EventLoop) {
    let result = uv_async_send(ptr::addr_of_mut!((*event_loop).async_));
    debug_assert_eq!(result, 0);
}

pub unsafe fn event_loop_unlock(event_loop: *mut EventLoop) {
    if (*event_loop).n_waiters.load(Ordering::SeqCst) == 0 {
        uv_cond_signal(ptr::addr_of_mut!((*event_loop).cond_var));
    }
    uv_mutex_unlock(ptr::addr_of_mut!((*event_loop).mutex));
}
