use core::ptr::null_mut;
use core::sync::atomic::AtomicI32;
use libuv_sys2::{uv_async_t, uv_cond_t, uv_loop_t, uv_mutex_t};

#[repr(C)]
pub struct EventLoop {
    pub loop_: *mut uv_loop_t,
    pub mutex: uv_mutex_t,
    pub cond_var: uv_cond_t,
    pub async_: uv_async_t,
    pub n_waiters: AtomicI32,
}

pub static mut GLOBAL_EV: EventLoop = EventLoop {
    loop_: null_mut(),
    mutex: unsafe { core::mem::zeroed() },
    cond_var: unsafe { core::mem::zeroed() },
    async_: unsafe { core::mem::zeroed() },
    n_waiters: AtomicI32::new(0),
};
