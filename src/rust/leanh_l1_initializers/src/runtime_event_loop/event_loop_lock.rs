use core::ptr;
use core::sync::atomic::Ordering;
use libuv_sys2::{uv_async_send, uv_mutex_lock, uv_mutex_trylock};

use crate::runtime_event_loop::event_loop::EventLoop;

pub unsafe fn event_loop_interrupt(event_loop: *mut EventLoop) {
    let result = uv_async_send(ptr::addr_of_mut!((*event_loop).async_));
    debug_assert_eq!(result, 0);
}

pub unsafe fn event_loop_lock(event_loop: *mut EventLoop) {
    if uv_mutex_trylock(ptr::addr_of_mut!((*event_loop).mutex)) != 0 {
        (*event_loop).n_waiters.fetch_add(1, Ordering::SeqCst);
        event_loop_interrupt(event_loop);
        uv_mutex_lock(ptr::addr_of_mut!((*event_loop).mutex));
        (*event_loop).n_waiters.fetch_sub(1, Ordering::SeqCst);
    }
}
