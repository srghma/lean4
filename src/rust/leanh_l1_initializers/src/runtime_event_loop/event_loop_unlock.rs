use core::ptr;
use core::sync::atomic::Ordering;
use libuv_sys2::{uv_cond_signal, uv_mutex_unlock};

use crate::runtime_event_loop::event_loop::EventLoop;

pub unsafe fn event_loop_unlock(event_loop: *mut EventLoop) {
    if (*event_loop).n_waiters.load(Ordering::SeqCst) == 0 {
        uv_cond_signal(ptr::addr_of_mut!((*event_loop).cond_var));
    }
    uv_mutex_unlock(ptr::addr_of_mut!((*event_loop).mutex));
}
