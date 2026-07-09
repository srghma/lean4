use leanh_l1::runtime_thread::p1::{lean_finalize_thread, lean_initialize_thread};
use libuv_sys2::{
    uv_cond_wait, uv_loop_alive, uv_mutex_lock, uv_mutex_unlock, uv_run, uv_run_mode_UV_RUN_ONCE,
};
use std::{ptr, sync::atomic::Ordering, thread};

use crate::{
    runtime_event_loop::{
        event_loop::{EventLoop, GLOBAL_EV},
        initialize_libuv_loop::initialize_libuv_loop,
    },
    runtime_signal::initialize_libuv_signal::initialize_libuv_signal,
    runtime_tcp::initialize_libuv_tcp_socket::initialize_libuv_tcp_socket,
    runtime_timer::initialize_libuv_timer::initialize_libuv_timer,
    runtime_udp::initialize_libuv_udp_socket::initialize_libuv_udp_socket,
};

unsafe fn event_loop_run_loop(event_loop: *mut EventLoop) {
    while uv_loop_alive((*event_loop).loop_) != 0 {
        uv_mutex_lock(ptr::addr_of_mut!((*event_loop).mutex));

        while (*event_loop).n_waiters.load(Ordering::SeqCst) != 0 {
            uv_cond_wait(
                ptr::addr_of_mut!((*event_loop).cond_var),
                ptr::addr_of_mut!((*event_loop).mutex),
            );
        }

        uv_run((*event_loop).loop_, uv_run_mode_UV_RUN_ONCE);
        uv_mutex_unlock(ptr::addr_of_mut!((*event_loop).mutex));
    }
}

pub unsafe fn initialize_libuv() {
    initialize_libuv_timer();
    initialize_libuv_tcp_socket();
    initialize_libuv_udp_socket();
    initialize_libuv_signal();
    initialize_libuv_loop();

    let event_loop_addr = ptr::addr_of_mut!(GLOBAL_EV) as usize;
    thread::spawn(move || unsafe {
        lean_initialize_thread();
        event_loop_run_loop(event_loop_addr as *mut EventLoop);
        lean_finalize_thread();
    });
}
