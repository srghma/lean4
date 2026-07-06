use core::ffi::{CStr, c_char, c_int, c_long, c_uchar, c_uint, c_void};

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
