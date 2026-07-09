use leanh_l1::{
    datatypes::{LeanExternalClass, LeanObject},
    emitted::lean_inc::lean_inc,
    runtime_apply::lean_apply_1,
};
use std::{
    ffi::c_void,
    ptr::{addr_of_mut, null_mut},
};

use crate::{
    r#priv::lean_register_external_class::lean_register_external_class,
    runtime_event_loop::{
        event_loop::GLOBAL_EV, event_loop_lock::event_loop_lock,
        event_loop_unlock::event_loop_unlock,
    },
};
use libuv_sys2::{uv_close, uv_handle_t};

static mut g_uv_udp_socket_external_class: *mut LeanExternalClass = null_mut();

#[repr(C)]
pub struct LeanUvUdpSocketObject {
    pub m_uv_udp: *mut c_void, // uv_udp_t*
    pub m_promise_read: *mut LeanObject,
    pub m_byte_array: *mut LeanObject,
}

pub(crate) unsafe fn foreach_cb(obj: *mut c_void, f: *mut LeanObject) {
    let udp_socket = obj.cast::<LeanUvUdpSocketObject>();
    if !(*udp_socket).m_promise_read.is_null() {
        lean_inc(f);
        lean_apply_1(f, (*udp_socket).m_promise_read);
    }
    if !(*udp_socket).m_byte_array.is_null() {
        lean_inc(f);
        lean_apply_1(f, (*udp_socket).m_byte_array);
    }
}

unsafe extern "C" fn close_cb(handle: *mut uv_handle_t) {
    let udp_socket = (*handle).data.cast::<LeanUvUdpSocketObject>();
    libc::free((*udp_socket).m_uv_udp);
    libc::free(udp_socket.cast());
}

unsafe fn lean_uv_udp_socket_finalizer(ptr: *mut c_void) {
    let udp_socket = ptr.cast::<LeanUvUdpSocketObject>();
    assert!((*udp_socket).m_promise_read.is_null());
    assert!((*udp_socket).m_byte_array.is_null());

    let handle = (*udp_socket).m_uv_udp.cast::<uv_handle_t>();
    (*handle).data = ptr;

    event_loop_lock(addr_of_mut!(GLOBAL_EV));

    uv_close((*udp_socket).m_uv_udp.cast::<uv_handle_t>(), Some(close_cb));

    event_loop_unlock(addr_of_mut!(GLOBAL_EV));
}

pub unsafe fn initialize_libuv_udp_socket() {
    g_uv_udp_socket_external_class =
        lean_register_external_class(Some(lean_uv_udp_socket_finalizer), Some(foreach_cb));
}
