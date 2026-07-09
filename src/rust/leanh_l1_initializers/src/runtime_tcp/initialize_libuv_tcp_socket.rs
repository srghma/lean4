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

#[repr(C)]
pub struct LeanUvTcpSocketObject {
    pub m_uv_tcp: *mut c_void, // uv_tcp_t*
    pub m_promise_accept: *mut LeanObject,
    pub m_promise_read: *mut LeanObject,
    pub m_promise_shutdown: *mut LeanObject,
    pub m_client: *mut LeanObject,
    pub m_byte_array: *mut LeanObject,
}

static mut g_uv_tcp_socket_external_class: *mut LeanExternalClass = null_mut();
pub unsafe fn initialize_libuv_tcp_socket() {
    unsafe fn foreach_cb(obj: *mut c_void, f: *mut LeanObject) {
        let tcp_socket = obj.cast::<LeanUvTcpSocketObject>();
        if !(*tcp_socket).m_promise_accept.is_null() {
            lean_inc(f);
            lean_apply_1(f, (*tcp_socket).m_promise_accept);
        }
        if !(*tcp_socket).m_promise_shutdown.is_null() {
            lean_inc(f);
            lean_apply_1(f, (*tcp_socket).m_promise_shutdown);
        }
        if !(*tcp_socket).m_promise_read.is_null() {
            lean_inc(f);
            lean_apply_1(f, (*tcp_socket).m_promise_read);
        }
        if !(*tcp_socket).m_byte_array.is_null() {
            lean_inc(f);
            lean_apply_1(f, (*tcp_socket).m_byte_array);
        }
    }

    unsafe fn lean_uv_tcp_socket_finalizer(ptr: *mut c_void) {
        let tcp_socket = ptr.cast::<LeanUvTcpSocketObject>();
        assert!((*tcp_socket).m_promise_shutdown.is_null());
        assert!((*tcp_socket).m_promise_accept.is_null());
        assert!((*tcp_socket).m_promise_read.is_null());
        assert!((*tcp_socket).m_byte_array.is_null());

        let handle = (*tcp_socket).m_uv_tcp.cast::<uv_handle_t>();
        (*handle).data = ptr;

        event_loop_lock(addr_of_mut!(GLOBAL_EV));

        unsafe extern "C" fn close_cb(handle: *mut uv_handle_t) {
            let tcp_socket = (*handle).data.cast::<LeanUvTcpSocketObject>();
            libc::free((*tcp_socket).m_uv_tcp);
            libc::free(tcp_socket.cast());
        }

        uv_close((*tcp_socket).m_uv_tcp.cast::<uv_handle_t>(), Some(close_cb));

        event_loop_unlock(addr_of_mut!(GLOBAL_EV));
    }

    g_uv_tcp_socket_external_class =
        lean_register_external_class(Some(lean_uv_tcp_socket_finalizer), Some(foreach_cb));
}
