/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

use crate::*;

#[cfg(all(feature = "std", not(target_family = "wasm")))]
pub(crate) mod runtime_udp_impl {
    use super::*;
    use core::mem::MaybeUninit;
    use core::ptr::{addr_of_mut, null_mut};

    #[repr(C)]
    pub struct LeanUvUdpSocketObject {
        pub m_uv_udp: *mut c_void, // uv_udp_t*
        pub m_promise_read: *mut LeanObject,
        pub m_byte_array: *mut LeanObject,
    }

    #[repr(C)]
    struct UdpSendData {
        promise: *mut LeanObject,
        data: *mut LeanObject,
        socket: *mut LeanObject,
        bufs: *mut uv_buf_t,
    }

    #[repr(C)]
    #[derive(Copy, Clone)]
    struct uv_buf_t {
        base: *mut c_char,
        len: usize,
    }

    #[repr(C, align(8))]
    struct uv_udp_send_t {
        _storage: [u8; 320],
    }

    extern "C" {
        fn uv_udp_init(loop_: *mut c_void, handle: *mut c_void) -> c_int;
        fn uv_udp_bind(handle: *mut c_void, addr: *const libc::sockaddr, flags: c_uint) -> c_int;
        fn uv_udp_connect(handle: *mut c_void, addr: *const libc::sockaddr) -> c_int;
        fn uv_udp_send(
            req: *mut uv_udp_send_t,
            handle: *mut c_void,
            bufs: *const uv_buf_t,
            nbufs: c_uint,
            addr: *const libc::sockaddr,
            cb: Option<unsafe extern "C" fn(*mut uv_udp_send_t, c_int)>,
        ) -> c_int;
        fn uv_udp_recv_start(
            handle: *mut c_void,
            alloc_cb: Option<unsafe extern "C" fn(*mut c_void, usize, *mut uv_buf_t)>,
            recv_cb: Option<
                unsafe extern "C" fn(
                    *mut c_void,
                    isize,
                    *const uv_buf_t,
                    *const libc::sockaddr,
                    c_uint,
                ),
            >,
        ) -> c_int;
        fn uv_udp_recv_stop(handle: *mut c_void) -> c_int;

        fn uv_udp_getpeername(
            handle: *const c_void,
            name: *mut libc::sockaddr,
            namelen: *mut c_int,
        ) -> c_int;
        fn uv_udp_getsockname(
            handle: *const c_void,
            name: *mut libc::sockaddr,
            namelen: *mut c_int,
        ) -> c_int;
        fn uv_udp_set_broadcast(handle: *mut c_void, on: c_int) -> c_int;
        fn uv_udp_set_multicast_loop(handle: *mut c_void, on: c_int) -> c_int;
        fn uv_udp_set_multicast_ttl(handle: *mut c_void, ttl: c_int) -> c_int;
        fn uv_udp_set_membership(
            handle: *mut c_void,
            multicast_addr: *const c_char,
            interface_addr: *const c_char,
            membership: c_int,
        ) -> c_int;
        fn uv_udp_set_multicast_interface(
            handle: *mut c_void,
            interface_addr: *const c_char,
        ) -> c_int;
        fn uv_udp_set_ttl(handle: *mut c_void, ttl: c_int) -> c_int;

        fn uv_close(handle: *mut UvHandle, close_cb: Option<unsafe extern "C" fn(*mut UvHandle)>);
        fn uv_buf_init(base: *mut c_char, len: c_uint) -> uv_buf_t;

        #[link_name = "_ZN4lean39lean_socket_address_to_sockaddr_storageEP11lean_objectP16sockaddr_storage"]
        fn lean_socket_address_to_sockaddr_storage(
            ip_addr: *mut LeanObject,
            out: *mut libc::sockaddr_storage,
        );
        #[link_name = "_ZN4lean30lean_sockaddr_to_socketaddressEPK8sockaddr"]
        fn lean_sockaddr_to_socketaddress(addr: *const libc::sockaddr) -> *mut LeanObject;
        #[link_name = "_ZN4lean30lean_promise_resolve_with_codeEiP11lean_object"]
        fn lean_promise_resolve_with_code(code: c_int, promise: *mut LeanObject);
    }

    static mut g_uv_udp_socket_external_class: *mut LeanExternalClass = null_mut();

    unsafe fn lean_uv_udp_socket_new(s: *mut LeanUvUdpSocketObject) -> *mut LeanObject {
        lean_runtime_alloc_external(g_uv_udp_socket_external_class, s.cast())
    }

    unsafe fn lean_to_uv_udp_socket(o: *mut LeanObject) -> *mut LeanUvUdpSocketObject {
        lean_runtime_get_external_data(o).cast()
    }

    unsafe fn mk_except_ok(value: *mut LeanObject) -> *mut LeanObject {
        let result = lean_runtime_alloc_ctor(1, 1, 0);
        lean_runtime_ctor_set(result, 0, value);
        result
    }

    unsafe fn mk_except_err(error: *mut LeanObject) -> *mut LeanObject {
        let result = lean_runtime_alloc_ctor(0, 1, 0);
        lean_runtime_ctor_set(result, 0, error);
        result
    }

    unsafe fn option_none() -> *mut LeanObject {
        lean_box(0)
    }

    unsafe fn option_some(value: *mut LeanObject) -> *mut LeanObject {
        let result = lean_runtime_alloc_ctor(1, 1, 0);
        lean_runtime_ctor_set(result, 0, value);
        result
    }

    unsafe extern "C" fn lean_uv_udp_socket_finalizer(ptr: *mut c_void) {
        let udp_socket = ptr.cast::<LeanUvUdpSocketObject>();
        assert!((*udp_socket).m_promise_read.is_null());
        assert!((*udp_socket).m_byte_array.is_null());

        let handle = (*udp_socket).m_uv_udp.cast::<UvHandle>();
        (*handle).data = ptr;

        event_loop_lock(addr_of_mut!(_ZN4lean9global_evE));

        unsafe extern "C" fn close_cb(handle: *mut UvHandle) {
            let udp_socket = (*handle).data.cast::<LeanUvUdpSocketObject>();
            libc::free((*udp_socket).m_uv_udp);
            libc::free(udp_socket.cast());
        }

        uv_close((*udp_socket).m_uv_udp.cast::<UvHandle>(), Some(close_cb));

        event_loop_unlock(addr_of_mut!(_ZN4lean9global_evE));
    }

    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean27initialize_libuv_udp_socketEv"
    )]
    pub unsafe extern "C" fn initialize_libuv_udp_socket() {
        unsafe extern "C" fn foreach_cb(obj: *mut c_void, f: *mut LeanObject) {
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

        g_uv_udp_socket_external_class =
            lean_register_external_class(Some(lean_uv_udp_socket_finalizer), Some(foreach_cb));
    }

    const UV_UDP_REUSEADDR: c_uint = 4;
    const UV_EALREADY: c_int = -3003;
    const UV_ENOBUFS: isize = -105;

    #[inline]
    pub(crate) unsafe fn lean_uv_udp_new() -> *mut LeanObject {
        let udp_socket = libc::malloc(core::mem::size_of::<LeanUvUdpSocketObject>())
            .cast::<LeanUvUdpSocketObject>();
        if udp_socket.is_null() {
            return lean_io_result_mk_error(lean_decode_io_error(libc::ENOMEM, null_mut()));
        }

        (*udp_socket).m_promise_read = null_mut();
        (*udp_socket).m_byte_array = null_mut();

        let uv_udp = libc::malloc(216); // sizeof(uv_udp_t)
        if uv_udp.is_null() {
            libc::free(udp_socket.cast());
            return lean_io_result_mk_error(lean_decode_io_error(libc::ENOMEM, null_mut()));
        }

        event_loop_lock(addr_of_mut!(_ZN4lean9global_evE));
        let result = uv_udp_init(_ZN4lean9global_evE.loop_.cast(), uv_udp);
        event_loop_unlock(addr_of_mut!(_ZN4lean9global_evE));

        if result != 0 {
            libc::free(uv_udp);
            libc::free(udp_socket.cast());
            return lean_io_result_mk_error(lean_decode_uv_error(result, null_mut()));
        }

        let obj = lean_uv_udp_socket_new(udp_socket);
        lean_mark_mt(obj);

        (*udp_socket).m_uv_udp = uv_udp;
        let handle = (*udp_socket).m_uv_udp.cast::<UvHandle>();
        (*handle).data = obj.cast();

        lean_io_result_mk_ok(obj)
    }

    #[inline]
    pub(crate) unsafe fn lean_uv_udp_bind(
        socket: *mut LeanObject,
        addr: *mut LeanObject,
    ) -> *mut LeanObject {
        let udp_socket = lean_to_uv_udp_socket(socket);

        let mut addr_ptr = MaybeUninit::<libc::sockaddr_storage>::uninit();
        lean_socket_address_to_sockaddr_storage(addr, addr_ptr.as_mut_ptr());

        event_loop_lock(addr_of_mut!(_ZN4lean9global_evE));
        let result = uv_udp_bind(
            (*udp_socket).m_uv_udp,
            addr_ptr.as_ptr().cast(),
            UV_UDP_REUSEADDR,
        );
        event_loop_unlock(addr_of_mut!(_ZN4lean9global_evE));

        if result < 0 {
            return lean_io_result_mk_error(lean_decode_uv_error(result, null_mut()));
        }

        lean_io_result_mk_ok(lean_box(0))
    }

    #[inline]
    pub(crate) unsafe fn lean_uv_udp_connect(
        socket: *mut LeanObject,
        addr: *mut LeanObject,
    ) -> *mut LeanObject {
        let udp_socket = lean_to_uv_udp_socket(socket);

        let mut addr_ptr = MaybeUninit::<libc::sockaddr_storage>::uninit();
        lean_socket_address_to_sockaddr_storage(addr, addr_ptr.as_mut_ptr());

        event_loop_lock(addr_of_mut!(_ZN4lean9global_evE));
        let result = uv_udp_connect((*udp_socket).m_uv_udp, addr_ptr.as_ptr().cast());
        event_loop_unlock(addr_of_mut!(_ZN4lean9global_evE));

        if result < 0 {
            return lean_io_result_mk_error(lean_decode_uv_error(result, null_mut()));
        }

        lean_io_result_mk_ok(lean_box(0))
    }

    #[inline]
    pub(crate) unsafe fn lean_uv_udp_send(
        socket: *mut LeanObject,
        data_array: *mut LeanObject,
        opt_addr: *mut LeanObject,
    ) -> *mut LeanObject {
        let udp_socket = lean_to_uv_udp_socket(socket);
        let array_len = lean_array_size(data_array);

        if array_len == 0 {
            lean_dec(data_array);
            let promise = lean_io_promise_new();
            lean_mark_mt(promise);
            lean_promise_resolve_with_code(0, promise);
            return lean_io_result_mk_ok(promise);
        }

        let bufs_byte_size = array_len.checked_mul(core::mem::size_of::<uv_buf_t>());
        if bufs_byte_size.is_none() {
            lean_dec(data_array);
            return lean_io_result_mk_error(lean_decode_io_error(libc::ENOMEM, null_mut()));
        }
        let bufs = libc::malloc(bufs_byte_size.unwrap()).cast::<uv_buf_t>();
        if bufs.is_null() {
            lean_dec(data_array);
            return lean_io_result_mk_error(lean_decode_io_error(libc::ENOMEM, null_mut()));
        }

        for i in 0..array_len {
            let byte_array = lean_array_get_core(data_array, i);
            let data_len = lean_sarray_size(byte_array);
            let data_str = lean_sarray_cptr(byte_array).cast_mut().cast::<c_char>();
            bufs.add(i).write(uv_buf_init(data_str, data_len as c_uint));
        }

        let promise = lean_io_promise_new();
        lean_mark_mt(promise);

        let send_uv = libc::malloc(core::mem::size_of::<uv_udp_send_t>()).cast::<uv_udp_send_t>();
        if send_uv.is_null() {
            lean_dec(data_array);
            lean_dec(promise);
            libc::free(bufs.cast());
            return lean_io_result_mk_error(lean_decode_io_error(libc::ENOMEM, null_mut()));
        }

        let send_handle = send_uv.cast::<UvHandle>();
        (*send_handle).data = libc::malloc(core::mem::size_of::<UdpSendData>());
        if (*send_handle).data.is_null() {
            lean_dec(data_array);
            lean_dec(promise);
            libc::free(bufs.cast());
            libc::free(send_uv.cast());
            return lean_io_result_mk_error(lean_decode_io_error(libc::ENOMEM, null_mut()));
        }

        let send_data = (*send_handle).data.cast::<UdpSendData>();
        (*send_data).promise = promise;
        (*send_data).data = data_array;
        (*send_data).socket = socket;
        (*send_data).bufs = bufs;

        lean_inc(promise);
        lean_inc(socket);

        let mut addr_ptr: *mut libc::sockaddr_storage = null_mut();

        if lean_obj_tag(opt_addr) == 1 {
            let addr = lean_ctor_get(opt_addr, 0);
            addr_ptr = libc::malloc(core::mem::size_of::<libc::sockaddr_storage>())
                .cast::<libc::sockaddr_storage>();
            if addr_ptr.is_null() {
                lean_dec(promise);
                lean_dec(promise);
                lean_dec(socket);
                lean_dec(data_array);
                libc::free(bufs.cast());
                libc::free((*send_handle).data);
                libc::free(send_uv.cast());
                return lean_io_result_mk_error(lean_decode_io_error(libc::ENOMEM, null_mut()));
            }
            lean_socket_address_to_sockaddr_storage(addr, addr_ptr);
        }

        event_loop_lock(addr_of_mut!(_ZN4lean9global_evE));

        unsafe extern "C" fn send_cb(req: *mut uv_udp_send_t, status: c_int) {
            let req_handle = req.cast::<UvHandle>();
            let tup = (*req_handle).data.cast::<UdpSendData>();
            lean_promise_resolve_with_code(status, (*tup).promise);

            lean_dec((*tup).promise);
            lean_dec((*tup).socket);
            lean_dec((*tup).data);

            libc::free((*tup).bufs.cast());
            libc::free((*req_handle).data);
            libc::free(req.cast());
        }

        let result = uv_udp_send(
            send_uv,
            (*udp_socket).m_uv_udp,
            bufs,
            array_len as c_uint,
            addr_ptr.cast(),
            Some(send_cb),
        );

        event_loop_unlock(addr_of_mut!(_ZN4lean9global_evE));

        if !addr_ptr.is_null() {
            libc::free(addr_ptr.cast());
        }

        if result < 0 {
            lean_dec(promise);
            lean_dec(promise);
            lean_dec(socket);
            lean_dec(data_array);
            libc::free(bufs.cast());
            libc::free((*send_handle).data);
            libc::free(send_uv.cast());

            return lean_io_result_mk_error(lean_decode_uv_error(result, null_mut()));
        }

        lean_io_result_mk_ok(promise)
    }

    #[inline]
    pub(crate) unsafe fn lean_uv_udp_recv(
        socket: *mut LeanObject,
        buffer_size: u64,
    ) -> *mut LeanObject {
        let udp_socket = lean_to_uv_udp_socket(socket);

        event_loop_lock(addr_of_mut!(_ZN4lean9global_evE));

        if !(*udp_socket).m_promise_read.is_null() {
            event_loop_unlock(addr_of_mut!(_ZN4lean9global_evE));
            return lean_io_result_mk_error(lean_decode_uv_error(UV_EALREADY, null_mut()));
        }

        let byte_array = lean_alloc_sarray(1, 0, buffer_size as Size);
        let promise = lean_io_promise_new();
        lean_mark_mt(promise);

        (*udp_socket).m_byte_array = byte_array;
        (*udp_socket).m_promise_read = promise;

        lean_inc(promise);
        lean_inc(socket);

        unsafe extern "C" fn alloc_cb(
            handle: *mut c_void,
            _suggested_size: usize,
            buf: *mut uv_buf_t,
        ) {
            let handle_ptr = handle.cast::<UvHandle>();
            let udp_socket = lean_to_uv_udp_socket((*handle_ptr).data.cast());
            (*buf).base = lean_sarray_cptr((*udp_socket).m_byte_array)
                .cast_mut()
                .cast::<c_char>();
            (*buf).len = lean_sarray_capacity((*udp_socket).m_byte_array);
        }

        unsafe extern "C" fn recv_cb(
            handle: *mut c_void,
            nread: isize,
            _buf: *const uv_buf_t,
            addr: *const libc::sockaddr,
            _flags: c_uint,
        ) {
            uv_udp_recv_stop(handle);

            let handle_ptr = handle.cast::<UvHandle>();
            let udp_socket = lean_to_uv_udp_socket((*handle_ptr).data.cast());
            let promise = (*udp_socket).m_promise_read;
            let byte_array = (*udp_socket).m_byte_array;

            (*udp_socket).m_promise_read = null_mut();
            (*udp_socket).m_byte_array = null_mut();

            if nread >= 0 {
                lean_sarray_set_size(byte_array, nread as Size);

                let addr_obj = if !addr.is_null() {
                    option_some(lean_sockaddr_to_socketaddress(addr))
                } else {
                    option_none()
                };

                let prod = lean_runtime_alloc_ctor(0, 2, 0);
                lean_runtime_ctor_set(prod, 0, byte_array);
                lean_runtime_ctor_set(prod, 1, addr_obj);

                lean_promise_resolve(mk_except_ok(prod), promise);
            } else if nread < 0 {
                lean_dec(byte_array);
                lean_promise_resolve(
                    mk_except_err(lean_decode_uv_error(nread as c_int, null_mut())),
                    promise,
                );
            }

            lean_dec(promise);
            lean_dec((*handle_ptr).data.cast::<LeanObject>());
        }

        let result = uv_udp_recv_start((*udp_socket).m_uv_udp, Some(alloc_cb), Some(recv_cb));

        if result < 0 {
            (*udp_socket).m_byte_array = null_mut();
            (*udp_socket).m_promise_read = null_mut();

            event_loop_unlock(addr_of_mut!(_ZN4lean9global_evE));

            lean_dec(byte_array);
            lean_dec(promise);
            lean_dec(promise);
            lean_dec(socket);

            return lean_io_result_mk_error(lean_decode_uv_error(result, null_mut()));
        }

        event_loop_unlock(addr_of_mut!(_ZN4lean9global_evE));

        lean_io_result_mk_ok(promise)
    }

    #[inline]
    pub(crate) unsafe fn lean_uv_udp_wait_readable(socket: *mut LeanObject) -> *mut LeanObject {
        let udp_socket = lean_to_uv_udp_socket(socket);

        event_loop_lock(addr_of_mut!(_ZN4lean9global_evE));

        if !(*udp_socket).m_promise_read.is_null() {
            event_loop_unlock(addr_of_mut!(_ZN4lean9global_evE));
            return lean_io_result_mk_error(lean_decode_uv_error(UV_EALREADY, null_mut()));
        }

        let promise = lean_io_promise_new();
        lean_mark_mt(promise);

        (*udp_socket).m_promise_read = promise;

        lean_inc(promise);
        lean_inc(socket);

        unsafe extern "C" fn alloc_cb(
            _handle: *mut c_void,
            _suggested_size: usize,
            buf: *mut uv_buf_t,
        ) {
            (*buf).base = null_mut();
            (*buf).len = 0;
        }

        unsafe extern "C" fn recv_cb(
            handle: *mut c_void,
            nread: isize,
            _buf: *const uv_buf_t,
            _addr: *const libc::sockaddr,
            _flags: c_uint,
        ) {
            uv_udp_recv_stop(handle);

            let handle_ptr = handle.cast::<UvHandle>();
            let udp_socket = lean_to_uv_udp_socket((*handle_ptr).data.cast());
            let promise = (*udp_socket).m_promise_read;

            (*udp_socket).m_promise_read = null_mut();

            if nread == UV_ENOBUFS {
                lean_promise_resolve(mk_except_ok(lean_box(0)), promise);
            } else if nread < 0 {
                lean_promise_resolve(
                    mk_except_err(lean_decode_uv_error(nread as c_int, null_mut())),
                    promise,
                );
            } else {
                assert!(false);
            }

            lean_dec(promise);
            lean_dec((*handle_ptr).data.cast::<LeanObject>());
        }

        let result = uv_udp_recv_start((*udp_socket).m_uv_udp, Some(alloc_cb), Some(recv_cb));

        if result < 0 {
            (*udp_socket).m_promise_read = null_mut();

            event_loop_unlock(addr_of_mut!(_ZN4lean9global_evE));

            lean_dec(promise);
            lean_dec(promise);
            lean_dec(socket);

            return lean_io_result_mk_error(lean_decode_uv_error(result, null_mut()));
        }

        event_loop_unlock(addr_of_mut!(_ZN4lean9global_evE));

        lean_io_result_mk_ok(promise)
    }

    #[inline]
    pub(crate) unsafe fn lean_uv_udp_cancel_recv(socket: *mut LeanObject) -> *mut LeanObject {
        let udp_socket = lean_to_uv_udp_socket(socket);

        lean_inc(socket);
        event_loop_lock(addr_of_mut!(_ZN4lean9global_evE));

        if (*udp_socket).m_promise_read.is_null() {
            event_loop_unlock(addr_of_mut!(_ZN4lean9global_evE));
            lean_dec(socket);
            return lean_io_result_mk_ok(lean_box(0));
        }

        uv_udp_recv_stop((*udp_socket).m_uv_udp);

        let promise = (*udp_socket).m_promise_read;
        lean_dec(promise);
        (*udp_socket).m_promise_read = null_mut();

        let byte_array = (*udp_socket).m_byte_array;
        if !byte_array.is_null() {
            lean_dec(byte_array);
            (*udp_socket).m_byte_array = null_mut();
        }

        event_loop_unlock(addr_of_mut!(_ZN4lean9global_evE));
        lean_dec(socket);

        lean_io_result_mk_ok(lean_box(0))
    }

    #[inline]
    pub(crate) unsafe fn lean_uv_udp_getpeername(socket: *mut LeanObject) -> *mut LeanObject {
        let udp_socket = lean_to_uv_udp_socket(socket);
        let mut addr_storage = MaybeUninit::<libc::sockaddr_storage>::uninit();
        let mut addr_len = core::mem::size_of::<libc::sockaddr_storage>() as c_int;

        event_loop_lock(addr_of_mut!(_ZN4lean9global_evE));
        let result = uv_udp_getpeername(
            (*udp_socket).m_uv_udp,
            addr_storage.as_mut_ptr().cast(),
            &mut addr_len,
        );
        event_loop_unlock(addr_of_mut!(_ZN4lean9global_evE));

        if result < 0 {
            return lean_io_result_mk_error(lean_decode_uv_error(result, null_mut()));
        }

        let lean_addr = lean_sockaddr_to_socketaddress(addr_storage.as_ptr().cast());
        lean_io_result_mk_ok(lean_addr)
    }

    #[inline]
    pub(crate) unsafe fn lean_uv_udp_getsockname(socket: *mut LeanObject) -> *mut LeanObject {
        let udp_socket = lean_to_uv_udp_socket(socket);
        let mut addr_storage = MaybeUninit::<libc::sockaddr_storage>::uninit();
        let mut addr_len = core::mem::size_of::<libc::sockaddr_storage>() as c_int;

        event_loop_lock(addr_of_mut!(_ZN4lean9global_evE));
        let result = uv_udp_getsockname(
            (*udp_socket).m_uv_udp,
            addr_storage.as_mut_ptr().cast(),
            &mut addr_len,
        );
        event_loop_unlock(addr_of_mut!(_ZN4lean9global_evE));

        if result < 0 {
            return lean_io_result_mk_error(lean_decode_uv_error(result, null_mut()));
        }

        let lean_addr = lean_sockaddr_to_socketaddress(addr_storage.as_ptr().cast());
        lean_io_result_mk_ok(lean_addr)
    }

    #[inline]
    pub(crate) unsafe fn lean_uv_udp_set_broadcast(
        socket: *mut LeanObject,
        enable: u8,
    ) -> *mut LeanObject {
        let udp_socket = lean_to_uv_udp_socket(socket);

        event_loop_lock(addr_of_mut!(_ZN4lean9global_evE));
        let result = uv_udp_set_broadcast((*udp_socket).m_uv_udp, enable as c_int);
        event_loop_unlock(addr_of_mut!(_ZN4lean9global_evE));

        if result < 0 {
            return lean_io_result_mk_error(lean_decode_uv_error(result, null_mut()));
        }

        lean_io_result_mk_ok(lean_box(0))
    }

    #[inline]
    pub(crate) unsafe fn lean_uv_udp_set_multicast_loop(
        socket: *mut LeanObject,
        enable: u8,
    ) -> *mut LeanObject {
        let udp_socket = lean_to_uv_udp_socket(socket);

        event_loop_lock(addr_of_mut!(_ZN4lean9global_evE));
        let result = uv_udp_set_multicast_loop((*udp_socket).m_uv_udp, enable as c_int);
        event_loop_unlock(addr_of_mut!(_ZN4lean9global_evE));

        if result < 0 {
            return lean_io_result_mk_error(lean_decode_uv_error(result, null_mut()));
        }

        lean_io_result_mk_ok(lean_box(0))
    }

    #[inline]
    pub(crate) unsafe fn lean_uv_udp_set_multicast_ttl(
        socket: *mut LeanObject,
        ttl: u32,
    ) -> *mut LeanObject {
        let udp_socket = lean_to_uv_udp_socket(socket);

        event_loop_lock(addr_of_mut!(_ZN4lean9global_evE));
        let result = uv_udp_set_multicast_ttl((*udp_socket).m_uv_udp, ttl as c_int);
        event_loop_unlock(addr_of_mut!(_ZN4lean9global_evE));

        if result < 0 {
            return lean_io_result_mk_error(lean_decode_uv_error(result, null_mut()));
        }

        lean_io_result_mk_ok(lean_box(0))
    }

    const INET_ADDRSTRLEN: usize = 16;

    #[inline]
    pub(crate) unsafe fn lean_uv_udp_set_membership(
        socket: *mut LeanObject,
        multicast_addr: *mut LeanObject,
        interface_addr: *mut LeanObject,
        membership: u8,
    ) -> *mut LeanObject {
        let udp_socket = lean_to_uv_udp_socket(socket);

        let mut multicast_addr_str = [0 as c_char; INET_ADDRSTRLEN];
        lean_ip_addr_ntop(
            multicast_addr,
            multicast_addr_str.as_mut_ptr(),
            multicast_addr_str.len(),
        );

        let is_interface_null = lean_is_scalar(interface_addr);
        let mut interface_addr_str = [0 as c_char; INET_ADDRSTRLEN];

        if !is_interface_null {
            let interface_addr_obj = lean_ctor_get(interface_addr, 0);
            lean_ip_addr_ntop(
                interface_addr_obj,
                interface_addr_str.as_mut_ptr(),
                interface_addr_str.len(),
            );
        }

        event_loop_lock(addr_of_mut!(_ZN4lean9global_evE));
        let result = uv_udp_set_membership(
            (*udp_socket).m_uv_udp,
            multicast_addr_str.as_ptr(),
            if is_interface_null {
                null_mut()
            } else {
                interface_addr_str.as_ptr()
            },
            membership as c_int,
        );
        event_loop_unlock(addr_of_mut!(_ZN4lean9global_evE));

        if result < 0 {
            return lean_io_result_mk_error(lean_decode_uv_error(result, null_mut()));
        }

        lean_io_result_mk_ok(lean_box(0))
    }

    #[inline]
    pub(crate) unsafe fn lean_uv_udp_set_multicast_interface(
        socket: *mut LeanObject,
        interface_addr: *mut LeanObject,
    ) -> *mut LeanObject {
        let udp_socket = lean_to_uv_udp_socket(socket);

        let mut interface_addr_str = [0 as c_char; INET_ADDRSTRLEN];
        lean_ip_addr_ntop(
            interface_addr,
            interface_addr_str.as_mut_ptr(),
            interface_addr_str.len(),
        );

        event_loop_lock(addr_of_mut!(_ZN4lean9global_evE));
        let result =
            uv_udp_set_multicast_interface((*udp_socket).m_uv_udp, interface_addr_str.as_ptr());
        event_loop_unlock(addr_of_mut!(_ZN4lean9global_evE));

        if result < 0 {
            return lean_io_result_mk_error(lean_decode_uv_error(result, null_mut()));
        }

        lean_io_result_mk_ok(lean_box(0))
    }

    #[inline]
    pub(crate) unsafe fn lean_uv_udp_set_ttl(
        socket: *mut LeanObject,
        ttl: u32,
    ) -> *mut LeanObject {
        let udp_socket = lean_to_uv_udp_socket(socket);

        event_loop_lock(addr_of_mut!(_ZN4lean9global_evE));
        let result = uv_udp_set_ttl((*udp_socket).m_uv_udp, ttl as c_int);
        event_loop_unlock(addr_of_mut!(_ZN4lean9global_evE));

        if result < 0 {
            return lean_io_result_mk_error(lean_decode_uv_error(result, null_mut()));
        }

        lean_io_result_mk_ok(lean_box(0))
    }
}

#[cfg(all(feature = "std", target_family = "wasm"))]
pub(crate) mod runtime_udp_impl {
    use super::*;

    #[inline]
    pub(crate) fn initialize_libuv_udp_socket() {}

    #[inline]
    pub(crate) fn lean_uv_udp_new() -> *mut LeanObject {
        panic!("Please build a version of Lean4 with libuv to invoke this.");
    }
    #[inline]
    pub(crate) fn lean_uv_udp_bind(_: *mut LeanObject, _: *mut LeanObject) -> *mut LeanObject {
        panic!("Please build a version of Lean4 with libuv to invoke this.");
    }
    #[inline]
    pub(crate) fn lean_uv_udp_connect(
        _: *mut LeanObject,
        _: *mut LeanObject,
    ) -> *mut LeanObject {
        panic!("Please build a version of Lean4 with libuv to invoke this.");
    }
    #[inline]
    pub(crate) fn lean_uv_udp_send(
        _: *mut LeanObject,
        _: *mut LeanObject,
        _: *mut LeanObject,
    ) -> *mut LeanObject {
        panic!("Please build a version of Lean4 with libuv to invoke this.");
    }
    #[inline]
    pub(crate) fn lean_uv_udp_recv(_: *mut LeanObject, _: u64) -> *mut LeanObject {
        panic!("Please build a version of Lean4 with libuv to invoke this.");
    }
    #[inline]
    pub(crate) fn lean_uv_udp_wait_readable(_: *mut LeanObject) -> *mut LeanObject {
        panic!("Please build a version of Lean4 with libuv to invoke this.");
    }
    #[inline]
    pub(crate) fn lean_uv_udp_cancel_recv(_: *mut LeanObject) -> *mut LeanObject {
        panic!("Please build a version of Lean4 with libuv to invoke this.");
    }
    #[inline]
    pub(crate) fn lean_uv_udp_getpeername(_: *mut LeanObject) -> *mut LeanObject {
        panic!("Please build a version of Lean4 with libuv to invoke this.");
    }
    #[inline]
    pub(crate) fn lean_uv_udp_getsockname(_: *mut LeanObject) -> *mut LeanObject {
        panic!("Please build a version of Lean4 with libuv to invoke this.");
    }
    #[inline]
    pub(crate) fn lean_uv_udp_set_broadcast(_: *mut LeanObject, _: u8) -> *mut LeanObject {
        panic!("Please build a version of Lean4 with libuv to invoke this.");
    }
    #[inline]
    pub(crate) fn lean_uv_udp_set_multicast_loop(_: *mut LeanObject, _: u8) -> *mut LeanObject {
        panic!("Please build a version of Lean4 with libuv to invoke this.");
    }
    #[inline]
    pub(crate) fn lean_uv_udp_set_multicast_ttl(_: *mut LeanObject, _: u32) -> *mut LeanObject {
        panic!("Please build a version of Lean4 with libuv to invoke this.");
    }
    #[inline]
    pub(crate) fn lean_uv_udp_set_membership(
        _: *mut LeanObject,
        _: *mut LeanObject,
        _: *mut LeanObject,
        _: u8,
    ) -> *mut LeanObject {
        panic!("Please build a version of Lean4 with libuv to invoke this.");
    }
    #[inline]
    pub(crate) fn lean_uv_udp_set_multicast_interface(
        _: *mut LeanObject,
        _: *mut LeanObject,
    ) -> *mut LeanObject {
        panic!("Please build a version of Lean4 with libuv to invoke this.");
    }
    #[inline]
    pub(crate) fn lean_uv_udp_set_ttl(_: *mut LeanObject, _: u32) -> *mut LeanObject {
        panic!("Please build a version of Lean4 with libuv to invoke this.");
    }
}
