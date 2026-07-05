/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

use leanh::*;
use core::ffi::{c_char, c_int, c_long, c_uchar, c_uint, c_void, CStr};
use core::ptr;
use core::sync::atomic::{AtomicBool, AtomicI32, AtomicPtr, AtomicU32, Ordering};


#[cfg(all(feature = "std", not(target_family = "wasm")))]
pub(crate) mod runtime_tcp_impl {
    use core::mem::MaybeUninit;
    use core::ptr::{addr_of_mut, null_mut};

    #[repr(C)]
    pub struct LeanUvTcpSocketObject {
        pub m_uv_tcp: *mut c_void, // uv_tcp_t*
        pub m_promise_accept: *mut LeanObject,
        pub m_promise_read: *mut LeanObject,
        pub m_promise_shutdown: *mut LeanObject,
        pub m_client: *mut LeanObject,
        pub m_byte_array: *mut LeanObject,
    }

    #[repr(C)]
    struct TcpConnectData {
        promise: *mut LeanObject,
        socket: *mut LeanObject,
    }

    #[repr(C)]
    struct TcpSendData {
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
    struct uv_connect_t {
        _storage: [u8; 96],
    }

    #[repr(C, align(8))]
    struct uv_write_t {
        _storage: [u8; 192],
    }

    #[repr(C, align(8))]
    struct uv_shutdown_t {
        _storage: [u8; 80],
    }

    extern "C" {
        fn uv_tcp_init(loop_: *mut c_void, handle: *mut c_void) -> c_int;
        fn uv_tcp_connect(
            req: *mut uv_connect_t,
            handle: *mut c_void,
            addr: *const libc::sockaddr,
            cb: Option<unsafe extern "C" fn(*mut uv_connect_t, c_int)>,
        ) -> c_int;
        fn uv_write(
            req: *mut uv_write_t,
            handle: *mut c_void,
            bufs: *const uv_buf_t,
            nbufs: c_uint,
            cb: Option<unsafe extern "C" fn(*mut uv_write_t, c_int)>,
        ) -> c_int;
        fn uv_read_start(
            stream: *mut c_void,
            alloc_cb: Option<unsafe extern "C" fn(*mut c_void, usize, *mut uv_buf_t)>,
            read_cb: Option<unsafe extern "C" fn(*mut c_void, isize, *const uv_buf_t)>,
        ) -> c_int;
        fn uv_read_stop(stream: *mut c_void) -> c_int;
        fn uv_tcp_bind(handle: *mut c_void, addr: *const libc::sockaddr, flags: c_uint) -> c_int;
        fn uv_listen(
            stream: *mut c_void,
            backlog: c_int,
            cb: Option<unsafe extern "C" fn(*mut c_void, c_int)>,
        ) -> c_int;
        fn uv_accept(server: *mut c_void, client: *mut c_void) -> c_int;
        fn uv_shutdown(
            req: *mut uv_shutdown_t,
            handle: *mut c_void,
            cb: Option<unsafe extern "C" fn(*mut uv_shutdown_t, c_int)>,
        ) -> c_int;
        fn uv_tcp_getpeername(
            handle: *const c_void,
            name: *mut libc::sockaddr,
            namelen: *mut c_int,
        ) -> c_int;
        fn uv_tcp_getsockname(
            handle: *const c_void,
            name: *mut libc::sockaddr,
            namelen: *mut c_int,
        ) -> c_int;
        fn uv_tcp_nodelay(handle: *mut c_void, enable: c_int) -> c_int;
        fn uv_tcp_keepalive(handle: *mut c_void, enable: c_int, delay: c_uint) -> c_int;

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

    static mut g_uv_tcp_socket_external_class: *mut LeanExternalClass = null_mut();

    unsafe fn lean_uv_tcp_socket_new(s: *mut LeanUvTcpSocketObject) -> *mut LeanObject {
        lean_runtime_alloc_external(g_uv_tcp_socket_external_class, s.cast())
    }

    unsafe fn lean_to_uv_tcp_socket(o: *mut LeanObject) -> *mut LeanUvTcpSocketObject {
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

    unsafe fn lean_uv_tcp_socket_finalizer(ptr: *mut c_void) {
        let tcp_socket = ptr.cast::<LeanUvTcpSocketObject>();
        assert!((*tcp_socket).m_promise_shutdown.is_null());
        assert!((*tcp_socket).m_promise_accept.is_null());
        assert!((*tcp_socket).m_promise_read.is_null());
        assert!((*tcp_socket).m_byte_array.is_null());

        let handle = (*tcp_socket).m_uv_tcp.cast::<UvHandle>();
        (*handle).data = ptr;

        event_loop_lock(addr_of_mut!(_ZN4lean9global_evE));

        unsafe fn close_cb(handle: *mut UvHandle) {
            let tcp_socket = (*handle).data.cast::<LeanUvTcpSocketObject>();
            libc::free((*tcp_socket).m_uv_tcp);
            libc::free(tcp_socket.cast());
        }

        uv_close((*tcp_socket).m_uv_tcp.cast::<UvHandle>(), Some(close_cb));

        event_loop_unlock(addr_of_mut!(_ZN4lean9global_evE));
    }

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

        g_uv_tcp_socket_external_class =
            lean_register_external_class(Some(lean_uv_tcp_socket_finalizer), Some(foreach_cb));
    }

    const UV_EALREADY: c_int = -3003;
    const UV_EOF: isize = -4095;
    const UV_ENOBUFS: isize = -105;
    const UV_EAGAIN: c_int = -11;

    #[inline]
    pub(crate) unsafe fn lean_uv_tcp_new() -> *mut LeanObject { // [lean-audit] Lean imports from Rust ([extern]): Rust defined this function and function body is not empty (correct) (✅) | Lean: src/Std/Internal/UV/TCP.lean:36
        let tcp_socket = libc::malloc(core::mem::size_of::<LeanUvTcpSocketObject>())
            .cast::<LeanUvTcpSocketObject>();
        if tcp_socket.is_null() {
            return lean_io_result_mk_error(lean_decode_io_error(libc::ENOMEM, null_mut()));
        }

        (*tcp_socket).m_promise_accept = null_mut();
        (*tcp_socket).m_promise_shutdown = null_mut();
        (*tcp_socket).m_promise_read = null_mut();
        (*tcp_socket).m_byte_array = null_mut();
        (*tcp_socket).m_client = null_mut();

        let uv_tcp = libc::malloc(248); // sizeof(uv_tcp_t)
        if uv_tcp.is_null() {
            libc::free(tcp_socket.cast());
            return lean_io_result_mk_error(lean_decode_io_error(libc::ENOMEM, null_mut()));
        }

        event_loop_lock(addr_of_mut!(_ZN4lean9global_evE));
        let result = uv_tcp_init(_ZN4lean9global_evE.loop_.cast(), uv_tcp);
        event_loop_unlock(addr_of_mut!(_ZN4lean9global_evE));

        if result != 0 {
            libc::free(uv_tcp);
            libc::free(tcp_socket.cast());
            return lean_io_result_mk_error(lean_decode_uv_error(result, null_mut()));
        }

        (*tcp_socket).m_uv_tcp = uv_tcp;

        let obj = lean_uv_tcp_socket_new(tcp_socket);
        lean_mark_mt(obj);

        let handle = (*tcp_socket).m_uv_tcp.cast::<UvHandle>();
        (*handle).data = obj.cast();

        lean_io_result_mk_ok(obj)
    }

    #[inline]
    pub(crate) unsafe fn lean_uv_tcp_connect( // [lean-audit] Lean imports from Rust ([extern]): Rust defined this function and function body is not empty (correct) (✅) | Lean: src/Std/Internal/UV/TCP.lean:42
        socket: *mut LeanObject,
        addr: *mut LeanObject,
    ) -> *mut LeanObject {
        let tcp_socket = lean_to_uv_tcp_socket(socket);

        let mut addr_struct = MaybeUninit::<libc::sockaddr_storage>::uninit();
        lean_socket_address_to_sockaddr_storage(addr, addr_struct.as_mut_ptr());

        let uv_connect = libc::malloc(core::mem::size_of::<uv_connect_t>()).cast::<uv_connect_t>();
        if uv_connect.is_null() {
            return lean_io_result_mk_error(lean_decode_io_error(libc::ENOMEM, null_mut()));
        }
        let connect_data =
            libc::malloc(core::mem::size_of::<TcpConnectData>()).cast::<TcpConnectData>();
        if connect_data.is_null() {
            libc::free(uv_connect.cast());
            return lean_io_result_mk_error(lean_decode_io_error(libc::ENOMEM, null_mut()));
        }

        let promise = lean_io_promise_new();
        lean_mark_mt(promise);

        (*connect_data).promise = promise;
        (*connect_data).socket = socket;

        let req_handle = uv_connect.cast::<UvHandle>();
        (*req_handle).data = connect_data.cast();

        lean_inc(socket);
        lean_inc(promise);

        event_loop_lock(addr_of_mut!(_ZN4lean9global_evE));

        unsafe extern "C" fn connect_cb(req: *mut uv_connect_t, status: c_int) {
            let req_handle = req.cast::<UvHandle>();
            let tup = (*req_handle).data.cast::<TcpConnectData>();
            lean_promise_resolve_with_code(status, (*tup).promise);

            lean_dec((*tup).socket);
            lean_dec((*tup).promise);

            libc::free((*req_handle).data);
            libc::free(req.cast());
        }

        let result = uv_tcp_connect(
            uv_connect,
            (*tcp_socket).m_uv_tcp,
            addr_struct.as_ptr().cast(),
            Some(connect_cb),
        );

        event_loop_unlock(addr_of_mut!(_ZN4lean9global_evE));

        if result < 0 {
            lean_dec(promise);
            lean_dec(promise);
            lean_dec(socket);

            let req_handle = uv_connect.cast::<UvHandle>();
            libc::free((*req_handle).data);
            libc::free(uv_connect.cast());

            return lean_io_result_mk_error(lean_decode_uv_error(result, null_mut()));
        }

        lean_io_result_mk_ok(promise)
    }

    #[inline]
    pub(crate) unsafe fn lean_uv_tcp_send( // [lean-audit] Lean imports from Rust ([extern]): Rust defined this function and function body is not empty (correct) (✅) | Lean: src/Std/Internal/UV/TCP.lean:48
        socket: *mut LeanObject,
        data_array: *mut LeanObject,
    ) -> *mut LeanObject {
        let tcp_socket = lean_to_uv_tcp_socket(socket);
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

        let write_uv = libc::malloc(core::mem::size_of::<uv_write_t>()).cast::<uv_write_t>();
        if write_uv.is_null() {
            lean_dec(data_array);
            libc::free(bufs.cast());
            return lean_io_result_mk_error(lean_decode_io_error(libc::ENOMEM, null_mut()));
        }

        let write_handle = write_uv.cast::<UvHandle>();
        (*write_handle).data = libc::malloc(core::mem::size_of::<TcpSendData>());
        if (*write_handle).data.is_null() {
            lean_dec(data_array);
            libc::free(bufs.cast());
            libc::free(write_uv.cast());
            return lean_io_result_mk_error(lean_decode_io_error(libc::ENOMEM, null_mut()));
        }

        let promise = lean_io_promise_new();
        lean_mark_mt(promise);

        let send_data = (*write_handle).data.cast::<TcpSendData>();
        (*send_data).promise = promise;
        (*send_data).data = data_array;
        (*send_data).socket = socket;
        (*send_data).bufs = bufs;

        lean_inc(promise);
        lean_inc(socket);

        event_loop_lock(addr_of_mut!(_ZN4lean9global_evE));

        unsafe extern "C" fn write_cb(req: *mut uv_write_t, status: c_int) {
            let req_handle = req.cast::<UvHandle>();
            let tup = (*req_handle).data.cast::<TcpSendData>();

            lean_promise_resolve_with_code(status, (*tup).promise);

            lean_dec((*tup).promise);
            lean_dec((*tup).data);
            lean_dec((*tup).socket);

            libc::free((*tup).bufs.cast());
            libc::free((*req_handle).data);
            libc::free(req.cast());
        }

        let result = uv_write(
            write_uv,
            (*tcp_socket).m_uv_tcp,
            bufs,
            array_len as c_uint,
            Some(write_cb),
        );

        event_loop_unlock(addr_of_mut!(_ZN4lean9global_evE));

        if result < 0 {
            lean_dec(promise);
            lean_dec(promise);
            lean_dec(socket);
            lean_dec(data_array);
            libc::free(bufs.cast());
            libc::free((*write_handle).data);
            libc::free(write_uv.cast());

            return lean_io_result_mk_error(lean_decode_uv_error(result, null_mut()));
        }

        lean_io_result_mk_ok(promise)
    }

    #[inline]
    pub(crate) unsafe fn lean_uv_tcp_recv( // [lean-audit] Lean imports from Rust ([extern]): Rust defined this function and function body is not empty (correct) (✅) | Lean: src/Std/Internal/UV/TCP.lean:58
        socket: *mut LeanObject,
        buffer_size: u64,
    ) -> *mut LeanObject {
        let tcp_socket = lean_to_uv_tcp_socket(socket);

        event_loop_lock(addr_of_mut!(_ZN4lean9global_evE));

        if !(*tcp_socket).m_promise_read.is_null() {
            event_loop_unlock(addr_of_mut!(_ZN4lean9global_evE));
            return lean_io_result_mk_error(lean_decode_uv_error(UV_EALREADY, null_mut()));
        }

        let byte_array = lean_alloc_sarray(1, 0, buffer_size as Size);
        (*tcp_socket).m_byte_array = byte_array;

        let promise = lean_io_promise_new();
        lean_mark_mt(promise);

        (*tcp_socket).m_promise_read = promise;

        lean_inc(socket);
        lean_inc(promise);

        unsafe extern "C" fn alloc_cb(
            handle: *mut c_void,
            _suggested_size: usize,
            buf: *mut uv_buf_t,
        ) {
            let handle_ptr = handle.cast::<UvHandle>();
            let tcp_socket = lean_to_uv_tcp_socket((*handle_ptr).data.cast());
            (*buf).base = lean_sarray_cptr((*tcp_socket).m_byte_array)
                .cast_mut()
                .cast::<c_char>();
            (*buf).len = lean_sarray_capacity((*tcp_socket).m_byte_array);
        }

        unsafe extern "C" fn read_cb(stream: *mut c_void, nread: isize, _buf: *const uv_buf_t) {
            uv_read_stop(stream);

            let handle_ptr = stream.cast::<UvHandle>();
            let tcp_socket = lean_to_uv_tcp_socket((*handle_ptr).data.cast());
            let promise = (*tcp_socket).m_promise_read;
            let byte_array = (*tcp_socket).m_byte_array;

            (*tcp_socket).m_promise_read = null_mut();
            (*tcp_socket).m_byte_array = null_mut();

            if nread >= 0 {
                lean_sarray_set_size(byte_array, nread as Size);
                lean_promise_resolve(mk_except_ok(option_some(byte_array)), promise);
            } else if nread == UV_EOF {
                lean_dec(byte_array);
                lean_promise_resolve(mk_except_ok(option_none()), promise);
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

        let result = uv_read_start((*tcp_socket).m_uv_tcp, Some(alloc_cb), Some(read_cb));

        if result < 0 {
            (*tcp_socket).m_byte_array = null_mut();
            (*tcp_socket).m_promise_read = null_mut();

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
    pub(crate) unsafe fn lean_uv_tcp_wait_readable(socket: *mut LeanObject) -> *mut LeanObject { // [lean-audit] Lean imports from Rust ([extern]): Rust defined this function and function body is not empty (correct) (✅) | Lean: src/Std/Internal/UV/TCP.lean:66
        let tcp_socket = lean_to_uv_tcp_socket(socket);

        event_loop_lock(addr_of_mut!(_ZN4lean9global_evE));

        if !(*tcp_socket).m_promise_read.is_null() {
            event_loop_unlock(addr_of_mut!(_ZN4lean9global_evE));
            return lean_io_result_mk_error(lean_decode_uv_error(UV_EALREADY, null_mut()));
        }

        let promise = lean_io_promise_new();
        lean_mark_mt(promise);

        (*tcp_socket).m_promise_read = promise;

        lean_inc(socket);
        lean_inc(promise);

        unsafe extern "C" fn alloc_cb(
            _handle: *mut c_void,
            _suggested_size: usize,
            buf: *mut uv_buf_t,
        ) {
            (*buf).base = null_mut();
            (*buf).len = 0;
        }

        unsafe extern "C" fn read_cb(stream: *mut c_void, nread: isize, _buf: *const uv_buf_t) {
            uv_read_stop(stream);

            let handle_ptr = stream.cast::<UvHandle>();
            let tcp_socket = lean_to_uv_tcp_socket((*handle_ptr).data.cast());
            let promise = (*tcp_socket).m_promise_read;

            (*tcp_socket).m_promise_read = null_mut();

            if nread == UV_ENOBUFS {
                lean_promise_resolve(mk_except_ok(lean_box(1)), promise);
            } else if nread == UV_EOF {
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

        let result = uv_read_start((*tcp_socket).m_uv_tcp, Some(alloc_cb), Some(read_cb));

        if result < 0 {
            (*tcp_socket).m_promise_read = null_mut();

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
    pub(crate) unsafe fn lean_uv_tcp_cancel_recv(socket: *mut LeanObject) -> *mut LeanObject { // [lean-audit] Lean imports from Rust ([extern]): Rust defined this function and function body is not empty (correct) (✅) | Lean: src/Std/Internal/UV/TCP.lean:77
        let tcp_socket = lean_to_uv_tcp_socket(socket);

        event_loop_lock(addr_of_mut!(_ZN4lean9global_evE));

        if (*tcp_socket).m_promise_read.is_null() {
            event_loop_unlock(addr_of_mut!(_ZN4lean9global_evE));
            return lean_io_result_mk_ok(lean_box(0));
        }

        uv_read_stop((*tcp_socket).m_uv_tcp);

        let promise = (*tcp_socket).m_promise_read;
        lean_dec(promise);
        (*tcp_socket).m_promise_read = null_mut();

        let byte_array = (*tcp_socket).m_byte_array;
        if !byte_array.is_null() {
            lean_dec(byte_array);
            (*tcp_socket).m_byte_array = null_mut();
        }

        lean_dec(socket);

        event_loop_unlock(addr_of_mut!(_ZN4lean9global_evE));
        lean_io_result_mk_ok(lean_box(0))
    }

    #[inline]
    pub(crate) unsafe fn lean_uv_tcp_bind( // [lean-audit] Lean imports from Rust ([extern]): Rust defined this function and function body is not empty (correct) (✅) | Lean: src/Std/Internal/UV/TCP.lean:83
        socket: *mut LeanObject,
        addr: *mut LeanObject,
    ) -> *mut LeanObject {
        let tcp_socket = lean_to_uv_tcp_socket(socket);

        let mut addr_ptr = MaybeUninit::<libc::sockaddr_storage>::uninit();
        lean_socket_address_to_sockaddr_storage(addr, addr_ptr.as_mut_ptr());

        event_loop_lock(addr_of_mut!(_ZN4lean9global_evE));
        let result = uv_tcp_bind((*tcp_socket).m_uv_tcp, addr_ptr.as_ptr().cast(), 0);
        event_loop_unlock(addr_of_mut!(_ZN4lean9global_evE));

        if result < 0 {
            return lean_io_result_mk_error(lean_decode_uv_error(result, null_mut()));
        }

        lean_io_result_mk_ok(lean_box(0))
    }

    #[inline]
    pub(crate) unsafe fn lean_uv_tcp_listen( // [lean-audit] Lean imports from Rust ([extern]): Rust defined this function and function body is not empty (correct) (✅) | Lean: src/Std/Internal/UV/TCP.lean:89
        socket: *mut LeanObject,
        backlog: i32,
    ) -> *mut LeanObject {
        let tcp_socket = lean_to_uv_tcp_socket(socket);

        event_loop_lock(addr_of_mut!(_ZN4lean9global_evE));

        unsafe extern "C" fn listen_cb(stream: *mut c_void, status: c_int) {
            let stream_handle = stream.cast::<UvHandle>();
            let tcp_socket = lean_to_uv_tcp_socket((*stream_handle).data.cast());

            if (*tcp_socket).m_promise_accept.is_null() {
                return;
            }

            let promise = (*tcp_socket).m_promise_accept;

            if status < 0 {
                lean_promise_resolve_with_code(status, promise);
                lean_dec(promise);
                (*tcp_socket).m_promise_accept = null_mut();
                return;
            }

            let client = (*tcp_socket).m_client;
            let client_socket = lean_to_uv_tcp_socket(client);

            let result = uv_accept((*tcp_socket).m_uv_tcp, (*client_socket).m_uv_tcp);

            (*tcp_socket).m_promise_accept = null_mut();
            (*tcp_socket).m_client = null_mut();

            if result < 0 {
                lean_dec(client);
                lean_promise_resolve_with_code(result, promise);
                lean_dec(promise);
                return;
            }

            lean_promise_resolve(mk_except_ok(client), promise);
            lean_dec(promise);

            lean_dec((*stream_handle).data.cast::<LeanObject>());
        }

        let result = uv_listen((*tcp_socket).m_uv_tcp, backlog, Some(listen_cb));

        event_loop_unlock(addr_of_mut!(_ZN4lean9global_evE));

        if result < 0 {
            return lean_io_result_mk_error(lean_decode_uv_error(result, null_mut()));
        }

        lean_io_result_mk_ok(lean_box(0))
    }

    #[inline]
    pub(crate) unsafe fn lean_uv_tcp_accept(socket: *mut LeanObject) -> *mut LeanObject { // [lean-audit] Lean imports from Rust ([extern]): Rust defined this function and function body is not empty (correct) (✅) | Lean: src/Std/Internal/UV/TCP.lean:95
        let tcp_socket = lean_to_uv_tcp_socket(socket);

        event_loop_lock(addr_of_mut!(_ZN4lean9global_evE));

        if !(*tcp_socket).m_promise_accept.is_null() {
            event_loop_unlock(addr_of_mut!(_ZN4lean9global_evE));
            return lean_io_result_mk_error(lean_decode_uv_error(
                UV_EALREADY,
                lean_mk_string(c"parallel accept is not allowed! consider binding multiple sockets to the same address and accepting on them instead".as_ptr()),
            ));
        }

        let promise = lean_io_promise_new();
        lean_mark_mt(promise);

        let client = lean_io_result_take_value(lean_uv_tcp_new());
        let client_socket = lean_to_uv_tcp_socket(client);

        let result = uv_accept((*tcp_socket).m_uv_tcp, (*client_socket).m_uv_tcp);

        if result < 0 && result != UV_EAGAIN {
            event_loop_unlock(addr_of_mut!(_ZN4lean9global_evE));
            lean_dec(client);
            lean_promise_resolve_with_code(result, promise);
        } else if result >= 0 {
            event_loop_unlock(addr_of_mut!(_ZN4lean9global_evE));
            lean_promise_resolve(mk_except_ok(client), promise);
        } else {
            lean_inc(socket);
            lean_inc(promise);

            (*tcp_socket).m_promise_accept = promise;
            (*tcp_socket).m_client = client;

            event_loop_unlock(addr_of_mut!(_ZN4lean9global_evE));
        }

        lean_io_result_mk_ok(promise)
    }

    #[inline]
    pub(crate) unsafe fn lean_uv_tcp_try_accept(socket: *mut LeanObject) -> *mut LeanObject { // [lean-audit] Lean imports from Rust ([extern]): Rust defined this function and function body is not empty (correct) (✅) | Lean: src/Std/Internal/UV/TCP.lean:101
        let tcp_socket = lean_to_uv_tcp_socket(socket);

        event_loop_lock(addr_of_mut!(_ZN4lean9global_evE));

        if !(*tcp_socket).m_promise_accept.is_null() {
            event_loop_unlock(addr_of_mut!(_ZN4lean9global_evE));
            return lean_io_result_mk_error(lean_decode_uv_error(
                UV_EALREADY,
                lean_mk_string(c"parallel accept is not allowed! consider binding multiple sockets to the same address and accepting on them instead".as_ptr()),
            ));
        }

        let client = lean_io_result_take_value(lean_uv_tcp_new());
        let client_socket = lean_to_uv_tcp_socket(client);

        let result = uv_accept((*tcp_socket).m_uv_tcp, (*client_socket).m_uv_tcp);

        if result < 0 && result != UV_EAGAIN {
            event_loop_unlock(addr_of_mut!(_ZN4lean9global_evE));
            lean_dec(client);
            return lean_io_result_mk_error(lean_decode_uv_error(result, null_mut()));
        } else if result >= 0 {
            event_loop_unlock(addr_of_mut!(_ZN4lean9global_evE));
            return lean_io_result_mk_ok(mk_except_ok(option_some(client)));
        } else {
            event_loop_unlock(addr_of_mut!(_ZN4lean9global_evE));
            lean_dec(client);
            return lean_io_result_mk_ok(mk_except_ok(option_none()));
        }
    }

    #[inline]
    pub(crate) unsafe fn lean_uv_tcp_cancel_accept(socket: *mut LeanObject) -> *mut LeanObject { // [lean-audit] Lean imports from Rust ([extern]): Rust defined this function and function body is not empty (correct) (✅) | Lean: src/Std/Internal/UV/TCP.lean:107
        let tcp_socket = lean_to_uv_tcp_socket(socket);

        event_loop_lock(addr_of_mut!(_ZN4lean9global_evE));

        if (*tcp_socket).m_promise_accept.is_null() {
            event_loop_unlock(addr_of_mut!(_ZN4lean9global_evE));
            return lean_io_result_mk_ok(lean_box(0));
        }

        let promise = (*tcp_socket).m_promise_accept;
        lean_dec(promise);
        (*tcp_socket).m_promise_accept = null_mut();

        let client = (*tcp_socket).m_client;
        if !client.is_null() {
            lean_dec(client);
            (*tcp_socket).m_client = null_mut();
        }

        lean_dec(socket);

        event_loop_unlock(addr_of_mut!(_ZN4lean9global_evE));
        lean_io_result_mk_ok(lean_box(0))
    }

    #[inline]
    pub(crate) unsafe fn lean_uv_tcp_shutdown(socket: *mut LeanObject) -> *mut LeanObject { // [lean-audit] Lean imports from Rust ([extern]): Rust defined this function and function body is not empty (correct) (✅) | Lean: src/Std/Internal/UV/TCP.lean:113
        let tcp_socket = lean_to_uv_tcp_socket(socket);

        event_loop_lock(addr_of_mut!(_ZN4lean9global_evE));

        if !(*tcp_socket).m_promise_shutdown.is_null() {
            event_loop_unlock(addr_of_mut!(_ZN4lean9global_evE));
            return lean_io_result_mk_error(lean_decode_uv_error(
                UV_EALREADY,
                lean_mk_string(c"shutdown already in progress".as_ptr()),
            ));
        }

        let shutdown_req =
            libc::malloc(core::mem::size_of::<uv_shutdown_t>()).cast::<uv_shutdown_t>();
        if shutdown_req.is_null() {
            event_loop_unlock(addr_of_mut!(_ZN4lean9global_evE));
            return lean_io_result_mk_error(lean_decode_io_error(libc::ENOMEM, null_mut()));
        }
        let shutdown_req_handle = shutdown_req.cast::<UvHandle>();
        (*shutdown_req_handle).data = socket.cast();

        let promise = lean_io_promise_new();
        lean_mark_mt(promise);
        (*tcp_socket).m_promise_shutdown = promise;
        lean_inc(promise);
        lean_inc(socket);

        unsafe extern "C" fn shutdown_cb(req: *mut uv_shutdown_t, status: c_int) {
            let req_handle = req.cast::<UvHandle>();
            let tcp_socket = lean_to_uv_tcp_socket((*req_handle).data.cast::<LeanObject>());

            if status < 0 {
                lean_promise_resolve_with_code(status, (*tcp_socket).m_promise_shutdown);
            } else {
                lean_promise_resolve(mk_except_ok(lean_box(0)), (*tcp_socket).m_promise_shutdown);
            }

            lean_dec((*tcp_socket).m_promise_shutdown);
            (*tcp_socket).m_promise_shutdown = null_mut();

            lean_dec((*req_handle).data.cast::<LeanObject>());
            libc::free(req.cast());
        }

        let result = uv_shutdown(shutdown_req, (*tcp_socket).m_uv_tcp, Some(shutdown_cb));

        if result < 0 {
            libc::free(shutdown_req.cast());
            lean_dec((*tcp_socket).m_promise_shutdown);
            (*tcp_socket).m_promise_shutdown = null_mut();
            event_loop_unlock(addr_of_mut!(_ZN4lean9global_evE));

            return lean_io_result_mk_error(lean_decode_uv_error(result, null_mut()));
        }

        event_loop_unlock(addr_of_mut!(_ZN4lean9global_evE));

        lean_io_result_mk_ok(promise)
    }

    #[inline]
    pub(crate) unsafe fn lean_uv_tcp_getpeername(socket: *mut LeanObject) -> *mut LeanObject { // [lean-audit] Lean imports from Rust ([extern]): Rust defined this function and function body is not empty (correct) (✅) | Lean: src/Std/Internal/UV/TCP.lean:119
        let tcp_socket = lean_to_uv_tcp_socket(socket);
        let mut addr_storage = MaybeUninit::<libc::sockaddr_storage>::uninit();
        let mut addr_len = core::mem::size_of::<libc::sockaddr_storage>() as c_int;

        event_loop_lock(addr_of_mut!(_ZN4lean9global_evE));
        let result = uv_tcp_getpeername(
            (*tcp_socket).m_uv_tcp,
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
    pub(crate) unsafe fn lean_uv_tcp_getsockname(socket: *mut LeanObject) -> *mut LeanObject { // [lean-audit] Lean imports from Rust ([extern]): Rust defined this function and function body is not empty (correct) (✅) | Lean: src/Std/Internal/UV/TCP.lean:125
        let tcp_socket = lean_to_uv_tcp_socket(socket);
        let mut addr_storage = MaybeUninit::<libc::sockaddr_storage>::uninit();
        let mut addr_len = core::mem::size_of::<libc::sockaddr_storage>() as c_int;

        event_loop_lock(addr_of_mut!(_ZN4lean9global_evE));
        let result = uv_tcp_getsockname(
            (*tcp_socket).m_uv_tcp,
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
    pub(crate) unsafe fn lean_uv_tcp_nodelay(socket: *mut LeanObject) -> *mut LeanObject { // [lean-audit] Lean imports from Rust ([extern]): Rust defined this function and function body is not empty (correct) (✅) | Lean: src/Std/Internal/UV/TCP.lean:131
        let tcp_socket = lean_to_uv_tcp_socket(socket);

        event_loop_lock(addr_of_mut!(_ZN4lean9global_evE));
        let result = uv_tcp_nodelay((*tcp_socket).m_uv_tcp, 1);
        event_loop_unlock(addr_of_mut!(_ZN4lean9global_evE));

        if result < 0 {
            return lean_io_result_mk_error(lean_decode_uv_error(result, null_mut()));
        }

        lean_io_result_mk_ok(lean_box(0))
    }

    #[inline]
    pub(crate) unsafe fn lean_uv_tcp_keepalive( // [lean-audit] Lean imports from Rust ([extern]): Rust defined this function and function body is not empty (correct) (✅) | Lean: src/Std/Internal/UV/TCP.lean:137
        socket: *mut LeanObject,
        enable: i32,
        delay: u32,
    ) -> *mut LeanObject {
        let tcp_socket = lean_to_uv_tcp_socket(socket);

        event_loop_lock(addr_of_mut!(_ZN4lean9global_evE));
        let result = uv_tcp_keepalive((*tcp_socket).m_uv_tcp, enable, delay);
        event_loop_unlock(addr_of_mut!(_ZN4lean9global_evE));

        if result < 0 {
            return lean_io_result_mk_error(lean_decode_uv_error(result, null_mut()));
        }

        lean_io_result_mk_ok(lean_box(0))
    }
}

#[cfg(all(feature = "std", target_family = "wasm"))]
pub(crate) mod runtime_tcp_impl {

    #[inline]
    pub(crate) fn lean_uv_tcp_new() -> *mut LeanObject {
        panic!("Please build a version of Lean4 with libuv to invoke this.");
    }
    #[inline]
    pub(crate) fn lean_uv_tcp_connect(
        _: *mut LeanObject,
        _: *mut LeanObject,
    ) -> *mut LeanObject {
        panic!("Please build a version of Lean4 with libuv to invoke this.");
    }
    #[inline]
    pub(crate) fn lean_uv_tcp_send(_: *mut LeanObject, _: *mut LeanObject) -> *mut LeanObject {
        panic!("Please build a version of Lean4 with libuv to invoke this.");
    }
    #[inline]
    pub(crate) fn lean_uv_tcp_recv(_: *mut LeanObject, _: u64) -> *mut LeanObject {
        panic!("Please build a version of Lean4 with libuv to invoke this.");
    }
    #[inline]
    pub(crate) fn lean_uv_tcp_wait_readable(_: *mut LeanObject) -> *mut LeanObject {
        panic!("Please build a version of Lean4 with libuv to invoke this.");
    }
    #[inline]
    pub(crate) fn lean_uv_tcp_cancel_recv(_: *mut LeanObject) -> *mut LeanObject {
        panic!("Please build a version of Lean4 with libuv to invoke this.");
    }
    #[inline]
    pub(crate) fn lean_uv_tcp_bind(_: *mut LeanObject, _: *mut LeanObject) -> *mut LeanObject {
        panic!("Please build a version of Lean4 with libuv to invoke this.");
    }
    #[inline]
    pub(crate) fn lean_uv_tcp_listen(_: *mut LeanObject, _: i32) -> *mut LeanObject {
        panic!("Please build a version of Lean4 with libuv to invoke this.");
    }
    #[inline]
    pub(crate) fn lean_uv_tcp_accept(_: *mut LeanObject) -> *mut LeanObject {
        panic!("Please build a version of Lean4 with libuv to invoke this.");
    }
    #[inline]
    pub(crate) fn lean_uv_tcp_try_accept(_: *mut LeanObject) -> *mut LeanObject {
        panic!("Please build a version of Lean4 with libuv to invoke this.");
    }
    #[inline]
    pub(crate) fn lean_uv_tcp_cancel_accept(_: *mut LeanObject) -> *mut LeanObject {
        panic!("Please build a version of Lean4 with libuv to invoke this.");
    }
    #[inline]
    pub(crate) fn lean_uv_tcp_shutdown(_: *mut LeanObject) -> *mut LeanObject {
        panic!("Please build a version of Lean4 with libuv to invoke this.");
    }
    #[inline]
    pub(crate) fn lean_uv_tcp_getpeername(_: *mut LeanObject) -> *mut LeanObject {
        panic!("Please build a version of Lean4 with libuv to invoke this.");
    }
    #[inline]
    pub(crate) fn lean_uv_tcp_getsockname(_: *mut LeanObject) -> *mut LeanObject {
        panic!("Please build a version of Lean4 with libuv to invoke this.");
    }
    #[inline]
    pub(crate) fn lean_uv_tcp_nodelay(_: *mut LeanObject) -> *mut LeanObject {
        panic!("Please build a version of Lean4 with libuv to invoke this.");
    }
    #[inline]
    pub(crate) fn lean_uv_tcp_keepalive(_: *mut LeanObject, _: i32, _: u32) -> *mut LeanObject {
        panic!("Please build a version of Lean4 with libuv to invoke this.");
    }
}
