/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

#[cfg(all(feature = "std", not(target_family = "wasm")))]
mod runtime_dns_impl {
    use super::*;
    use core::mem::MaybeUninit;
    use core::ptr::{addr_of_mut, null_mut};
    use libuv_sys2::{
        uv_freeaddrinfo as uv_freeaddrinfo_sys, uv_getaddrinfo as uv_getaddrinfo_sys,
        uv_getnameinfo as uv_getnameinfo_sys,
    };

    #[repr(C, align(8))]
    struct UvGetAddrInfo {
        _storage: [u8; 160],
    }

    #[repr(C, align(8))]
    struct UvGetNameInfo {
        _storage: [u8; 1320],
    }

    unsafe fn uv_getaddrinfo(
        loop_: *mut c_void,
        req: *mut UvGetAddrInfo,
        cb: Option<unsafe fn(*mut UvGetAddrInfo, c_int, *mut libc::addrinfo)>,
        node: *const c_char,
        service: *const c_char,
        hints: *const libc::addrinfo,
    ) -> c_int {
        uv_getaddrinfo_sys(
            loop_,
            req.cast(),
            cb.map(|cb| core::mem::transmute(cb)),
            node,
            service,
            hints,
        )
    }

    unsafe fn uv_freeaddrinfo(ai: *mut libc::addrinfo) {
        uv_freeaddrinfo_sys(ai)
    }

    unsafe fn uv_getnameinfo(
        loop_: *mut c_void,
        req: *mut UvGetNameInfo,
        cb: Option<unsafe fn(*mut UvGetNameInfo, c_int, *const c_char, *const c_char)>,
        addr: *const libc::sockaddr,
        flags: c_int,
    ) -> c_int {
        uv_getnameinfo_sys(
            loop_,
            req.cast(),
            cb.map(|cb| core::mem::transmute(cb)),
            addr,
            flags,
        )
    }

    extern "C" {
        fn lean_in6_addr_to_ipv6_addr(ipv6_addr: *const libc::in6_addr) -> *mut LeanObject;
        fn lean_in_addr_to_ipv4_addr(ipv4_addr: *const libc::in_addr) -> *mut LeanObject;
        fn lean_socket_address_to_sockaddr_storage(
            ip_addr: *mut LeanObject,
            out: *mut libc::sockaddr_storage,
        );
        fn lean_in_addr_storage_to_ip_addr(family: i16, out: *mut InAddrStorage)
        -> *mut LeanObject;

        fn lean_promise_resolve_with_code(code: c_int, promise: *mut LeanObject);
    }

    fn is_safe_ascii_str(s: *const c_char, mut len: usize) -> bool {
        let mut ptr = s;
        while len > 0 {
            let c = unsafe { *ptr } as u8;
            if !((c >= b'a' && c <= b'z')
                || (c >= b'A' && c <= b'Z')
                || (c >= b'0' && c <= b'9')
                || c == b'-'
                || c == b'_'
                || c == b'.'
                || c == b':'
                || c == b'/'
                || c == b'+'
                || c == b'~'
                || c == b'@'
                || c == b'='
                || c == b','
                || c == b'%')
            {
                return false;
            }
            ptr = unsafe { ptr.add(1) };
            len -= 1;
        }
        true
    }

    unsafe fn mk_except_ok(value: *mut LeanObject) -> *mut LeanObject {
        let result = lean_runtime_alloc_ctor(1, 1, 0);
        lean_runtime_ctor_set(result, 0, value);
        result
    }

    pub unsafe fn lean_uv_dns_get_info(
        name: *mut LeanObject,
        service: *mut LeanObject,
        family: u8,
    ) -> *mut LeanObject {
        let name_cstr = lean_string_cstr(name);
        let service_cstr = lean_string_cstr(service);

        if !is_safe_ascii_str(name_cstr, lean_string_size(name) - 1) {
            return lean_io_result_mk_error(lean_mk_io_error_invalid_argument(
                libc::EINVAL as u32,
                lean_mk_string(b"name is not ASCII\0".as_ptr().cast()),
            ));
        }

        if !is_safe_ascii_str(service_cstr, lean_string_size(service) - 1) {
            return lean_io_result_mk_error(lean_mk_io_error_invalid_argument(
                libc::EINVAL as u32,
                lean_mk_string(b"service is not ASCII\0".as_ptr().cast()),
            ));
        }

        let resolver = libc::malloc(core::mem::size_of::<UvGetAddrInfo>()).cast::<UvGetAddrInfo>();
        if resolver.is_null() {
            return lean_io_result_mk_error(lean_decode_io_error(libc::ENOMEM, null_mut()));
        }

        let promise = lean_io_promise_new();
        lean_mark_mt(promise);
        let resolver_handle = resolver.cast::<UvHandle>();
        (*resolver_handle).data = promise.cast();

        let mut hints = MaybeUninit::<libc::addrinfo>::zeroed().assume_init();
        match family {
            0 => hints.ai_family = libc::PF_UNSPEC,
            1 => hints.ai_family = libc::PF_INET,
            2 => hints.ai_family = libc::PF_INET6,
            _ => hints.ai_family = libc::PF_UNSPEC,
        }

        event_loop_lock(addr_of_mut!(_ZN4lean9global_evE));
        lean_inc(promise);

        unsafe fn getaddrinfo_cb(req: *mut UvGetAddrInfo, status: c_int, res: *mut libc::addrinfo) {
            let handle = req.cast::<UvHandle>();
            let promise = (*handle).data.cast::<LeanObject>();

            if status != 0 {
                lean_promise_resolve_with_code(status, promise);
                lean_dec(promise);
                libc::free(req.cast());
                return;
            }

            let mut arr = lean_alloc_array(0, 1);
            let mut ai = res;
            while !ai.is_null() {
                let sin_addr = (*ai).ai_addr;
                let family = (*sin_addr).sa_family as c_int;

                let mut storage_addr = MaybeUninit::<InAddrStorage>::uninit();
                if family == libc::AF_INET {
                    let ipv4 = sin_addr.cast::<libc::sockaddr_in>();
                    let ipv4_storage = addr_of_mut!((*storage_addr.as_mut_ptr()).ipv4);
                    ipv4_storage.write((*ipv4).sin_addr);
                } else if family == libc::AF_INET6 {
                    let ipv6 = sin_addr.cast::<libc::sockaddr_in6>();
                    let ipv6_storage = addr_of_mut!((*storage_addr.as_mut_ptr()).ipv6);
                    ipv6_storage.write((*ipv6).sin6_addr);
                } else {
                    ai = (*ai).ai_next;
                    continue;
                }

                let addr =
                    lean_in_addr_storage_to_ip_addr(family as i16, storage_addr.as_mut_ptr());
                arr = lean_array_push(arr, addr);
                ai = (*ai).ai_next;
            }

            lean_promise_resolve(mk_except_ok(arr), promise);
            uv_freeaddrinfo(res);
            lean_dec(promise);
            libc::free(req.cast());
        }

        let result = uv_getaddrinfo(
            _ZN4lean9global_evE.loop_.cast(),
            resolver,
            Some(getaddrinfo_cb),
            name_cstr,
            service_cstr,
            &hints,
        );

        if result != 0 {
            lean_dec(promise);
            lean_dec(promise);
            libc::free(resolver.cast());
            event_loop_unlock(addr_of_mut!(_ZN4lean9global_evE));
            return lean_io_result_mk_error(lean_decode_uv_error(result, null_mut()));
        }

        event_loop_unlock(addr_of_mut!(_ZN4lean9global_evE));
        lean_io_result_mk_ok(promise)
    }

    pub unsafe fn lean_uv_dns_get_name(addr: *mut LeanObject) -> *mut LeanObject {
        let req = libc::malloc(core::mem::size_of::<UvGetNameInfo>()).cast::<UvGetNameInfo>();
        if req.is_null() {
            return lean_io_result_mk_error(lean_decode_io_error(libc::ENOMEM, null_mut()));
        }

        let promise = lean_io_promise_new();
        lean_mark_mt(promise);
        let req_handle = req.cast::<UvHandle>();
        (*req_handle).data = promise.cast();

        let mut addr_ptr = MaybeUninit::<libc::sockaddr_storage>::zeroed().assume_init();
        lean_socket_address_to_sockaddr_storage(addr, &mut addr_ptr);

        event_loop_lock(addr_of_mut!(_ZN4lean9global_evE));
        lean_inc(promise);

        unsafe fn getnameinfo_cb(
            req: *mut UvGetNameInfo,
            status: c_int,
            hostname: *const c_char,
            service: *const c_char,
        ) {
            let handle = req.cast::<UvHandle>();
            let promise = (*handle).data.cast::<LeanObject>();

            if status != 0 {
                lean_promise_resolve_with_code(status, promise);
                lean_dec(promise);
                libc::free(req.cast());
                return;
            }

            let r = lean_runtime_alloc_ctor(0, 2, 0);
            lean_runtime_ctor_set(r, 0, lean_mk_string(hostname));
            lean_runtime_ctor_set(r, 1, lean_mk_string(service));

            lean_promise_resolve(mk_except_ok(r), promise);
            lean_dec(promise);
            libc::free(req.cast());
        }

        let result = uv_getnameinfo(
            _ZN4lean9global_evE.loop_.cast(),
            req,
            Some(getnameinfo_cb),
            addr_of_mut!(addr_ptr).cast(),
            0,
        );

        if result != 0 {
            lean_dec(promise);
            lean_dec(promise);
            libc::free(req.cast());
            event_loop_unlock(addr_of_mut!(_ZN4lean9global_evE));
            return lean_io_result_mk_error(lean_decode_uv_error(result, null_mut()));
        }

        event_loop_unlock(addr_of_mut!(_ZN4lean9global_evE));
        lean_io_result_mk_ok(promise)
    }
}

#[cfg(all(feature = "std", not(target_family = "wasm")))]
pub use runtime_dns_impl::*;

#[cfg(all(feature = "std", target_family = "wasm"))]
mod runtime_dns_impl {
    use super::*;

    pub fn lean_uv_dns_get_info(_: *mut LeanObject, _: *mut LeanObject, _: u8) -> *mut LeanObject {
        panic!("Please build a version of Lean4 with libuv to invoke this.");
    }

    pub fn lean_uv_dns_get_name(_: *mut LeanObject) -> *mut LeanObject {
        panic!("Please build a version of Lean4 with libuv to invoke this.");
    }
}

#[cfg(all(feature = "std", target_family = "wasm"))]
pub use runtime_dns_impl::*;
