/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

use crate::*;

#[cfg(all(feature = "std", not(target_family = "wasm")))]
pub(crate) mod runtime_net_addr_impl {
    use super::*;
    use core::mem::MaybeUninit;
    use core::ptr::{addr_of, null_mut};

    const INET_ADDRSTRLEN: usize = 16;
    const INET6_ADDRSTRLEN: usize = 46;

    #[repr(C)]
    pub union InAddrStorage {
        pub ipv4: libc::in_addr,
        pub ipv6: libc::in6_addr,
    }

    #[repr(C)]
    union UvInterfaceSockaddr {
        address4: libc::sockaddr_in,
        address6: libc::sockaddr_in6,
    }

    #[repr(C)]
    struct UvInterfaceAddress {
        name: *mut c_char,
        phys_addr: [c_char; 6],
        is_internal: c_int,
        address: UvInterfaceSockaddr,
        netmask: UvInterfaceSockaddr,
    }

    extern "C" {
        fn uv_inet_pton(af: c_int, src: *const c_char, dst: *mut c_void) -> c_int;
        fn uv_inet_ntop(af: c_int, src: *const c_void, dst: *mut c_char, size: usize) -> c_int;
        fn uv_interface_addresses(
            addresses: *mut *mut UvInterfaceAddress,
            count: *mut c_int,
        ) -> c_int;
        fn uv_free_interface_addresses(addresses: *mut UvInterfaceAddress, count: c_int);
        #[link_name = "lean_internal_panic"]
        fn lean_internal_panic(msg: *const c_char) -> !;
    }

    unsafe fn assert_uv(result: c_int) {
        if result != 0 {
            lean_internal_panic(
                b"unexpected libuv network-address conversion failure\0"
                    .as_ptr()
                    .cast(),
            );
        }
    }

    unsafe fn option_none() -> *mut LeanObject {
        lean_box(0)
    }

    unsafe fn option_some(value: *mut LeanObject) -> *mut LeanObject {
        let result = lean_runtime_alloc_ctor(1, 1, 0);
        lean_runtime_ctor_set(result, 0, value);
        result
    }

    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean25lean_ipv4_addr_to_in_addrEP11lean_objectP7in_addr"
    )]
    pub unsafe extern "C" fn lean_ipv4_addr_to_in_addr(
        ipv4_addr: *mut LeanObject,
        out: *mut libc::in_addr,
    ) {
        let mut host_addr = 0u32;
        for index in 0..4 {
            let octet = lean_unbox(lean_array_get(ipv4_addr, index)) as u32;
            host_addr |= octet << ((3 - index) * 8);
        }
        (*out).s_addr = host_addr.to_be();
    }

    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean26lean_ipv6_addr_to_in6_addrEP11lean_objectP8in6_addr"
    )]
    pub unsafe extern "C" fn lean_ipv6_addr_to_in6_addr(
        ipv6_addr: *mut LeanObject,
        out: *mut libc::in6_addr,
    ) {
        for index in 0..8 {
            let segment = lean_unbox(lean_array_get(ipv6_addr, index)) as u16;
            let bytes = segment.to_be_bytes();
            (*out).s6_addr[2 * index] = bytes[0];
            (*out).s6_addr[2 * index + 1] = bytes[1];
        }
    }

    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean31lean_ip_addr_to_in_addr_storageEP11lean_objectPiPNS_15in_addr_storageE"
    )]
    pub unsafe extern "C" fn lean_ip_addr_to_in_addr_storage(
        ip_addr: *mut LeanObject,
        ip_type: *mut c_int,
        out: *mut InAddrStorage,
    ) {
        let ip_obj = lean_ctor_get(ip_addr, 0);
        if lean_ptr_tag(ip_addr) == 0 {
            lean_ipv4_addr_to_in_addr(ip_obj, addr_of!((*out).ipv4).cast_mut());
            *ip_type = libc::AF_INET;
        } else {
            lean_ipv6_addr_to_in6_addr(ip_obj, addr_of!((*out).ipv6).cast_mut());
            *ip_type = libc::AF_INET6;
        }
    }

    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean17lean_ip_addr_ntopEP11lean_objectPcm"
    )]
    pub unsafe extern "C" fn lean_ip_addr_ntop(
        ip_addr: *mut LeanObject,
        buffer: *mut c_char,
        buffer_size: usize,
    ) {
        let mut ip_type = 0;
        let mut storage = MaybeUninit::<InAddrStorage>::uninit();
        lean_ip_addr_to_in_addr_storage(ip_addr, &mut ip_type, storage.as_mut_ptr());
        assert_uv(uv_inet_ntop(
            ip_type,
            storage.as_ptr().cast(),
            buffer,
            buffer_size,
        ));
    }

    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean39lean_socket_address_to_sockaddr_storageEP11lean_objectP16sockaddr_storage"
    )]
    pub unsafe extern "C" fn lean_socket_address_to_sockaddr_storage(
        ip_addr: *mut LeanObject,
        out: *mut libc::sockaddr_storage,
    ) {
        out.write(core::mem::zeroed());
        let socket_addr_obj = lean_ctor_get(ip_addr, 0);
        let ip_addr_obj = lean_ctor_get(socket_addr_obj, 0);
        let port = lean_ctor_get_uint16(socket_addr_obj, core::mem::size_of::<*mut LeanObject>());

        if lean_ptr_tag(ip_addr) == 0 {
            let cast = out.cast::<libc::sockaddr_in>();
            lean_ipv4_addr_to_in_addr(ip_addr_obj, addr_of!((*cast).sin_addr).cast_mut());
            (*cast).sin_family = libc::AF_INET as libc::sa_family_t;
            (*cast).sin_port = port.to_be();
        } else {
            let cast = out.cast::<libc::sockaddr_in6>();
            lean_ipv6_addr_to_in6_addr(ip_addr_obj, addr_of!((*cast).sin6_addr).cast_mut());
            (*cast).sin6_family = libc::AF_INET6 as libc::sa_family_t;
            (*cast).sin6_port = port.to_be();
        }
    }

    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean25lean_in_addr_to_ipv4_addrEPK7in_addr"
    )]
    pub unsafe extern "C" fn lean_in_addr_to_ipv4_addr(
        ipv4_addr: *const libc::in_addr,
    ) -> *mut LeanObject {
        let result = lean_alloc_array(0, 4);
        let host_addr = u32::from_be((*ipv4_addr).s_addr);
        let mut array = result;
        for index in 0..4 {
            let octet = (host_addr >> ((3 - index) * 8)) as u8;
            array = lean_array_push(array, lean_box(octet as usize));
        }
        debug_assert_eq!(lean_array_size(array), 4);
        array
    }

    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean26lean_in6_addr_to_ipv6_addrEPK8in6_addr"
    )]
    pub unsafe extern "C" fn lean_in6_addr_to_ipv6_addr(
        ipv6_addr: *const libc::in6_addr,
    ) -> *mut LeanObject {
        let result = lean_alloc_array(0, 8);
        let mut array = result;
        for index in 0..8 {
            let offset = 2 * index;
            let segment = u16::from_be_bytes([
                (*ipv6_addr).s6_addr[offset],
                (*ipv6_addr).s6_addr[offset + 1],
            ]);
            array = lean_array_push(array, lean_box(segment as usize));
        }
        debug_assert_eq!(lean_array_size(array), 8);
        array
    }

    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean26lean_phys_addr_to_mac_addrEPc"
    )]
    pub unsafe extern "C" fn lean_phys_addr_to_mac_addr(phys_addr: *mut c_char) -> *mut LeanObject {
        let result = lean_alloc_array(0, 6);
        let mut array = result;
        for index in 0..6 {
            array = lean_array_push(array, lean_box(*phys_addr.add(index) as u8 as usize));
        }
        debug_assert_eq!(lean_array_size(array), 6);
        array
    }

    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean21lean_mk_socketaddressEP11lean_objectt"
    )]
    pub unsafe extern "C" fn lean_mk_socketaddress(
        ip_addr: *mut LeanObject,
        port: u16,
    ) -> *mut LeanObject {
        let socket_addr = lean_runtime_alloc_ctor(0, 1, 2);
        lean_runtime_ctor_set(socket_addr, 0, ip_addr);
        lean_ctor_set_uint16(socket_addr, core::mem::size_of::<*mut LeanObject>(), port);
        socket_addr
    }

    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean31lean_in_addr_storage_to_ip_addrEsPNS_15in_addr_storageE"
    )]
    pub unsafe extern "C" fn lean_in_addr_storage_to_ip_addr(
        family: i16,
        ip_addr: *mut InAddrStorage,
    ) -> *mut LeanObject {
        let part = if family as c_int == libc::AF_INET {
            lean_in_addr_to_ipv4_addr(addr_of!((*ip_addr).ipv4))
        } else if family as c_int == libc::AF_INET6 {
            lean_in6_addr_to_ipv6_addr(addr_of!((*ip_addr).ipv6))
        } else {
            lean_internal_panic(b"unsupported socket address family\0".as_ptr().cast());
        };

        let ctor = lean_runtime_alloc_ctor(
            if family as c_int == libc::AF_INET6 {
                1
            } else {
                0
            },
            1,
            0,
        );
        lean_runtime_ctor_set(ctor, 0, part);
        ctor
    }

    #[cfg_attr(
        feature = "export-runtime-ffi",
        export_name = "_ZN4lean30lean_sockaddr_to_socketaddressEPK8sockaddr"
    )]
    pub unsafe extern "C" fn lean_sockaddr_to_socketaddress(
        sockaddr: *const libc::sockaddr,
    ) -> *mut LeanObject {
        let (part, tag) = if (*sockaddr).sa_family as c_int == libc::AF_INET {
            let addr_in = sockaddr.cast::<libc::sockaddr_in>();
            let lean_ipv4 = lean_in_addr_to_ipv4_addr(addr_of!((*addr_in).sin_addr));
            let port = u16::from_be((*addr_in).sin_port);
            (lean_mk_socketaddress(lean_ipv4, port), 0)
        } else if (*sockaddr).sa_family as c_int == libc::AF_INET6 {
            let addr_in6 = sockaddr.cast::<libc::sockaddr_in6>();
            let lean_ipv6 = lean_in6_addr_to_ipv6_addr(addr_of!((*addr_in6).sin6_addr));
            let port = u16::from_be((*addr_in6).sin6_port);
            (lean_mk_socketaddress(lean_ipv6, port), 1)
        } else {
            lean_internal_panic(b"unsupported socket address family\0".as_ptr().cast());
        };

        let ctor = lean_runtime_alloc_ctor(tag, 1, 0);
        lean_runtime_ctor_set(ctor, 0, part);
        ctor
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_uv_pton_v4(str_obj: *mut LeanObject) -> *mut LeanObject {
        let str_ptr = lean_string_cstr(str_obj);
        if CStr::from_ptr(str_ptr).to_bytes().len() != lean_string_size(str_obj) - 1 {
            return option_none();
        }

        let mut internal = MaybeUninit::<libc::in_addr>::uninit();
        if uv_inet_pton(libc::AF_INET, str_ptr, internal.as_mut_ptr().cast()) == 0 {
            option_some(lean_in_addr_to_ipv4_addr(internal.as_ptr()))
        } else {
            option_none()
        }
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_uv_ntop_v4(ipv4_addr: *mut LeanObject) -> *mut LeanObject {
        let mut internal = MaybeUninit::<libc::in_addr>::uninit();
        lean_ipv4_addr_to_in_addr(ipv4_addr, internal.as_mut_ptr());
        let mut dst = [0 as c_char; INET_ADDRSTRLEN];
        assert_uv(uv_inet_ntop(
            libc::AF_INET,
            internal.as_ptr().cast(),
            dst.as_mut_ptr(),
            dst.len(),
        ));
        lean_mk_string(dst.as_ptr())
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_uv_pton_v6(str_obj: *mut LeanObject) -> *mut LeanObject {
        let str_ptr = lean_string_cstr(str_obj);
        if CStr::from_ptr(str_ptr).to_bytes().len() != lean_string_size(str_obj) - 1 {
            return option_none();
        }

        let mut internal = MaybeUninit::<libc::in6_addr>::uninit();
        if uv_inet_pton(libc::AF_INET6, str_ptr, internal.as_mut_ptr().cast()) == 0 {
            option_some(lean_in6_addr_to_ipv6_addr(internal.as_ptr()))
        } else {
            option_none()
        }
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_uv_ntop_v6(ipv6_addr: *mut LeanObject) -> *mut LeanObject {
        let mut internal = MaybeUninit::<libc::in6_addr>::uninit();
        lean_ipv6_addr_to_in6_addr(ipv6_addr, internal.as_mut_ptr());
        let mut dst = [0 as c_char; INET6_ADDRSTRLEN];
        assert_uv(uv_inet_ntop(
            libc::AF_INET6,
            internal.as_ptr().cast(),
            dst.as_mut_ptr(),
            dst.len(),
        ));
        lean_mk_string(dst.as_ptr())
    }

    #[cfg_attr(feature = "export-runtime-ffi", no_mangle)]
    pub unsafe extern "C" fn lean_uv_interface_addresses() -> *mut LeanObject {
        let mut info = null_mut();
        let mut count = 0;

        if uv_interface_addresses(&mut info, &mut count) != 0 {
            let details = lean_mk_string(b"failed to get interface addresses\0".as_ptr().cast());
            let error = lean_mk_io_error_invalid_argument(libc::EINVAL as u32, details);
            return lean_io_result_mk_error(error);
        }

        let mut array = lean_alloc_array(0, count.max(0) as usize);
        for index in 0..count as isize {
            let interface = info.offset(index);
            let family = (*interface).address.address4.sin_family as c_int;
            let (socket_address, netmask_address) = if family == libc::AF_INET {
                (
                    addr_of!((*interface).address.address4.sin_addr).cast::<InAddrStorage>(),
                    addr_of!((*interface).netmask.address4.sin_addr).cast::<InAddrStorage>(),
                )
            } else if family == libc::AF_INET6 {
                (
                    addr_of!((*interface).address.address6.sin6_addr).cast::<InAddrStorage>(),
                    addr_of!((*interface).netmask.address6.sin6_addr).cast::<InAddrStorage>(),
                )
            } else {
                continue;
            };

            let iface = lean_runtime_alloc_ctor(0, 4, 1);
            lean_runtime_ctor_set(iface, 0, lean_mk_string((*interface).name));
            lean_runtime_ctor_set(
                iface,
                1,
                lean_phys_addr_to_mac_addr((*interface).phys_addr.as_mut_ptr()),
            );
            lean_ctor_set_uint8(
                iface,
                core::mem::size_of::<*mut LeanObject>() * 4,
                (*interface).is_internal as u8,
            );
            lean_runtime_ctor_set(
                iface,
                2,
                lean_in_addr_storage_to_ip_addr(family as i16, socket_address.cast_mut()),
            );
            lean_runtime_ctor_set(
                iface,
                3,
                lean_in_addr_storage_to_ip_addr(family as i16, netmask_address.cast_mut()),
            );

            array = lean_array_push(array, iface);
        }

        uv_free_interface_addresses(info, count);
        lean_io_result_mk_ok(array)
    }
}

#[cfg(all(feature = "std", not(target_family = "wasm")))]
pub use runtime_net_addr_impl::*;
