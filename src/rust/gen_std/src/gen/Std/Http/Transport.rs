// Lean compiler output
// Module: Std.Http.Transport
// Imports: Std.Http.Protocol.H1
use crate::ffi::{
    lean_array_size, lean_array_uget_borrowed, lean_byte_array_copy_slice, lean_byte_array_size,
    lean_io_promise_new, lean_io_promise_resolve, lean_io_promise_result_opt, lean_task_map,
    lean_uint64_dec_le, lean_uint64_of_nat, lean_usize_add, lean_usize_dec_lt, lean_uv_tcp_recv,
    lean_uv_tcp_send,
};
use crate::r#gen::Init::System::IO::l_BaseIO_chainTask___redArg;
use crate::r#gen::Init::System::IOError::lean_mk_io_user_error;
use crate::r#gen::Init::System::Promise::l_IO_Promise_result_x21___redArg;
use crate::r#gen::Std::Async::Basic::l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask;
use crate::r#gen::Std::Async::TCP::l_Std_Async_TCP_Socket_Client_recvSelector___boxed;
use crate::r#gen::Std::Http::Protocol::H1::{
    initialize_Std_Http_Protocol_H1, runtime_initialize_Std_Http_Protocol_H1,
};
use crate::r#gen::Std::Sync::Channel::{
    l_Std_CloseableChannel_close___redArg, l_Std_CloseableChannel_isClosed___redArg,
    l_Std_CloseableChannel_new___redArg, l_Std_CloseableChannel_recv___redArg,
    l_Std_CloseableChannel_recvSelector___redArg, l_Std_CloseableChannel_send___redArg,
    l_Std_CloseableChannel_tryRecv___redArg,
};
pub static l_Std_Http_instTransportClient___lam__2___closed__0_value:
    crate::leanh::LeanStringObject<44> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 44,
    m_capacity: 44,
    m_length: 43,
    m_data: [
        116, 104, 101, 32, 112, 114, 111, 109, 105, 115, 101, 32, 108, 105, 110, 107, 101, 100, 32,
        116, 111, 32, 116, 104, 101, 32, 65, 115, 121, 110, 99, 32, 119, 97, 115, 32, 100, 114,
        111, 112, 112, 101, 100, 0,
    ],
};
static mut l_Std_Http_instTransportClient___lam__2___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instTransportClient___lam__2___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instTransportClient___lam__2___closed__1_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_instTransportClient___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_instTransportClient___lam__2___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Http_instTransportClient___lam__2___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instTransportClient___lam__2___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instTransportClient___lam__2___closed__2_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_instTransportClient___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_instTransportClient___lam__2___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Http_instTransportClient___lam__2___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instTransportClient___lam__2___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instTransportClient___lam__5___closed__0_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_instTransportClient___lam__3___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_instTransportClient___lam__2___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Http_instTransportClient___lam__5___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instTransportClient___lam__5___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instTransportClient___lam__5___closed__1_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_instTransportClient___lam__4___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_instTransportClient___lam__5___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Http_instTransportClient___lam__5___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instTransportClient___lam__5___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instTransportClient___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Http_instTransportClient___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_instTransportClient___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instTransportClient___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instTransportClient___closed__1_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Http_instTransportClient___lam__5___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_instTransportClient___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instTransportClient___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instTransportClient___closed__2_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Async_TCP_Socket_Client_recvSelector___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_instTransportClient___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instTransportClient___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instTransportClient___closed__3_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Http_instTransportClient___lam__6___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_instTransportClient___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instTransportClient___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_instTransportClient___closed__4_value: crate::leanh::LeanCtorObject<4> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_instTransportClient___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Http_instTransportClient___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Http_instTransportClient___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Http_instTransportClient___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Http_instTransportClient___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instTransportClient___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Http_instTransportClient: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_instTransportClient___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Internal_Mock_recvJoined___closed__0_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_Internal_Mock_recvJoined___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Internal_Mock_recvJoined___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_Mock_recvJoined___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Internal_Mock_recvJoined___closed__1_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_Internal_Mock_recvJoined___lam__4 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Internal_Mock_recvJoined___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_Mock_recvJoined___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Internal_Mock_send___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<44> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 44,
    m_capacity: 44,
    m_length: 43,
    m_data: [
        116, 114, 121, 105, 110, 103, 32, 116, 111, 32, 115, 101, 110, 100, 32, 111, 110, 32, 97,
        110, 32, 97, 108, 114, 101, 97, 100, 121, 32, 99, 108, 111, 115, 101, 100, 32, 99, 104, 97,
        110, 110, 101, 108, 0,
    ],
};
static mut l_Std_Http_Internal_Mock_send___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_Mock_send___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Internal_Mock_send___lam__0___closed__1_value:
    crate::leanh::LeanStringObject<42> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 42,
    m_capacity: 42,
    m_length: 41,
    m_data: [
        116, 114, 121, 105, 110, 103, 32, 116, 111, 32, 99, 108, 111, 115, 101, 32, 97, 110, 32,
        97, 108, 114, 101, 97, 100, 121, 32, 99, 108, 111, 115, 101, 100, 32, 99, 104, 97, 110,
        110, 101, 108, 0,
    ],
};
static mut l_Std_Http_Internal_Mock_send___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_Mock_send___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Internal_Mock_send___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Http_Internal_Mock_send___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Internal_Mock_send___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_Mock_send___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Internal_Mock_send___closed__1_value: crate::leanh::LeanClosureObject<1> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Http_Internal_Mock_send___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_Internal_Mock_send___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Http_Internal_Mock_send___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_Mock_send___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Internal_Mock_sendAll___lam__0___closed__0_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Http_Internal_Mock_sendAll___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_Mock_sendAll___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Internal_Mock_sendAll___lam__0___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_Internal_Mock_sendAll___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Http_Internal_Mock_sendAll___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_Mock_sendAll___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0___closed__0_value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0___lam__0___boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 1, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Internal_Mock_sendAll___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Http_Internal_Mock_sendAll___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Internal_Mock_sendAll___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_Mock_sendAll___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Internal_Mock_Client_close___closed__0_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 18,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_Internal_Mock_send___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Http_Internal_Mock_Client_close___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_Mock_Client_close___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Internal_Mock_Client_close___closed__1_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 18,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_Internal_Mock_send___lam__0___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Http_Internal_Mock_Client_close___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_Mock_Client_close___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Internal_instTransportClient___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_Internal_instTransportClient___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Internal_instTransportClient___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_instTransportClient___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Internal_instTransportClient___closed__1_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_Internal_instTransportClient___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Internal_instTransportClient___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_instTransportClient___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Internal_instTransportClient___closed__2_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_Internal_instTransportClient___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Internal_instTransportClient___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_instTransportClient___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Internal_instTransportClient___closed__3_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_Internal_Mock_Client_close___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Internal_instTransportClient___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_instTransportClient___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Internal_instTransportClient___closed__4_value: crate::leanh::LeanCtorObject<
    4,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_Internal_instTransportClient___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_Internal_instTransportClient___closed__1_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_Internal_instTransportClient___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_Internal_instTransportClient___closed__3_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Http_Internal_instTransportClient___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_instTransportClient___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Http_Internal_instTransportClient: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_instTransportClient___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Internal_instTransportServer___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_Internal_instTransportServer___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Internal_instTransportServer___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_instTransportServer___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Internal_instTransportServer___closed__1_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_Internal_instTransportServer___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Internal_instTransportServer___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_instTransportServer___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Internal_instTransportServer___closed__2_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_Internal_instTransportServer___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Internal_instTransportServer___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_instTransportServer___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Internal_instTransportServer___closed__3_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_Internal_Mock_Server_close___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Internal_instTransportServer___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_instTransportServer___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Internal_instTransportServer___closed__4_value: crate::leanh::LeanCtorObject<
    4,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_Internal_instTransportServer___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_Internal_instTransportServer___closed__1_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_Internal_instTransportServer___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_Internal_instTransportServer___closed__3_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Http_Internal_instTransportServer___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_instTransportServer___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Http_Internal_instTransportServer: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_instTransportServer___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Std_Http_instTransportClient___lam__0(
    mut v___x_957_: *mut crate::leanh::LeanObject,
    mut v_x_958_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_958_) == 0 {
        let mut v___x_959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_959_ = lean_mk_io_user_error(v___x_957_);
        v___x_960_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_960_, 0, v___x_959_);
        return v___x_960_;
    } else {
        let mut v_val_961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v___x_957_);
        v_val_961_ = crate::leanh::lean_ctor_get(v_x_958_, 0);
        crate::leanh::lean_inc(v_val_961_);
        return v_val_961_;
    }
}
pub unsafe fn l_Std_Http_instTransportClient___lam__0___boxed(
    mut v___x_962_: *mut crate::leanh::LeanObject,
    mut v_x_963_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_964_ = l_Std_Http_instTransportClient___lam__0(v___x_962_, v_x_963_);
    crate::leanh::lean_dec(v_x_963_);
    return v_res_964_;
}
pub unsafe fn l_Std_Http_instTransportClient___lam__1(
    mut v___f_965_: *mut crate::leanh::LeanObject,
    mut v_x_966_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_971_: u8 = 0;
    let mut v___x_973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_976_: u8 = 0;
    let mut v_a_977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_981_: u8 = 0;
    let mut v___x_983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_986_: u8 = 0;
    let mut v_a_987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_990_: u8 = 0;
    let mut v___x_991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_966_) == 0 {
                    crate::leanh::lean_dec_ref(v___f_965_);
                    v_a_968_ = crate::leanh::lean_ctor_get(v_x_966_, 0);
                    v_isSharedCheck_976_ = (!crate::leanh::lean_is_exclusive(v_x_966_)) as u8;
                    if v_isSharedCheck_976_ == 0 {
                        v___x_970_ = v_x_966_;
                        v_isShared_971_ = v_isSharedCheck_976_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_968_);
                        crate::leanh::lean_dec(v_x_966_);
                        v___x_970_ = crate::leanh::lean_box(0);
                        v_isShared_971_ = v_isSharedCheck_976_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_977_ = crate::leanh::lean_ctor_get(v_x_966_, 0);
                    crate::leanh::lean_inc(v_a_977_);
                    crate::leanh::lean_dec_ref_known(v_x_966_, 1);
                    if crate::leanh::lean_obj_tag(v_a_977_) == 0 {
                        crate::leanh::lean_dec_ref(v___f_965_);
                        v_a_978_ = crate::leanh::lean_ctor_get(v_a_977_, 0);
                        v_isSharedCheck_986_ = (!crate::leanh::lean_is_exclusive(v_a_977_)) as u8;
                        if v_isSharedCheck_986_ == 0 {
                            v___x_980_ = v_a_977_;
                            v_isShared_981_ = v_isSharedCheck_986_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_978_);
                            crate::leanh::lean_dec(v_a_977_);
                            v___x_980_ = crate::leanh::lean_box(0);
                            v_isShared_981_ = v_isSharedCheck_986_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_987_ = crate::leanh::lean_ctor_get(v_a_977_, 0);
                        crate::leanh::lean_inc(v_a_987_);
                        crate::leanh::lean_dec_ref_known(v_a_977_, 1);
                        v___x_988_ = lean_io_promise_result_opt(v_a_987_);
                        crate::leanh::lean_dec(v_a_987_);
                        v___x_989_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_990_ = 0;
                        v___x_991_ = lean_task_map(v___f_965_, v___x_988_, v___x_989_, v___x_990_);
                        v___x_992_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_992_, 0, v___x_991_);
                        return v___x_992_;
                    }
                }
            }
            1 => {
                if v_isShared_971_ == 0 {
                    v___x_973_ = v___x_970_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_975_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_975_, 0, v_a_968_);
                    v___x_973_ = v_reuseFailAlloc_975_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_974_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_974_, 0, v___x_973_);
                return v___x_974_;
            }
            3 => {
                if v_isShared_981_ == 0 {
                    v___x_983_ = v___x_980_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_985_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_985_, 0, v_a_978_);
                    v___x_983_ = v_reuseFailAlloc_985_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_984_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_984_, 0, v___x_983_);
                return v___x_984_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_instTransportClient___lam__1___boxed(
    mut v___f_993_: *mut crate::leanh::LeanObject,
    mut v_x_994_: *mut crate::leanh::LeanObject,
    mut v___y_995_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_996_ = l_Std_Http_instTransportClient___lam__1(v___f_993_, v_x_994_);
    return v_res_996_;
}
pub unsafe fn l_Std_Http_instTransportClient___lam__2(
    mut v_client_1002_: *mut crate::leanh::LeanObject,
    mut v_expect_1003_: u64,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1011_: u8 = 0;
    let mut v___x_1012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1017_: u8 = 0;
    let mut v___x_1019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1021_: u8 = 0;
    let mut v_a_1022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1025_: u8 = 0;
    let mut v___x_1027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1029_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1005_ = l_Std_Http_instTransportClient___lam__2___closed__2;
                v___x_1013_ = lean_uv_tcp_recv(v_client_1002_, v_expect_1003_);
                if crate::leanh::lean_obj_tag(v___x_1013_) == 0 {
                    v_a_1014_ = crate::leanh::lean_ctor_get(v___x_1013_, 0);
                    v_isSharedCheck_1021_ = (!crate::leanh::lean_is_exclusive(v___x_1013_)) as u8;
                    if v_isSharedCheck_1021_ == 0 {
                        v___x_1016_ = v___x_1013_;
                        v_isShared_1017_ = v_isSharedCheck_1021_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1014_);
                        crate::leanh::lean_dec(v___x_1013_);
                        v___x_1016_ = crate::leanh::lean_box(0);
                        v_isShared_1017_ = v_isSharedCheck_1021_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_1022_ = crate::leanh::lean_ctor_get(v___x_1013_, 0);
                    v_isSharedCheck_1029_ = (!crate::leanh::lean_is_exclusive(v___x_1013_)) as u8;
                    if v_isSharedCheck_1029_ == 0 {
                        v___x_1024_ = v___x_1013_;
                        v_isShared_1025_ = v_isSharedCheck_1029_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1022_);
                        crate::leanh::lean_dec(v___x_1013_);
                        v___x_1024_ = crate::leanh::lean_box(0);
                        v_isShared_1025_ = v_isSharedCheck_1029_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1008_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1008_, 0, v_val_1007_);
                v___x_1009_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1009_, 0, v___x_1008_);
                v___x_1010_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1011_ = 0;
                v___x_1012_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_1010_,
                    v___x_1011_,
                    v___x_1009_,
                    v___f_1005_,
                );
                return v___x_1012_;
            }
            2 => {
                if v_isShared_1017_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1016_, 1);
                    v___x_1019_ = v___x_1016_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1020_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1020_, 0, v_a_1014_);
                    v___x_1019_ = v_reuseFailAlloc_1020_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_val_1007_ = v___x_1019_;
                state = 1;
                continue;
            }
            4 => {
                if v_isShared_1025_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1024_, 0);
                    v___x_1027_ = v___x_1024_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1028_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1028_, 0, v_a_1022_);
                    v___x_1027_ = v_reuseFailAlloc_1028_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_val_1007_ = v___x_1027_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_instTransportClient___lam__2___boxed(
    mut v_client_1030_: *mut crate::leanh::LeanObject,
    mut v_expect_1031_: *mut crate::leanh::LeanObject,
    mut v___y_1032_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_expect_boxed_1033_: u64 = 0;
    let mut v_res_1034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_expect_boxed_1033_ = crate::leanh::lean_unbox_uint64(v_expect_1031_);
    crate::leanh::lean_dec_ref(v_expect_1031_);
    v_res_1034_ = l_Std_Http_instTransportClient___lam__2(v_client_1030_, v_expect_boxed_1033_);
    crate::leanh::lean_dec(v_client_1030_);
    return v_res_1034_;
}
pub unsafe fn l_Std_Http_instTransportClient___lam__3(
    mut v___x_1035_: *mut crate::leanh::LeanObject,
    mut v_x_1036_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1036_) == 0 {
        let mut v___x_1037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1037_ = lean_mk_io_user_error(v___x_1035_);
        v___x_1038_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1038_, 0, v___x_1037_);
        return v___x_1038_;
    } else {
        let mut v_val_1039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v___x_1035_);
        v_val_1039_ = crate::leanh::lean_ctor_get(v_x_1036_, 0);
        crate::leanh::lean_inc(v_val_1039_);
        return v_val_1039_;
    }
}
pub unsafe fn l_Std_Http_instTransportClient___lam__3___boxed(
    mut v___x_1040_: *mut crate::leanh::LeanObject,
    mut v_x_1041_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1042_ = l_Std_Http_instTransportClient___lam__3(v___x_1040_, v_x_1041_);
    crate::leanh::lean_dec(v_x_1041_);
    return v_res_1042_;
}
pub unsafe fn l_Std_Http_instTransportClient___lam__4(
    mut v___f_1043_: *mut crate::leanh::LeanObject,
    mut v_x_1044_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1049_: u8 = 0;
    let mut v___x_1051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1054_: u8 = 0;
    let mut v_a_1055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1059_: u8 = 0;
    let mut v___x_1061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1064_: u8 = 0;
    let mut v_a_1065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1068_: u8 = 0;
    let mut v___x_1069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1044_) == 0 {
                    crate::leanh::lean_dec_ref(v___f_1043_);
                    v_a_1046_ = crate::leanh::lean_ctor_get(v_x_1044_, 0);
                    v_isSharedCheck_1054_ = (!crate::leanh::lean_is_exclusive(v_x_1044_)) as u8;
                    if v_isSharedCheck_1054_ == 0 {
                        v___x_1048_ = v_x_1044_;
                        v_isShared_1049_ = v_isSharedCheck_1054_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1046_);
                        crate::leanh::lean_dec(v_x_1044_);
                        v___x_1048_ = crate::leanh::lean_box(0);
                        v_isShared_1049_ = v_isSharedCheck_1054_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1055_ = crate::leanh::lean_ctor_get(v_x_1044_, 0);
                    crate::leanh::lean_inc(v_a_1055_);
                    crate::leanh::lean_dec_ref_known(v_x_1044_, 1);
                    if crate::leanh::lean_obj_tag(v_a_1055_) == 0 {
                        crate::leanh::lean_dec_ref(v___f_1043_);
                        v_a_1056_ = crate::leanh::lean_ctor_get(v_a_1055_, 0);
                        v_isSharedCheck_1064_ = (!crate::leanh::lean_is_exclusive(v_a_1055_)) as u8;
                        if v_isSharedCheck_1064_ == 0 {
                            v___x_1058_ = v_a_1055_;
                            v_isShared_1059_ = v_isSharedCheck_1064_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1056_);
                            crate::leanh::lean_dec(v_a_1055_);
                            v___x_1058_ = crate::leanh::lean_box(0);
                            v_isShared_1059_ = v_isSharedCheck_1064_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_1065_ = crate::leanh::lean_ctor_get(v_a_1055_, 0);
                        crate::leanh::lean_inc(v_a_1065_);
                        crate::leanh::lean_dec_ref_known(v_a_1055_, 1);
                        v___x_1066_ = lean_io_promise_result_opt(v_a_1065_);
                        crate::leanh::lean_dec(v_a_1065_);
                        v___x_1067_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_1068_ = 0;
                        v___x_1069_ =
                            lean_task_map(v___f_1043_, v___x_1066_, v___x_1067_, v___x_1068_);
                        v___x_1070_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1070_, 0, v___x_1069_);
                        return v___x_1070_;
                    }
                }
            }
            1 => {
                if v_isShared_1049_ == 0 {
                    v___x_1051_ = v___x_1048_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1053_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1053_, 0, v_a_1046_);
                    v___x_1051_ = v_reuseFailAlloc_1053_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1052_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1052_, 0, v___x_1051_);
                return v___x_1052_;
            }
            3 => {
                if v_isShared_1059_ == 0 {
                    v___x_1061_ = v___x_1058_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1063_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1063_, 0, v_a_1056_);
                    v___x_1061_ = v_reuseFailAlloc_1063_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1062_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1062_, 0, v___x_1061_);
                return v___x_1062_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_instTransportClient___lam__4___boxed(
    mut v___f_1071_: *mut crate::leanh::LeanObject,
    mut v_x_1072_: *mut crate::leanh::LeanObject,
    mut v___y_1073_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1074_ = l_Std_Http_instTransportClient___lam__4(v___f_1071_, v_x_1072_);
    return v_res_1074_;
}
pub unsafe fn l_Std_Http_instTransportClient___lam__5(
    mut v_client_1079_: *mut crate::leanh::LeanObject,
    mut v_data_1080_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1088_: u8 = 0;
    let mut v___x_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1094_: u8 = 0;
    let mut v___x_1096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1098_: u8 = 0;
    let mut v_a_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1102_: u8 = 0;
    let mut v___x_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1106_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1082_ = l_Std_Http_instTransportClient___lam__5___closed__1;
                v___x_1090_ = lean_uv_tcp_send(v_client_1079_, v_data_1080_);
                if crate::leanh::lean_obj_tag(v___x_1090_) == 0 {
                    v_a_1091_ = crate::leanh::lean_ctor_get(v___x_1090_, 0);
                    v_isSharedCheck_1098_ = (!crate::leanh::lean_is_exclusive(v___x_1090_)) as u8;
                    if v_isSharedCheck_1098_ == 0 {
                        v___x_1093_ = v___x_1090_;
                        v_isShared_1094_ = v_isSharedCheck_1098_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1091_);
                        crate::leanh::lean_dec(v___x_1090_);
                        v___x_1093_ = crate::leanh::lean_box(0);
                        v_isShared_1094_ = v_isSharedCheck_1098_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_1099_ = crate::leanh::lean_ctor_get(v___x_1090_, 0);
                    v_isSharedCheck_1106_ = (!crate::leanh::lean_is_exclusive(v___x_1090_)) as u8;
                    if v_isSharedCheck_1106_ == 0 {
                        v___x_1101_ = v___x_1090_;
                        v_isShared_1102_ = v_isSharedCheck_1106_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1099_);
                        crate::leanh::lean_dec(v___x_1090_);
                        v___x_1101_ = crate::leanh::lean_box(0);
                        v_isShared_1102_ = v_isSharedCheck_1106_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1085_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1085_, 0, v_val_1084_);
                v___x_1086_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1086_, 0, v___x_1085_);
                v___x_1087_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1088_ = 0;
                v___x_1089_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_1087_,
                    v___x_1088_,
                    v___x_1086_,
                    v___f_1082_,
                );
                return v___x_1089_;
            }
            2 => {
                if v_isShared_1094_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1093_, 1);
                    v___x_1096_ = v___x_1093_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1097_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1097_, 0, v_a_1091_);
                    v___x_1096_ = v_reuseFailAlloc_1097_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_val_1084_ = v___x_1096_;
                state = 1;
                continue;
            }
            4 => {
                if v_isShared_1102_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1101_, 0);
                    v___x_1104_ = v___x_1101_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1105_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_a_1099_);
                    v___x_1104_ = v_reuseFailAlloc_1105_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_val_1084_ = v___x_1104_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_instTransportClient___lam__5___boxed(
    mut v_client_1107_: *mut crate::leanh::LeanObject,
    mut v_data_1108_: *mut crate::leanh::LeanObject,
    mut v___y_1109_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1110_ = l_Std_Http_instTransportClient___lam__5(v_client_1107_, v_data_1108_);
    crate::leanh::lean_dec(v_client_1107_);
    return v_res_1110_;
}
pub unsafe fn l_Std_Http_instTransportClient___lam__6(
    mut v_x_1111_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1113_ = crate::leanh::lean_box(0);
    v___x_1114_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1114_, 0, v___x_1113_);
    return v___x_1114_;
}
pub unsafe fn l_Std_Http_instTransportClient___lam__6___boxed(
    mut v_x_1115_: *mut crate::leanh::LeanObject,
    mut v___y_1116_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1117_ = l_Std_Http_instTransportClient___lam__6(v_x_1115_);
    crate::leanh::lean_dec(v_x_1115_);
    return v_res_1117_;
}
pub unsafe fn l_Std_Http_Internal_Mock_new() -> *mut crate::leanh::LeanObject {
    let mut v___x_1129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1129_ = crate::leanh::lean_box(0);
    v___x_1130_ = l_Std_CloseableChannel_new___redArg(v___x_1129_);
    v___x_1131_ = l_Std_CloseableChannel_new___redArg(v___x_1129_);
    v___x_1132_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1132_, 0, v___x_1130_);
    crate::leanh::lean_ctor_set(v___x_1132_, 1, v___x_1131_);
    crate::leanh::lean_inc_ref(v___x_1132_);
    v___x_1133_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1133_, 0, v___x_1132_);
    crate::leanh::lean_ctor_set(v___x_1133_, 1, v___x_1132_);
    return v___x_1133_;
}
pub unsafe fn l_Std_Http_Internal_Mock_new___boxed(
    mut v_a_1134_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1135_ = l_Std_Http_Internal_Mock_new();
    return v_res_1135_;
}
pub unsafe fn l_Std_Http_Internal_Mock_recvJoined___lam__0(
    mut v_x_1136_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1141_: u8 = 0;
    let mut v___x_1143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1146_: u8 = 0;
    let mut v_a_1147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1150_: u8 = 0;
    let mut v___x_1151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1156_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1136_) == 0 {
                    v_a_1138_ = crate::leanh::lean_ctor_get(v_x_1136_, 0);
                    v_isSharedCheck_1146_ = (!crate::leanh::lean_is_exclusive(v_x_1136_)) as u8;
                    if v_isSharedCheck_1146_ == 0 {
                        v___x_1140_ = v_x_1136_;
                        v_isShared_1141_ = v_isSharedCheck_1146_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1138_);
                        crate::leanh::lean_dec(v_x_1136_);
                        v___x_1140_ = crate::leanh::lean_box(0);
                        v_isShared_1141_ = v_isSharedCheck_1146_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1147_ = crate::leanh::lean_ctor_get(v_x_1136_, 0);
                    v_isSharedCheck_1156_ = (!crate::leanh::lean_is_exclusive(v_x_1136_)) as u8;
                    if v_isSharedCheck_1156_ == 0 {
                        v___x_1149_ = v_x_1136_;
                        v_isShared_1150_ = v_isSharedCheck_1156_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1147_);
                        crate::leanh::lean_dec(v_x_1136_);
                        v___x_1149_ = crate::leanh::lean_box(0);
                        v_isShared_1150_ = v_isSharedCheck_1156_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1141_ == 0 {
                    v___x_1143_ = v___x_1140_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1145_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1145_, 0, v_a_1138_);
                    v___x_1143_ = v_reuseFailAlloc_1145_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1144_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1144_, 0, v___x_1143_);
                return v___x_1144_;
            }
            3 => {
                v___x_1151_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1151_, 0, v_a_1147_);
                if v_isShared_1150_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1149_, 0, v___x_1151_);
                    v___x_1153_ = v___x_1149_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1155_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1155_, 0, v___x_1151_);
                    v___x_1153_ = v_reuseFailAlloc_1155_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1154_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1154_, 0, v___x_1153_);
                return v___x_1154_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Internal_Mock_recvJoined___lam__0___boxed(
    mut v_x_1157_: *mut crate::leanh::LeanObject,
    mut v___y_1158_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1159_ = l_Std_Http_Internal_Mock_recvJoined___lam__0(v_x_1157_);
    return v_res_1159_;
}
pub unsafe fn l_Std_Http_Internal_Mock_recvJoined___lam__1(
    mut v_a_1160_: *mut crate::leanh::LeanObject,
    mut v_x_1161_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1166_: u8 = 0;
    let mut v___x_1168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1171_: u8 = 0;
    let mut v___x_1172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1161_) == 0 {
                    v_a_1163_ = crate::leanh::lean_ctor_get(v_x_1161_, 0);
                    v_isSharedCheck_1171_ = (!crate::leanh::lean_is_exclusive(v_x_1161_)) as u8;
                    if v_isSharedCheck_1171_ == 0 {
                        v___x_1165_ = v_x_1161_;
                        v_isShared_1166_ = v_isSharedCheck_1171_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1163_);
                        crate::leanh::lean_dec(v_x_1161_);
                        v___x_1165_ = crate::leanh::lean_box(0);
                        v_isShared_1166_ = v_isSharedCheck_1171_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v_x_1161_, 1);
                    v___x_1172_ = l_IO_Promise_result_x21___redArg(v_a_1160_);
                    v___x_1173_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1173_, 0, v___x_1172_);
                    return v___x_1173_;
                }
            }
            1 => {
                if v_isShared_1166_ == 0 {
                    v___x_1168_ = v___x_1165_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1170_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1170_, 0, v_a_1163_);
                    v___x_1168_ = v_reuseFailAlloc_1170_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1169_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1169_, 0, v___x_1168_);
                return v___x_1169_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Internal_Mock_recvJoined___lam__1___boxed(
    mut v_a_1174_: *mut crate::leanh::LeanObject,
    mut v_x_1175_: *mut crate::leanh::LeanObject,
    mut v___y_1176_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1177_ = l_Std_Http_Internal_Mock_recvJoined___lam__1(v_a_1174_, v_x_1175_);
    crate::leanh::lean_dec(v_a_1174_);
    return v_res_1177_;
}
pub unsafe fn l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___at___00Std_Http_Internal_Mock_recvJoined_spec__0___lam__1(
    mut v_b_1178_: *mut crate::leanh::LeanObject,
    mut v_x_1179_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1184_: u8 = 0;
    let mut v___x_1186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1189_: u8 = 0;
    let mut v_a_1190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1193_: u8 = 0;
    let mut v___x_1194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1202_: u8 = 0;
    let mut v___x_1203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1206_: u8 = 0;
    let mut v___x_1207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1215_: u8 = 0;
    let mut v_isSharedCheck_1216_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1179_) == 0 {
                    crate::leanh::lean_dec_ref(v_b_1178_);
                    v_a_1181_ = crate::leanh::lean_ctor_get(v_x_1179_, 0);
                    v_isSharedCheck_1189_ = (!crate::leanh::lean_is_exclusive(v_x_1179_)) as u8;
                    if v_isSharedCheck_1189_ == 0 {
                        v___x_1183_ = v_x_1179_;
                        v_isShared_1184_ = v_isSharedCheck_1189_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1181_);
                        crate::leanh::lean_dec(v_x_1179_);
                        v___x_1183_ = crate::leanh::lean_box(0);
                        v_isShared_1184_ = v_isSharedCheck_1189_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1190_ = crate::leanh::lean_ctor_get(v_x_1179_, 0);
                    v_isSharedCheck_1216_ = (!crate::leanh::lean_is_exclusive(v_x_1179_)) as u8;
                    if v_isSharedCheck_1216_ == 0 {
                        v___x_1192_ = v_x_1179_;
                        v_isShared_1193_ = v_isSharedCheck_1216_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1190_);
                        crate::leanh::lean_dec(v_x_1179_);
                        v___x_1192_ = crate::leanh::lean_box(0);
                        v_isShared_1193_ = v_isSharedCheck_1216_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1184_ == 0 {
                    v___x_1186_ = v___x_1183_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1188_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1188_, 0, v_a_1181_);
                    v___x_1186_ = v_reuseFailAlloc_1188_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1187_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1187_, 0, v___x_1186_);
                return v___x_1187_;
            }
            3 => {
                if crate::leanh::lean_obj_tag(v_a_1190_) == 0 {
                    v___x_1194_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1194_, 0, v_b_1178_);
                    if v_isShared_1193_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1192_, 0, v___x_1194_);
                        v___x_1196_ = v___x_1192_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1198_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1198_, 0, v___x_1194_);
                        v___x_1196_ = v_reuseFailAlloc_1198_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_val_1199_ = crate::leanh::lean_ctor_get(v_a_1190_, 0);
                    v_isSharedCheck_1215_ = (!crate::leanh::lean_is_exclusive(v_a_1190_)) as u8;
                    if v_isSharedCheck_1215_ == 0 {
                        v___x_1201_ = v_a_1190_;
                        v_isShared_1202_ = v_isSharedCheck_1215_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1199_);
                        crate::leanh::lean_dec(v_a_1190_);
                        v___x_1201_ = crate::leanh::lean_box(0);
                        v_isShared_1202_ = v_isSharedCheck_1215_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                v___x_1197_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1197_, 0, v___x_1196_);
                return v___x_1197_;
            }
            5 => {
                v___x_1203_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1204_ = lean_byte_array_size(v_b_1178_);
                v___x_1205_ = lean_byte_array_size(v_val_1199_);
                v___x_1206_ = 0;
                v___x_1207_ = lean_byte_array_copy_slice(
                    v_val_1199_,
                    v___x_1203_,
                    v_b_1178_,
                    v___x_1204_,
                    v___x_1205_,
                    v___x_1206_,
                );
                crate::leanh::lean_dec(v_val_1199_);
                if v_isShared_1202_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1201_, 0, v___x_1207_);
                    v___x_1209_ = v___x_1201_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1214_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1214_, 0, v___x_1207_);
                    v___x_1209_ = v_reuseFailAlloc_1214_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_1193_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1192_, 0, v___x_1209_);
                    v___x_1211_ = v___x_1192_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1213_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1213_, 0, v___x_1209_);
                    v___x_1211_ = v_reuseFailAlloc_1213_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_1212_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1212_, 0, v___x_1211_);
                return v___x_1212_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___at___00Std_Http_Internal_Mock_recvJoined_spec__0___lam__1___boxed(
    mut v_b_1217_: *mut crate::leanh::LeanObject,
    mut v_x_1218_: *mut crate::leanh::LeanObject,
    mut v___y_1219_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1220_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___at___00Std_Http_Internal_Mock_recvJoined_spec__0___lam__1(v_b_1217_, v_x_1218_);
    return v_res_1220_;
}
pub unsafe fn l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___at___00Std_Http_Internal_Mock_recvJoined_spec__0___lam__0___boxed(
    mut v_promise_1221_: *mut crate::leanh::LeanObject,
    mut v_recvChan_1222_: *mut crate::leanh::LeanObject,
    mut v_expect_1223_: *mut crate::leanh::LeanObject,
    mut v_prio_1224_: *mut crate::leanh::LeanObject,
    mut v_x_1225_: *mut crate::leanh::LeanObject,
    mut v___y_1226_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1227_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___at___00Std_Http_Internal_Mock_recvJoined_spec__0___lam__0(v_promise_1221_, v_recvChan_1222_, v_expect_1223_, v_prio_1224_, v_x_1225_);
    return v_res_1227_;
}
pub unsafe fn l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___at___00Std_Http_Internal_Mock_recvJoined_spec__0(
    mut v_recvChan_1228_: *mut crate::leanh::LeanObject,
    mut v_expect_1229_: *mut crate::leanh::LeanObject,
    mut v_prio_1230_: *mut crate::leanh::LeanObject,
    mut v_promise_1231_: *mut crate::leanh::LeanObject,
    mut v_b_1232_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1245_: u8 = 0;
    let mut v___x_1246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1251_: u8 = 0;
    let mut v___x_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1256_: u8 = 0;
    let mut v_a_1257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1265_: u64 = 0;
    let mut v___x_1266_: u64 = 0;
    let mut v___x_1267_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_prio_1230_);
                crate::leanh::lean_inc(v_expect_1229_);
                crate::leanh::lean_inc_ref(v_recvChan_1228_);
                crate::leanh::lean_inc(v_promise_1231_);
                v___f_1238_ = crate::leanh::lean_alloc_closure(l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___at___00Std_Http_Internal_Mock_recvJoined_spec__0___lam__0___boxed as *mut core::ffi::c_void, 6, 4);
                crate::leanh::lean_closure_set(v___f_1238_, 0, v_promise_1231_);
                crate::leanh::lean_closure_set(v___f_1238_, 1, v_recvChan_1228_);
                crate::leanh::lean_closure_set(v___f_1238_, 2, v_expect_1229_);
                crate::leanh::lean_closure_set(v___f_1238_, 3, v_prio_1230_);
                crate::leanh::lean_inc_ref(v_b_1232_);
                v___f_1239_ = crate::leanh::lean_alloc_closure(l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___at___00Std_Http_Internal_Mock_recvJoined_spec__0___lam__1___boxed as *mut core::ffi::c_void, 3, 1);
                crate::leanh::lean_closure_set(v___f_1239_, 0, v_b_1232_);
                if crate::leanh::lean_obj_tag(v_expect_1229_) == 1 {
                    v_val_1263_ = crate::leanh::lean_ctor_get(v_expect_1229_, 0);
                    v___x_1264_ = lean_byte_array_size(v_b_1232_);
                    v___x_1265_ = lean_uint64_of_nat(v___x_1264_);
                    v___x_1266_ = crate::leanh::lean_unbox_uint64(v_val_1263_);
                    v___x_1267_ = lean_uint64_dec_le(v___x_1266_, v___x_1265_);
                    if v___x_1267_ == 0 {
                        crate::leanh::lean_dec_ref(v_b_1232_);
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref_known(v_expect_1229_, 1);
                        crate::leanh::lean_dec_ref(v___f_1239_);
                        crate::leanh::lean_dec_ref(v___f_1238_);
                        crate::leanh::lean_dec(v_prio_1230_);
                        crate::leanh::lean_dec_ref(v_recvChan_1228_);
                        v_a_1235_ = v_b_1232_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_b_1232_);
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_1236_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1236_, 0, v_a_1235_);
                v___x_1237_ = lean_io_promise_resolve(v___x_1236_, v_promise_1231_);
                crate::leanh::lean_dec(v_promise_1231_);
                return v___x_1237_;
            }
            2 => {
                crate::leanh::lean_inc_ref(v_recvChan_1228_);
                v___x_1241_ = l_Std_CloseableChannel_tryRecv___redArg(v_recvChan_1228_);
                v___x_1242_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1242_, 0, v___x_1241_);
                v___x_1243_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1243_, 0, v___x_1242_);
                v___x_1244_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1245_ = 0;
                v___x_1246_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_1244_,
                    v___x_1245_,
                    v___x_1243_,
                    v___f_1239_,
                );
                if crate::leanh::lean_obj_tag(v___x_1246_) == 0 {
                    crate::leanh::lean_dec_ref(v___f_1238_);
                    v_a_1247_ = crate::leanh::lean_ctor_get(v___x_1246_, 0);
                    crate::leanh::lean_inc(v_a_1247_);
                    crate::leanh::lean_dec_ref_known(v___x_1246_, 1);
                    if crate::leanh::lean_obj_tag(v_a_1247_) == 0 {
                        crate::leanh::lean_dec(v_prio_1230_);
                        crate::leanh::lean_dec(v_expect_1229_);
                        crate::leanh::lean_dec_ref(v_recvChan_1228_);
                        v_a_1248_ = crate::leanh::lean_ctor_get(v_a_1247_, 0);
                        v_isSharedCheck_1256_ = (!crate::leanh::lean_is_exclusive(v_a_1247_)) as u8;
                        if v_isSharedCheck_1256_ == 0 {
                            v___x_1250_ = v_a_1247_;
                            v_isShared_1251_ = v_isSharedCheck_1256_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1248_);
                            crate::leanh::lean_dec(v_a_1247_);
                            v___x_1250_ = crate::leanh::lean_box(0);
                            v_isShared_1251_ = v_isSharedCheck_1256_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_1257_ = crate::leanh::lean_ctor_get(v_a_1247_, 0);
                        crate::leanh::lean_inc(v_a_1257_);
                        crate::leanh::lean_dec_ref_known(v_a_1247_, 1);
                        if crate::leanh::lean_obj_tag(v_a_1257_) == 0 {
                            crate::leanh::lean_dec(v_prio_1230_);
                            crate::leanh::lean_dec(v_expect_1229_);
                            crate::leanh::lean_dec_ref(v_recvChan_1228_);
                            v_a_1258_ = crate::leanh::lean_ctor_get(v_a_1257_, 0);
                            crate::leanh::lean_inc(v_a_1258_);
                            crate::leanh::lean_dec_ref_known(v_a_1257_, 1);
                            v_a_1235_ = v_a_1258_;
                            state = 1;
                            continue;
                        } else {
                            v_a_1259_ = crate::leanh::lean_ctor_get(v_a_1257_, 0);
                            crate::leanh::lean_inc(v_a_1259_);
                            crate::leanh::lean_dec_ref_known(v_a_1257_, 1);
                            v_b_1232_ = v_a_1259_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_promise_1231_);
                    crate::leanh::lean_dec(v_expect_1229_);
                    crate::leanh::lean_dec_ref(v_recvChan_1228_);
                    v_a_1261_ = crate::leanh::lean_ctor_get(v___x_1246_, 0);
                    crate::leanh::lean_inc_ref(v_a_1261_);
                    crate::leanh::lean_dec_ref_known(v___x_1246_, 1);
                    v___x_1262_ = l_BaseIO_chainTask___redArg(
                        v_a_1261_,
                        v___f_1238_,
                        v_prio_1230_,
                        v___x_1245_,
                    );
                    return v___x_1262_;
                }
            }
            3 => {
                if v_isShared_1251_ == 0 {
                    v___x_1253_ = v___x_1250_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1255_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1255_, 0, v_a_1248_);
                    v___x_1253_ = v_reuseFailAlloc_1255_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1254_ = lean_io_promise_resolve(v___x_1253_, v_promise_1231_);
                crate::leanh::lean_dec(v_promise_1231_);
                return v___x_1254_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___at___00Std_Http_Internal_Mock_recvJoined_spec__0___lam__0(
    mut v_promise_1268_: *mut crate::leanh::LeanObject,
    mut v_recvChan_1269_: *mut crate::leanh::LeanObject,
    mut v_expect_1270_: *mut crate::leanh::LeanObject,
    mut v_prio_1271_: *mut crate::leanh::LeanObject,
    mut v_x_1272_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1277_: u8 = 0;
    let mut v___x_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1282_: u8 = 0;
    let mut v_a_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1286_: u8 = 0;
    let mut v_a_1287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1294_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1272_) == 0 {
                    crate::leanh::lean_dec(v_prio_1271_);
                    crate::leanh::lean_dec(v_expect_1270_);
                    crate::leanh::lean_dec_ref(v_recvChan_1269_);
                    v_a_1274_ = crate::leanh::lean_ctor_get(v_x_1272_, 0);
                    v_isSharedCheck_1282_ = (!crate::leanh::lean_is_exclusive(v_x_1272_)) as u8;
                    if v_isSharedCheck_1282_ == 0 {
                        v___x_1276_ = v_x_1272_;
                        v_isShared_1277_ = v_isSharedCheck_1282_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1274_);
                        crate::leanh::lean_dec(v_x_1272_);
                        v___x_1276_ = crate::leanh::lean_box(0);
                        v_isShared_1277_ = v_isSharedCheck_1282_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1283_ = crate::leanh::lean_ctor_get(v_x_1272_, 0);
                    v_isSharedCheck_1294_ = (!crate::leanh::lean_is_exclusive(v_x_1272_)) as u8;
                    if v_isSharedCheck_1294_ == 0 {
                        v___x_1285_ = v_x_1272_;
                        v_isShared_1286_ = v_isSharedCheck_1294_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1283_);
                        crate::leanh::lean_dec(v_x_1272_);
                        v___x_1285_ = crate::leanh::lean_box(0);
                        v_isShared_1286_ = v_isSharedCheck_1294_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1277_ == 0 {
                    v___x_1279_ = v___x_1276_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1281_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1281_, 0, v_a_1274_);
                    v___x_1279_ = v_reuseFailAlloc_1281_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1280_ = lean_io_promise_resolve(v___x_1279_, v_promise_1268_);
                crate::leanh::lean_dec(v_promise_1268_);
                return v___x_1280_;
            }
            3 => {
                if crate::leanh::lean_obj_tag(v_a_1283_) == 0 {
                    crate::leanh::lean_dec(v_prio_1271_);
                    crate::leanh::lean_dec(v_expect_1270_);
                    crate::leanh::lean_dec_ref(v_recvChan_1269_);
                    v_a_1287_ = crate::leanh::lean_ctor_get(v_a_1283_, 0);
                    crate::leanh::lean_inc(v_a_1287_);
                    crate::leanh::lean_dec_ref_known(v_a_1283_, 1);
                    if v_isShared_1286_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1285_, 0, v_a_1287_);
                        v___x_1289_ = v___x_1285_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1291_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_a_1287_);
                        v___x_1289_ = v_reuseFailAlloc_1291_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1285_);
                    v_a_1292_ = crate::leanh::lean_ctor_get(v_a_1283_, 0);
                    crate::leanh::lean_inc(v_a_1292_);
                    crate::leanh::lean_dec_ref_known(v_a_1283_, 1);
                    v___x_1293_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___at___00Std_Http_Internal_Mock_recvJoined_spec__0(v_recvChan_1269_, v_expect_1270_, v_prio_1271_, v_promise_1268_, v_a_1292_);
                    return v___x_1293_;
                }
            }
            4 => {
                v___x_1290_ = lean_io_promise_resolve(v___x_1289_, v_promise_1268_);
                crate::leanh::lean_dec(v_promise_1268_);
                return v___x_1290_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___at___00Std_Http_Internal_Mock_recvJoined_spec__0___boxed(
    mut v_recvChan_1295_: *mut crate::leanh::LeanObject,
    mut v_expect_1296_: *mut crate::leanh::LeanObject,
    mut v_prio_1297_: *mut crate::leanh::LeanObject,
    mut v_promise_1298_: *mut crate::leanh::LeanObject,
    mut v_b_1299_: *mut crate::leanh::LeanObject,
    mut v_a_1300_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1301_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___at___00Std_Http_Internal_Mock_recvJoined_spec__0(v_recvChan_1295_, v_expect_1296_, v_prio_1297_, v_promise_1298_, v_b_1299_);
    return v_res_1301_;
}
pub unsafe fn l_Std_Http_Internal_Mock_recvJoined___lam__2(
    mut v_recvChan_1302_: *mut crate::leanh::LeanObject,
    mut v_expect_1303_: *mut crate::leanh::LeanObject,
    mut v___x_1304_: *mut crate::leanh::LeanObject,
    mut v_val_1305_: *mut crate::leanh::LeanObject,
    mut v_x_1306_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1311_: u8 = 0;
    let mut v___x_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1316_: u8 = 0;
    let mut v_a_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1320_: u8 = 0;
    let mut v___x_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: u8 = 0;
    let mut v___x_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1329_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1306_) == 0 {
                    crate::leanh::lean_dec_ref(v_val_1305_);
                    crate::leanh::lean_dec(v___x_1304_);
                    crate::leanh::lean_dec(v_expect_1303_);
                    crate::leanh::lean_dec_ref(v_recvChan_1302_);
                    v_a_1308_ = crate::leanh::lean_ctor_get(v_x_1306_, 0);
                    v_isSharedCheck_1316_ = (!crate::leanh::lean_is_exclusive(v_x_1306_)) as u8;
                    if v_isSharedCheck_1316_ == 0 {
                        v___x_1310_ = v_x_1306_;
                        v_isShared_1311_ = v_isSharedCheck_1316_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1308_);
                        crate::leanh::lean_dec(v_x_1306_);
                        v___x_1310_ = crate::leanh::lean_box(0);
                        v_isShared_1311_ = v_isSharedCheck_1316_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1317_ = crate::leanh::lean_ctor_get(v_x_1306_, 0);
                    v_isSharedCheck_1329_ = (!crate::leanh::lean_is_exclusive(v_x_1306_)) as u8;
                    if v_isSharedCheck_1329_ == 0 {
                        v___x_1319_ = v_x_1306_;
                        v_isShared_1320_ = v_isSharedCheck_1329_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1317_);
                        crate::leanh::lean_dec(v_x_1306_);
                        v___x_1319_ = crate::leanh::lean_box(0);
                        v_isShared_1320_ = v_isSharedCheck_1329_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1311_ == 0 {
                    v___x_1313_ = v___x_1310_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1315_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1315_, 0, v_a_1308_);
                    v___x_1313_ = v_reuseFailAlloc_1315_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1314_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1314_, 0, v___x_1313_);
                return v___x_1314_;
            }
            3 => {
                crate::leanh::lean_inc(v_a_1317_);
                crate::leanh::lean_inc(v___x_1304_);
                v___x_1321_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___at___00Std_Http_Internal_Mock_recvJoined_spec__0(v_recvChan_1302_, v_expect_1303_, v___x_1304_, v_a_1317_, v_val_1305_);
                v___f_1322_ = crate::leanh::lean_alloc_closure(
                    l_Std_Http_Internal_Mock_recvJoined___lam__1___boxed as *mut core::ffi::c_void,
                    3,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1322_, 0, v_a_1317_);
                if v_isShared_1320_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1319_, 0, v___x_1321_);
                    v___x_1324_ = v___x_1319_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1328_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1328_, 0, v___x_1321_);
                    v___x_1324_ = v_reuseFailAlloc_1328_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1325_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1325_, 0, v___x_1324_);
                v___x_1326_ = 0;
                v___x_1327_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_1304_,
                    v___x_1326_,
                    v___x_1325_,
                    v___f_1322_,
                );
                return v___x_1327_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Internal_Mock_recvJoined___lam__2___boxed(
    mut v_recvChan_1330_: *mut crate::leanh::LeanObject,
    mut v_expect_1331_: *mut crate::leanh::LeanObject,
    mut v___x_1332_: *mut crate::leanh::LeanObject,
    mut v_val_1333_: *mut crate::leanh::LeanObject,
    mut v_x_1334_: *mut crate::leanh::LeanObject,
    mut v___y_1335_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1336_ = l_Std_Http_Internal_Mock_recvJoined___lam__2(
        v_recvChan_1330_,
        v_expect_1331_,
        v___x_1332_,
        v_val_1333_,
        v_x_1334_,
    );
    return v_res_1336_;
}
pub unsafe fn l_Std_Http_Internal_Mock_recvJoined___lam__3(
    mut v_recvChan_1337_: *mut crate::leanh::LeanObject,
    mut v_expect_1338_: *mut crate::leanh::LeanObject,
    mut v___f_1339_: *mut crate::leanh::LeanObject,
    mut v_x_1340_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1347_: u8 = 0;
    let mut v_val_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1351_: u8 = 0;
    let mut v___x_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: u8 = 0;
    let mut v___x_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1364_: u8 = 0;
    let mut v_isSharedCheck_1365_: u8 = 0;
    let mut v_unused_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1340_) == 0 {
                    crate::leanh::lean_dec_ref(v___f_1339_);
                    crate::leanh::lean_dec(v_expect_1338_);
                    crate::leanh::lean_dec_ref(v_recvChan_1337_);
                    v___x_1342_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1342_, 0, v_x_1340_);
                    return v___x_1342_;
                } else {
                    v_a_1343_ = crate::leanh::lean_ctor_get(v_x_1340_, 0);
                    crate::leanh::lean_inc(v_a_1343_);
                    if crate::leanh::lean_obj_tag(v_a_1343_) == 0 {
                        crate::leanh::lean_dec_ref(v___f_1339_);
                        crate::leanh::lean_dec(v_expect_1338_);
                        crate::leanh::lean_dec_ref(v_recvChan_1337_);
                        v___x_1344_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1344_, 0, v_x_1340_);
                        return v___x_1344_;
                    } else {
                        v_isSharedCheck_1365_ = (!crate::leanh::lean_is_exclusive(v_x_1340_)) as u8;
                        if v_isSharedCheck_1365_ == 0 {
                            v_unused_1366_ = crate::leanh::lean_ctor_get(v_x_1340_, 0);
                            crate::leanh::lean_dec(v_unused_1366_);
                            v___x_1346_ = v_x_1340_;
                            v_isShared_1347_ = v_isSharedCheck_1365_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_1340_);
                            v___x_1346_ = crate::leanh::lean_box(0);
                            v_isShared_1347_ = v_isSharedCheck_1365_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_val_1348_ = crate::leanh::lean_ctor_get(v_a_1343_, 0);
                v_isSharedCheck_1364_ = (!crate::leanh::lean_is_exclusive(v_a_1343_)) as u8;
                if v_isSharedCheck_1364_ == 0 {
                    v___x_1350_ = v_a_1343_;
                    v_isShared_1351_ = v_isSharedCheck_1364_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_val_1348_);
                    crate::leanh::lean_dec(v_a_1343_);
                    v___x_1350_ = crate::leanh::lean_box(0);
                    v_isShared_1351_ = v_isSharedCheck_1364_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1352_ = lean_io_promise_new();
                v___x_1353_ = crate::leanh::lean_unsigned_to_nat(0);
                v___f_1354_ = crate::leanh::lean_alloc_closure(
                    l_Std_Http_Internal_Mock_recvJoined___lam__2___boxed as *mut core::ffi::c_void,
                    6,
                    4,
                );
                crate::leanh::lean_closure_set(v___f_1354_, 0, v_recvChan_1337_);
                crate::leanh::lean_closure_set(v___f_1354_, 1, v_expect_1338_);
                crate::leanh::lean_closure_set(v___f_1354_, 2, v___x_1353_);
                crate::leanh::lean_closure_set(v___f_1354_, 3, v_val_1348_);
                if v_isShared_1347_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1346_, 0, v___x_1352_);
                    v___x_1356_ = v___x_1346_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1363_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1363_, 0, v___x_1352_);
                    v___x_1356_ = v_reuseFailAlloc_1363_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1351_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1350_, 0);
                    crate::leanh::lean_ctor_set(v___x_1350_, 0, v___x_1356_);
                    v___x_1358_ = v___x_1350_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1362_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1362_, 0, v___x_1356_);
                    v___x_1358_ = v_reuseFailAlloc_1362_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1359_ = 0;
                v___x_1360_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_1353_,
                    v___x_1359_,
                    v___x_1358_,
                    v___f_1354_,
                );
                v___x_1361_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_1353_,
                    v___x_1359_,
                    v___x_1360_,
                    v___f_1339_,
                );
                return v___x_1361_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Internal_Mock_recvJoined___lam__3___boxed(
    mut v_recvChan_1367_: *mut crate::leanh::LeanObject,
    mut v_expect_1368_: *mut crate::leanh::LeanObject,
    mut v___f_1369_: *mut crate::leanh::LeanObject,
    mut v_x_1370_: *mut crate::leanh::LeanObject,
    mut v___y_1371_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1372_ = l_Std_Http_Internal_Mock_recvJoined___lam__3(
        v_recvChan_1367_,
        v_expect_1368_,
        v___f_1369_,
        v_x_1370_,
    );
    return v_res_1372_;
}
pub unsafe fn l_Std_Http_Internal_Mock_recvJoined___lam__4(
    mut v_a_1373_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1374_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1374_, 0, v_a_1373_);
    return v___x_1374_;
}
pub unsafe fn l_Std_Http_Internal_Mock_recvJoined___lam__5(
    mut v___f_1375_: *mut crate::leanh::LeanObject,
    mut v___f_1376_: *mut crate::leanh::LeanObject,
    mut v_x_1377_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1382_: u8 = 0;
    let mut v___x_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1387_: u8 = 0;
    let mut v_a_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: u8 = 0;
    let mut v___x_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1377_) == 0 {
                    crate::leanh::lean_dec_ref(v___f_1376_);
                    crate::leanh::lean_dec_ref(v___f_1375_);
                    v_a_1379_ = crate::leanh::lean_ctor_get(v_x_1377_, 0);
                    v_isSharedCheck_1387_ = (!crate::leanh::lean_is_exclusive(v_x_1377_)) as u8;
                    if v_isSharedCheck_1387_ == 0 {
                        v___x_1381_ = v_x_1377_;
                        v_isShared_1382_ = v_isSharedCheck_1387_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1379_);
                        crate::leanh::lean_dec(v_x_1377_);
                        v___x_1381_ = crate::leanh::lean_box(0);
                        v_isShared_1382_ = v_isSharedCheck_1387_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1388_ = crate::leanh::lean_ctor_get(v_x_1377_, 0);
                    crate::leanh::lean_inc(v_a_1388_);
                    crate::leanh::lean_dec_ref_known(v_x_1377_, 1);
                    v___x_1389_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1390_ = 0;
                    v___x_1391_ = lean_task_map(v___f_1375_, v_a_1388_, v___x_1389_, v___x_1390_);
                    v___x_1392_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1392_, 0, v___x_1391_);
                    v___x_1393_ =
                        l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v___x_1389_,
                            v___x_1390_,
                            v___x_1392_,
                            v___f_1376_,
                        );
                    return v___x_1393_;
                }
            }
            1 => {
                if v_isShared_1382_ == 0 {
                    v___x_1384_ = v___x_1381_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1386_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1386_, 0, v_a_1379_);
                    v___x_1384_ = v_reuseFailAlloc_1386_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1385_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1385_, 0, v___x_1384_);
                return v___x_1385_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Internal_Mock_recvJoined___lam__5___boxed(
    mut v___f_1394_: *mut crate::leanh::LeanObject,
    mut v___f_1395_: *mut crate::leanh::LeanObject,
    mut v_x_1396_: *mut crate::leanh::LeanObject,
    mut v___y_1397_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1398_ = l_Std_Http_Internal_Mock_recvJoined___lam__5(v___f_1394_, v___f_1395_, v_x_1396_);
    return v_res_1398_;
}
pub unsafe fn l_Std_Http_Internal_Mock_recvJoined(
    mut v_recvChan_1401_: *mut crate::leanh::LeanObject,
    mut v_expect_1402_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: u8 = 0;
    let mut v___x_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_recvChan_1401_);
    v___x_1404_ = l_Std_CloseableChannel_recv___redArg(v_recvChan_1401_);
    v___f_1405_ = l_Std_Http_Internal_Mock_recvJoined___closed__0;
    v___f_1406_ = crate::leanh::lean_alloc_closure(
        l_Std_Http_Internal_Mock_recvJoined___lam__3___boxed as *mut core::ffi::c_void,
        5,
        3,
    );
    crate::leanh::lean_closure_set(v___f_1406_, 0, v_recvChan_1401_);
    crate::leanh::lean_closure_set(v___f_1406_, 1, v_expect_1402_);
    crate::leanh::lean_closure_set(v___f_1406_, 2, v___f_1405_);
    v___f_1407_ = l_Std_Http_Internal_Mock_recvJoined___closed__1;
    v___f_1408_ = crate::leanh::lean_alloc_closure(
        l_Std_Http_Internal_Mock_recvJoined___lam__5___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1408_, 0, v___f_1407_);
    crate::leanh::lean_closure_set(v___f_1408_, 1, v___f_1406_);
    v___x_1409_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1409_, 0, v___x_1404_);
    v___x_1410_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1410_, 0, v___x_1409_);
    v___x_1411_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1412_ = 0;
    v___x_1413_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1411_,
        v___x_1412_,
        v___x_1410_,
        v___f_1408_,
    );
    return v___x_1413_;
}
pub unsafe fn l_Std_Http_Internal_Mock_recvJoined___boxed(
    mut v_recvChan_1414_: *mut crate::leanh::LeanObject,
    mut v_expect_1415_: *mut crate::leanh::LeanObject,
    mut v_a_1416_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1417_ = l_Std_Http_Internal_Mock_recvJoined(v_recvChan_1414_, v_expect_1415_);
    return v_res_1417_;
}
pub unsafe fn l_Std_Http_Internal_Mock_send___lam__0(
    mut v___y_1420_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: u8 = 0;
    let mut v___x_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1432_: u8 = 0;
    let mut v___x_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1436_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v___y_1420_) == 0 {
                    v_a_1425_ = crate::leanh::lean_ctor_get(v___y_1420_, 0);
                    crate::leanh::lean_inc(v_a_1425_);
                    crate::leanh::lean_dec_ref_known(v___y_1420_, 1);
                    v___x_1426_ = (crate::leanh::lean_unbox(v_a_1425_) as u8);
                    crate::leanh::lean_dec(v_a_1425_);
                    if v___x_1426_ == 0 {
                        v___x_1427_ = l_Std_Http_Internal_Mock_send___lam__0___closed__0;
                        v___y_1422_ = v___x_1427_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1428_ = l_Std_Http_Internal_Mock_send___lam__0___closed__1;
                        v___y_1422_ = v___x_1428_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1429_ = crate::leanh::lean_ctor_get(v___y_1420_, 0);
                    v_isSharedCheck_1436_ = (!crate::leanh::lean_is_exclusive(v___y_1420_)) as u8;
                    if v_isSharedCheck_1436_ == 0 {
                        v___x_1431_ = v___y_1420_;
                        v_isShared_1432_ = v_isSharedCheck_1436_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1429_);
                        crate::leanh::lean_dec(v___y_1420_);
                        v___x_1431_ = crate::leanh::lean_box(0);
                        v_isShared_1432_ = v_isSharedCheck_1436_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v___y_1422_);
                v___x_1423_ = lean_mk_io_user_error(v___y_1422_);
                v___x_1424_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1424_, 0, v___x_1423_);
                return v___x_1424_;
            }
            2 => {
                if v_isShared_1432_ == 0 {
                    v___x_1434_ = v___x_1431_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1435_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1435_, 0, v_a_1429_);
                    v___x_1434_ = v_reuseFailAlloc_1435_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1434_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Internal_Mock_send___lam__1(
    mut v___f_1437_: *mut crate::leanh::LeanObject,
    mut v_x_1438_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1443_: u8 = 0;
    let mut v___x_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1448_: u8 = 0;
    let mut v_a_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: u8 = 0;
    let mut v___x_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1438_) == 0 {
                    crate::leanh::lean_dec_ref(v___f_1437_);
                    v_a_1440_ = crate::leanh::lean_ctor_get(v_x_1438_, 0);
                    v_isSharedCheck_1448_ = (!crate::leanh::lean_is_exclusive(v_x_1438_)) as u8;
                    if v_isSharedCheck_1448_ == 0 {
                        v___x_1442_ = v_x_1438_;
                        v_isShared_1443_ = v_isSharedCheck_1448_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1440_);
                        crate::leanh::lean_dec(v_x_1438_);
                        v___x_1442_ = crate::leanh::lean_box(0);
                        v_isShared_1443_ = v_isSharedCheck_1448_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1449_ = crate::leanh::lean_ctor_get(v_x_1438_, 0);
                    crate::leanh::lean_inc(v_a_1449_);
                    crate::leanh::lean_dec_ref_known(v_x_1438_, 1);
                    v___x_1450_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1451_ = 0;
                    v___x_1452_ = lean_task_map(v___f_1437_, v_a_1449_, v___x_1450_, v___x_1451_);
                    v___x_1453_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1453_, 0, v___x_1452_);
                    return v___x_1453_;
                }
            }
            1 => {
                if v_isShared_1443_ == 0 {
                    v___x_1445_ = v___x_1442_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1447_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1447_, 0, v_a_1440_);
                    v___x_1445_ = v_reuseFailAlloc_1447_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1446_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1446_, 0, v___x_1445_);
                return v___x_1446_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Internal_Mock_send___lam__1___boxed(
    mut v___f_1454_: *mut crate::leanh::LeanObject,
    mut v_x_1455_: *mut crate::leanh::LeanObject,
    mut v___y_1456_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1457_ = l_Std_Http_Internal_Mock_send___lam__1(v___f_1454_, v_x_1455_);
    return v_res_1457_;
}
pub unsafe fn l_Std_Http_Internal_Mock_send(
    mut v_sendChan_1461_: *mut crate::leanh::LeanObject,
    mut v_data_1462_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: u8 = 0;
    let mut v___x_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1464_ = l_Std_CloseableChannel_send___redArg(v_sendChan_1461_, v_data_1462_);
    v___f_1465_ = l_Std_Http_Internal_Mock_send___closed__1;
    v___x_1466_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1466_, 0, v___x_1464_);
    v___x_1467_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1467_, 0, v___x_1466_);
    v___x_1468_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1469_ = 0;
    v___x_1470_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1468_,
        v___x_1469_,
        v___x_1467_,
        v___f_1465_,
    );
    return v___x_1470_;
}
pub unsafe fn l_Std_Http_Internal_Mock_send___boxed(
    mut v_sendChan_1471_: *mut crate::leanh::LeanObject,
    mut v_data_1472_: *mut crate::leanh::LeanObject,
    mut v_a_1473_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1474_ = l_Std_Http_Internal_Mock_send(v_sendChan_1471_, v_data_1472_);
    return v_res_1474_;
}
pub unsafe fn l_Std_Http_Internal_Mock_sendAll___lam__0(
    mut v_x_1479_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1479_) == 0 {
        let mut v___x_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1481_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1481_, 0, v_x_1479_);
        return v___x_1481_;
    } else {
        let mut v___x_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref_known(v_x_1479_, 1);
        v___x_1482_ = l_Std_Http_Internal_Mock_sendAll___lam__0___closed__1;
        return v___x_1482_;
    }
}
pub unsafe fn l_Std_Http_Internal_Mock_sendAll___lam__0___boxed(
    mut v_x_1483_: *mut crate::leanh::LeanObject,
    mut v___y_1484_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1485_ = l_Std_Http_Internal_Mock_sendAll___lam__0(v_x_1483_);
    return v_res_1485_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0___lam__0(
    mut v___x_1486_: *mut crate::leanh::LeanObject,
    mut v_x_1487_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1492_: u8 = 0;
    let mut v___x_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1497_: u8 = 0;
    let mut v___x_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1500_: u8 = 0;
    let mut v___x_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1506_: u8 = 0;
    let mut v_unused_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1487_) == 0 {
                    v_a_1489_ = crate::leanh::lean_ctor_get(v_x_1487_, 0);
                    v_isSharedCheck_1497_ = (!crate::leanh::lean_is_exclusive(v_x_1487_)) as u8;
                    if v_isSharedCheck_1497_ == 0 {
                        v___x_1491_ = v_x_1487_;
                        v_isShared_1492_ = v_isSharedCheck_1497_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1489_);
                        crate::leanh::lean_dec(v_x_1487_);
                        v___x_1491_ = crate::leanh::lean_box(0);
                        v_isShared_1492_ = v_isSharedCheck_1497_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_isSharedCheck_1506_ = (!crate::leanh::lean_is_exclusive(v_x_1487_)) as u8;
                    if v_isSharedCheck_1506_ == 0 {
                        v_unused_1507_ = crate::leanh::lean_ctor_get(v_x_1487_, 0);
                        crate::leanh::lean_dec(v_unused_1507_);
                        v___x_1499_ = v_x_1487_;
                        v_isShared_1500_ = v_isSharedCheck_1506_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_x_1487_);
                        v___x_1499_ = crate::leanh::lean_box(0);
                        v_isShared_1500_ = v_isSharedCheck_1506_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1492_ == 0 {
                    v___x_1494_ = v___x_1491_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1496_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1496_, 0, v_a_1489_);
                    v___x_1494_ = v_reuseFailAlloc_1496_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1495_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1495_, 0, v___x_1494_);
                return v___x_1495_;
            }
            3 => {
                v___x_1501_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1501_, 0, v___x_1486_);
                if v_isShared_1500_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1499_, 0, v___x_1501_);
                    v___x_1503_ = v___x_1499_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1505_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1505_, 0, v___x_1501_);
                    v___x_1503_ = v_reuseFailAlloc_1505_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1504_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1504_, 0, v___x_1503_);
                return v___x_1504_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0___lam__0___boxed(
    mut v___x_1508_: *mut crate::leanh::LeanObject,
    mut v_x_1509_: *mut crate::leanh::LeanObject,
    mut v___y_1510_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1511_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0___lam__0(v___x_1508_, v_x_1509_);
    return v_res_1511_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0___lam__1___boxed(
    mut v_i_1514_: *mut crate::leanh::LeanObject,
    mut v_sendChan_1515_: *mut crate::leanh::LeanObject,
    mut v_as_1516_: *mut crate::leanh::LeanObject,
    mut v_sz_1517_: *mut crate::leanh::LeanObject,
    mut v_x_1518_: *mut crate::leanh::LeanObject,
    mut v___y_1519_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1520_: usize = 0;
    let mut v_sz_boxed_1521_: usize = 0;
    let mut v_res_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1520_ = crate::leanh::lean_unbox_usize(v_i_1514_);
    crate::leanh::lean_dec(v_i_1514_);
    v_sz_boxed_1521_ = crate::leanh::lean_unbox_usize(v_sz_1517_);
    crate::leanh::lean_dec(v_sz_1517_);
    v_res_1522_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0___lam__1(v_i_boxed_1520_, v_sendChan_1515_, v_as_1516_, v_sz_boxed_1521_, v_x_1518_);
    return v_res_1522_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0(
    mut v_sendChan_1523_: *mut crate::leanh::LeanObject,
    mut v_as_1524_: *mut crate::leanh::LeanObject,
    mut v_sz_1525_: usize,
    mut v_i_1526_: usize,
    mut v_b_1527_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1529_: u8 = 0;
    v___x_1529_ = lean_usize_dec_lt(v_i_1526_, v_sz_1525_);
    if v___x_1529_ == 0 {
        let mut v___x_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_as_1524_);
        crate::leanh::lean_dec_ref(v_sendChan_1523_);
        v___x_1530_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1530_, 0, v_b_1527_);
        v___x_1531_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1531_, 0, v___x_1530_);
        return v___x_1531_;
    } else {
        let mut v_a_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1536_: u8 = 0;
        let mut v___x_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_1532_ = lean_array_uget_borrowed(v_as_1524_, v_i_1526_);
        crate::leanh::lean_inc(v_a_1532_);
        crate::leanh::lean_inc_ref(v_sendChan_1523_);
        v___x_1533_ = l_Std_Http_Internal_Mock_send(v_sendChan_1523_, v_a_1532_);
        v___f_1534_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0___closed__0;
        v___x_1535_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_1536_ = 0;
        v___x_1537_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_1535_,
            v___x_1536_,
            v___x_1533_,
            v___f_1534_,
        );
        v___x_1538_ = crate::leanh::lean_box_usize(v_i_1526_);
        v___x_1539_ = crate::leanh::lean_box_usize(v_sz_1525_);
        v___f_1540_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0___lam__1___boxed as *mut core::ffi::c_void, 6, 4);
        crate::leanh::lean_closure_set(v___f_1540_, 0, v___x_1538_);
        crate::leanh::lean_closure_set(v___f_1540_, 1, v_sendChan_1523_);
        crate::leanh::lean_closure_set(v___f_1540_, 2, v_as_1524_);
        crate::leanh::lean_closure_set(v___f_1540_, 3, v___x_1539_);
        v___x_1541_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_1535_,
            v___x_1536_,
            v___x_1537_,
            v___f_1540_,
        );
        return v___x_1541_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0___lam__1(
    mut v_i_1542_: usize,
    mut v_sendChan_1543_: *mut crate::leanh::LeanObject,
    mut v_as_1544_: *mut crate::leanh::LeanObject,
    mut v_sz_1545_: usize,
    mut v_x_1546_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1551_: u8 = 0;
    let mut v___x_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1556_: u8 = 0;
    let mut v_a_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1560_: u8 = 0;
    let mut v_a_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1564_: u8 = 0;
    let mut v___x_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1571_: u8 = 0;
    let mut v_a_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: usize = 0;
    let mut v___x_1574_: usize = 0;
    let mut v___x_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1576_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1546_) == 0 {
                    crate::leanh::lean_dec_ref(v_as_1544_);
                    crate::leanh::lean_dec_ref(v_sendChan_1543_);
                    v_a_1548_ = crate::leanh::lean_ctor_get(v_x_1546_, 0);
                    v_isSharedCheck_1556_ = (!crate::leanh::lean_is_exclusive(v_x_1546_)) as u8;
                    if v_isSharedCheck_1556_ == 0 {
                        v___x_1550_ = v_x_1546_;
                        v_isShared_1551_ = v_isSharedCheck_1556_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1548_);
                        crate::leanh::lean_dec(v_x_1546_);
                        v___x_1550_ = crate::leanh::lean_box(0);
                        v_isShared_1551_ = v_isSharedCheck_1556_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1557_ = crate::leanh::lean_ctor_get(v_x_1546_, 0);
                    v_isSharedCheck_1576_ = (!crate::leanh::lean_is_exclusive(v_x_1546_)) as u8;
                    if v_isSharedCheck_1576_ == 0 {
                        v___x_1559_ = v_x_1546_;
                        v_isShared_1560_ = v_isSharedCheck_1576_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1557_);
                        crate::leanh::lean_dec(v_x_1546_);
                        v___x_1559_ = crate::leanh::lean_box(0);
                        v_isShared_1560_ = v_isSharedCheck_1576_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1551_ == 0 {
                    v___x_1553_ = v___x_1550_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1555_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1555_, 0, v_a_1548_);
                    v___x_1553_ = v_reuseFailAlloc_1555_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1554_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1554_, 0, v___x_1553_);
                return v___x_1554_;
            }
            3 => {
                if crate::leanh::lean_obj_tag(v_a_1557_) == 0 {
                    crate::leanh::lean_dec_ref(v_as_1544_);
                    crate::leanh::lean_dec_ref(v_sendChan_1543_);
                    v_a_1561_ = crate::leanh::lean_ctor_get(v_a_1557_, 0);
                    v_isSharedCheck_1571_ = (!crate::leanh::lean_is_exclusive(v_a_1557_)) as u8;
                    if v_isSharedCheck_1571_ == 0 {
                        v___x_1563_ = v_a_1557_;
                        v_isShared_1564_ = v_isSharedCheck_1571_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1561_);
                        crate::leanh::lean_dec(v_a_1557_);
                        v___x_1563_ = crate::leanh::lean_box(0);
                        v_isShared_1564_ = v_isSharedCheck_1571_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1559_);
                    v_a_1572_ = crate::leanh::lean_ctor_get(v_a_1557_, 0);
                    crate::leanh::lean_inc(v_a_1572_);
                    crate::leanh::lean_dec_ref_known(v_a_1557_, 1);
                    v___x_1573_ = 1usize;
                    v___x_1574_ = lean_usize_add(v_i_1542_, v___x_1573_);
                    v___x_1575_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0(v_sendChan_1543_, v_as_1544_, v_sz_1545_, v___x_1574_, v_a_1572_);
                    return v___x_1575_;
                }
            }
            4 => {
                if v_isShared_1560_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1559_, 0, v_a_1561_);
                    v___x_1566_ = v___x_1559_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1570_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1570_, 0, v_a_1561_);
                    v___x_1566_ = v_reuseFailAlloc_1570_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_1564_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1563_, 0, v___x_1566_);
                    v___x_1568_ = v___x_1563_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1569_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1569_, 0, v___x_1566_);
                    v___x_1568_ = v_reuseFailAlloc_1569_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1568_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0___boxed(
    mut v_sendChan_1577_: *mut crate::leanh::LeanObject,
    mut v_as_1578_: *mut crate::leanh::LeanObject,
    mut v_sz_1579_: *mut crate::leanh::LeanObject,
    mut v_i_1580_: *mut crate::leanh::LeanObject,
    mut v_b_1581_: *mut crate::leanh::LeanObject,
    mut v___y_1582_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1583_: usize = 0;
    let mut v_i_boxed_1584_: usize = 0;
    let mut v_res_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1583_ = crate::leanh::lean_unbox_usize(v_sz_1579_);
    crate::leanh::lean_dec(v_sz_1579_);
    v_i_boxed_1584_ = crate::leanh::lean_unbox_usize(v_i_1580_);
    crate::leanh::lean_dec(v_i_1580_);
    v_res_1585_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0(v_sendChan_1577_, v_as_1578_, v_sz_boxed_1583_, v_i_boxed_1584_, v_b_1581_);
    return v_res_1585_;
}
pub unsafe fn l_Std_Http_Internal_Mock_sendAll(
    mut v_sendChan_1587_: *mut crate::leanh::LeanObject,
    mut v_data_1588_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1591_: usize = 0;
    let mut v___x_1592_: usize = 0;
    let mut v___x_1593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: u8 = 0;
    let mut v___x_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1590_ = crate::leanh::lean_box(0);
    v_sz_1591_ = lean_array_size(v_data_1588_);
    v___x_1592_ = 0usize;
    v___x_1593_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Http_Internal_Mock_sendAll_spec__0(v_sendChan_1587_, v_data_1588_, v_sz_1591_, v___x_1592_, v___x_1590_);
    v___f_1594_ = l_Std_Http_Internal_Mock_sendAll___closed__0;
    v___x_1595_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1596_ = 0;
    v___x_1597_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1595_,
        v___x_1596_,
        v___x_1593_,
        v___f_1594_,
    );
    return v___x_1597_;
}
pub unsafe fn l_Std_Http_Internal_Mock_sendAll___boxed(
    mut v_sendChan_1598_: *mut crate::leanh::LeanObject,
    mut v_data_1599_: *mut crate::leanh::LeanObject,
    mut v_a_1600_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1601_ = l_Std_Http_Internal_Mock_sendAll(v_sendChan_1598_, v_data_1599_);
    return v_res_1601_;
}
pub unsafe fn l_Std_Http_Internal_Mock_recvSelector(
    mut v_recvChan_1602_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1603_ = l_Std_CloseableChannel_recvSelector___redArg(v_recvChan_1602_);
    return v___x_1603_;
}
pub unsafe fn l_Std_Http_Internal_Mock_Client_getRecvChan(
    mut v_client_1604_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_serverToClient_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_serverToClient_1605_ = crate::leanh::lean_ctor_get(v_client_1604_, 1);
    crate::leanh::lean_inc_ref(v_serverToClient_1605_);
    return v_serverToClient_1605_;
}
pub unsafe fn l_Std_Http_Internal_Mock_Client_getRecvChan___boxed(
    mut v_client_1606_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1607_ = l_Std_Http_Internal_Mock_Client_getRecvChan(v_client_1606_);
    crate::leanh::lean_dec_ref(v_client_1606_);
    return v_res_1607_;
}
pub unsafe fn l_Std_Http_Internal_Mock_Client_getSendChan(
    mut v_client_1608_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_clientToServer_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_clientToServer_1609_ = crate::leanh::lean_ctor_get(v_client_1608_, 0);
    crate::leanh::lean_inc_ref(v_clientToServer_1609_);
    return v_clientToServer_1609_;
}
pub unsafe fn l_Std_Http_Internal_Mock_Client_getSendChan___boxed(
    mut v_client_1610_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1611_ = l_Std_Http_Internal_Mock_Client_getSendChan(v_client_1610_);
    crate::leanh::lean_dec_ref(v_client_1610_);
    return v_res_1611_;
}
pub unsafe fn l_Std_Http_Internal_Mock_Client_send(
    mut v_client_1612_: *mut crate::leanh::LeanObject,
    mut v_data_1613_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_clientToServer_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_clientToServer_1615_ = crate::leanh::lean_ctor_get(v_client_1612_, 0);
    crate::leanh::lean_inc_ref(v_clientToServer_1615_);
    crate::leanh::lean_dec_ref(v_client_1612_);
    v___x_1616_ = l_Std_Http_Internal_Mock_send(v_clientToServer_1615_, v_data_1613_);
    return v___x_1616_;
}
pub unsafe fn l_Std_Http_Internal_Mock_Client_send___boxed(
    mut v_client_1617_: *mut crate::leanh::LeanObject,
    mut v_data_1618_: *mut crate::leanh::LeanObject,
    mut v_a_1619_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1620_ = l_Std_Http_Internal_Mock_Client_send(v_client_1617_, v_data_1618_);
    return v_res_1620_;
}
pub unsafe fn l_Std_Http_Internal_Mock_Client_recv_x3f(
    mut v_client_1621_: *mut crate::leanh::LeanObject,
    mut v_expect_1622_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_serverToClient_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_serverToClient_1624_ = crate::leanh::lean_ctor_get(v_client_1621_, 1);
    crate::leanh::lean_inc_ref(v_serverToClient_1624_);
    crate::leanh::lean_dec_ref(v_client_1621_);
    v___x_1625_ = l_Std_Http_Internal_Mock_recvJoined(v_serverToClient_1624_, v_expect_1622_);
    return v___x_1625_;
}
pub unsafe fn l_Std_Http_Internal_Mock_Client_recv_x3f___boxed(
    mut v_client_1626_: *mut crate::leanh::LeanObject,
    mut v_expect_1627_: *mut crate::leanh::LeanObject,
    mut v_a_1628_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1629_ = l_Std_Http_Internal_Mock_Client_recv_x3f(v_client_1626_, v_expect_1627_);
    return v_res_1629_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Std_Http_Internal_Mock_Client_tryRecv_x3f_spec__0___redArg(
    mut v___x_1630_: *mut crate::leanh::LeanObject,
    mut v_a_1631_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: u8 = 0;
    let mut v___x_1639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v___x_1630_);
                v___x_1633_ = l_Std_CloseableChannel_tryRecv___redArg(v___x_1630_);
                if crate::leanh::lean_obj_tag(v___x_1633_) == 0 {
                    crate::leanh::lean_dec_ref(v___x_1630_);
                    return v_a_1631_;
                } else {
                    v_val_1634_ = crate::leanh::lean_ctor_get(v___x_1633_, 0);
                    crate::leanh::lean_inc(v_val_1634_);
                    crate::leanh::lean_dec_ref_known(v___x_1633_, 1);
                    v___x_1635_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1636_ = lean_byte_array_size(v_a_1631_);
                    v___x_1637_ = lean_byte_array_size(v_val_1634_);
                    v___x_1638_ = 0;
                    v___x_1639_ = lean_byte_array_copy_slice(
                        v_val_1634_,
                        v___x_1635_,
                        v_a_1631_,
                        v___x_1636_,
                        v___x_1637_,
                        v___x_1638_,
                    );
                    crate::leanh::lean_dec(v_val_1634_);
                    v_a_1631_ = v___x_1639_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Std_Http_Internal_Mock_Client_tryRecv_x3f_spec__0___redArg___boxed(
    mut v___x_1641_: *mut crate::leanh::LeanObject,
    mut v_a_1642_: *mut crate::leanh::LeanObject,
    mut v___y_1643_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1644_ = l___private_Init_While_0__whileM_erased___at___00Std_Http_Internal_Mock_Client_tryRecv_x3f_spec__0___redArg(v___x_1641_, v_a_1642_);
    return v_res_1644_;
}
pub unsafe fn l_Std_Http_Internal_Mock_Client_tryRecv_x3f___redArg(
    mut v_client_1645_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_serverToClient_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1652_: u8 = 0;
    let mut v___x_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1657_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_serverToClient_1647_ = crate::leanh::lean_ctor_get(v_client_1645_, 1);
                crate::leanh::lean_inc_ref_n(v_serverToClient_1647_, 2);
                crate::leanh::lean_dec_ref(v_client_1645_);
                v___x_1648_ = l_Std_CloseableChannel_tryRecv___redArg(v_serverToClient_1647_);
                if crate::leanh::lean_obj_tag(v___x_1648_) == 0 {
                    crate::leanh::lean_dec_ref(v_serverToClient_1647_);
                    return v___x_1648_;
                } else {
                    v_val_1649_ = crate::leanh::lean_ctor_get(v___x_1648_, 0);
                    v_isSharedCheck_1657_ = (!crate::leanh::lean_is_exclusive(v___x_1648_)) as u8;
                    if v_isSharedCheck_1657_ == 0 {
                        v___x_1651_ = v___x_1648_;
                        v_isShared_1652_ = v_isSharedCheck_1657_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1649_);
                        crate::leanh::lean_dec(v___x_1648_);
                        v___x_1651_ = crate::leanh::lean_box(0);
                        v_isShared_1652_ = v_isSharedCheck_1657_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1653_ = l___private_Init_While_0__whileM_erased___at___00Std_Http_Internal_Mock_Client_tryRecv_x3f_spec__0___redArg(v_serverToClient_1647_, v_val_1649_);
                if v_isShared_1652_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1651_, 0, v___x_1653_);
                    v___x_1655_ = v___x_1651_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1656_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1656_, 0, v___x_1653_);
                    v___x_1655_ = v_reuseFailAlloc_1656_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1655_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Internal_Mock_Client_tryRecv_x3f___redArg___boxed(
    mut v_client_1658_: *mut crate::leanh::LeanObject,
    mut v_a_1659_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1660_ = l_Std_Http_Internal_Mock_Client_tryRecv_x3f___redArg(v_client_1658_);
    return v_res_1660_;
}
pub unsafe fn l_Std_Http_Internal_Mock_Client_tryRecv_x3f(
    mut v_client_1661_: *mut crate::leanh::LeanObject,
    mut v___expect_1662_: u64,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1664_ = l_Std_Http_Internal_Mock_Client_tryRecv_x3f___redArg(v_client_1661_);
    return v___x_1664_;
}
pub unsafe fn l_Std_Http_Internal_Mock_Client_tryRecv_x3f___boxed(
    mut v_client_1665_: *mut crate::leanh::LeanObject,
    mut v___expect_1666_: *mut crate::leanh::LeanObject,
    mut v_a_1667_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___expect_boxed_1668_: u64 = 0;
    let mut v_res_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___expect_boxed_1668_ = crate::leanh::lean_unbox_uint64(v___expect_1666_);
    crate::leanh::lean_dec_ref(v___expect_1666_);
    v_res_1669_ =
        l_Std_Http_Internal_Mock_Client_tryRecv_x3f(v_client_1665_, v___expect_boxed_1668_);
    return v_res_1669_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Std_Http_Internal_Mock_Client_tryRecv_x3f_spec__0(
    mut v___x_1670_: *mut crate::leanh::LeanObject,
    mut v_inst_1671_: *mut crate::leanh::LeanObject,
    mut v_a_1672_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1674_ = l___private_Init_While_0__whileM_erased___at___00Std_Http_Internal_Mock_Client_tryRecv_x3f_spec__0___redArg(v___x_1670_, v_a_1672_);
    return v___x_1674_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Std_Http_Internal_Mock_Client_tryRecv_x3f_spec__0___boxed(
    mut v___x_1675_: *mut crate::leanh::LeanObject,
    mut v_inst_1676_: *mut crate::leanh::LeanObject,
    mut v_a_1677_: *mut crate::leanh::LeanObject,
    mut v___y_1678_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1679_ = l___private_Init_While_0__whileM_erased___at___00Std_Http_Internal_Mock_Client_tryRecv_x3f_spec__0(v___x_1675_, v_inst_1676_, v_a_1677_);
    return v_res_1679_;
}
pub unsafe fn l_Std_Http_Internal_Mock_Client_close(
    mut v_client_1684_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_clientToServer_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_serverToClient_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: u8 = 0;
    let mut v___x_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1694_: u8 = 0;
    let mut v___x_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1698_: u8 = 0;
    let mut v_a_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1702_: u8 = 0;
    let mut v___x_1703_: u8 = 0;
    let mut v___x_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1712_: u8 = 0;
    let mut v___x_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: u8 = 0;
    let mut v___x_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1720_: u8 = 0;
    let mut v___x_1721_: u8 = 0;
    let mut v___x_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1730_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_clientToServer_1686_ = crate::leanh::lean_ctor_get(v_client_1684_, 0);
                crate::leanh::lean_inc_ref_n(v_clientToServer_1686_, 2);
                v_serverToClient_1687_ = crate::leanh::lean_ctor_get(v_client_1684_, 1);
                crate::leanh::lean_inc_ref(v_serverToClient_1687_);
                crate::leanh::lean_dec_ref(v_client_1684_);
                v___x_1715_ = l_Std_CloseableChannel_isClosed___redArg(v_clientToServer_1686_);
                if v___x_1715_ == 0 {
                    v___x_1716_ = l_Std_CloseableChannel_close___redArg(v_clientToServer_1686_);
                    if crate::leanh::lean_obj_tag(v___x_1716_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_1716_, 1);
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_serverToClient_1687_);
                        v_a_1717_ = crate::leanh::lean_ctor_get(v___x_1716_, 0);
                        v_isSharedCheck_1730_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1716_)) as u8;
                        if v_isSharedCheck_1730_ == 0 {
                            v___x_1719_ = v___x_1716_;
                            v_isShared_1720_ = v_isSharedCheck_1730_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1717_);
                            crate::leanh::lean_dec(v___x_1716_);
                            v___x_1719_ = crate::leanh::lean_box(0);
                            v_isShared_1720_ = v_isSharedCheck_1730_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_clientToServer_1686_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_serverToClient_1687_);
                v___x_1689_ = l_Std_CloseableChannel_isClosed___redArg(v_serverToClient_1687_);
                if v___x_1689_ == 0 {
                    v___x_1690_ = l_Std_CloseableChannel_close___redArg(v_serverToClient_1687_);
                    if crate::leanh::lean_obj_tag(v___x_1690_) == 0 {
                        v_a_1691_ = crate::leanh::lean_ctor_get(v___x_1690_, 0);
                        v_isSharedCheck_1698_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1690_)) as u8;
                        if v_isSharedCheck_1698_ == 0 {
                            v___x_1693_ = v___x_1690_;
                            v_isShared_1694_ = v_isSharedCheck_1698_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1691_);
                            crate::leanh::lean_dec(v___x_1690_);
                            v___x_1693_ = crate::leanh::lean_box(0);
                            v_isShared_1694_ = v_isSharedCheck_1698_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_a_1699_ = crate::leanh::lean_ctor_get(v___x_1690_, 0);
                        v_isSharedCheck_1712_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1690_)) as u8;
                        if v_isSharedCheck_1712_ == 0 {
                            v___x_1701_ = v___x_1690_;
                            v_isShared_1702_ = v_isSharedCheck_1712_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1699_);
                            crate::leanh::lean_dec(v___x_1690_);
                            v___x_1701_ = crate::leanh::lean_box(0);
                            v_isShared_1702_ = v_isSharedCheck_1712_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_serverToClient_1687_);
                    v___x_1713_ = crate::leanh::lean_box(0);
                    v___x_1714_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1714_, 0, v___x_1713_);
                    return v___x_1714_;
                }
            }
            2 => {
                if v_isShared_1694_ == 0 {
                    v___x_1696_ = v___x_1693_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1697_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1697_, 0, v_a_1691_);
                    v___x_1696_ = v_reuseFailAlloc_1697_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1696_;
            }
            4 => {
                v___x_1703_ = (crate::leanh::lean_unbox(v_a_1699_) as u8);
                crate::leanh::lean_dec(v_a_1699_);
                if v___x_1703_ == 0 {
                    v___x_1704_ = l_Std_Http_Internal_Mock_Client_close___closed__0;
                    if v_isShared_1702_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1701_, 0, v___x_1704_);
                        v___x_1706_ = v___x_1701_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1707_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1707_, 0, v___x_1704_);
                        v___x_1706_ = v_reuseFailAlloc_1707_;
                        state = 5;
                        continue;
                    }
                } else {
                    v___x_1708_ = l_Std_Http_Internal_Mock_Client_close___closed__1;
                    if v_isShared_1702_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1701_, 0, v___x_1708_);
                        v___x_1710_ = v___x_1701_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1711_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1711_, 0, v___x_1708_);
                        v___x_1710_ = v_reuseFailAlloc_1711_;
                        state = 6;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_1706_;
            }
            6 => {
                return v___x_1710_;
            }
            7 => {
                v___x_1721_ = (crate::leanh::lean_unbox(v_a_1717_) as u8);
                crate::leanh::lean_dec(v_a_1717_);
                if v___x_1721_ == 0 {
                    v___x_1722_ = l_Std_Http_Internal_Mock_Client_close___closed__0;
                    if v_isShared_1720_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1719_, 0, v___x_1722_);
                        v___x_1724_ = v___x_1719_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_1725_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1725_, 0, v___x_1722_);
                        v___x_1724_ = v_reuseFailAlloc_1725_;
                        state = 8;
                        continue;
                    }
                } else {
                    v___x_1726_ = l_Std_Http_Internal_Mock_Client_close___closed__1;
                    if v_isShared_1720_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1719_, 0, v___x_1726_);
                        v___x_1728_ = v___x_1719_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_1729_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1729_, 0, v___x_1726_);
                        v___x_1728_ = v_reuseFailAlloc_1729_;
                        state = 9;
                        continue;
                    }
                }
            }
            8 => {
                return v___x_1724_;
            }
            9 => {
                return v___x_1728_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Internal_Mock_Client_close___boxed(
    mut v_client_1731_: *mut crate::leanh::LeanObject,
    mut v_a_1732_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1733_ = l_Std_Http_Internal_Mock_Client_close(v_client_1731_);
    return v_res_1733_;
}
pub unsafe fn l_Std_Http_Internal_Mock_Server_getRecvChan(
    mut v_server_1734_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_clientToServer_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_clientToServer_1735_ = crate::leanh::lean_ctor_get(v_server_1734_, 0);
    crate::leanh::lean_inc_ref(v_clientToServer_1735_);
    return v_clientToServer_1735_;
}
pub unsafe fn l_Std_Http_Internal_Mock_Server_getRecvChan___boxed(
    mut v_server_1736_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1737_ = l_Std_Http_Internal_Mock_Server_getRecvChan(v_server_1736_);
    crate::leanh::lean_dec_ref(v_server_1736_);
    return v_res_1737_;
}
pub unsafe fn l_Std_Http_Internal_Mock_Server_getSendChan(
    mut v_server_1738_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_serverToClient_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_serverToClient_1739_ = crate::leanh::lean_ctor_get(v_server_1738_, 1);
    crate::leanh::lean_inc_ref(v_serverToClient_1739_);
    return v_serverToClient_1739_;
}
pub unsafe fn l_Std_Http_Internal_Mock_Server_getSendChan___boxed(
    mut v_server_1740_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1741_ = l_Std_Http_Internal_Mock_Server_getSendChan(v_server_1740_);
    crate::leanh::lean_dec_ref(v_server_1740_);
    return v_res_1741_;
}
pub unsafe fn l_Std_Http_Internal_Mock_Server_send(
    mut v_server_1742_: *mut crate::leanh::LeanObject,
    mut v_data_1743_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_serverToClient_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_serverToClient_1745_ = crate::leanh::lean_ctor_get(v_server_1742_, 1);
    crate::leanh::lean_inc_ref(v_serverToClient_1745_);
    crate::leanh::lean_dec_ref(v_server_1742_);
    v___x_1746_ = l_Std_Http_Internal_Mock_send(v_serverToClient_1745_, v_data_1743_);
    return v___x_1746_;
}
pub unsafe fn l_Std_Http_Internal_Mock_Server_send___boxed(
    mut v_server_1747_: *mut crate::leanh::LeanObject,
    mut v_data_1748_: *mut crate::leanh::LeanObject,
    mut v_a_1749_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1750_ = l_Std_Http_Internal_Mock_Server_send(v_server_1747_, v_data_1748_);
    return v_res_1750_;
}
pub unsafe fn l_Std_Http_Internal_Mock_Server_recv_x3f(
    mut v_server_1751_: *mut crate::leanh::LeanObject,
    mut v_expect_1752_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_clientToServer_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_clientToServer_1754_ = crate::leanh::lean_ctor_get(v_server_1751_, 0);
    crate::leanh::lean_inc_ref(v_clientToServer_1754_);
    crate::leanh::lean_dec_ref(v_server_1751_);
    v___x_1755_ = l_Std_Http_Internal_Mock_recvJoined(v_clientToServer_1754_, v_expect_1752_);
    return v___x_1755_;
}
pub unsafe fn l_Std_Http_Internal_Mock_Server_recv_x3f___boxed(
    mut v_server_1756_: *mut crate::leanh::LeanObject,
    mut v_expect_1757_: *mut crate::leanh::LeanObject,
    mut v_a_1758_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1759_ = l_Std_Http_Internal_Mock_Server_recv_x3f(v_server_1756_, v_expect_1757_);
    return v_res_1759_;
}
pub unsafe fn l_Std_Http_Internal_Mock_Server_tryRecv_x3f___redArg(
    mut v_server_1760_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_clientToServer_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1767_: u8 = 0;
    let mut v___x_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1772_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_clientToServer_1762_ = crate::leanh::lean_ctor_get(v_server_1760_, 0);
                crate::leanh::lean_inc_ref_n(v_clientToServer_1762_, 2);
                crate::leanh::lean_dec_ref(v_server_1760_);
                v___x_1763_ = l_Std_CloseableChannel_tryRecv___redArg(v_clientToServer_1762_);
                if crate::leanh::lean_obj_tag(v___x_1763_) == 0 {
                    crate::leanh::lean_dec_ref(v_clientToServer_1762_);
                    return v___x_1763_;
                } else {
                    v_val_1764_ = crate::leanh::lean_ctor_get(v___x_1763_, 0);
                    v_isSharedCheck_1772_ = (!crate::leanh::lean_is_exclusive(v___x_1763_)) as u8;
                    if v_isSharedCheck_1772_ == 0 {
                        v___x_1766_ = v___x_1763_;
                        v_isShared_1767_ = v_isSharedCheck_1772_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1764_);
                        crate::leanh::lean_dec(v___x_1763_);
                        v___x_1766_ = crate::leanh::lean_box(0);
                        v_isShared_1767_ = v_isSharedCheck_1772_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1768_ = l___private_Init_While_0__whileM_erased___at___00Std_Http_Internal_Mock_Client_tryRecv_x3f_spec__0___redArg(v_clientToServer_1762_, v_val_1764_);
                if v_isShared_1767_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1766_, 0, v___x_1768_);
                    v___x_1770_ = v___x_1766_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1771_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1771_, 0, v___x_1768_);
                    v___x_1770_ = v_reuseFailAlloc_1771_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1770_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Internal_Mock_Server_tryRecv_x3f___redArg___boxed(
    mut v_server_1773_: *mut crate::leanh::LeanObject,
    mut v_a_1774_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1775_ = l_Std_Http_Internal_Mock_Server_tryRecv_x3f___redArg(v_server_1773_);
    return v_res_1775_;
}
pub unsafe fn l_Std_Http_Internal_Mock_Server_tryRecv_x3f(
    mut v_server_1776_: *mut crate::leanh::LeanObject,
    mut v___expect_1777_: u64,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1779_ = l_Std_Http_Internal_Mock_Server_tryRecv_x3f___redArg(v_server_1776_);
    return v___x_1779_;
}
pub unsafe fn l_Std_Http_Internal_Mock_Server_tryRecv_x3f___boxed(
    mut v_server_1780_: *mut crate::leanh::LeanObject,
    mut v___expect_1781_: *mut crate::leanh::LeanObject,
    mut v_a_1782_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___expect_boxed_1783_: u64 = 0;
    let mut v_res_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___expect_boxed_1783_ = crate::leanh::lean_unbox_uint64(v___expect_1781_);
    crate::leanh::lean_dec_ref(v___expect_1781_);
    v_res_1784_ =
        l_Std_Http_Internal_Mock_Server_tryRecv_x3f(v_server_1780_, v___expect_boxed_1783_);
    return v_res_1784_;
}
pub unsafe fn l_Std_Http_Internal_Mock_Server_close(
    mut v_server_1785_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_clientToServer_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_serverToClient_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: u8 = 0;
    let mut v___x_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1795_: u8 = 0;
    let mut v___x_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1799_: u8 = 0;
    let mut v_a_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1803_: u8 = 0;
    let mut v___x_1804_: u8 = 0;
    let mut v___x_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1813_: u8 = 0;
    let mut v___x_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: u8 = 0;
    let mut v___x_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1821_: u8 = 0;
    let mut v___x_1822_: u8 = 0;
    let mut v___x_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1831_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_clientToServer_1787_ = crate::leanh::lean_ctor_get(v_server_1785_, 0);
                crate::leanh::lean_inc_ref_n(v_clientToServer_1787_, 2);
                v_serverToClient_1788_ = crate::leanh::lean_ctor_get(v_server_1785_, 1);
                crate::leanh::lean_inc_ref(v_serverToClient_1788_);
                crate::leanh::lean_dec_ref(v_server_1785_);
                v___x_1816_ = l_Std_CloseableChannel_isClosed___redArg(v_clientToServer_1787_);
                if v___x_1816_ == 0 {
                    v___x_1817_ = l_Std_CloseableChannel_close___redArg(v_clientToServer_1787_);
                    if crate::leanh::lean_obj_tag(v___x_1817_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_1817_, 1);
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_serverToClient_1788_);
                        v_a_1818_ = crate::leanh::lean_ctor_get(v___x_1817_, 0);
                        v_isSharedCheck_1831_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1817_)) as u8;
                        if v_isSharedCheck_1831_ == 0 {
                            v___x_1820_ = v___x_1817_;
                            v_isShared_1821_ = v_isSharedCheck_1831_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1818_);
                            crate::leanh::lean_dec(v___x_1817_);
                            v___x_1820_ = crate::leanh::lean_box(0);
                            v_isShared_1821_ = v_isSharedCheck_1831_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_clientToServer_1787_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_serverToClient_1788_);
                v___x_1790_ = l_Std_CloseableChannel_isClosed___redArg(v_serverToClient_1788_);
                if v___x_1790_ == 0 {
                    v___x_1791_ = l_Std_CloseableChannel_close___redArg(v_serverToClient_1788_);
                    if crate::leanh::lean_obj_tag(v___x_1791_) == 0 {
                        v_a_1792_ = crate::leanh::lean_ctor_get(v___x_1791_, 0);
                        v_isSharedCheck_1799_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1791_)) as u8;
                        if v_isSharedCheck_1799_ == 0 {
                            v___x_1794_ = v___x_1791_;
                            v_isShared_1795_ = v_isSharedCheck_1799_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1792_);
                            crate::leanh::lean_dec(v___x_1791_);
                            v___x_1794_ = crate::leanh::lean_box(0);
                            v_isShared_1795_ = v_isSharedCheck_1799_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_a_1800_ = crate::leanh::lean_ctor_get(v___x_1791_, 0);
                        v_isSharedCheck_1813_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1791_)) as u8;
                        if v_isSharedCheck_1813_ == 0 {
                            v___x_1802_ = v___x_1791_;
                            v_isShared_1803_ = v_isSharedCheck_1813_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1800_);
                            crate::leanh::lean_dec(v___x_1791_);
                            v___x_1802_ = crate::leanh::lean_box(0);
                            v_isShared_1803_ = v_isSharedCheck_1813_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_serverToClient_1788_);
                    v___x_1814_ = crate::leanh::lean_box(0);
                    v___x_1815_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1815_, 0, v___x_1814_);
                    return v___x_1815_;
                }
            }
            2 => {
                if v_isShared_1795_ == 0 {
                    v___x_1797_ = v___x_1794_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1798_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1798_, 0, v_a_1792_);
                    v___x_1797_ = v_reuseFailAlloc_1798_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1797_;
            }
            4 => {
                v___x_1804_ = (crate::leanh::lean_unbox(v_a_1800_) as u8);
                crate::leanh::lean_dec(v_a_1800_);
                if v___x_1804_ == 0 {
                    v___x_1805_ = l_Std_Http_Internal_Mock_Client_close___closed__0;
                    if v_isShared_1803_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1802_, 0, v___x_1805_);
                        v___x_1807_ = v___x_1802_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1808_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1808_, 0, v___x_1805_);
                        v___x_1807_ = v_reuseFailAlloc_1808_;
                        state = 5;
                        continue;
                    }
                } else {
                    v___x_1809_ = l_Std_Http_Internal_Mock_Client_close___closed__1;
                    if v_isShared_1803_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1802_, 0, v___x_1809_);
                        v___x_1811_ = v___x_1802_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1812_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1812_, 0, v___x_1809_);
                        v___x_1811_ = v_reuseFailAlloc_1812_;
                        state = 6;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_1807_;
            }
            6 => {
                return v___x_1811_;
            }
            7 => {
                v___x_1822_ = (crate::leanh::lean_unbox(v_a_1818_) as u8);
                crate::leanh::lean_dec(v_a_1818_);
                if v___x_1822_ == 0 {
                    v___x_1823_ = l_Std_Http_Internal_Mock_Client_close___closed__0;
                    if v_isShared_1821_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1820_, 0, v___x_1823_);
                        v___x_1825_ = v___x_1820_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_1826_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1826_, 0, v___x_1823_);
                        v___x_1825_ = v_reuseFailAlloc_1826_;
                        state = 8;
                        continue;
                    }
                } else {
                    v___x_1827_ = l_Std_Http_Internal_Mock_Client_close___closed__1;
                    if v_isShared_1821_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1820_, 0, v___x_1827_);
                        v___x_1829_ = v___x_1820_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_1830_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1830_, 0, v___x_1827_);
                        v___x_1829_ = v_reuseFailAlloc_1830_;
                        state = 9;
                        continue;
                    }
                }
            }
            8 => {
                return v___x_1825_;
            }
            9 => {
                return v___x_1829_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Internal_Mock_Server_close___boxed(
    mut v_server_1832_: *mut crate::leanh::LeanObject,
    mut v_a_1833_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1834_ = l_Std_Http_Internal_Mock_Server_close(v_server_1832_);
    return v_res_1834_;
}
pub unsafe fn l_Std_Http_Internal_instTransportClient___lam__0(
    mut v_client_1835_: *mut crate::leanh::LeanObject,
    mut v_expect_1836_: u64,
) -> *mut crate::leanh::LeanObject {
    let mut v_serverToClient_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_serverToClient_1838_ = crate::leanh::lean_ctor_get(v_client_1835_, 1);
    crate::leanh::lean_inc_ref(v_serverToClient_1838_);
    crate::leanh::lean_dec_ref(v_client_1835_);
    v___x_1839_ = crate::leanh::lean_box_uint64(v_expect_1836_);
    v___x_1840_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1840_, 0, v___x_1839_);
    v___x_1841_ = l_Std_Http_Internal_Mock_recvJoined(v_serverToClient_1838_, v___x_1840_);
    return v___x_1841_;
}
pub unsafe fn l_Std_Http_Internal_instTransportClient___lam__0___boxed(
    mut v_client_1842_: *mut crate::leanh::LeanObject,
    mut v_expect_1843_: *mut crate::leanh::LeanObject,
    mut v___y_1844_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_expect_boxed_1845_: u64 = 0;
    let mut v_res_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_expect_boxed_1845_ = crate::leanh::lean_unbox_uint64(v_expect_1843_);
    crate::leanh::lean_dec_ref(v_expect_1843_);
    v_res_1846_ =
        l_Std_Http_Internal_instTransportClient___lam__0(v_client_1842_, v_expect_boxed_1845_);
    return v_res_1846_;
}
pub unsafe fn l_Std_Http_Internal_instTransportClient___lam__1(
    mut v_client_1847_: *mut crate::leanh::LeanObject,
    mut v_data_1848_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_clientToServer_1850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_clientToServer_1850_ = crate::leanh::lean_ctor_get(v_client_1847_, 0);
    crate::leanh::lean_inc_ref(v_clientToServer_1850_);
    crate::leanh::lean_dec_ref(v_client_1847_);
    v___x_1851_ = l_Std_Http_Internal_Mock_sendAll(v_clientToServer_1850_, v_data_1848_);
    return v___x_1851_;
}
pub unsafe fn l_Std_Http_Internal_instTransportClient___lam__1___boxed(
    mut v_client_1852_: *mut crate::leanh::LeanObject,
    mut v_data_1853_: *mut crate::leanh::LeanObject,
    mut v___y_1854_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1855_ = l_Std_Http_Internal_instTransportClient___lam__1(v_client_1852_, v_data_1853_);
    return v_res_1855_;
}
pub unsafe fn l_Std_Http_Internal_instTransportClient___lam__2(
    mut v_client_1856_: *mut crate::leanh::LeanObject,
    mut v_x_1857_: u64,
) -> *mut crate::leanh::LeanObject {
    let mut v_serverToClient_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_serverToClient_1858_ = crate::leanh::lean_ctor_get(v_client_1856_, 1);
    crate::leanh::lean_inc_ref(v_serverToClient_1858_);
    crate::leanh::lean_dec_ref(v_client_1856_);
    v___x_1859_ = l_Std_CloseableChannel_recvSelector___redArg(v_serverToClient_1858_);
    return v___x_1859_;
}
pub unsafe fn l_Std_Http_Internal_instTransportClient___lam__2___boxed(
    mut v_client_1860_: *mut crate::leanh::LeanObject,
    mut v_x_1861_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_43__boxed_1862_: u64 = 0;
    let mut v_res_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_43__boxed_1862_ = crate::leanh::lean_unbox_uint64(v_x_1861_);
    crate::leanh::lean_dec_ref(v_x_1861_);
    v_res_1863_ =
        l_Std_Http_Internal_instTransportClient___lam__2(v_client_1860_, v_x_43__boxed_1862_);
    return v_res_1863_;
}
pub unsafe fn l_Std_Http_Internal_instTransportServer___lam__0(
    mut v_server_1874_: *mut crate::leanh::LeanObject,
    mut v_expect_1875_: u64,
) -> *mut crate::leanh::LeanObject {
    let mut v_clientToServer_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_clientToServer_1877_ = crate::leanh::lean_ctor_get(v_server_1874_, 0);
    crate::leanh::lean_inc_ref(v_clientToServer_1877_);
    crate::leanh::lean_dec_ref(v_server_1874_);
    v___x_1878_ = crate::leanh::lean_box_uint64(v_expect_1875_);
    v___x_1879_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1879_, 0, v___x_1878_);
    v___x_1880_ = l_Std_Http_Internal_Mock_recvJoined(v_clientToServer_1877_, v___x_1879_);
    return v___x_1880_;
}
pub unsafe fn l_Std_Http_Internal_instTransportServer___lam__0___boxed(
    mut v_server_1881_: *mut crate::leanh::LeanObject,
    mut v_expect_1882_: *mut crate::leanh::LeanObject,
    mut v___y_1883_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_expect_boxed_1884_: u64 = 0;
    let mut v_res_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_expect_boxed_1884_ = crate::leanh::lean_unbox_uint64(v_expect_1882_);
    crate::leanh::lean_dec_ref(v_expect_1882_);
    v_res_1885_ =
        l_Std_Http_Internal_instTransportServer___lam__0(v_server_1881_, v_expect_boxed_1884_);
    return v_res_1885_;
}
pub unsafe fn l_Std_Http_Internal_instTransportServer___lam__1(
    mut v_server_1886_: *mut crate::leanh::LeanObject,
    mut v_data_1887_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_serverToClient_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_serverToClient_1889_ = crate::leanh::lean_ctor_get(v_server_1886_, 1);
    crate::leanh::lean_inc_ref(v_serverToClient_1889_);
    crate::leanh::lean_dec_ref(v_server_1886_);
    v___x_1890_ = l_Std_Http_Internal_Mock_sendAll(v_serverToClient_1889_, v_data_1887_);
    return v___x_1890_;
}
pub unsafe fn l_Std_Http_Internal_instTransportServer___lam__1___boxed(
    mut v_server_1891_: *mut crate::leanh::LeanObject,
    mut v_data_1892_: *mut crate::leanh::LeanObject,
    mut v___y_1893_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1894_ = l_Std_Http_Internal_instTransportServer___lam__1(v_server_1891_, v_data_1892_);
    return v_res_1894_;
}
pub unsafe fn l_Std_Http_Internal_instTransportServer___lam__2(
    mut v_server_1895_: *mut crate::leanh::LeanObject,
    mut v_x_1896_: u64,
) -> *mut crate::leanh::LeanObject {
    let mut v_clientToServer_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_clientToServer_1897_ = crate::leanh::lean_ctor_get(v_server_1895_, 0);
    crate::leanh::lean_inc_ref(v_clientToServer_1897_);
    crate::leanh::lean_dec_ref(v_server_1895_);
    v___x_1898_ = l_Std_CloseableChannel_recvSelector___redArg(v_clientToServer_1897_);
    return v___x_1898_;
}
pub unsafe fn l_Std_Http_Internal_instTransportServer___lam__2___boxed(
    mut v_server_1899_: *mut crate::leanh::LeanObject,
    mut v_x_1900_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_43__boxed_1901_: u64 = 0;
    let mut v_res_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_43__boxed_1901_ = crate::leanh::lean_unbox_uint64(v_x_1900_);
    crate::leanh::lean_dec_ref(v_x_1900_);
    v_res_1902_ =
        l_Std_Http_Internal_instTransportServer___lam__2(v_server_1899_, v_x_43__boxed_1901_);
    return v_res_1902_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Http_Transport(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Http_Protocol_H1(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Http_Transport(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Http_Transport(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Http_Protocol_H1(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Transport(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Http_Transport(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Http_Transport(builtin);
}
