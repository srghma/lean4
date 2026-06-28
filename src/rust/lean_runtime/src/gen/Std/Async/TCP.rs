// Lean compiler output
// Module: Std.Async.TCP
// Imports: Std.Time Std.Internal.UV.TCP Std.Async.Select
use crate::r#gen::Init::Control::Except::l_Except_map;
use crate::r#gen::Init::Data::Int::Basic::l_Int_toNat;
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr4, l_Lean_mkAtom};
use crate::r#gen::Init::System::IO::{l_EIO_chainTask___redArg, l_IO_ofExcept___redArg};
use crate::r#gen::Init::System::IOError::{lean_io_error_to_string, lean_mk_io_user_error};
use crate::r#gen::Init::System::Promise::l_IO_Promise_isResolved___redArg;
use crate::r#gen::Std::Async::Basic::l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask;
use crate::r#gen::Std::Async::Select::{
    initialize_Std_Async_Select, runtime_initialize_Std_Async_Select,
};
use crate::r#gen::Std::Internal::UV::TCP::{
    initialize_Std_Internal_UV_TCP, runtime_initialize_Std_Internal_UV_TCP,
};
use crate::r#gen::Std::Time::{initialize_Std_Time, runtime_initialize_Std_Time};
use crate::lean_imports_rs::Init::Core::{
    lean_task_bind, lean_task_get_own, lean_task_map, lean_task_pure,
};
use crate::lean_imports_rs::Init::Data::SInt::Basic::lean_bool_to_int8;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::lean_uint32_of_nat;
use crate::lean_imports_rs::Init::Prelude::{lean_array_push, lean_mk_empty_array_with_capacity};
use crate::lean_imports_rs::Init::System::IO::{lean_io_as_task, lean_io_map_task};
use crate::lean_imports_rs::Init::System::Promise::{
    lean_io_promise_resolve, lean_io_promise_result_opt,
};
use crate::lean_imports_rs::Init::System::ST::{lean_st_ref_set, lean_st_ref_take};
use crate::lean_imports_rs::Std::Internal::UV::TCP::{
    lean_uv_tcp_accept, lean_uv_tcp_bind, lean_uv_tcp_cancel_accept, lean_uv_tcp_cancel_recv,
    lean_uv_tcp_connect, lean_uv_tcp_getpeername, lean_uv_tcp_getsockname, lean_uv_tcp_keepalive,
    lean_uv_tcp_listen, lean_uv_tcp_new, lean_uv_tcp_nodelay, lean_uv_tcp_recv, lean_uv_tcp_send,
    lean_uv_tcp_shutdown, lean_uv_tcp_try_accept, lean_uv_tcp_wait_readable,
};
pub static l_Std_Async_TCP_Socket_Server_accept___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Std_Async_TCP_Socket_Server_accept___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Async_TCP_Socket_Server_accept___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_TCP_Socket_Server_accept___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_TCP_Socket_Server_accept___closed__1_value: crate::leanh::LeanStringObject<
    44,
> = crate::leanh::LeanStringObject {
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
static mut l_Std_Async_TCP_Socket_Server_accept___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_TCP_Socket_Server_accept___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_TCP_Socket_Server_accept___closed__2_value: crate::leanh::LeanClosureObject<
    1,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Async_TCP_Socket_Server_accept___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Std_Async_TCP_Socket_Server_accept___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Async_TCP_Socket_Server_accept___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_TCP_Socket_Server_accept___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_TCP_Socket_Server_accept___closed__3_value: crate::leanh::LeanClosureObject<
    1,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Async_TCP_Socket_Server_accept___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Std_Async_TCP_Socket_Server_accept___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Async_TCP_Socket_Server_accept___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_TCP_Socket_Server_accept___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_TCP_Socket_Server_accept___closed__4_value: crate::leanh::LeanClosureObject<
    4,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Except_map as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 4,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Async_TCP_Socket_Server_accept___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Async_TCP_Socket_Server_accept___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_TCP_Socket_Server_accept___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_TCP_Socket_Server_tryAccept___closed__0_value:
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
    m_fun: lean_io_error_to_string as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Async_TCP_Socket_Server_tryAccept___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_TCP_Socket_Server_tryAccept___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_TCP_Socket_Server_acceptSelector___lam__2___closed__0_value:
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
    m_fun: l_Std_Async_TCP_Socket_Server_acceptSelector___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Async_TCP_Socket_Server_acceptSelector___lam__2___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_TCP_Socket_Server_acceptSelector___lam__2___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__0_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [76, 101, 97, 110, 0],
};
static mut l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__1_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [80, 97, 114, 115, 101, 114, 0],
};
static mut l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__2_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [84, 97, 99, 116, 105, 99, 0],
};
static mut l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__3_value:
    crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0],
};
static mut l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__4_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__4_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__4_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__4_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__4_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__4_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__4_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__3_value)
            as *mut crate::leanh::LeanObject,
        8504843326314613972 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__5_value:
    crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__6_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 19,
    m_capacity: 19,
    m_length: 18,
    m_data: [
        116, 97, 99, 116, 105, 99, 83, 101, 113, 49, 73, 110, 100, 101, 110, 116, 101, 100, 0,
    ],
};
static mut l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__6_value)
        as *mut crate::leanh::LeanObject;
static l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__7_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__7_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__7_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__7_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__7_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__7_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__7_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__6_value)
            as *mut crate::leanh::LeanObject,
        17228437386856258271 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__8_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [110, 117, 108, 108, 0],
};
static mut l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__9_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__8_value)
            as *mut crate::leanh::LeanObject,
        9855511589286918680 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__10_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [100, 101, 99, 105, 100, 101, 0],
};
static mut l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__10_value)
        as *mut crate::leanh::LeanObject;
static l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__11_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__11_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__11_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__11_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__11_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__11_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__11_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__10_value)
            as *mut crate::leanh::LeanObject,
        14249328086033210933 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__11:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__11_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__12_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__13_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__14_value:
    crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [111, 112, 116, 67, 111, 110, 102, 105, 103, 0],
};
static mut l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__14:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__14_value)
        as *mut crate::leanh::LeanObject;
static l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__15_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__15_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__15_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__15_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__15_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__15_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__15_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__14_value)
            as *mut crate::leanh::LeanObject,
        3488656302031949961 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__15:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__16_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 1,
    },
    m_objs: [
        (((2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__9_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__16:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__16_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__17_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__17:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__18_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__18:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__19_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__19:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__20_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__20:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__21_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__21:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__22_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__22:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__23_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__23:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__24_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__24:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__25_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__25:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__26_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__26:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Std_Async_TCP_Socket_Server_keepAlive___auto__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Async_TCP_Socket_Client_connect___closed__0_value:
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
    m_fun: l_Std_Async_TCP_Socket_Client_connect___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Std_Async_TCP_Socket_Server_accept___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Async_TCP_Socket_Client_connect___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_TCP_Socket_Client_connect___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_TCP_Socket_Client_connect___closed__1_value:
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
    m_fun: l_Std_Async_TCP_Socket_Client_connect___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Std_Async_TCP_Socket_Client_connect___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Async_TCP_Socket_Client_connect___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_TCP_Socket_Client_connect___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_TCP_Socket_Client_recv_x3f___closed__0_value:
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
    m_fun: l_Std_Async_TCP_Socket_Client_recv_x3f___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Std_Async_TCP_Socket_Server_accept___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Async_TCP_Socket_Client_recv_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_TCP_Socket_Client_recv_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_TCP_Socket_Client_recv_x3f___closed__1_value:
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
    m_fun: l_Std_Async_TCP_Socket_Client_recv_x3f___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Std_Async_TCP_Socket_Client_recv_x3f___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Async_TCP_Socket_Client_recv_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_TCP_Socket_Client_recv_x3f___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0___lam__0 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Async_TCP_Socket_Client_recvSelector___lam__0___closed__0_value:
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
static mut l_Std_Async_TCP_Socket_Client_recvSelector___lam__0___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_TCP_Socket_Client_recvSelector___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_TCP_Socket_Client_recvSelector___lam__0___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Async_TCP_Socket_Client_recvSelector___lam__0___closed__0_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Async_TCP_Socket_Client_recvSelector___lam__0___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_TCP_Socket_Client_recvSelector___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_TCP_Socket_Client_recvSelector___lam__3___closed__0_value:
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
static mut l_Std_Async_TCP_Socket_Client_recvSelector___lam__3___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_TCP_Socket_Client_recvSelector___lam__3___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_TCP_Socket_Client_recvSelector___lam__3___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Async_TCP_Socket_Client_recvSelector___lam__3___closed__0_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Async_TCP_Socket_Client_recvSelector___lam__3___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_TCP_Socket_Client_recvSelector___lam__3___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_TCP_Socket_Client_recvSelector___closed__0_value:
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
    m_fun: l_Std_Async_TCP_Socket_Client_recvSelector___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Async_TCP_Socket_Client_recvSelector___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_TCP_Socket_Client_recvSelector___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_TCP_Socket_Client_recvSelector___closed__1_value:
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
    m_fun: l_Std_Async_TCP_Socket_Client_recvSelector___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Async_TCP_Socket_Client_recvSelector___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_TCP_Socket_Client_recvSelector___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Async_TCP_Socket_Client_keepAlive___auto__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Std_Async_TCP_Socket_Server_mk() -> *mut crate::leanh::LeanObject {
    let mut v___x_1284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1288_: u8 = 0;
    let mut v___x_1290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1292_: u8 = 0;
    let mut v_a_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1296_: u8 = 0;
    let mut v___x_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1300_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1284_ = lean_uv_tcp_new();
                if crate::leanh::lean_obj_tag(v___x_1284_) == 0 {
                    v_a_1285_ = crate::leanh::lean_ctor_get(v___x_1284_, 0);
                    v_isSharedCheck_1292_ = (!crate::leanh::lean_is_exclusive(v___x_1284_)) as u8;
                    if v_isSharedCheck_1292_ == 0 {
                        v___x_1287_ = v___x_1284_;
                        v_isShared_1288_ = v_isSharedCheck_1292_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1285_);
                        crate::leanh::lean_dec(v___x_1284_);
                        v___x_1287_ = crate::leanh::lean_box(0);
                        v_isShared_1288_ = v_isSharedCheck_1292_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1293_ = crate::leanh::lean_ctor_get(v___x_1284_, 0);
                    v_isSharedCheck_1300_ = (!crate::leanh::lean_is_exclusive(v___x_1284_)) as u8;
                    if v_isSharedCheck_1300_ == 0 {
                        v___x_1295_ = v___x_1284_;
                        v_isShared_1296_ = v_isSharedCheck_1300_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1293_);
                        crate::leanh::lean_dec(v___x_1284_);
                        v___x_1295_ = crate::leanh::lean_box(0);
                        v_isShared_1296_ = v_isSharedCheck_1300_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1288_ == 0 {
                    v___x_1290_ = v___x_1287_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1291_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_a_1285_);
                    v___x_1290_ = v_reuseFailAlloc_1291_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1290_;
            }
            3 => {
                if v_isShared_1296_ == 0 {
                    v___x_1298_ = v___x_1295_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1299_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1299_, 0, v_a_1293_);
                    v___x_1298_ = v_reuseFailAlloc_1299_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1298_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_TCP_Socket_Server_mk___boxed(
    mut v_a_1301_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1302_ = l_Std_Async_TCP_Socket_Server_mk();
    return v_res_1302_;
}
pub unsafe fn l_Std_Async_TCP_Socket_Server_bind(
    mut v_s_1303_: *mut crate::leanh::LeanObject,
    mut v_addr_1304_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1306_ = lean_uv_tcp_bind(v_s_1303_, v_addr_1304_);
    return v___x_1306_;
}
pub unsafe fn l_Std_Async_TCP_Socket_Server_bind___boxed(
    mut v_s_1307_: *mut crate::leanh::LeanObject,
    mut v_addr_1308_: *mut crate::leanh::LeanObject,
    mut v_a_1309_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1310_ = l_Std_Async_TCP_Socket_Server_bind(v_s_1307_, v_addr_1308_);
    crate::leanh::lean_dec_ref(v_addr_1308_);
    crate::leanh::lean_dec(v_s_1307_);
    return v_res_1310_;
}
pub unsafe fn l_Std_Async_TCP_Socket_Server_listen(
    mut v_s_1311_: *mut crate::leanh::LeanObject,
    mut v_backlog_1312_: u32,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1314_ = lean_uv_tcp_listen(v_s_1311_, v_backlog_1312_);
    return v___x_1314_;
}
pub unsafe fn l_Std_Async_TCP_Socket_Server_listen___boxed(
    mut v_s_1315_: *mut crate::leanh::LeanObject,
    mut v_backlog_1316_: *mut crate::leanh::LeanObject,
    mut v_a_1317_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_backlog_boxed_1318_: u32 = 0;
    let mut v_res_1319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_backlog_boxed_1318_ = crate::leanh::lean_unbox_uint32(v_backlog_1316_);
    crate::leanh::lean_dec(v_backlog_1316_);
    v_res_1319_ = l_Std_Async_TCP_Socket_Server_listen(v_s_1315_, v_backlog_boxed_1318_);
    crate::leanh::lean_dec(v_s_1315_);
    return v_res_1319_;
}
pub unsafe fn l_Std_Async_TCP_Socket_Server_accept___lam__0(
    mut v_native_1320_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_native_1320_);
    return v_native_1320_;
}
pub unsafe fn l_Std_Async_TCP_Socket_Server_accept___lam__0___boxed(
    mut v_native_1321_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1322_ = l_Std_Async_TCP_Socket_Server_accept___lam__0(v_native_1321_);
    crate::leanh::lean_dec(v_native_1321_);
    return v_res_1322_;
}
pub unsafe fn l_Std_Async_TCP_Socket_Server_accept___lam__1(
    mut v___x_1323_: *mut crate::leanh::LeanObject,
    mut v_x_1324_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1324_) == 0 {
        let mut v___x_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1325_ = lean_mk_io_user_error(v___x_1323_);
        v___x_1326_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1326_, 0, v___x_1325_);
        return v___x_1326_;
    } else {
        let mut v_val_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v___x_1323_);
        v_val_1327_ = crate::leanh::lean_ctor_get(v_x_1324_, 0);
        crate::leanh::lean_inc(v_val_1327_);
        return v_val_1327_;
    }
}
pub unsafe fn l_Std_Async_TCP_Socket_Server_accept___lam__1___boxed(
    mut v___x_1328_: *mut crate::leanh::LeanObject,
    mut v_x_1329_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1330_ = l_Std_Async_TCP_Socket_Server_accept___lam__1(v___x_1328_, v_x_1329_);
    crate::leanh::lean_dec(v_x_1329_);
    return v_res_1330_;
}
pub unsafe fn l_Std_Async_TCP_Socket_Server_accept___lam__2(
    mut v___f_1331_: *mut crate::leanh::LeanObject,
    mut v_x_1332_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1337_: u8 = 0;
    let mut v___x_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1342_: u8 = 0;
    let mut v_a_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1347_: u8 = 0;
    let mut v___x_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1352_: u8 = 0;
    let mut v_a_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: u8 = 0;
    let mut v___x_1357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1332_) == 0 {
                    crate::leanh::lean_dec_ref(v___f_1331_);
                    v_a_1334_ = crate::leanh::lean_ctor_get(v_x_1332_, 0);
                    v_isSharedCheck_1342_ = (!crate::leanh::lean_is_exclusive(v_x_1332_)) as u8;
                    if v_isSharedCheck_1342_ == 0 {
                        v___x_1336_ = v_x_1332_;
                        v_isShared_1337_ = v_isSharedCheck_1342_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1334_);
                        crate::leanh::lean_dec(v_x_1332_);
                        v___x_1336_ = crate::leanh::lean_box(0);
                        v_isShared_1337_ = v_isSharedCheck_1342_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1343_ = crate::leanh::lean_ctor_get(v_x_1332_, 0);
                    crate::leanh::lean_inc(v_a_1343_);
                    crate::leanh::lean_dec_ref_known(v_x_1332_, 1);
                    if crate::leanh::lean_obj_tag(v_a_1343_) == 0 {
                        crate::leanh::lean_dec_ref(v___f_1331_);
                        v_a_1344_ = crate::leanh::lean_ctor_get(v_a_1343_, 0);
                        v_isSharedCheck_1352_ = (!crate::leanh::lean_is_exclusive(v_a_1343_)) as u8;
                        if v_isSharedCheck_1352_ == 0 {
                            v___x_1346_ = v_a_1343_;
                            v_isShared_1347_ = v_isSharedCheck_1352_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1344_);
                            crate::leanh::lean_dec(v_a_1343_);
                            v___x_1346_ = crate::leanh::lean_box(0);
                            v_isShared_1347_ = v_isSharedCheck_1352_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_1353_ = crate::leanh::lean_ctor_get(v_a_1343_, 0);
                        crate::leanh::lean_inc(v_a_1353_);
                        crate::leanh::lean_dec_ref_known(v_a_1343_, 1);
                        v___x_1354_ = lean_io_promise_result_opt(v_a_1353_);
                        crate::leanh::lean_dec(v_a_1353_);
                        v___x_1355_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_1356_ = 0;
                        v___x_1357_ =
                            lean_task_map(v___f_1331_, v___x_1354_, v___x_1355_, v___x_1356_);
                        v___x_1358_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1358_, 0, v___x_1357_);
                        return v___x_1358_;
                    }
                }
            }
            1 => {
                if v_isShared_1337_ == 0 {
                    v___x_1339_ = v___x_1336_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1341_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1341_, 0, v_a_1334_);
                    v___x_1339_ = v_reuseFailAlloc_1341_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1340_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1340_, 0, v___x_1339_);
                return v___x_1340_;
            }
            3 => {
                if v_isShared_1347_ == 0 {
                    v___x_1349_ = v___x_1346_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1351_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1351_, 0, v_a_1344_);
                    v___x_1349_ = v_reuseFailAlloc_1351_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1350_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1350_, 0, v___x_1349_);
                return v___x_1350_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_TCP_Socket_Server_accept___lam__2___boxed(
    mut v___f_1359_: *mut crate::leanh::LeanObject,
    mut v_x_1360_: *mut crate::leanh::LeanObject,
    mut v___y_1361_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1362_ = l_Std_Async_TCP_Socket_Server_accept___lam__2(v___f_1359_, v_x_1360_);
    return v_res_1362_;
}
pub unsafe fn l_Std_Async_TCP_Socket_Server_accept(
    mut v_s_1371_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: u8 = 0;
    let mut v___x_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1388_: u8 = 0;
    let mut v___x_1390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1392_: u8 = 0;
    let mut v_a_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1396_: u8 = 0;
    let mut v___x_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1400_: u8 = 0;
    let mut v_a_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1404_: u8 = 0;
    let mut v___x_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1410_: u8 = 0;
    let mut v___x_1411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1415_: u8 = 0;
    let mut v___x_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1419_: u8 = 0;
    let mut v_a_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1423_: u8 = 0;
    let mut v___x_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1427_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1376_ = l_Std_Async_TCP_Socket_Server_accept___closed__3;
                v___x_1411_ = lean_uv_tcp_accept(v_s_1371_);
                if crate::leanh::lean_obj_tag(v___x_1411_) == 0 {
                    v_a_1412_ = crate::leanh::lean_ctor_get(v___x_1411_, 0);
                    v_isSharedCheck_1419_ = (!crate::leanh::lean_is_exclusive(v___x_1411_)) as u8;
                    if v_isSharedCheck_1419_ == 0 {
                        v___x_1414_ = v___x_1411_;
                        v_isShared_1415_ = v_isSharedCheck_1419_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1412_);
                        crate::leanh::lean_dec(v___x_1411_);
                        v___x_1414_ = crate::leanh::lean_box(0);
                        v_isShared_1415_ = v_isSharedCheck_1419_;
                        state = 9;
                        continue;
                    }
                } else {
                    v_a_1420_ = crate::leanh::lean_ctor_get(v___x_1411_, 0);
                    v_isSharedCheck_1427_ = (!crate::leanh::lean_is_exclusive(v___x_1411_)) as u8;
                    if v_isSharedCheck_1427_ == 0 {
                        v___x_1422_ = v___x_1411_;
                        v_isShared_1423_ = v_isSharedCheck_1427_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1420_);
                        crate::leanh::lean_dec(v___x_1411_);
                        v___x_1422_ = crate::leanh::lean_box(0);
                        v_isShared_1423_ = v_isSharedCheck_1427_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1375_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1375_, 0, v___y_1374_);
                return v___x_1375_;
            }
            2 => {
                v___x_1379_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1379_, 0, v_val_1378_);
                v___x_1380_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1380_, 0, v___x_1379_);
                v___x_1381_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1382_ = 0;
                v___x_1383_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_1381_,
                    v___x_1382_,
                    v___x_1380_,
                    v___f_1376_,
                );
                if crate::leanh::lean_obj_tag(v___x_1383_) == 0 {
                    v_a_1384_ = crate::leanh::lean_ctor_get(v___x_1383_, 0);
                    crate::leanh::lean_inc(v_a_1384_);
                    crate::leanh::lean_dec_ref_known(v___x_1383_, 1);
                    if crate::leanh::lean_obj_tag(v_a_1384_) == 0 {
                        v_a_1385_ = crate::leanh::lean_ctor_get(v_a_1384_, 0);
                        v_isSharedCheck_1392_ = (!crate::leanh::lean_is_exclusive(v_a_1384_)) as u8;
                        if v_isSharedCheck_1392_ == 0 {
                            v___x_1387_ = v_a_1384_;
                            v_isShared_1388_ = v_isSharedCheck_1392_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1385_);
                            crate::leanh::lean_dec(v_a_1384_);
                            v___x_1387_ = crate::leanh::lean_box(0);
                            v_isShared_1388_ = v_isSharedCheck_1392_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_1393_ = crate::leanh::lean_ctor_get(v_a_1384_, 0);
                        v_isSharedCheck_1400_ = (!crate::leanh::lean_is_exclusive(v_a_1384_)) as u8;
                        if v_isSharedCheck_1400_ == 0 {
                            v___x_1395_ = v_a_1384_;
                            v_isShared_1396_ = v_isSharedCheck_1400_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1393_);
                            crate::leanh::lean_dec(v_a_1384_);
                            v___x_1395_ = crate::leanh::lean_box(0);
                            v_isShared_1396_ = v_isSharedCheck_1400_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    v_a_1401_ = crate::leanh::lean_ctor_get(v___x_1383_, 0);
                    v_isSharedCheck_1410_ = (!crate::leanh::lean_is_exclusive(v___x_1383_)) as u8;
                    if v_isSharedCheck_1410_ == 0 {
                        v___x_1403_ = v___x_1383_;
                        v_isShared_1404_ = v_isSharedCheck_1410_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1401_);
                        crate::leanh::lean_dec(v___x_1383_);
                        v___x_1403_ = crate::leanh::lean_box(0);
                        v_isShared_1404_ = v_isSharedCheck_1410_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_1388_ == 0 {
                    v___x_1390_ = v___x_1387_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1391_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1391_, 0, v_a_1385_);
                    v___x_1390_ = v_reuseFailAlloc_1391_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___y_1374_ = v___x_1390_;
                state = 1;
                continue;
            }
            5 => {
                if v_isShared_1396_ == 0 {
                    v___x_1398_ = v___x_1395_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1399_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1399_, 0, v_a_1393_);
                    v___x_1398_ = v_reuseFailAlloc_1399_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___y_1374_ = v___x_1398_;
                state = 1;
                continue;
            }
            7 => {
                v___x_1405_ = l_Std_Async_TCP_Socket_Server_accept___closed__4;
                v___x_1406_ = lean_task_map(v___x_1405_, v_a_1401_, v___x_1381_, v___x_1382_);
                if v_isShared_1404_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1403_, 0, v___x_1406_);
                    v___x_1408_ = v___x_1403_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1409_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1409_, 0, v___x_1406_);
                    v___x_1408_ = v_reuseFailAlloc_1409_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1408_;
            }
            9 => {
                if v_isShared_1415_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1414_, 1);
                    v___x_1417_ = v___x_1414_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1418_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1418_, 0, v_a_1412_);
                    v___x_1417_ = v_reuseFailAlloc_1418_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v_val_1378_ = v___x_1417_;
                state = 2;
                continue;
            }
            11 => {
                if v_isShared_1423_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1422_, 0);
                    v___x_1425_ = v___x_1422_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1426_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1426_, 0, v_a_1420_);
                    v___x_1425_ = v_reuseFailAlloc_1426_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v_val_1378_ = v___x_1425_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_TCP_Socket_Server_accept___boxed(
    mut v_s_1428_: *mut crate::leanh::LeanObject,
    mut v_a_1429_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1430_ = l_Std_Async_TCP_Socket_Server_accept(v_s_1428_);
    crate::leanh::lean_dec(v_s_1428_);
    return v_res_1430_;
}
pub unsafe fn l_Std_Async_TCP_Socket_Server_tryAccept(
    mut v_s_1432_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1441_: u8 = 0;
    let mut v___x_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1449_: u8 = 0;
    let mut v___x_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1456_: u8 = 0;
    let mut v_isSharedCheck_1457_: u8 = 0;
    let mut v_a_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1461_: u8 = 0;
    let mut v___x_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1465_: u8 = 0;
    let mut v_a_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1469_: u8 = 0;
    let mut v___x_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1473_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1434_ = lean_uv_tcp_try_accept(v_s_1432_);
                if crate::leanh::lean_obj_tag(v___x_1434_) == 0 {
                    v_a_1435_ = crate::leanh::lean_ctor_get(v___x_1434_, 0);
                    crate::leanh::lean_inc(v_a_1435_);
                    crate::leanh::lean_dec_ref_known(v___x_1434_, 1);
                    v___x_1436_ = l_Std_Async_TCP_Socket_Server_tryAccept___closed__0;
                    v___x_1437_ = l_IO_ofExcept___redArg(v___x_1436_, v_a_1435_);
                    if crate::leanh::lean_obj_tag(v___x_1437_) == 0 {
                        v_a_1438_ = crate::leanh::lean_ctor_get(v___x_1437_, 0);
                        v_isSharedCheck_1457_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1437_)) as u8;
                        if v_isSharedCheck_1457_ == 0 {
                            v___x_1440_ = v___x_1437_;
                            v_isShared_1441_ = v_isSharedCheck_1457_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1438_);
                            crate::leanh::lean_dec(v___x_1437_);
                            v___x_1440_ = crate::leanh::lean_box(0);
                            v_isShared_1441_ = v_isSharedCheck_1457_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_1458_ = crate::leanh::lean_ctor_get(v___x_1437_, 0);
                        v_isSharedCheck_1465_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1437_)) as u8;
                        if v_isSharedCheck_1465_ == 0 {
                            v___x_1460_ = v___x_1437_;
                            v_isShared_1461_ = v_isSharedCheck_1465_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1458_);
                            crate::leanh::lean_dec(v___x_1437_);
                            v___x_1460_ = crate::leanh::lean_box(0);
                            v_isShared_1461_ = v_isSharedCheck_1465_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    v_a_1466_ = crate::leanh::lean_ctor_get(v___x_1434_, 0);
                    v_isSharedCheck_1473_ = (!crate::leanh::lean_is_exclusive(v___x_1434_)) as u8;
                    if v_isSharedCheck_1473_ == 0 {
                        v___x_1468_ = v___x_1434_;
                        v_isShared_1469_ = v_isSharedCheck_1473_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1466_);
                        crate::leanh::lean_dec(v___x_1434_);
                        v___x_1468_ = crate::leanh::lean_box(0);
                        v_isShared_1469_ = v_isSharedCheck_1473_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_1438_) == 0 {
                    v___x_1442_ = crate::leanh::lean_box(0);
                    if v_isShared_1441_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1440_, 0, v___x_1442_);
                        v___x_1444_ = v___x_1440_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1445_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1445_, 0, v___x_1442_);
                        v___x_1444_ = v_reuseFailAlloc_1445_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_val_1446_ = crate::leanh::lean_ctor_get(v_a_1438_, 0);
                    v_isSharedCheck_1456_ = (!crate::leanh::lean_is_exclusive(v_a_1438_)) as u8;
                    if v_isSharedCheck_1456_ == 0 {
                        v___x_1448_ = v_a_1438_;
                        v_isShared_1449_ = v_isSharedCheck_1456_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1446_);
                        crate::leanh::lean_dec(v_a_1438_);
                        v___x_1448_ = crate::leanh::lean_box(0);
                        v_isShared_1449_ = v_isSharedCheck_1456_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1444_;
            }
            3 => {
                if v_isShared_1449_ == 0 {
                    v___x_1451_ = v___x_1448_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1455_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1455_, 0, v_val_1446_);
                    v___x_1451_ = v_reuseFailAlloc_1455_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1441_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1440_, 0, v___x_1451_);
                    v___x_1453_ = v___x_1440_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1454_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1454_, 0, v___x_1451_);
                    v___x_1453_ = v_reuseFailAlloc_1454_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1453_;
            }
            6 => {
                if v_isShared_1461_ == 0 {
                    v___x_1463_ = v___x_1460_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1464_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1464_, 0, v_a_1458_);
                    v___x_1463_ = v_reuseFailAlloc_1464_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1463_;
            }
            8 => {
                if v_isShared_1469_ == 0 {
                    v___x_1471_ = v___x_1468_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1472_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1472_, 0, v_a_1466_);
                    v___x_1471_ = v_reuseFailAlloc_1472_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1471_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_TCP_Socket_Server_tryAccept___boxed(
    mut v_s_1474_: *mut crate::leanh::LeanObject,
    mut v_a_1475_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1476_ = l_Std_Async_TCP_Socket_Server_tryAccept(v_s_1474_);
    crate::leanh::lean_dec(v_s_1474_);
    return v_res_1476_;
}
pub unsafe fn l_IO_ofExcept___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__0___redArg(
    mut v_e_1477_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1482_: u8 = 0;
    let mut v___x_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1488_: u8 = 0;
    let mut v_a_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1492_: u8 = 0;
    let mut v___x_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1496_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_e_1477_) == 0 {
                    v_a_1479_ = crate::leanh::lean_ctor_get(v_e_1477_, 0);
                    v_isSharedCheck_1488_ = (!crate::leanh::lean_is_exclusive(v_e_1477_)) as u8;
                    if v_isSharedCheck_1488_ == 0 {
                        v___x_1481_ = v_e_1477_;
                        v_isShared_1482_ = v_isSharedCheck_1488_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1479_);
                        crate::leanh::lean_dec(v_e_1477_);
                        v___x_1481_ = crate::leanh::lean_box(0);
                        v_isShared_1482_ = v_isSharedCheck_1488_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1489_ = crate::leanh::lean_ctor_get(v_e_1477_, 0);
                    v_isSharedCheck_1496_ = (!crate::leanh::lean_is_exclusive(v_e_1477_)) as u8;
                    if v_isSharedCheck_1496_ == 0 {
                        v___x_1491_ = v_e_1477_;
                        v_isShared_1492_ = v_isSharedCheck_1496_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1489_);
                        crate::leanh::lean_dec(v_e_1477_);
                        v___x_1491_ = crate::leanh::lean_box(0);
                        v_isShared_1492_ = v_isSharedCheck_1496_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1483_ = lean_io_error_to_string(v_a_1479_);
                v___x_1484_ = lean_mk_io_user_error(v___x_1483_);
                if v_isShared_1482_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1481_, 1);
                    crate::leanh::lean_ctor_set(v___x_1481_, 0, v___x_1484_);
                    v___x_1486_ = v___x_1481_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1487_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1487_, 0, v___x_1484_);
                    v___x_1486_ = v_reuseFailAlloc_1487_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1486_;
            }
            3 => {
                if v_isShared_1492_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1491_, 0);
                    v___x_1494_ = v___x_1491_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1495_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1495_, 0, v_a_1489_);
                    v___x_1494_ = v_reuseFailAlloc_1495_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1494_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_ofExcept___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__0___redArg___boxed(
    mut v_e_1497_: *mut crate::leanh::LeanObject,
    mut v_a_1498_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1499_ =
        l_IO_ofExcept___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__0___redArg(
            v_e_1497_,
        );
    return v_res_1499_;
}
pub unsafe fn l_IO_ofExcept___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__0(
    mut v_00_u03b1_1500_: *mut crate::leanh::LeanObject,
    mut v_e_1501_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1503_ =
        l_IO_ofExcept___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__0___redArg(
            v_e_1501_,
        );
    return v___x_1503_;
}
pub unsafe fn l_IO_ofExcept___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__0___boxed(
    mut v_00_u03b1_1504_: *mut crate::leanh::LeanObject,
    mut v_e_1505_: *mut crate::leanh::LeanObject,
    mut v_a_1506_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1507_ = l_IO_ofExcept___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__0(
        v_00_u03b1_1504_,
        v_e_1505_,
    );
    return v_res_1507_;
}
pub unsafe fn l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__1(
    mut v_val_1508_: *mut crate::leanh::LeanObject,
    mut v_w_1509_: *mut crate::leanh::LeanObject,
    mut v_lose_1510_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_finished_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_promise_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1516_: u8 = 0;
    let mut v___x_1517_: u8 = 0;
    let mut v___x_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1525_: u8 = 0;
    let mut v___x_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1531_: u8 = 0;
    let mut v_a_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1535_: u8 = 0;
    let mut v___x_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1541_: u8 = 0;
    let mut v___x_1542_: u8 = 0;
    let mut v___x_1543_: u8 = 0;
    let mut v___x_1544_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_finished_1512_ = crate::leanh::lean_ctor_get(v_w_1509_, 0);
                v_promise_1513_ = crate::leanh::lean_ctor_get(v_w_1509_, 1);
                v___x_1514_ = lean_st_ref_take(v_finished_1512_);
                v___x_1542_ = (crate::leanh::lean_unbox(v___x_1514_) as u8);
                crate::leanh::lean_dec(v___x_1514_);
                if v___x_1542_ == 0 {
                    v___x_1543_ = 1;
                    v___y_1516_ = v___x_1543_;
                    state = 1;
                    continue;
                } else {
                    v___x_1544_ = 0;
                    v___y_1516_ = v___x_1544_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1517_ = 1;
                v___x_1518_ = crate::leanh::lean_box((v___x_1517_) as usize);
                v___x_1519_ = lean_st_ref_set(v_finished_1512_, v___x_1518_);
                if v___y_1516_ == 0 {
                    crate::leanh::lean_dec_ref(v_val_1508_);
                    v___x_1520_ =
                        crate::leanh::lean_apply_1(v_lose_1510_, crate::leanh::lean_box(0));
                    return v___x_1520_;
                } else {
                    crate::leanh::lean_dec_ref(v_lose_1510_);
                    v___x_1521_ = l_IO_ofExcept___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__0___redArg(v_val_1508_);
                    if crate::leanh::lean_obj_tag(v___x_1521_) == 0 {
                        v_a_1522_ = crate::leanh::lean_ctor_get(v___x_1521_, 0);
                        v_isSharedCheck_1531_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1521_)) as u8;
                        if v_isSharedCheck_1531_ == 0 {
                            v___x_1524_ = v___x_1521_;
                            v_isShared_1525_ = v_isSharedCheck_1531_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1522_);
                            crate::leanh::lean_dec(v___x_1521_);
                            v___x_1524_ = crate::leanh::lean_box(0);
                            v_isShared_1525_ = v_isSharedCheck_1531_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_a_1532_ = crate::leanh::lean_ctor_get(v___x_1521_, 0);
                        v_isSharedCheck_1541_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1521_)) as u8;
                        if v_isSharedCheck_1541_ == 0 {
                            v___x_1534_ = v___x_1521_;
                            v_isShared_1535_ = v_isSharedCheck_1541_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1532_);
                            crate::leanh::lean_dec(v___x_1521_);
                            v___x_1534_ = crate::leanh::lean_box(0);
                            v_isShared_1535_ = v_isSharedCheck_1541_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                v___x_1526_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1526_, 0, v_a_1522_);
                v___x_1527_ = lean_io_promise_resolve(v___x_1526_, v_promise_1513_);
                if v_isShared_1525_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1524_, 0, v___x_1527_);
                    v___x_1529_ = v___x_1524_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1530_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1530_, 0, v___x_1527_);
                    v___x_1529_ = v_reuseFailAlloc_1530_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1529_;
            }
            4 => {
                v___x_1536_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1536_, 0, v_a_1532_);
                v___x_1537_ = lean_io_promise_resolve(v___x_1536_, v_promise_1513_);
                if v_isShared_1535_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1534_, 0);
                    crate::leanh::lean_ctor_set(v___x_1534_, 0, v___x_1537_);
                    v___x_1539_ = v___x_1534_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1540_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1540_, 0, v___x_1537_);
                    v___x_1539_ = v_reuseFailAlloc_1540_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1539_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__1___boxed(
    mut v_val_1545_: *mut crate::leanh::LeanObject,
    mut v_w_1546_: *mut crate::leanh::LeanObject,
    mut v_lose_1547_: *mut crate::leanh::LeanObject,
    mut v___y_1548_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1549_ =
        l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__1(
            v_val_1545_,
            v_w_1546_,
            v_lose_1547_,
        );
    crate::leanh::lean_dec_ref(v_w_1546_);
    return v_res_1549_;
}
pub unsafe fn l_Std_Async_TCP_Socket_Server_acceptSelector___lam__0(
    mut v_s_1550_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1564_: u8 = 0;
    let mut v_a_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1574_: u8 = 0;
    let mut v___x_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1578_: u8 = 0;
    let mut v_isSharedCheck_1579_: u8 = 0;
    let mut v_a_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1558_ = lean_uv_tcp_try_accept(v_s_1550_);
                if crate::leanh::lean_obj_tag(v___x_1558_) == 0 {
                    v_a_1559_ = crate::leanh::lean_ctor_get(v___x_1558_, 0);
                    crate::leanh::lean_inc(v_a_1559_);
                    crate::leanh::lean_dec_ref_known(v___x_1558_, 1);
                    v___x_1560_ = l_IO_ofExcept___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__0___redArg(v_a_1559_);
                    if crate::leanh::lean_obj_tag(v___x_1560_) == 0 {
                        v_a_1561_ = crate::leanh::lean_ctor_get(v___x_1560_, 0);
                        v_isSharedCheck_1579_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1560_)) as u8;
                        if v_isSharedCheck_1579_ == 0 {
                            v___x_1563_ = v___x_1560_;
                            v_isShared_1564_ = v_isSharedCheck_1579_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1561_);
                            crate::leanh::lean_dec(v___x_1560_);
                            v___x_1563_ = crate::leanh::lean_box(0);
                            v_isShared_1564_ = v_isSharedCheck_1579_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_1580_ = crate::leanh::lean_ctor_get(v___x_1560_, 0);
                        crate::leanh::lean_inc(v_a_1580_);
                        crate::leanh::lean_dec_ref_known(v___x_1560_, 1);
                        v_a_1556_ = v_a_1580_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_1581_ = crate::leanh::lean_ctor_get(v___x_1558_, 0);
                    crate::leanh::lean_inc(v_a_1581_);
                    crate::leanh::lean_dec_ref_known(v___x_1558_, 1);
                    v_a_1556_ = v_a_1581_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_1554_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1554_, 0, v_val_1553_);
                return v___x_1554_;
            }
            2 => {
                v___x_1557_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1557_, 0, v_a_1556_);
                v_val_1553_ = v___x_1557_;
                state = 1;
                continue;
            }
            3 => {
                if crate::leanh::lean_obj_tag(v_a_1561_) == 0 {
                    v___x_1570_ = crate::leanh::lean_box(0);
                    v_a_1566_ = v___x_1570_;
                    state = 4;
                    continue;
                } else {
                    v_val_1571_ = crate::leanh::lean_ctor_get(v_a_1561_, 0);
                    v_isSharedCheck_1578_ = (!crate::leanh::lean_is_exclusive(v_a_1561_)) as u8;
                    if v_isSharedCheck_1578_ == 0 {
                        v___x_1573_ = v_a_1561_;
                        v_isShared_1574_ = v_isSharedCheck_1578_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1571_);
                        crate::leanh::lean_dec(v_a_1561_);
                        v___x_1573_ = crate::leanh::lean_box(0);
                        v_isShared_1574_ = v_isSharedCheck_1578_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_1564_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1563_, 1);
                    crate::leanh::lean_ctor_set(v___x_1563_, 0, v_a_1566_);
                    v___x_1568_ = v___x_1563_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1569_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1569_, 0, v_a_1566_);
                    v___x_1568_ = v_reuseFailAlloc_1569_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_val_1553_ = v___x_1568_;
                state = 1;
                continue;
            }
            6 => {
                if v_isShared_1574_ == 0 {
                    v___x_1576_ = v___x_1573_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1577_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1577_, 0, v_val_1571_);
                    v___x_1576_ = v_reuseFailAlloc_1577_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v_a_1566_ = v___x_1576_;
                state = 4;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_TCP_Socket_Server_acceptSelector___lam__0___boxed(
    mut v_s_1582_: *mut crate::leanh::LeanObject,
    mut v___y_1583_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1584_ = l_Std_Async_TCP_Socket_Server_acceptSelector___lam__0(v_s_1582_);
    crate::leanh::lean_dec(v_s_1582_);
    return v_res_1584_;
}
pub unsafe fn l_Std_Async_TCP_Socket_Server_acceptSelector___lam__1(
    mut v___x_1585_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1587_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1587_, 0, v___x_1585_);
    return v___x_1587_;
}
pub unsafe fn l_Std_Async_TCP_Socket_Server_acceptSelector___lam__1___boxed(
    mut v___x_1588_: *mut crate::leanh::LeanObject,
    mut v___y_1589_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1590_ = l_Std_Async_TCP_Socket_Server_acceptSelector___lam__1(v___x_1588_);
    return v_res_1590_;
}
pub unsafe fn l_Std_Async_TCP_Socket_Server_acceptSelector___lam__2(
    mut v_waiter_1593_: *mut crate::leanh::LeanObject,
    mut v_res_1594_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_res_1594_) == 0 {
        let mut v___x_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1596_ = crate::leanh::lean_box(0);
        v___x_1597_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1597_, 0, v___x_1596_);
        return v___x_1597_;
    } else {
        let mut v_val_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_1598_ = crate::leanh::lean_ctor_get(v_res_1594_, 0);
        crate::leanh::lean_inc(v_val_1598_);
        crate::leanh::lean_dec_ref_known(v_res_1594_, 1);
        v___f_1599_ = l_Std_Async_TCP_Socket_Server_acceptSelector___lam__2___closed__0;
        v___x_1600_ =
            l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__1(
                v_val_1598_,
                v_waiter_1593_,
                v___f_1599_,
            );
        return v___x_1600_;
    }
}
pub unsafe fn l_Std_Async_TCP_Socket_Server_acceptSelector___lam__2___boxed(
    mut v_waiter_1601_: *mut crate::leanh::LeanObject,
    mut v_res_1602_: *mut crate::leanh::LeanObject,
    mut v___y_1603_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1604_ =
        l_Std_Async_TCP_Socket_Server_acceptSelector___lam__2(v_waiter_1601_, v_res_1602_);
    crate::leanh::lean_dec_ref(v_waiter_1601_);
    return v_res_1604_;
}
pub unsafe fn l_Std_Async_TCP_Socket_Server_acceptSelector___lam__3(
    mut v___f_1605_: *mut crate::leanh::LeanObject,
    mut v_x_1606_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1614_: u8 = 0;
    let mut v___x_1616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1619_: u8 = 0;
    let mut v_a_1620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1623_: u8 = 0;
    let mut v___x_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1626_: u8 = 0;
    let mut v___x_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1636_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1606_) == 0 {
                    crate::leanh::lean_dec_ref(v___f_1605_);
                    v_a_1611_ = crate::leanh::lean_ctor_get(v_x_1606_, 0);
                    v_isSharedCheck_1619_ = (!crate::leanh::lean_is_exclusive(v_x_1606_)) as u8;
                    if v_isSharedCheck_1619_ == 0 {
                        v___x_1613_ = v_x_1606_;
                        v_isShared_1614_ = v_isSharedCheck_1619_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1611_);
                        crate::leanh::lean_dec(v_x_1606_);
                        v___x_1613_ = crate::leanh::lean_box(0);
                        v_isShared_1614_ = v_isSharedCheck_1619_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_1620_ = crate::leanh::lean_ctor_get(v_x_1606_, 0);
                    v_isSharedCheck_1636_ = (!crate::leanh::lean_is_exclusive(v_x_1606_)) as u8;
                    if v_isSharedCheck_1636_ == 0 {
                        v___x_1622_ = v_x_1606_;
                        v_isShared_1623_ = v_isSharedCheck_1636_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1620_);
                        crate::leanh::lean_dec(v_x_1606_);
                        v___x_1622_ = crate::leanh::lean_box(0);
                        v_isShared_1623_ = v_isSharedCheck_1636_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1610_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1610_, 0, v_val_1609_);
                return v___x_1610_;
            }
            2 => {
                if v_isShared_1614_ == 0 {
                    v___x_1616_ = v___x_1613_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1618_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1618_, 0, v_a_1611_);
                    v___x_1616_ = v_reuseFailAlloc_1618_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1617_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1617_, 0, v___x_1616_);
                return v___x_1617_;
            }
            4 => {
                v___x_1624_ = lean_io_promise_result_opt(v_a_1620_);
                crate::leanh::lean_dec(v_a_1620_);
                v___x_1625_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1626_ = 0;
                v___x_1627_ =
                    l_EIO_chainTask___redArg(v___x_1624_, v___f_1605_, v___x_1625_, v___x_1626_);
                if crate::leanh::lean_obj_tag(v___x_1627_) == 0 {
                    v_a_1628_ = crate::leanh::lean_ctor_get(v___x_1627_, 0);
                    crate::leanh::lean_inc(v_a_1628_);
                    crate::leanh::lean_dec_ref_known(v___x_1627_, 1);
                    if v_isShared_1623_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1622_, 0, v_a_1628_);
                        v___x_1630_ = v___x_1622_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1631_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1631_, 0, v_a_1628_);
                        v___x_1630_ = v_reuseFailAlloc_1631_;
                        state = 5;
                        continue;
                    }
                } else {
                    v_a_1632_ = crate::leanh::lean_ctor_get(v___x_1627_, 0);
                    crate::leanh::lean_inc(v_a_1632_);
                    crate::leanh::lean_dec_ref_known(v___x_1627_, 1);
                    if v_isShared_1623_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_1622_, 0);
                        crate::leanh::lean_ctor_set(v___x_1622_, 0, v_a_1632_);
                        v___x_1634_ = v___x_1622_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1635_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1635_, 0, v_a_1632_);
                        v___x_1634_ = v_reuseFailAlloc_1635_;
                        state = 6;
                        continue;
                    }
                }
            }
            5 => {
                v_val_1609_ = v___x_1630_;
                state = 1;
                continue;
            }
            6 => {
                v_val_1609_ = v___x_1634_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_TCP_Socket_Server_acceptSelector___lam__3___boxed(
    mut v___f_1637_: *mut crate::leanh::LeanObject,
    mut v_x_1638_: *mut crate::leanh::LeanObject,
    mut v___y_1639_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1640_ = l_Std_Async_TCP_Socket_Server_acceptSelector___lam__3(v___f_1637_, v_x_1638_);
    return v_res_1640_;
}
pub unsafe fn l_Std_Async_TCP_Socket_Server_acceptSelector___lam__4(
    mut v_s_1641_: *mut crate::leanh::LeanObject,
    mut v_waiter_1642_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: u8 = 0;
    let mut v___x_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1656_: u8 = 0;
    let mut v___x_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1660_: u8 = 0;
    let mut v_a_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1664_: u8 = 0;
    let mut v___x_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1668_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1644_ = crate::leanh::lean_alloc_closure(
                    l_Std_Async_TCP_Socket_Server_acceptSelector___lam__2___boxed
                        as *mut core::ffi::c_void,
                    3,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1644_, 0, v_waiter_1642_);
                v___f_1645_ = crate::leanh::lean_alloc_closure(
                    l_Std_Async_TCP_Socket_Server_acceptSelector___lam__3___boxed
                        as *mut core::ffi::c_void,
                    3,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1645_, 0, v___f_1644_);
                v___x_1652_ = lean_uv_tcp_accept(v_s_1641_);
                if crate::leanh::lean_obj_tag(v___x_1652_) == 0 {
                    v_a_1653_ = crate::leanh::lean_ctor_get(v___x_1652_, 0);
                    v_isSharedCheck_1660_ = (!crate::leanh::lean_is_exclusive(v___x_1652_)) as u8;
                    if v_isSharedCheck_1660_ == 0 {
                        v___x_1655_ = v___x_1652_;
                        v_isShared_1656_ = v_isSharedCheck_1660_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1653_);
                        crate::leanh::lean_dec(v___x_1652_);
                        v___x_1655_ = crate::leanh::lean_box(0);
                        v_isShared_1656_ = v_isSharedCheck_1660_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_1661_ = crate::leanh::lean_ctor_get(v___x_1652_, 0);
                    v_isSharedCheck_1668_ = (!crate::leanh::lean_is_exclusive(v___x_1652_)) as u8;
                    if v_isSharedCheck_1668_ == 0 {
                        v___x_1663_ = v___x_1652_;
                        v_isShared_1664_ = v_isSharedCheck_1668_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1661_);
                        crate::leanh::lean_dec(v___x_1652_);
                        v___x_1663_ = crate::leanh::lean_box(0);
                        v_isShared_1664_ = v_isSharedCheck_1668_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1648_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1648_, 0, v_val_1647_);
                v___x_1649_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1650_ = 0;
                v___x_1651_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_1649_,
                    v___x_1650_,
                    v___x_1648_,
                    v___f_1645_,
                );
                return v___x_1651_;
            }
            2 => {
                if v_isShared_1656_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1655_, 1);
                    v___x_1658_ = v___x_1655_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1659_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1659_, 0, v_a_1653_);
                    v___x_1658_ = v_reuseFailAlloc_1659_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_val_1647_ = v___x_1658_;
                state = 1;
                continue;
            }
            4 => {
                if v_isShared_1664_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1663_, 0);
                    v___x_1666_ = v___x_1663_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1667_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1667_, 0, v_a_1661_);
                    v___x_1666_ = v_reuseFailAlloc_1667_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_val_1647_ = v___x_1666_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_TCP_Socket_Server_acceptSelector___lam__4___boxed(
    mut v_s_1669_: *mut crate::leanh::LeanObject,
    mut v_waiter_1670_: *mut crate::leanh::LeanObject,
    mut v___y_1671_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1672_ = l_Std_Async_TCP_Socket_Server_acceptSelector___lam__4(v_s_1669_, v_waiter_1670_);
    crate::leanh::lean_dec(v_s_1669_);
    return v_res_1672_;
}
pub unsafe fn l_Std_Async_TCP_Socket_Server_acceptSelector___lam__5(
    mut v_s_1673_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1682_: u8 = 0;
    let mut v___x_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1686_: u8 = 0;
    let mut v_a_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1690_: u8 = 0;
    let mut v___x_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1694_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1678_ = lean_uv_tcp_cancel_accept(v_s_1673_);
                if crate::leanh::lean_obj_tag(v___x_1678_) == 0 {
                    v_a_1679_ = crate::leanh::lean_ctor_get(v___x_1678_, 0);
                    v_isSharedCheck_1686_ = (!crate::leanh::lean_is_exclusive(v___x_1678_)) as u8;
                    if v_isSharedCheck_1686_ == 0 {
                        v___x_1681_ = v___x_1678_;
                        v_isShared_1682_ = v_isSharedCheck_1686_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1679_);
                        crate::leanh::lean_dec(v___x_1678_);
                        v___x_1681_ = crate::leanh::lean_box(0);
                        v_isShared_1682_ = v_isSharedCheck_1686_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_1687_ = crate::leanh::lean_ctor_get(v___x_1678_, 0);
                    v_isSharedCheck_1694_ = (!crate::leanh::lean_is_exclusive(v___x_1678_)) as u8;
                    if v_isSharedCheck_1694_ == 0 {
                        v___x_1689_ = v___x_1678_;
                        v_isShared_1690_ = v_isSharedCheck_1694_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1687_);
                        crate::leanh::lean_dec(v___x_1678_);
                        v___x_1689_ = crate::leanh::lean_box(0);
                        v_isShared_1690_ = v_isSharedCheck_1694_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1677_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1677_, 0, v_val_1676_);
                return v___x_1677_;
            }
            2 => {
                if v_isShared_1682_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1681_, 1);
                    v___x_1684_ = v___x_1681_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1685_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1685_, 0, v_a_1679_);
                    v___x_1684_ = v_reuseFailAlloc_1685_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_val_1676_ = v___x_1684_;
                state = 1;
                continue;
            }
            4 => {
                if v_isShared_1690_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1689_, 0);
                    v___x_1692_ = v___x_1689_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1693_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1693_, 0, v_a_1687_);
                    v___x_1692_ = v_reuseFailAlloc_1693_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_val_1676_ = v___x_1692_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_TCP_Socket_Server_acceptSelector___lam__5___boxed(
    mut v_s_1695_: *mut crate::leanh::LeanObject,
    mut v___y_1696_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1697_ = l_Std_Async_TCP_Socket_Server_acceptSelector___lam__5(v_s_1695_);
    crate::leanh::lean_dec(v_s_1695_);
    return v_res_1697_;
}
pub unsafe fn l_Std_Async_TCP_Socket_Server_acceptSelector(
    mut v_s_1698_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_n(v_s_1698_, 2);
    v___f_1699_ = crate::leanh::lean_alloc_closure(
        l_Std_Async_TCP_Socket_Server_acceptSelector___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1699_, 0, v_s_1698_);
    v___f_1700_ = crate::leanh::lean_alloc_closure(
        l_Std_Async_TCP_Socket_Server_acceptSelector___lam__4___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1700_, 0, v_s_1698_);
    v___f_1701_ = crate::leanh::lean_alloc_closure(
        l_Std_Async_TCP_Socket_Server_acceptSelector___lam__5___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1701_, 0, v_s_1698_);
    v___x_1702_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1702_, 0, v___f_1699_);
    crate::leanh::lean_ctor_set(v___x_1702_, 1, v___f_1700_);
    crate::leanh::lean_ctor_set(v___x_1702_, 2, v___f_1701_);
    return v___x_1702_;
}
pub unsafe fn l_Std_Async_TCP_Socket_Server_getSockName(
    mut v_s_1703_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1705_ = lean_uv_tcp_getsockname(v_s_1703_);
    return v___x_1705_;
}
pub unsafe fn l_Std_Async_TCP_Socket_Server_getSockName___boxed(
    mut v_s_1706_: *mut crate::leanh::LeanObject,
    mut v_a_1707_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1708_ = l_Std_Async_TCP_Socket_Server_getSockName(v_s_1706_);
    crate::leanh::lean_dec(v_s_1706_);
    return v_res_1708_;
}
pub unsafe fn l_Std_Async_TCP_Socket_Server_noDelay(
    mut v_s_1709_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1711_ = lean_uv_tcp_nodelay(v_s_1709_);
    return v___x_1711_;
}
pub unsafe fn l_Std_Async_TCP_Socket_Server_noDelay___boxed(
    mut v_s_1712_: *mut crate::leanh::LeanObject,
    mut v_a_1713_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1714_ = l_Std_Async_TCP_Socket_Server_noDelay(v_s_1712_);
    crate::leanh::lean_dec(v_s_1712_);
    return v_res_1714_;
}
pub unsafe fn _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1741_ = l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__10;
    v___x_1742_ = l_Lean_mkAtom(v___x_1741_);
    return v___x_1742_;
}
pub unsafe fn _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1743_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__12),
        core::ptr::addr_of_mut!(
            l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__12_once
        ),
        _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__12,
    );
    v___x_1744_ = l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__5;
    v___x_1745_ = lean_array_push(v___x_1744_, v___x_1743_);
    return v___x_1745_;
}
pub unsafe fn _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1756_ = l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__16;
    v___x_1757_ = l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__5;
    v___x_1758_ = lean_array_push(v___x_1757_, v___x_1756_);
    return v___x_1758_;
}
pub unsafe fn _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__18()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1759_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__17),
        core::ptr::addr_of_mut!(
            l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__17_once
        ),
        _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__17,
    );
    v___x_1760_ = l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__15;
    v___x_1761_ = crate::leanh::lean_box(2);
    v___x_1762_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1762_, 0, v___x_1761_);
    crate::leanh::lean_ctor_set(v___x_1762_, 1, v___x_1760_);
    crate::leanh::lean_ctor_set(v___x_1762_, 2, v___x_1759_);
    return v___x_1762_;
}
pub unsafe fn _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1763_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__18),
        core::ptr::addr_of_mut!(
            l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__18_once
        ),
        _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__18,
    );
    v___x_1764_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__13),
        core::ptr::addr_of_mut!(
            l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__13_once
        ),
        _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__13,
    );
    v___x_1765_ = lean_array_push(v___x_1764_, v___x_1763_);
    return v___x_1765_;
}
pub unsafe fn _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__20()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1766_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__19),
        core::ptr::addr_of_mut!(
            l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__19_once
        ),
        _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__19,
    );
    v___x_1767_ = l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__11;
    v___x_1768_ = crate::leanh::lean_box(2);
    v___x_1769_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1769_, 0, v___x_1768_);
    crate::leanh::lean_ctor_set(v___x_1769_, 1, v___x_1767_);
    crate::leanh::lean_ctor_set(v___x_1769_, 2, v___x_1766_);
    return v___x_1769_;
}
pub unsafe fn _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__21()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1770_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__20),
        core::ptr::addr_of_mut!(
            l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__20_once
        ),
        _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__20,
    );
    v___x_1771_ = l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__5;
    v___x_1772_ = lean_array_push(v___x_1771_, v___x_1770_);
    return v___x_1772_;
}
pub unsafe fn _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__22()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1773_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__21),
        core::ptr::addr_of_mut!(
            l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__21_once
        ),
        _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__21,
    );
    v___x_1774_ = l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__9;
    v___x_1775_ = crate::leanh::lean_box(2);
    v___x_1776_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1776_, 0, v___x_1775_);
    crate::leanh::lean_ctor_set(v___x_1776_, 1, v___x_1774_);
    crate::leanh::lean_ctor_set(v___x_1776_, 2, v___x_1773_);
    return v___x_1776_;
}
pub unsafe fn _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__23()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1777_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__22),
        core::ptr::addr_of_mut!(
            l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__22_once
        ),
        _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__22,
    );
    v___x_1778_ = l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__5;
    v___x_1779_ = lean_array_push(v___x_1778_, v___x_1777_);
    return v___x_1779_;
}
pub unsafe fn _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__24()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1780_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__23),
        core::ptr::addr_of_mut!(
            l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__23_once
        ),
        _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__23,
    );
    v___x_1781_ = l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__7;
    v___x_1782_ = crate::leanh::lean_box(2);
    v___x_1783_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1783_, 0, v___x_1782_);
    crate::leanh::lean_ctor_set(v___x_1783_, 1, v___x_1781_);
    crate::leanh::lean_ctor_set(v___x_1783_, 2, v___x_1780_);
    return v___x_1783_;
}
pub unsafe fn _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__25()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1784_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__24),
        core::ptr::addr_of_mut!(
            l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__24_once
        ),
        _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__24,
    );
    v___x_1785_ = l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__5;
    v___x_1786_ = lean_array_push(v___x_1785_, v___x_1784_);
    return v___x_1786_;
}
pub unsafe fn _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__26()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1787_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__25),
        core::ptr::addr_of_mut!(
            l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__25_once
        ),
        _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__25,
    );
    v___x_1788_ = l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__4;
    v___x_1789_ = crate::leanh::lean_box(2);
    v___x_1790_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1790_, 0, v___x_1789_);
    crate::leanh::lean_ctor_set(v___x_1790_, 1, v___x_1788_);
    crate::leanh::lean_ctor_set(v___x_1790_, 2, v___x_1787_);
    return v___x_1790_;
}
pub unsafe fn _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1791_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__26),
        core::ptr::addr_of_mut!(
            l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__26_once
        ),
        _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__26,
    );
    return v___x_1791_;
}
pub unsafe fn l_Std_Async_TCP_Socket_Server_keepAlive___redArg(
    mut v_s_1792_: *mut crate::leanh::LeanObject,
    mut v_enable_1793_: u8,
    mut v_delay_1794_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1796_: u8 = 0;
    let mut v___x_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: u32 = 0;
    let mut v___x_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1796_ = lean_bool_to_int8(v_enable_1793_);
    v___x_1797_ = l_Int_toNat(v_delay_1794_);
    v___x_1798_ = lean_uint32_of_nat(v___x_1797_);
    crate::leanh::lean_dec(v___x_1797_);
    v___x_1799_ = lean_uv_tcp_keepalive(v_s_1792_, v___x_1796_, v___x_1798_);
    return v___x_1799_;
}
pub unsafe fn l_Std_Async_TCP_Socket_Server_keepAlive___redArg___boxed(
    mut v_s_1800_: *mut crate::leanh::LeanObject,
    mut v_enable_1801_: *mut crate::leanh::LeanObject,
    mut v_delay_1802_: *mut crate::leanh::LeanObject,
    mut v_a_1803_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_enable_boxed_1804_: u8 = 0;
    let mut v_res_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_enable_boxed_1804_ = (crate::leanh::lean_unbox(v_enable_1801_) as u8);
    v_res_1805_ = l_Std_Async_TCP_Socket_Server_keepAlive___redArg(
        v_s_1800_,
        v_enable_boxed_1804_,
        v_delay_1802_,
    );
    crate::leanh::lean_dec(v_delay_1802_);
    crate::leanh::lean_dec(v_s_1800_);
    return v_res_1805_;
}
pub unsafe fn l_Std_Async_TCP_Socket_Server_keepAlive(
    mut v_s_1806_: *mut crate::leanh::LeanObject,
    mut v_enable_1807_: u8,
    mut v_delay_1808_: *mut crate::leanh::LeanObject,
    mut v_x_1809_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1811_: u8 = 0;
    let mut v___x_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: u32 = 0;
    let mut v___x_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1811_ = lean_bool_to_int8(v_enable_1807_);
    v___x_1812_ = l_Int_toNat(v_delay_1808_);
    v___x_1813_ = lean_uint32_of_nat(v___x_1812_);
    crate::leanh::lean_dec(v___x_1812_);
    v___x_1814_ = lean_uv_tcp_keepalive(v_s_1806_, v___x_1811_, v___x_1813_);
    return v___x_1814_;
}
pub unsafe fn l_Std_Async_TCP_Socket_Server_keepAlive___boxed(
    mut v_s_1815_: *mut crate::leanh::LeanObject,
    mut v_enable_1816_: *mut crate::leanh::LeanObject,
    mut v_delay_1817_: *mut crate::leanh::LeanObject,
    mut v_x_1818_: *mut crate::leanh::LeanObject,
    mut v_a_1819_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_enable_boxed_1820_: u8 = 0;
    let mut v_res_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_enable_boxed_1820_ = (crate::leanh::lean_unbox(v_enable_1816_) as u8);
    v_res_1821_ = l_Std_Async_TCP_Socket_Server_keepAlive(
        v_s_1815_,
        v_enable_boxed_1820_,
        v_delay_1817_,
        v_x_1818_,
    );
    crate::leanh::lean_dec(v_delay_1817_);
    crate::leanh::lean_dec(v_s_1815_);
    return v_res_1821_;
}
pub unsafe fn l_Std_Async_TCP_Socket_Client_mk() -> *mut crate::leanh::LeanObject {
    let mut v___x_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1827_: u8 = 0;
    let mut v___x_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1831_: u8 = 0;
    let mut v_a_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1835_: u8 = 0;
    let mut v___x_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1839_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1823_ = lean_uv_tcp_new();
                if crate::leanh::lean_obj_tag(v___x_1823_) == 0 {
                    v_a_1824_ = crate::leanh::lean_ctor_get(v___x_1823_, 0);
                    v_isSharedCheck_1831_ = (!crate::leanh::lean_is_exclusive(v___x_1823_)) as u8;
                    if v_isSharedCheck_1831_ == 0 {
                        v___x_1826_ = v___x_1823_;
                        v_isShared_1827_ = v_isSharedCheck_1831_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1824_);
                        crate::leanh::lean_dec(v___x_1823_);
                        v___x_1826_ = crate::leanh::lean_box(0);
                        v_isShared_1827_ = v_isSharedCheck_1831_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1832_ = crate::leanh::lean_ctor_get(v___x_1823_, 0);
                    v_isSharedCheck_1839_ = (!crate::leanh::lean_is_exclusive(v___x_1823_)) as u8;
                    if v_isSharedCheck_1839_ == 0 {
                        v___x_1834_ = v___x_1823_;
                        v_isShared_1835_ = v_isSharedCheck_1839_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1832_);
                        crate::leanh::lean_dec(v___x_1823_);
                        v___x_1834_ = crate::leanh::lean_box(0);
                        v_isShared_1835_ = v_isSharedCheck_1839_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1827_ == 0 {
                    v___x_1829_ = v___x_1826_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1830_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_a_1824_);
                    v___x_1829_ = v_reuseFailAlloc_1830_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1829_;
            }
            3 => {
                if v_isShared_1835_ == 0 {
                    v___x_1837_ = v___x_1834_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1838_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1838_, 0, v_a_1832_);
                    v___x_1837_ = v_reuseFailAlloc_1838_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1837_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_TCP_Socket_Client_mk___boxed(
    mut v_a_1840_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1841_ = l_Std_Async_TCP_Socket_Client_mk();
    return v_res_1841_;
}
pub unsafe fn l_Std_Async_TCP_Socket_Client_bind(
    mut v_s_1842_: *mut crate::leanh::LeanObject,
    mut v_addr_1843_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1845_ = lean_uv_tcp_bind(v_s_1842_, v_addr_1843_);
    return v___x_1845_;
}
pub unsafe fn l_Std_Async_TCP_Socket_Client_bind___boxed(
    mut v_s_1846_: *mut crate::leanh::LeanObject,
    mut v_addr_1847_: *mut crate::leanh::LeanObject,
    mut v_a_1848_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1849_ = l_Std_Async_TCP_Socket_Client_bind(v_s_1846_, v_addr_1847_);
    crate::leanh::lean_dec_ref(v_addr_1847_);
    crate::leanh::lean_dec(v_s_1846_);
    return v_res_1849_;
}
pub unsafe fn l_Std_Async_TCP_Socket_Client_connect___lam__0(
    mut v___x_1850_: *mut crate::leanh::LeanObject,
    mut v_x_1851_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1851_) == 0 {
        let mut v___x_1852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1852_ = lean_mk_io_user_error(v___x_1850_);
        v___x_1853_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1853_, 0, v___x_1852_);
        return v___x_1853_;
    } else {
        let mut v_val_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v___x_1850_);
        v_val_1854_ = crate::leanh::lean_ctor_get(v_x_1851_, 0);
        crate::leanh::lean_inc(v_val_1854_);
        return v_val_1854_;
    }
}
pub unsafe fn l_Std_Async_TCP_Socket_Client_connect___lam__0___boxed(
    mut v___x_1855_: *mut crate::leanh::LeanObject,
    mut v_x_1856_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1857_ = l_Std_Async_TCP_Socket_Client_connect___lam__0(v___x_1855_, v_x_1856_);
    crate::leanh::lean_dec(v_x_1856_);
    return v_res_1857_;
}
pub unsafe fn l_Std_Async_TCP_Socket_Client_connect___lam__1(
    mut v___f_1858_: *mut crate::leanh::LeanObject,
    mut v_x_1859_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1864_: u8 = 0;
    let mut v___x_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1869_: u8 = 0;
    let mut v_a_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1874_: u8 = 0;
    let mut v___x_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1879_: u8 = 0;
    let mut v_a_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: u8 = 0;
    let mut v___x_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1859_) == 0 {
                    crate::leanh::lean_dec_ref(v___f_1858_);
                    v_a_1861_ = crate::leanh::lean_ctor_get(v_x_1859_, 0);
                    v_isSharedCheck_1869_ = (!crate::leanh::lean_is_exclusive(v_x_1859_)) as u8;
                    if v_isSharedCheck_1869_ == 0 {
                        v___x_1863_ = v_x_1859_;
                        v_isShared_1864_ = v_isSharedCheck_1869_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1861_);
                        crate::leanh::lean_dec(v_x_1859_);
                        v___x_1863_ = crate::leanh::lean_box(0);
                        v_isShared_1864_ = v_isSharedCheck_1869_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1870_ = crate::leanh::lean_ctor_get(v_x_1859_, 0);
                    crate::leanh::lean_inc(v_a_1870_);
                    crate::leanh::lean_dec_ref_known(v_x_1859_, 1);
                    if crate::leanh::lean_obj_tag(v_a_1870_) == 0 {
                        crate::leanh::lean_dec_ref(v___f_1858_);
                        v_a_1871_ = crate::leanh::lean_ctor_get(v_a_1870_, 0);
                        v_isSharedCheck_1879_ = (!crate::leanh::lean_is_exclusive(v_a_1870_)) as u8;
                        if v_isSharedCheck_1879_ == 0 {
                            v___x_1873_ = v_a_1870_;
                            v_isShared_1874_ = v_isSharedCheck_1879_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1871_);
                            crate::leanh::lean_dec(v_a_1870_);
                            v___x_1873_ = crate::leanh::lean_box(0);
                            v_isShared_1874_ = v_isSharedCheck_1879_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_1880_ = crate::leanh::lean_ctor_get(v_a_1870_, 0);
                        crate::leanh::lean_inc(v_a_1880_);
                        crate::leanh::lean_dec_ref_known(v_a_1870_, 1);
                        v___x_1881_ = lean_io_promise_result_opt(v_a_1880_);
                        crate::leanh::lean_dec(v_a_1880_);
                        v___x_1882_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_1883_ = 0;
                        v___x_1884_ =
                            lean_task_map(v___f_1858_, v___x_1881_, v___x_1882_, v___x_1883_);
                        v___x_1885_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1885_, 0, v___x_1884_);
                        return v___x_1885_;
                    }
                }
            }
            1 => {
                if v_isShared_1864_ == 0 {
                    v___x_1866_ = v___x_1863_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1868_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1868_, 0, v_a_1861_);
                    v___x_1866_ = v_reuseFailAlloc_1868_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1867_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1867_, 0, v___x_1866_);
                return v___x_1867_;
            }
            3 => {
                if v_isShared_1874_ == 0 {
                    v___x_1876_ = v___x_1873_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1878_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1878_, 0, v_a_1871_);
                    v___x_1876_ = v_reuseFailAlloc_1878_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1877_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1877_, 0, v___x_1876_);
                return v___x_1877_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_TCP_Socket_Client_connect___lam__1___boxed(
    mut v___f_1886_: *mut crate::leanh::LeanObject,
    mut v_x_1887_: *mut crate::leanh::LeanObject,
    mut v___y_1888_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1889_ = l_Std_Async_TCP_Socket_Client_connect___lam__1(v___f_1886_, v_x_1887_);
    return v_res_1889_;
}
pub unsafe fn l_Std_Async_TCP_Socket_Client_connect(
    mut v_s_1894_: *mut crate::leanh::LeanObject,
    mut v_addr_1895_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: u8 = 0;
    let mut v___x_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1909_: u8 = 0;
    let mut v___x_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1913_: u8 = 0;
    let mut v_a_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1917_: u8 = 0;
    let mut v___x_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1921_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1897_ = l_Std_Async_TCP_Socket_Client_connect___closed__1;
                v___x_1905_ = lean_uv_tcp_connect(v_s_1894_, v_addr_1895_);
                if crate::leanh::lean_obj_tag(v___x_1905_) == 0 {
                    v_a_1906_ = crate::leanh::lean_ctor_get(v___x_1905_, 0);
                    v_isSharedCheck_1913_ = (!crate::leanh::lean_is_exclusive(v___x_1905_)) as u8;
                    if v_isSharedCheck_1913_ == 0 {
                        v___x_1908_ = v___x_1905_;
                        v_isShared_1909_ = v_isSharedCheck_1913_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1906_);
                        crate::leanh::lean_dec(v___x_1905_);
                        v___x_1908_ = crate::leanh::lean_box(0);
                        v_isShared_1909_ = v_isSharedCheck_1913_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_1914_ = crate::leanh::lean_ctor_get(v___x_1905_, 0);
                    v_isSharedCheck_1921_ = (!crate::leanh::lean_is_exclusive(v___x_1905_)) as u8;
                    if v_isSharedCheck_1921_ == 0 {
                        v___x_1916_ = v___x_1905_;
                        v_isShared_1917_ = v_isSharedCheck_1921_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1914_);
                        crate::leanh::lean_dec(v___x_1905_);
                        v___x_1916_ = crate::leanh::lean_box(0);
                        v_isShared_1917_ = v_isSharedCheck_1921_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1900_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1900_, 0, v_val_1899_);
                v___x_1901_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1901_, 0, v___x_1900_);
                v___x_1902_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1903_ = 0;
                v___x_1904_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_1902_,
                    v___x_1903_,
                    v___x_1901_,
                    v___f_1897_,
                );
                return v___x_1904_;
            }
            2 => {
                if v_isShared_1909_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1908_, 1);
                    v___x_1911_ = v___x_1908_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1912_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1912_, 0, v_a_1906_);
                    v___x_1911_ = v_reuseFailAlloc_1912_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_val_1899_ = v___x_1911_;
                state = 1;
                continue;
            }
            4 => {
                if v_isShared_1917_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1916_, 0);
                    v___x_1919_ = v___x_1916_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1920_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1920_, 0, v_a_1914_);
                    v___x_1919_ = v_reuseFailAlloc_1920_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_val_1899_ = v___x_1919_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_TCP_Socket_Client_connect___boxed(
    mut v_s_1922_: *mut crate::leanh::LeanObject,
    mut v_addr_1923_: *mut crate::leanh::LeanObject,
    mut v_a_1924_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1925_ = l_Std_Async_TCP_Socket_Client_connect(v_s_1922_, v_addr_1923_);
    crate::leanh::lean_dec_ref(v_addr_1923_);
    crate::leanh::lean_dec(v_s_1922_);
    return v_res_1925_;
}
pub unsafe fn l_Std_Async_TCP_Socket_Client_sendAll(
    mut v_s_1926_: *mut crate::leanh::LeanObject,
    mut v_data_1927_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1935_: u8 = 0;
    let mut v___x_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1941_: u8 = 0;
    let mut v___x_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1945_: u8 = 0;
    let mut v_a_1946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1949_: u8 = 0;
    let mut v___x_1951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1953_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1929_ = l_Std_Async_TCP_Socket_Client_connect___closed__1;
                v___x_1937_ = lean_uv_tcp_send(v_s_1926_, v_data_1927_);
                if crate::leanh::lean_obj_tag(v___x_1937_) == 0 {
                    v_a_1938_ = crate::leanh::lean_ctor_get(v___x_1937_, 0);
                    v_isSharedCheck_1945_ = (!crate::leanh::lean_is_exclusive(v___x_1937_)) as u8;
                    if v_isSharedCheck_1945_ == 0 {
                        v___x_1940_ = v___x_1937_;
                        v_isShared_1941_ = v_isSharedCheck_1945_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1938_);
                        crate::leanh::lean_dec(v___x_1937_);
                        v___x_1940_ = crate::leanh::lean_box(0);
                        v_isShared_1941_ = v_isSharedCheck_1945_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_1946_ = crate::leanh::lean_ctor_get(v___x_1937_, 0);
                    v_isSharedCheck_1953_ = (!crate::leanh::lean_is_exclusive(v___x_1937_)) as u8;
                    if v_isSharedCheck_1953_ == 0 {
                        v___x_1948_ = v___x_1937_;
                        v_isShared_1949_ = v_isSharedCheck_1953_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1946_);
                        crate::leanh::lean_dec(v___x_1937_);
                        v___x_1948_ = crate::leanh::lean_box(0);
                        v_isShared_1949_ = v_isSharedCheck_1953_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1932_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1932_, 0, v_val_1931_);
                v___x_1933_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1933_, 0, v___x_1932_);
                v___x_1934_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1935_ = 0;
                v___x_1936_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_1934_,
                    v___x_1935_,
                    v___x_1933_,
                    v___f_1929_,
                );
                return v___x_1936_;
            }
            2 => {
                if v_isShared_1941_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1940_, 1);
                    v___x_1943_ = v___x_1940_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1944_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1944_, 0, v_a_1938_);
                    v___x_1943_ = v_reuseFailAlloc_1944_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_val_1931_ = v___x_1943_;
                state = 1;
                continue;
            }
            4 => {
                if v_isShared_1949_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1948_, 0);
                    v___x_1951_ = v___x_1948_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1952_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1952_, 0, v_a_1946_);
                    v___x_1951_ = v_reuseFailAlloc_1952_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_val_1931_ = v___x_1951_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_TCP_Socket_Client_sendAll___boxed(
    mut v_s_1954_: *mut crate::leanh::LeanObject,
    mut v_data_1955_: *mut crate::leanh::LeanObject,
    mut v_a_1956_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1957_ = l_Std_Async_TCP_Socket_Client_sendAll(v_s_1954_, v_data_1955_);
    crate::leanh::lean_dec(v_s_1954_);
    return v_res_1957_;
}
pub unsafe fn l_Std_Async_TCP_Socket_Client_send(
    mut v_s_1958_: *mut crate::leanh::LeanObject,
    mut v_data_1959_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: u8 = 0;
    let mut v___x_1971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1976_: u8 = 0;
    let mut v___x_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1980_: u8 = 0;
    let mut v_a_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1984_: u8 = 0;
    let mut v___x_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1988_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1961_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1962_ = lean_mk_empty_array_with_capacity(v___x_1961_);
                v___x_1963_ = lean_array_push(v___x_1962_, v_data_1959_);
                v___f_1964_ = l_Std_Async_TCP_Socket_Client_connect___closed__1;
                v___x_1972_ = lean_uv_tcp_send(v_s_1958_, v___x_1963_);
                if crate::leanh::lean_obj_tag(v___x_1972_) == 0 {
                    v_a_1973_ = crate::leanh::lean_ctor_get(v___x_1972_, 0);
                    v_isSharedCheck_1980_ = (!crate::leanh::lean_is_exclusive(v___x_1972_)) as u8;
                    if v_isSharedCheck_1980_ == 0 {
                        v___x_1975_ = v___x_1972_;
                        v_isShared_1976_ = v_isSharedCheck_1980_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1973_);
                        crate::leanh::lean_dec(v___x_1972_);
                        v___x_1975_ = crate::leanh::lean_box(0);
                        v_isShared_1976_ = v_isSharedCheck_1980_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_1981_ = crate::leanh::lean_ctor_get(v___x_1972_, 0);
                    v_isSharedCheck_1988_ = (!crate::leanh::lean_is_exclusive(v___x_1972_)) as u8;
                    if v_isSharedCheck_1988_ == 0 {
                        v___x_1983_ = v___x_1972_;
                        v_isShared_1984_ = v_isSharedCheck_1988_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1981_);
                        crate::leanh::lean_dec(v___x_1972_);
                        v___x_1983_ = crate::leanh::lean_box(0);
                        v_isShared_1984_ = v_isSharedCheck_1988_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1967_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1967_, 0, v_val_1966_);
                v___x_1968_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1968_, 0, v___x_1967_);
                v___x_1969_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1970_ = 0;
                v___x_1971_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_1969_,
                    v___x_1970_,
                    v___x_1968_,
                    v___f_1964_,
                );
                return v___x_1971_;
            }
            2 => {
                if v_isShared_1976_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1975_, 1);
                    v___x_1978_ = v___x_1975_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1979_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1979_, 0, v_a_1973_);
                    v___x_1978_ = v_reuseFailAlloc_1979_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_val_1966_ = v___x_1978_;
                state = 1;
                continue;
            }
            4 => {
                if v_isShared_1984_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1983_, 0);
                    v___x_1986_ = v___x_1983_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1987_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1987_, 0, v_a_1981_);
                    v___x_1986_ = v_reuseFailAlloc_1987_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_val_1966_ = v___x_1986_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_TCP_Socket_Client_send___boxed(
    mut v_s_1989_: *mut crate::leanh::LeanObject,
    mut v_data_1990_: *mut crate::leanh::LeanObject,
    mut v_a_1991_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1992_ = l_Std_Async_TCP_Socket_Client_send(v_s_1989_, v_data_1990_);
    crate::leanh::lean_dec(v_s_1989_);
    return v_res_1992_;
}
pub unsafe fn l_Std_Async_TCP_Socket_Client_recv_x3f___lam__0(
    mut v___x_1993_: *mut crate::leanh::LeanObject,
    mut v_x_1994_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1994_) == 0 {
        let mut v___x_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1995_ = lean_mk_io_user_error(v___x_1993_);
        v___x_1996_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1996_, 0, v___x_1995_);
        return v___x_1996_;
    } else {
        let mut v_val_1997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v___x_1993_);
        v_val_1997_ = crate::leanh::lean_ctor_get(v_x_1994_, 0);
        crate::leanh::lean_inc(v_val_1997_);
        return v_val_1997_;
    }
}
pub unsafe fn l_Std_Async_TCP_Socket_Client_recv_x3f___lam__0___boxed(
    mut v___x_1998_: *mut crate::leanh::LeanObject,
    mut v_x_1999_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2000_ = l_Std_Async_TCP_Socket_Client_recv_x3f___lam__0(v___x_1998_, v_x_1999_);
    crate::leanh::lean_dec(v_x_1999_);
    return v_res_2000_;
}
pub unsafe fn l_Std_Async_TCP_Socket_Client_recv_x3f___lam__1(
    mut v___f_2001_: *mut crate::leanh::LeanObject,
    mut v_x_2002_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2007_: u8 = 0;
    let mut v___x_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2012_: u8 = 0;
    let mut v_a_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2017_: u8 = 0;
    let mut v___x_2019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2022_: u8 = 0;
    let mut v_a_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: u8 = 0;
    let mut v___x_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2002_) == 0 {
                    crate::leanh::lean_dec_ref(v___f_2001_);
                    v_a_2004_ = crate::leanh::lean_ctor_get(v_x_2002_, 0);
                    v_isSharedCheck_2012_ = (!crate::leanh::lean_is_exclusive(v_x_2002_)) as u8;
                    if v_isSharedCheck_2012_ == 0 {
                        v___x_2006_ = v_x_2002_;
                        v_isShared_2007_ = v_isSharedCheck_2012_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2004_);
                        crate::leanh::lean_dec(v_x_2002_);
                        v___x_2006_ = crate::leanh::lean_box(0);
                        v_isShared_2007_ = v_isSharedCheck_2012_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2013_ = crate::leanh::lean_ctor_get(v_x_2002_, 0);
                    crate::leanh::lean_inc(v_a_2013_);
                    crate::leanh::lean_dec_ref_known(v_x_2002_, 1);
                    if crate::leanh::lean_obj_tag(v_a_2013_) == 0 {
                        crate::leanh::lean_dec_ref(v___f_2001_);
                        v_a_2014_ = crate::leanh::lean_ctor_get(v_a_2013_, 0);
                        v_isSharedCheck_2022_ = (!crate::leanh::lean_is_exclusive(v_a_2013_)) as u8;
                        if v_isSharedCheck_2022_ == 0 {
                            v___x_2016_ = v_a_2013_;
                            v_isShared_2017_ = v_isSharedCheck_2022_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2014_);
                            crate::leanh::lean_dec(v_a_2013_);
                            v___x_2016_ = crate::leanh::lean_box(0);
                            v_isShared_2017_ = v_isSharedCheck_2022_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_2023_ = crate::leanh::lean_ctor_get(v_a_2013_, 0);
                        crate::leanh::lean_inc(v_a_2023_);
                        crate::leanh::lean_dec_ref_known(v_a_2013_, 1);
                        v___x_2024_ = lean_io_promise_result_opt(v_a_2023_);
                        crate::leanh::lean_dec(v_a_2023_);
                        v___x_2025_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_2026_ = 0;
                        v___x_2027_ =
                            lean_task_map(v___f_2001_, v___x_2024_, v___x_2025_, v___x_2026_);
                        v___x_2028_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2028_, 0, v___x_2027_);
                        return v___x_2028_;
                    }
                }
            }
            1 => {
                if v_isShared_2007_ == 0 {
                    v___x_2009_ = v___x_2006_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2011_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2011_, 0, v_a_2004_);
                    v___x_2009_ = v_reuseFailAlloc_2011_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2010_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2010_, 0, v___x_2009_);
                return v___x_2010_;
            }
            3 => {
                if v_isShared_2017_ == 0 {
                    v___x_2019_ = v___x_2016_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2021_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2021_, 0, v_a_2014_);
                    v___x_2019_ = v_reuseFailAlloc_2021_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2020_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2020_, 0, v___x_2019_);
                return v___x_2020_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_TCP_Socket_Client_recv_x3f___lam__1___boxed(
    mut v___f_2029_: *mut crate::leanh::LeanObject,
    mut v_x_2030_: *mut crate::leanh::LeanObject,
    mut v___y_2031_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2032_ = l_Std_Async_TCP_Socket_Client_recv_x3f___lam__1(v___f_2029_, v_x_2030_);
    return v_res_2032_;
}
pub unsafe fn l_Std_Async_TCP_Socket_Client_recv_x3f(
    mut v_s_2037_: *mut crate::leanh::LeanObject,
    mut v_size_2038_: u64,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2046_: u8 = 0;
    let mut v___x_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2052_: u8 = 0;
    let mut v___x_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2056_: u8 = 0;
    let mut v_a_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2060_: u8 = 0;
    let mut v___x_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2064_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_2040_ = l_Std_Async_TCP_Socket_Client_recv_x3f___closed__1;
                v___x_2048_ = lean_uv_tcp_recv(v_s_2037_, v_size_2038_);
                if crate::leanh::lean_obj_tag(v___x_2048_) == 0 {
                    v_a_2049_ = crate::leanh::lean_ctor_get(v___x_2048_, 0);
                    v_isSharedCheck_2056_ = (!crate::leanh::lean_is_exclusive(v___x_2048_)) as u8;
                    if v_isSharedCheck_2056_ == 0 {
                        v___x_2051_ = v___x_2048_;
                        v_isShared_2052_ = v_isSharedCheck_2056_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2049_);
                        crate::leanh::lean_dec(v___x_2048_);
                        v___x_2051_ = crate::leanh::lean_box(0);
                        v_isShared_2052_ = v_isSharedCheck_2056_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_2057_ = crate::leanh::lean_ctor_get(v___x_2048_, 0);
                    v_isSharedCheck_2064_ = (!crate::leanh::lean_is_exclusive(v___x_2048_)) as u8;
                    if v_isSharedCheck_2064_ == 0 {
                        v___x_2059_ = v___x_2048_;
                        v_isShared_2060_ = v_isSharedCheck_2064_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2057_);
                        crate::leanh::lean_dec(v___x_2048_);
                        v___x_2059_ = crate::leanh::lean_box(0);
                        v_isShared_2060_ = v_isSharedCheck_2064_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2043_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2043_, 0, v_val_2042_);
                v___x_2044_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2044_, 0, v___x_2043_);
                v___x_2045_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2046_ = 0;
                v___x_2047_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_2045_,
                    v___x_2046_,
                    v___x_2044_,
                    v___f_2040_,
                );
                return v___x_2047_;
            }
            2 => {
                if v_isShared_2052_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2051_, 1);
                    v___x_2054_ = v___x_2051_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2055_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2055_, 0, v_a_2049_);
                    v___x_2054_ = v_reuseFailAlloc_2055_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_val_2042_ = v___x_2054_;
                state = 1;
                continue;
            }
            4 => {
                if v_isShared_2060_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2059_, 0);
                    v___x_2062_ = v___x_2059_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2063_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2063_, 0, v_a_2057_);
                    v___x_2062_ = v_reuseFailAlloc_2063_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_val_2042_ = v___x_2062_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_TCP_Socket_Client_recv_x3f___boxed(
    mut v_s_2065_: *mut crate::leanh::LeanObject,
    mut v_size_2066_: *mut crate::leanh::LeanObject,
    mut v_a_2067_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_boxed_2068_: u64 = 0;
    let mut v_res_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_size_boxed_2068_ = crate::leanh::lean_unbox_uint64(v_size_2066_);
    crate::leanh::lean_dec_ref(v_size_2066_);
    v_res_2069_ = l_Std_Async_TCP_Socket_Client_recv_x3f(v_s_2065_, v_size_boxed_2068_);
    crate::leanh::lean_dec(v_s_2065_);
    return v_res_2069_;
}
pub unsafe fn l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0___lam__0(
    mut v_x_2070_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2070_) == 0 {
        let mut v_a_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_2071_ = crate::leanh::lean_ctor_get(v_x_2070_, 0);
        crate::leanh::lean_inc(v_a_2071_);
        crate::leanh::lean_dec_ref_known(v_x_2070_, 1);
        v___x_2072_ = lean_task_pure(v_a_2071_);
        return v___x_2072_;
    } else {
        let mut v_a_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_2073_ = crate::leanh::lean_ctor_get(v_x_2070_, 0);
        crate::leanh::lean_inc_ref(v_a_2073_);
        crate::leanh::lean_dec_ref_known(v_x_2070_, 1);
        return v_a_2073_;
    }
}
pub unsafe fn l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0___lam__2(
    mut v___f_2074_: *mut crate::leanh::LeanObject,
    mut v___x_2075_: *mut crate::leanh::LeanObject,
    mut v_x_2076_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2081_: u8 = 0;
    let mut v___x_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2086_: u8 = 0;
    let mut v_a_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2091_: u8 = 0;
    let mut v___x_2093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2096_: u8 = 0;
    let mut v_a_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: u8 = 0;
    let mut v___x_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2076_) == 0 {
                    crate::leanh::lean_dec(v___x_2075_);
                    crate::leanh::lean_dec_ref(v___f_2074_);
                    v_a_2078_ = crate::leanh::lean_ctor_get(v_x_2076_, 0);
                    v_isSharedCheck_2086_ = (!crate::leanh::lean_is_exclusive(v_x_2076_)) as u8;
                    if v_isSharedCheck_2086_ == 0 {
                        v___x_2080_ = v_x_2076_;
                        v_isShared_2081_ = v_isSharedCheck_2086_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2078_);
                        crate::leanh::lean_dec(v_x_2076_);
                        v___x_2080_ = crate::leanh::lean_box(0);
                        v_isShared_2081_ = v_isSharedCheck_2086_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2087_ = crate::leanh::lean_ctor_get(v_x_2076_, 0);
                    crate::leanh::lean_inc(v_a_2087_);
                    crate::leanh::lean_dec_ref_known(v_x_2076_, 1);
                    if crate::leanh::lean_obj_tag(v_a_2087_) == 0 {
                        crate::leanh::lean_dec(v___x_2075_);
                        crate::leanh::lean_dec_ref(v___f_2074_);
                        v_a_2088_ = crate::leanh::lean_ctor_get(v_a_2087_, 0);
                        v_isSharedCheck_2096_ = (!crate::leanh::lean_is_exclusive(v_a_2087_)) as u8;
                        if v_isSharedCheck_2096_ == 0 {
                            v___x_2090_ = v_a_2087_;
                            v_isShared_2091_ = v_isSharedCheck_2096_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2088_);
                            crate::leanh::lean_dec(v_a_2087_);
                            v___x_2090_ = crate::leanh::lean_box(0);
                            v_isShared_2091_ = v_isSharedCheck_2096_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_2097_ = crate::leanh::lean_ctor_get(v_a_2087_, 0);
                        crate::leanh::lean_inc(v_a_2097_);
                        crate::leanh::lean_dec_ref_known(v_a_2087_, 1);
                        v___x_2098_ = lean_io_promise_result_opt(v_a_2097_);
                        crate::leanh::lean_dec(v_a_2097_);
                        v___x_2099_ = 0;
                        v___x_2100_ =
                            lean_task_map(v___f_2074_, v___x_2098_, v___x_2075_, v___x_2099_);
                        v___x_2101_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2101_, 0, v___x_2100_);
                        return v___x_2101_;
                    }
                }
            }
            1 => {
                if v_isShared_2081_ == 0 {
                    v___x_2083_ = v___x_2080_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2085_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2085_, 0, v_a_2078_);
                    v___x_2083_ = v_reuseFailAlloc_2085_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2084_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2084_, 0, v___x_2083_);
                return v___x_2084_;
            }
            3 => {
                if v_isShared_2091_ == 0 {
                    v___x_2093_ = v___x_2090_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2095_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2095_, 0, v_a_2088_);
                    v___x_2093_ = v_reuseFailAlloc_2095_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2094_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2094_, 0, v___x_2093_);
                return v___x_2094_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0___lam__2___boxed(
    mut v___f_2102_: *mut crate::leanh::LeanObject,
    mut v___x_2103_: *mut crate::leanh::LeanObject,
    mut v_x_2104_: *mut crate::leanh::LeanObject,
    mut v___y_2105_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2106_ =
        l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0___lam__2(
            v___f_2102_,
            v___x_2103_,
            v_x_2104_,
        );
    return v_res_2106_;
}
pub unsafe fn l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0___lam__1(
    mut v___x_2107_: *mut crate::leanh::LeanObject,
    mut v_s_2108_: *mut crate::leanh::LeanObject,
    mut v_size_2109_: u64,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: u8 = 0;
    let mut v___x_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2123_: u8 = 0;
    let mut v___x_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2127_: u8 = 0;
    let mut v_a_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2131_: u8 = 0;
    let mut v___x_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2135_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_2111_ = l_Std_Async_TCP_Socket_Client_recv_x3f___closed__0;
                crate::leanh::lean_inc(v___x_2107_);
                v___f_2112_ = crate::leanh::lean_alloc_closure(l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0___lam__2___boxed as *mut core::ffi::c_void, 4, 2);
                crate::leanh::lean_closure_set(v___f_2112_, 0, v___f_2111_);
                crate::leanh::lean_closure_set(v___f_2112_, 1, v___x_2107_);
                v___x_2119_ = lean_uv_tcp_recv(v_s_2108_, v_size_2109_);
                if crate::leanh::lean_obj_tag(v___x_2119_) == 0 {
                    v_a_2120_ = crate::leanh::lean_ctor_get(v___x_2119_, 0);
                    v_isSharedCheck_2127_ = (!crate::leanh::lean_is_exclusive(v___x_2119_)) as u8;
                    if v_isSharedCheck_2127_ == 0 {
                        v___x_2122_ = v___x_2119_;
                        v_isShared_2123_ = v_isSharedCheck_2127_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2120_);
                        crate::leanh::lean_dec(v___x_2119_);
                        v___x_2122_ = crate::leanh::lean_box(0);
                        v_isShared_2123_ = v_isSharedCheck_2127_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_2128_ = crate::leanh::lean_ctor_get(v___x_2119_, 0);
                    v_isSharedCheck_2135_ = (!crate::leanh::lean_is_exclusive(v___x_2119_)) as u8;
                    if v_isSharedCheck_2135_ == 0 {
                        v___x_2130_ = v___x_2119_;
                        v_isShared_2131_ = v_isSharedCheck_2135_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2128_);
                        crate::leanh::lean_dec(v___x_2119_);
                        v___x_2130_ = crate::leanh::lean_box(0);
                        v_isShared_2131_ = v_isSharedCheck_2135_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2115_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2115_, 0, v_val_2114_);
                v___x_2116_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2116_, 0, v___x_2115_);
                v___x_2117_ = 0;
                v___x_2118_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_2107_,
                    v___x_2117_,
                    v___x_2116_,
                    v___f_2112_,
                );
                return v___x_2118_;
            }
            2 => {
                if v_isShared_2123_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2122_, 1);
                    v___x_2125_ = v___x_2122_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2126_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2126_, 0, v_a_2120_);
                    v___x_2125_ = v_reuseFailAlloc_2126_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_val_2114_ = v___x_2125_;
                state = 1;
                continue;
            }
            4 => {
                if v_isShared_2131_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2130_, 0);
                    v___x_2133_ = v___x_2130_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2134_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2134_, 0, v_a_2128_);
                    v___x_2133_ = v_reuseFailAlloc_2134_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_val_2114_ = v___x_2133_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0___lam__1___boxed(
    mut v___x_2136_: *mut crate::leanh::LeanObject,
    mut v_s_2137_: *mut crate::leanh::LeanObject,
    mut v_size_2138_: *mut crate::leanh::LeanObject,
    mut v___y_2139_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_boxed_2140_: u64 = 0;
    let mut v_res_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_size_boxed_2140_ = crate::leanh::lean_unbox_uint64(v_size_2138_);
    crate::leanh::lean_dec_ref(v_size_2138_);
    v_res_2141_ =
        l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0___lam__1(
            v___x_2136_,
            v_s_2137_,
            v_size_boxed_2140_,
        );
    crate::leanh::lean_dec(v_s_2137_);
    return v_res_2141_;
}
pub unsafe fn l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0(
    mut v_val_2143_: *mut crate::leanh::LeanObject,
    mut v_s_2144_: *mut crate::leanh::LeanObject,
    mut v_size_2145_: u64,
    mut v_w_2146_: *mut crate::leanh::LeanObject,
    mut v_lose_2147_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_finished_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_promise_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2159_: u8 = 0;
    let mut v___x_2160_: u8 = 0;
    let mut v___x_2161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2167_: u8 = 0;
    let mut v___x_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2179_: u8 = 0;
    let mut v_unused_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: u8 = 0;
    let mut v___x_2183_: u8 = 0;
    let mut v___x_2184_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_finished_2149_ = crate::leanh::lean_ctor_get(v_w_2146_, 0);
                v_promise_2150_ = crate::leanh::lean_ctor_get(v_w_2146_, 1);
                v___x_2156_ = lean_st_ref_take(v_finished_2149_);
                v___f_2157_ = l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0___closed__0;
                v___x_2182_ = (crate::leanh::lean_unbox(v___x_2156_) as u8);
                crate::leanh::lean_dec(v___x_2156_);
                if v___x_2182_ == 0 {
                    v___x_2183_ = 1;
                    v___y_2159_ = v___x_2183_;
                    state = 2;
                    continue;
                } else {
                    v___x_2184_ = 0;
                    v___y_2159_ = v___x_2184_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_2153_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2153_, 0, v_a_2152_);
                v___x_2154_ = lean_io_promise_resolve(v___x_2153_, v_promise_2150_);
                v___x_2155_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2155_, 0, v___x_2154_);
                return v___x_2155_;
            }
            2 => {
                v___x_2160_ = 1;
                v___x_2161_ = crate::leanh::lean_box((v___x_2160_) as usize);
                v___x_2162_ = lean_st_ref_set(v_finished_2149_, v___x_2161_);
                if v___y_2159_ == 0 {
                    crate::leanh::lean_dec(v_s_2144_);
                    crate::leanh::lean_dec_ref(v_val_2143_);
                    v___x_2163_ =
                        crate::leanh::lean_apply_1(v_lose_2147_, crate::leanh::lean_box(0));
                    return v___x_2163_;
                } else {
                    crate::leanh::lean_dec_ref(v_lose_2147_);
                    v___x_2164_ = l_IO_ofExcept___at___00Std_Async_TCP_Socket_Server_acceptSelector_spec__0___redArg(v_val_2143_);
                    if crate::leanh::lean_obj_tag(v___x_2164_) == 0 {
                        v_isSharedCheck_2179_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2164_)) as u8;
                        if v_isSharedCheck_2179_ == 0 {
                            v_unused_2180_ = crate::leanh::lean_ctor_get(v___x_2164_, 0);
                            crate::leanh::lean_dec(v_unused_2180_);
                            v___x_2166_ = v___x_2164_;
                            v_isShared_2167_ = v_isSharedCheck_2179_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_2164_);
                            v___x_2166_ = crate::leanh::lean_box(0);
                            v_isShared_2167_ = v_isSharedCheck_2179_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_s_2144_);
                        v_a_2181_ = crate::leanh::lean_ctor_get(v___x_2164_, 0);
                        crate::leanh::lean_inc(v_a_2181_);
                        crate::leanh::lean_dec_ref_known(v___x_2164_, 1);
                        v_a_2152_ = v_a_2181_;
                        state = 1;
                        continue;
                    }
                }
            }
            3 => {
                v___x_2168_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2169_ = crate::leanh::lean_box_uint64(v_size_2145_);
                v___f_2170_ = crate::leanh::lean_alloc_closure(l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0___lam__1___boxed as *mut core::ffi::c_void, 4, 3);
                crate::leanh::lean_closure_set(v___f_2170_, 0, v___x_2168_);
                crate::leanh::lean_closure_set(v___f_2170_, 1, v_s_2144_);
                crate::leanh::lean_closure_set(v___f_2170_, 2, v___x_2169_);
                v___x_2171_ = lean_io_as_task(v___f_2170_, v___x_2168_);
                v___x_2172_ = lean_task_bind(v___x_2171_, v___f_2157_, v___x_2168_, v___y_2159_);
                v___x_2173_ = lean_task_get_own(v___x_2172_);
                if crate::leanh::lean_obj_tag(v___x_2173_) == 0 {
                    crate::leanh::lean_del_object(v___x_2166_);
                    v_a_2174_ = crate::leanh::lean_ctor_get(v___x_2173_, 0);
                    crate::leanh::lean_inc(v_a_2174_);
                    crate::leanh::lean_dec_ref_known(v___x_2173_, 1);
                    v_a_2152_ = v_a_2174_;
                    state = 1;
                    continue;
                } else {
                    v___x_2175_ = lean_io_promise_resolve(v___x_2173_, v_promise_2150_);
                    if v_isShared_2167_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2166_, 0, v___x_2175_);
                        v___x_2177_ = v___x_2166_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2178_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2178_, 0, v___x_2175_);
                        v___x_2177_ = v_reuseFailAlloc_2178_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_2177_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0___boxed(
    mut v_val_2185_: *mut crate::leanh::LeanObject,
    mut v_s_2186_: *mut crate::leanh::LeanObject,
    mut v_size_2187_: *mut crate::leanh::LeanObject,
    mut v_w_2188_: *mut crate::leanh::LeanObject,
    mut v_lose_2189_: *mut crate::leanh::LeanObject,
    mut v___y_2190_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_boxed_2191_: u64 = 0;
    let mut v_res_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_size_boxed_2191_ = crate::leanh::lean_unbox_uint64(v_size_2187_);
    crate::leanh::lean_dec_ref(v_size_2187_);
    v_res_2192_ = l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0(
        v_val_2185_,
        v_s_2186_,
        v_size_boxed_2191_,
        v_w_2188_,
        v_lose_2189_,
    );
    crate::leanh::lean_dec_ref(v_w_2188_);
    return v_res_2192_;
}
pub unsafe fn l_Std_Async_TCP_Socket_Client_recvSelector___lam__1(
    mut v_x_2193_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2198_: u8 = 0;
    let mut v___x_2200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2203_: u8 = 0;
    let mut v_a_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2207_: u8 = 0;
    let mut v___x_2208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2213_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2193_) == 0 {
                    v_a_2195_ = crate::leanh::lean_ctor_get(v_x_2193_, 0);
                    v_isSharedCheck_2203_ = (!crate::leanh::lean_is_exclusive(v_x_2193_)) as u8;
                    if v_isSharedCheck_2203_ == 0 {
                        v___x_2197_ = v_x_2193_;
                        v_isShared_2198_ = v_isSharedCheck_2203_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2195_);
                        crate::leanh::lean_dec(v_x_2193_);
                        v___x_2197_ = crate::leanh::lean_box(0);
                        v_isShared_2198_ = v_isSharedCheck_2203_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2204_ = crate::leanh::lean_ctor_get(v_x_2193_, 0);
                    v_isSharedCheck_2213_ = (!crate::leanh::lean_is_exclusive(v_x_2193_)) as u8;
                    if v_isSharedCheck_2213_ == 0 {
                        v___x_2206_ = v_x_2193_;
                        v_isShared_2207_ = v_isSharedCheck_2213_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2204_);
                        crate::leanh::lean_dec(v_x_2193_);
                        v___x_2206_ = crate::leanh::lean_box(0);
                        v_isShared_2207_ = v_isSharedCheck_2213_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2198_ == 0 {
                    v___x_2200_ = v___x_2197_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2202_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2202_, 0, v_a_2195_);
                    v___x_2200_ = v_reuseFailAlloc_2202_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2201_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2201_, 0, v___x_2200_);
                return v___x_2201_;
            }
            3 => {
                v___x_2208_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2208_, 0, v_a_2204_);
                if v_isShared_2207_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2206_, 0, v___x_2208_);
                    v___x_2210_ = v___x_2206_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2212_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2212_, 0, v___x_2208_);
                    v___x_2210_ = v_reuseFailAlloc_2212_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2211_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2211_, 0, v___x_2210_);
                return v___x_2211_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_TCP_Socket_Client_recvSelector___lam__1___boxed(
    mut v_x_2214_: *mut crate::leanh::LeanObject,
    mut v___y_2215_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2216_ = l_Std_Async_TCP_Socket_Client_recvSelector___lam__1(v_x_2214_);
    return v_res_2216_;
}
pub unsafe fn l_Std_Async_TCP_Socket_Client_recvSelector___lam__0(
    mut v_x_2221_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2226_: u8 = 0;
    let mut v___x_2228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2231_: u8 = 0;
    let mut v___x_2232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2221_) == 0 {
                    v_a_2223_ = crate::leanh::lean_ctor_get(v_x_2221_, 0);
                    v_isSharedCheck_2231_ = (!crate::leanh::lean_is_exclusive(v_x_2221_)) as u8;
                    if v_isSharedCheck_2231_ == 0 {
                        v___x_2225_ = v_x_2221_;
                        v_isShared_2226_ = v_isSharedCheck_2231_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2223_);
                        crate::leanh::lean_dec(v_x_2221_);
                        v___x_2225_ = crate::leanh::lean_box(0);
                        v_isShared_2226_ = v_isSharedCheck_2231_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v_x_2221_, 1);
                    v___x_2232_ = l_Std_Async_TCP_Socket_Client_recvSelector___lam__0___closed__1;
                    return v___x_2232_;
                }
            }
            1 => {
                if v_isShared_2226_ == 0 {
                    v___x_2228_ = v___x_2225_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2230_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2230_, 0, v_a_2223_);
                    v___x_2228_ = v_reuseFailAlloc_2230_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2229_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2229_, 0, v___x_2228_);
                return v___x_2229_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_TCP_Socket_Client_recvSelector___lam__0___boxed(
    mut v_x_2233_: *mut crate::leanh::LeanObject,
    mut v___y_2234_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2235_ = l_Std_Async_TCP_Socket_Client_recvSelector___lam__0(v_x_2233_);
    return v_res_2235_;
}
pub unsafe fn l_Std_Async_TCP_Socket_Client_recvSelector___lam__2(
    mut v_s_2236_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2245_: u8 = 0;
    let mut v___x_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2249_: u8 = 0;
    let mut v_a_2250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2253_: u8 = 0;
    let mut v___x_2255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2257_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2241_ = lean_uv_tcp_cancel_recv(v_s_2236_);
                if crate::leanh::lean_obj_tag(v___x_2241_) == 0 {
                    v_a_2242_ = crate::leanh::lean_ctor_get(v___x_2241_, 0);
                    v_isSharedCheck_2249_ = (!crate::leanh::lean_is_exclusive(v___x_2241_)) as u8;
                    if v_isSharedCheck_2249_ == 0 {
                        v___x_2244_ = v___x_2241_;
                        v_isShared_2245_ = v_isSharedCheck_2249_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2242_);
                        crate::leanh::lean_dec(v___x_2241_);
                        v___x_2244_ = crate::leanh::lean_box(0);
                        v_isShared_2245_ = v_isSharedCheck_2249_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_2250_ = crate::leanh::lean_ctor_get(v___x_2241_, 0);
                    v_isSharedCheck_2257_ = (!crate::leanh::lean_is_exclusive(v___x_2241_)) as u8;
                    if v_isSharedCheck_2257_ == 0 {
                        v___x_2252_ = v___x_2241_;
                        v_isShared_2253_ = v_isSharedCheck_2257_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2250_);
                        crate::leanh::lean_dec(v___x_2241_);
                        v___x_2252_ = crate::leanh::lean_box(0);
                        v_isShared_2253_ = v_isSharedCheck_2257_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2240_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2240_, 0, v_val_2239_);
                return v___x_2240_;
            }
            2 => {
                if v_isShared_2245_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2244_, 1);
                    v___x_2247_ = v___x_2244_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2248_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2248_, 0, v_a_2242_);
                    v___x_2247_ = v_reuseFailAlloc_2248_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_val_2239_ = v___x_2247_;
                state = 1;
                continue;
            }
            4 => {
                if v_isShared_2253_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2252_, 0);
                    v___x_2255_ = v___x_2252_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2256_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2256_, 0, v_a_2250_);
                    v___x_2255_ = v_reuseFailAlloc_2256_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_val_2239_ = v___x_2255_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_TCP_Socket_Client_recvSelector___lam__2___boxed(
    mut v_s_2258_: *mut crate::leanh::LeanObject,
    mut v___y_2259_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2260_ = l_Std_Async_TCP_Socket_Client_recvSelector___lam__2(v_s_2258_);
    crate::leanh::lean_dec(v_s_2258_);
    return v_res_2260_;
}
pub unsafe fn l_Std_Async_TCP_Socket_Client_recvSelector___lam__4(
    mut v_s_2261_: *mut crate::leanh::LeanObject,
    mut v_size_2262_: u64,
    mut v_waiter_2263_: *mut crate::leanh::LeanObject,
    mut v_a_2264_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2277_: u8 = 0;
    let mut v___x_2279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2281_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_2264_) == 0 {
                    crate::leanh::lean_dec(v_s_2261_);
                    v___x_2269_ = crate::leanh::lean_box(0);
                    v_a_2267_ = v___x_2269_;
                    state = 1;
                    continue;
                } else {
                    v_val_2270_ = crate::leanh::lean_ctor_get(v_a_2264_, 0);
                    crate::leanh::lean_inc(v_val_2270_);
                    crate::leanh::lean_dec_ref_known(v_a_2264_, 1);
                    v___f_2271_ = l_Std_Async_TCP_Socket_Server_acceptSelector___lam__2___closed__0;
                    v___x_2272_ = l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0(v_val_2270_, v_s_2261_, v_size_2262_, v_waiter_2263_, v___f_2271_);
                    if crate::leanh::lean_obj_tag(v___x_2272_) == 0 {
                        v_a_2273_ = crate::leanh::lean_ctor_get(v___x_2272_, 0);
                        crate::leanh::lean_inc(v_a_2273_);
                        crate::leanh::lean_dec_ref_known(v___x_2272_, 1);
                        v_a_2267_ = v_a_2273_;
                        state = 1;
                        continue;
                    } else {
                        v_a_2274_ = crate::leanh::lean_ctor_get(v___x_2272_, 0);
                        v_isSharedCheck_2281_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2272_)) as u8;
                        if v_isSharedCheck_2281_ == 0 {
                            v___x_2276_ = v___x_2272_;
                            v_isShared_2277_ = v_isSharedCheck_2281_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2274_);
                            crate::leanh::lean_dec(v___x_2272_);
                            v___x_2276_ = crate::leanh::lean_box(0);
                            v_isShared_2277_ = v_isSharedCheck_2281_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2268_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2268_, 0, v_a_2267_);
                return v___x_2268_;
            }
            2 => {
                if v_isShared_2277_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2276_, 0);
                    v___x_2279_ = v___x_2276_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2280_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2280_, 0, v_a_2274_);
                    v___x_2279_ = v_reuseFailAlloc_2280_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2279_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_TCP_Socket_Client_recvSelector___lam__4___boxed(
    mut v_s_2282_: *mut crate::leanh::LeanObject,
    mut v_size_2283_: *mut crate::leanh::LeanObject,
    mut v_waiter_2284_: *mut crate::leanh::LeanObject,
    mut v_a_2285_: *mut crate::leanh::LeanObject,
    mut v___y_2286_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_boxed_2287_: u64 = 0;
    let mut v_res_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_size_boxed_2287_ = crate::leanh::lean_unbox_uint64(v_size_2283_);
    crate::leanh::lean_dec_ref(v_size_2283_);
    v_res_2288_ = l_Std_Async_TCP_Socket_Client_recvSelector___lam__4(
        v_s_2282_,
        v_size_boxed_2287_,
        v_waiter_2284_,
        v_a_2285_,
    );
    crate::leanh::lean_dec_ref(v_waiter_2284_);
    return v_res_2288_;
}
pub unsafe fn l_Std_Async_TCP_Socket_Client_recvSelector___lam__3(
    mut v___f_2293_: *mut crate::leanh::LeanObject,
    mut v_x_2294_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2299_: u8 = 0;
    let mut v___x_2301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2304_: u8 = 0;
    let mut v_a_2305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: u8 = 0;
    let mut v___x_2309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2294_) == 0 {
                    crate::leanh::lean_dec_ref(v___f_2293_);
                    v_a_2296_ = crate::leanh::lean_ctor_get(v_x_2294_, 0);
                    v_isSharedCheck_2304_ = (!crate::leanh::lean_is_exclusive(v_x_2294_)) as u8;
                    if v_isSharedCheck_2304_ == 0 {
                        v___x_2298_ = v_x_2294_;
                        v_isShared_2299_ = v_isSharedCheck_2304_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2296_);
                        crate::leanh::lean_dec(v_x_2294_);
                        v___x_2298_ = crate::leanh::lean_box(0);
                        v_isShared_2299_ = v_isSharedCheck_2304_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2305_ = crate::leanh::lean_ctor_get(v_x_2294_, 0);
                    crate::leanh::lean_inc(v_a_2305_);
                    crate::leanh::lean_dec_ref_known(v_x_2294_, 1);
                    v___x_2306_ = lean_io_promise_result_opt(v_a_2305_);
                    crate::leanh::lean_dec(v_a_2305_);
                    v___x_2307_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2308_ = 0;
                    v___x_2309_ =
                        lean_io_map_task(v___f_2293_, v___x_2306_, v___x_2307_, v___x_2308_);
                    crate::leanh::lean_dec_ref(v___x_2309_);
                    v___x_2310_ = l_Std_Async_TCP_Socket_Client_recvSelector___lam__3___closed__1;
                    return v___x_2310_;
                }
            }
            1 => {
                if v_isShared_2299_ == 0 {
                    v___x_2301_ = v___x_2298_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2303_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2303_, 0, v_a_2296_);
                    v___x_2301_ = v_reuseFailAlloc_2303_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2302_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2302_, 0, v___x_2301_);
                return v___x_2302_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_TCP_Socket_Client_recvSelector___lam__3___boxed(
    mut v___f_2311_: *mut crate::leanh::LeanObject,
    mut v_x_2312_: *mut crate::leanh::LeanObject,
    mut v___y_2313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2314_ = l_Std_Async_TCP_Socket_Client_recvSelector___lam__3(v___f_2311_, v_x_2312_);
    return v_res_2314_;
}
pub unsafe fn l_Std_Async_TCP_Socket_Client_recvSelector___lam__5(
    mut v_s_2315_: *mut crate::leanh::LeanObject,
    mut v_size_2316_: u64,
    mut v_waiter_2317_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: u8 = 0;
    let mut v___x_2327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2332_: u8 = 0;
    let mut v___x_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2336_: u8 = 0;
    let mut v_a_2337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2340_: u8 = 0;
    let mut v___x_2342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2344_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2319_ = crate::leanh::lean_box_uint64(v_size_2316_);
                crate::leanh::lean_inc(v_s_2315_);
                v___f_2320_ = crate::leanh::lean_alloc_closure(
                    l_Std_Async_TCP_Socket_Client_recvSelector___lam__4___boxed
                        as *mut core::ffi::c_void,
                    5,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_2320_, 0, v_s_2315_);
                crate::leanh::lean_closure_set(v___f_2320_, 1, v___x_2319_);
                crate::leanh::lean_closure_set(v___f_2320_, 2, v_waiter_2317_);
                v___f_2321_ = crate::leanh::lean_alloc_closure(
                    l_Std_Async_TCP_Socket_Client_recvSelector___lam__3___boxed
                        as *mut core::ffi::c_void,
                    3,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2321_, 0, v___f_2320_);
                v___x_2328_ = lean_uv_tcp_wait_readable(v_s_2315_);
                crate::leanh::lean_dec(v_s_2315_);
                if crate::leanh::lean_obj_tag(v___x_2328_) == 0 {
                    v_a_2329_ = crate::leanh::lean_ctor_get(v___x_2328_, 0);
                    v_isSharedCheck_2336_ = (!crate::leanh::lean_is_exclusive(v___x_2328_)) as u8;
                    if v_isSharedCheck_2336_ == 0 {
                        v___x_2331_ = v___x_2328_;
                        v_isShared_2332_ = v_isSharedCheck_2336_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2329_);
                        crate::leanh::lean_dec(v___x_2328_);
                        v___x_2331_ = crate::leanh::lean_box(0);
                        v_isShared_2332_ = v_isSharedCheck_2336_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_2337_ = crate::leanh::lean_ctor_get(v___x_2328_, 0);
                    v_isSharedCheck_2344_ = (!crate::leanh::lean_is_exclusive(v___x_2328_)) as u8;
                    if v_isSharedCheck_2344_ == 0 {
                        v___x_2339_ = v___x_2328_;
                        v_isShared_2340_ = v_isSharedCheck_2344_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2337_);
                        crate::leanh::lean_dec(v___x_2328_);
                        v___x_2339_ = crate::leanh::lean_box(0);
                        v_isShared_2340_ = v_isSharedCheck_2344_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2324_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2324_, 0, v_val_2323_);
                v___x_2325_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2326_ = 0;
                v___x_2327_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_2325_,
                    v___x_2326_,
                    v___x_2324_,
                    v___f_2321_,
                );
                return v___x_2327_;
            }
            2 => {
                if v_isShared_2332_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2331_, 1);
                    v___x_2334_ = v___x_2331_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2335_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2335_, 0, v_a_2329_);
                    v___x_2334_ = v_reuseFailAlloc_2335_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_val_2323_ = v___x_2334_;
                state = 1;
                continue;
            }
            4 => {
                if v_isShared_2340_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2339_, 0);
                    v___x_2342_ = v___x_2339_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2343_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2343_, 0, v_a_2337_);
                    v___x_2342_ = v_reuseFailAlloc_2343_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_val_2323_ = v___x_2342_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_TCP_Socket_Client_recvSelector___lam__5___boxed(
    mut v_s_2345_: *mut crate::leanh::LeanObject,
    mut v_size_2346_: *mut crate::leanh::LeanObject,
    mut v_waiter_2347_: *mut crate::leanh::LeanObject,
    mut v___y_2348_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_boxed_2349_: u64 = 0;
    let mut v_res_2350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_size_boxed_2349_ = crate::leanh::lean_unbox_uint64(v_size_2346_);
    crate::leanh::lean_dec_ref(v_size_2346_);
    v_res_2350_ = l_Std_Async_TCP_Socket_Client_recvSelector___lam__5(
        v_s_2345_,
        v_size_boxed_2349_,
        v_waiter_2347_,
    );
    return v_res_2350_;
}
pub unsafe fn l_Std_Async_TCP_Socket_Client_recvSelector___lam__9(
    mut v___f_2351_: *mut crate::leanh::LeanObject,
    mut v_s_2352_: *mut crate::leanh::LeanObject,
    mut v_size_2353_: u64,
    mut v___f_2354_: *mut crate::leanh::LeanObject,
    mut v___f_2355_: *mut crate::leanh::LeanObject,
    mut v_x_2356_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2361_: u8 = 0;
    let mut v___x_2363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2366_: u8 = 0;
    let mut v_a_2367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2370_: u8 = 0;
    let mut v_val_2372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: u8 = 0;
    let mut v___x_2376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: u8 = 0;
    let mut v___x_2378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: u8 = 0;
    let mut v___x_2392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: u8 = 0;
    let mut v___x_2396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2397_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2356_) == 0 {
                    crate::leanh::lean_dec_ref(v___f_2355_);
                    crate::leanh::lean_dec_ref(v___f_2354_);
                    crate::leanh::lean_dec(v_s_2352_);
                    crate::leanh::lean_dec_ref(v___f_2351_);
                    v_a_2358_ = crate::leanh::lean_ctor_get(v_x_2356_, 0);
                    v_isSharedCheck_2366_ = (!crate::leanh::lean_is_exclusive(v_x_2356_)) as u8;
                    if v_isSharedCheck_2366_ == 0 {
                        v___x_2360_ = v_x_2356_;
                        v_isShared_2361_ = v_isSharedCheck_2366_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2358_);
                        crate::leanh::lean_dec(v_x_2356_);
                        v___x_2360_ = crate::leanh::lean_box(0);
                        v_isShared_2361_ = v_isSharedCheck_2366_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2367_ = crate::leanh::lean_ctor_get(v_x_2356_, 0);
                    v_isSharedCheck_2397_ = (!crate::leanh::lean_is_exclusive(v_x_2356_)) as u8;
                    if v_isSharedCheck_2397_ == 0 {
                        v___x_2369_ = v_x_2356_;
                        v_isShared_2370_ = v_isSharedCheck_2397_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2367_);
                        crate::leanh::lean_dec(v_x_2356_);
                        v___x_2369_ = crate::leanh::lean_box(0);
                        v_isShared_2370_ = v_isSharedCheck_2397_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2361_ == 0 {
                    v___x_2363_ = v___x_2360_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2365_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2365_, 0, v_a_2358_);
                    v___x_2363_ = v_reuseFailAlloc_2365_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2364_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2364_, 0, v___x_2363_);
                return v___x_2364_;
            }
            3 => {
                v___x_2377_ = (crate::leanh::lean_unbox(v_a_2367_) as u8);
                if v___x_2377_ == 0 {
                    crate::leanh::lean_dec_ref(v___f_2355_);
                    crate::leanh::lean_dec_ref(v___f_2354_);
                    v___x_2378_ = lean_uv_tcp_cancel_recv(v_s_2352_);
                    crate::leanh::lean_dec(v_s_2352_);
                    if crate::leanh::lean_obj_tag(v___x_2378_) == 0 {
                        v_a_2379_ = crate::leanh::lean_ctor_get(v___x_2378_, 0);
                        crate::leanh::lean_inc(v_a_2379_);
                        crate::leanh::lean_dec_ref_known(v___x_2378_, 1);
                        if v_isShared_2370_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2369_, 0, v_a_2379_);
                            v___x_2381_ = v___x_2369_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_2382_ =
                                crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2382_, 0, v_a_2379_);
                            v___x_2381_ = v_reuseFailAlloc_2382_;
                            state = 5;
                            continue;
                        }
                    } else {
                        v_a_2383_ = crate::leanh::lean_ctor_get(v___x_2378_, 0);
                        crate::leanh::lean_inc(v_a_2383_);
                        crate::leanh::lean_dec_ref_known(v___x_2378_, 1);
                        if v_isShared_2370_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_2369_, 0);
                            crate::leanh::lean_ctor_set(v___x_2369_, 0, v_a_2383_);
                            v___x_2385_ = v___x_2369_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_2386_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2386_, 0, v_a_2383_);
                            v___x_2385_ = v_reuseFailAlloc_2386_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2369_);
                    crate::leanh::lean_dec_ref(v___f_2351_);
                    v___x_2387_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2388_ = crate::leanh::lean_box_uint64(v_size_2353_);
                    v___f_2389_ = crate::leanh::lean_alloc_closure(l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0___lam__1___boxed as *mut core::ffi::c_void, 4, 3);
                    crate::leanh::lean_closure_set(v___f_2389_, 0, v___x_2387_);
                    crate::leanh::lean_closure_set(v___f_2389_, 1, v_s_2352_);
                    crate::leanh::lean_closure_set(v___f_2389_, 2, v___x_2388_);
                    v___x_2390_ = lean_io_as_task(v___f_2389_, v___x_2387_);
                    v___x_2391_ = (crate::leanh::lean_unbox(v_a_2367_) as u8);
                    crate::leanh::lean_dec(v_a_2367_);
                    v___x_2392_ =
                        lean_task_bind(v___x_2390_, v___f_2354_, v___x_2387_, v___x_2391_);
                    v___x_2393_ = lean_task_get_own(v___x_2392_);
                    v___x_2394_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2394_, 0, v___x_2393_);
                    v___x_2395_ = 0;
                    v___x_2396_ =
                        l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v___x_2387_,
                            v___x_2395_,
                            v___x_2394_,
                            v___f_2355_,
                        );
                    return v___x_2396_;
                }
            }
            4 => {
                v___x_2373_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2373_, 0, v_val_2372_);
                v___x_2374_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2375_ = (crate::leanh::lean_unbox(v_a_2367_) as u8);
                crate::leanh::lean_dec(v_a_2367_);
                v___x_2376_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_2374_,
                    v___x_2375_,
                    v___x_2373_,
                    v___f_2351_,
                );
                return v___x_2376_;
            }
            5 => {
                v_val_2372_ = v___x_2381_;
                state = 4;
                continue;
            }
            6 => {
                v_val_2372_ = v___x_2385_;
                state = 4;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_TCP_Socket_Client_recvSelector___lam__9___boxed(
    mut v___f_2398_: *mut crate::leanh::LeanObject,
    mut v_s_2399_: *mut crate::leanh::LeanObject,
    mut v_size_2400_: *mut crate::leanh::LeanObject,
    mut v___f_2401_: *mut crate::leanh::LeanObject,
    mut v___f_2402_: *mut crate::leanh::LeanObject,
    mut v_x_2403_: *mut crate::leanh::LeanObject,
    mut v___y_2404_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_boxed_2405_: u64 = 0;
    let mut v_res_2406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_size_boxed_2405_ = crate::leanh::lean_unbox_uint64(v_size_2400_);
    crate::leanh::lean_dec_ref(v_size_2400_);
    v_res_2406_ = l_Std_Async_TCP_Socket_Client_recvSelector___lam__9(
        v___f_2398_,
        v_s_2399_,
        v_size_boxed_2405_,
        v___f_2401_,
        v___f_2402_,
        v_x_2403_,
    );
    return v_res_2406_;
}
pub unsafe fn l_Std_Async_TCP_Socket_Client_recvSelector___lam__6(
    mut v___f_2407_: *mut crate::leanh::LeanObject,
    mut v_x_2408_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2413_: u8 = 0;
    let mut v___x_2415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2418_: u8 = 0;
    let mut v_a_2419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2422_: u8 = 0;
    let mut v___x_2423_: u8 = 0;
    let mut v___x_2424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: u8 = 0;
    let mut v___x_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2432_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2408_) == 0 {
                    crate::leanh::lean_dec_ref(v___f_2407_);
                    v_a_2410_ = crate::leanh::lean_ctor_get(v_x_2408_, 0);
                    v_isSharedCheck_2418_ = (!crate::leanh::lean_is_exclusive(v_x_2408_)) as u8;
                    if v_isSharedCheck_2418_ == 0 {
                        v___x_2412_ = v_x_2408_;
                        v_isShared_2413_ = v_isSharedCheck_2418_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2410_);
                        crate::leanh::lean_dec(v_x_2408_);
                        v___x_2412_ = crate::leanh::lean_box(0);
                        v_isShared_2413_ = v_isSharedCheck_2418_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2419_ = crate::leanh::lean_ctor_get(v_x_2408_, 0);
                    v_isSharedCheck_2432_ = (!crate::leanh::lean_is_exclusive(v_x_2408_)) as u8;
                    if v_isSharedCheck_2432_ == 0 {
                        v___x_2421_ = v_x_2408_;
                        v_isShared_2422_ = v_isSharedCheck_2432_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2419_);
                        crate::leanh::lean_dec(v_x_2408_);
                        v___x_2421_ = crate::leanh::lean_box(0);
                        v_isShared_2422_ = v_isSharedCheck_2432_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2413_ == 0 {
                    v___x_2415_ = v___x_2412_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2417_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2417_, 0, v_a_2410_);
                    v___x_2415_ = v_reuseFailAlloc_2417_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2416_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2416_, 0, v___x_2415_);
                return v___x_2416_;
            }
            3 => {
                v___x_2423_ = l_IO_Promise_isResolved___redArg(v_a_2419_);
                crate::leanh::lean_dec(v_a_2419_);
                v___x_2424_ = crate::leanh::lean_box((v___x_2423_) as usize);
                if v_isShared_2422_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2421_, 0, v___x_2424_);
                    v___x_2426_ = v___x_2421_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2431_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2431_, 0, v___x_2424_);
                    v___x_2426_ = v_reuseFailAlloc_2431_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2427_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2427_, 0, v___x_2426_);
                v___x_2428_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2429_ = 0;
                v___x_2430_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_2428_,
                    v___x_2429_,
                    v___x_2427_,
                    v___f_2407_,
                );
                return v___x_2430_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_TCP_Socket_Client_recvSelector___lam__6___boxed(
    mut v___f_2433_: *mut crate::leanh::LeanObject,
    mut v_x_2434_: *mut crate::leanh::LeanObject,
    mut v___y_2435_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2436_ = l_Std_Async_TCP_Socket_Client_recvSelector___lam__6(v___f_2433_, v_x_2434_);
    return v_res_2436_;
}
pub unsafe fn l_Std_Async_TCP_Socket_Client_recvSelector___lam__7(
    mut v___f_2437_: *mut crate::leanh::LeanObject,
    mut v_s_2438_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_2441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: u8 = 0;
    let mut v___x_2445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2450_: u8 = 0;
    let mut v___x_2452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2454_: u8 = 0;
    let mut v_a_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2458_: u8 = 0;
    let mut v___x_2460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2462_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2446_ = lean_uv_tcp_wait_readable(v_s_2438_);
                if crate::leanh::lean_obj_tag(v___x_2446_) == 0 {
                    v_a_2447_ = crate::leanh::lean_ctor_get(v___x_2446_, 0);
                    v_isSharedCheck_2454_ = (!crate::leanh::lean_is_exclusive(v___x_2446_)) as u8;
                    if v_isSharedCheck_2454_ == 0 {
                        v___x_2449_ = v___x_2446_;
                        v_isShared_2450_ = v_isSharedCheck_2454_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2447_);
                        crate::leanh::lean_dec(v___x_2446_);
                        v___x_2449_ = crate::leanh::lean_box(0);
                        v_isShared_2450_ = v_isSharedCheck_2454_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_2455_ = crate::leanh::lean_ctor_get(v___x_2446_, 0);
                    v_isSharedCheck_2462_ = (!crate::leanh::lean_is_exclusive(v___x_2446_)) as u8;
                    if v_isSharedCheck_2462_ == 0 {
                        v___x_2457_ = v___x_2446_;
                        v_isShared_2458_ = v_isSharedCheck_2462_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2455_);
                        crate::leanh::lean_dec(v___x_2446_);
                        v___x_2457_ = crate::leanh::lean_box(0);
                        v_isShared_2458_ = v_isSharedCheck_2462_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2442_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2442_, 0, v_val_2441_);
                v___x_2443_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2444_ = 0;
                v___x_2445_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_2443_,
                    v___x_2444_,
                    v___x_2442_,
                    v___f_2437_,
                );
                return v___x_2445_;
            }
            2 => {
                if v_isShared_2450_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2449_, 1);
                    v___x_2452_ = v___x_2449_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2453_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2453_, 0, v_a_2447_);
                    v___x_2452_ = v_reuseFailAlloc_2453_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_val_2441_ = v___x_2452_;
                state = 1;
                continue;
            }
            4 => {
                if v_isShared_2458_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2457_, 0);
                    v___x_2460_ = v___x_2457_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2461_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2461_, 0, v_a_2455_);
                    v___x_2460_ = v_reuseFailAlloc_2461_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_val_2441_ = v___x_2460_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_TCP_Socket_Client_recvSelector___lam__7___boxed(
    mut v___f_2463_: *mut crate::leanh::LeanObject,
    mut v_s_2464_: *mut crate::leanh::LeanObject,
    mut v___y_2465_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2466_ = l_Std_Async_TCP_Socket_Client_recvSelector___lam__7(v___f_2463_, v_s_2464_);
    crate::leanh::lean_dec(v_s_2464_);
    return v_res_2466_;
}
pub unsafe fn l_Std_Async_TCP_Socket_Client_recvSelector(
    mut v_s_2469_: *mut crate::leanh::LeanObject,
    mut v_size_2470_: u64,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2471_ = l_Std_Async_Waiter_race___at___00Std_Async_TCP_Socket_Client_recvSelector_spec__0___closed__0;
    v___f_2472_ = l_Std_Async_TCP_Socket_Client_recvSelector___closed__0;
    v___f_2473_ = l_Std_Async_TCP_Socket_Client_recvSelector___closed__1;
    crate::leanh::lean_inc_n(v_s_2469_, 3);
    v___f_2474_ = crate::leanh::lean_alloc_closure(
        l_Std_Async_TCP_Socket_Client_recvSelector___lam__2___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2474_, 0, v_s_2469_);
    v___x_2475_ = crate::leanh::lean_box_uint64(v_size_2470_);
    v___f_2476_ = crate::leanh::lean_alloc_closure(
        l_Std_Async_TCP_Socket_Client_recvSelector___lam__5___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2476_, 0, v_s_2469_);
    crate::leanh::lean_closure_set(v___f_2476_, 1, v___x_2475_);
    v___x_2477_ = crate::leanh::lean_box_uint64(v_size_2470_);
    v___f_2478_ = crate::leanh::lean_alloc_closure(
        l_Std_Async_TCP_Socket_Client_recvSelector___lam__9___boxed as *mut core::ffi::c_void,
        7,
        5,
    );
    crate::leanh::lean_closure_set(v___f_2478_, 0, v___f_2473_);
    crate::leanh::lean_closure_set(v___f_2478_, 1, v_s_2469_);
    crate::leanh::lean_closure_set(v___f_2478_, 2, v___x_2477_);
    crate::leanh::lean_closure_set(v___f_2478_, 3, v___f_2471_);
    crate::leanh::lean_closure_set(v___f_2478_, 4, v___f_2472_);
    v___f_2479_ = crate::leanh::lean_alloc_closure(
        l_Std_Async_TCP_Socket_Client_recvSelector___lam__6___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2479_, 0, v___f_2478_);
    v___f_2480_ = crate::leanh::lean_alloc_closure(
        l_Std_Async_TCP_Socket_Client_recvSelector___lam__7___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2480_, 0, v___f_2479_);
    crate::leanh::lean_closure_set(v___f_2480_, 1, v_s_2469_);
    v___x_2481_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2481_, 0, v___f_2480_);
    crate::leanh::lean_ctor_set(v___x_2481_, 1, v___f_2476_);
    crate::leanh::lean_ctor_set(v___x_2481_, 2, v___f_2474_);
    return v___x_2481_;
}
pub unsafe fn l_Std_Async_TCP_Socket_Client_recvSelector___boxed(
    mut v_s_2482_: *mut crate::leanh::LeanObject,
    mut v_size_2483_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_boxed_2484_: u64 = 0;
    let mut v_res_2485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_size_boxed_2484_ = crate::leanh::lean_unbox_uint64(v_size_2483_);
    crate::leanh::lean_dec_ref(v_size_2483_);
    v_res_2485_ = l_Std_Async_TCP_Socket_Client_recvSelector(v_s_2482_, v_size_boxed_2484_);
    return v_res_2485_;
}
pub unsafe fn l_Std_Async_TCP_Socket_Client_shutdown(
    mut v_s_2486_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2494_: u8 = 0;
    let mut v___x_2495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2500_: u8 = 0;
    let mut v___x_2502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2504_: u8 = 0;
    let mut v_a_2505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2508_: u8 = 0;
    let mut v___x_2510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2512_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_2488_ = l_Std_Async_TCP_Socket_Client_connect___closed__1;
                v___x_2496_ = lean_uv_tcp_shutdown(v_s_2486_);
                if crate::leanh::lean_obj_tag(v___x_2496_) == 0 {
                    v_a_2497_ = crate::leanh::lean_ctor_get(v___x_2496_, 0);
                    v_isSharedCheck_2504_ = (!crate::leanh::lean_is_exclusive(v___x_2496_)) as u8;
                    if v_isSharedCheck_2504_ == 0 {
                        v___x_2499_ = v___x_2496_;
                        v_isShared_2500_ = v_isSharedCheck_2504_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2497_);
                        crate::leanh::lean_dec(v___x_2496_);
                        v___x_2499_ = crate::leanh::lean_box(0);
                        v_isShared_2500_ = v_isSharedCheck_2504_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_2505_ = crate::leanh::lean_ctor_get(v___x_2496_, 0);
                    v_isSharedCheck_2512_ = (!crate::leanh::lean_is_exclusive(v___x_2496_)) as u8;
                    if v_isSharedCheck_2512_ == 0 {
                        v___x_2507_ = v___x_2496_;
                        v_isShared_2508_ = v_isSharedCheck_2512_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2505_);
                        crate::leanh::lean_dec(v___x_2496_);
                        v___x_2507_ = crate::leanh::lean_box(0);
                        v_isShared_2508_ = v_isSharedCheck_2512_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2491_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2491_, 0, v_val_2490_);
                v___x_2492_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2492_, 0, v___x_2491_);
                v___x_2493_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2494_ = 0;
                v___x_2495_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_2493_,
                    v___x_2494_,
                    v___x_2492_,
                    v___f_2488_,
                );
                return v___x_2495_;
            }
            2 => {
                if v_isShared_2500_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2499_, 1);
                    v___x_2502_ = v___x_2499_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2503_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2503_, 0, v_a_2497_);
                    v___x_2502_ = v_reuseFailAlloc_2503_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_val_2490_ = v___x_2502_;
                state = 1;
                continue;
            }
            4 => {
                if v_isShared_2508_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2507_, 0);
                    v___x_2510_ = v___x_2507_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2511_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2511_, 0, v_a_2505_);
                    v___x_2510_ = v_reuseFailAlloc_2511_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_val_2490_ = v___x_2510_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_TCP_Socket_Client_shutdown___boxed(
    mut v_s_2513_: *mut crate::leanh::LeanObject,
    mut v_a_2514_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2515_ = l_Std_Async_TCP_Socket_Client_shutdown(v_s_2513_);
    crate::leanh::lean_dec(v_s_2513_);
    return v_res_2515_;
}
pub unsafe fn l_Std_Async_TCP_Socket_Client_getPeerName(
    mut v_s_2516_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2518_ = lean_uv_tcp_getpeername(v_s_2516_);
    return v___x_2518_;
}
pub unsafe fn l_Std_Async_TCP_Socket_Client_getPeerName___boxed(
    mut v_s_2519_: *mut crate::leanh::LeanObject,
    mut v_a_2520_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2521_ = l_Std_Async_TCP_Socket_Client_getPeerName(v_s_2519_);
    crate::leanh::lean_dec(v_s_2519_);
    return v_res_2521_;
}
pub unsafe fn l_Std_Async_TCP_Socket_Client_getSockName(
    mut v_s_2522_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2524_ = lean_uv_tcp_getsockname(v_s_2522_);
    return v___x_2524_;
}
pub unsafe fn l_Std_Async_TCP_Socket_Client_getSockName___boxed(
    mut v_s_2525_: *mut crate::leanh::LeanObject,
    mut v_a_2526_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2527_ = l_Std_Async_TCP_Socket_Client_getSockName(v_s_2525_);
    crate::leanh::lean_dec(v_s_2525_);
    return v_res_2527_;
}
pub unsafe fn l_Std_Async_TCP_Socket_Client_noDelay(
    mut v_s_2528_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2530_ = lean_uv_tcp_nodelay(v_s_2528_);
    return v___x_2530_;
}
pub unsafe fn l_Std_Async_TCP_Socket_Client_noDelay___boxed(
    mut v_s_2531_: *mut crate::leanh::LeanObject,
    mut v_a_2532_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2533_ = l_Std_Async_TCP_Socket_Client_noDelay(v_s_2531_);
    crate::leanh::lean_dec(v_s_2531_);
    return v_res_2533_;
}
pub unsafe fn _init_l_Std_Async_TCP_Socket_Client_keepAlive___auto__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2534_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__26),
        core::ptr::addr_of_mut!(
            l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__26_once
        ),
        _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1___closed__26,
    );
    return v___x_2534_;
}
pub unsafe fn l_Std_Async_TCP_Socket_Client_keepAlive___redArg(
    mut v_s_2535_: *mut crate::leanh::LeanObject,
    mut v_enable_2536_: u8,
    mut v_delay_2537_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2539_: u8 = 0;
    let mut v___x_2540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: u32 = 0;
    let mut v___x_2542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2539_ = lean_bool_to_int8(v_enable_2536_);
    v___x_2540_ = l_Int_toNat(v_delay_2537_);
    v___x_2541_ = lean_uint32_of_nat(v___x_2540_);
    crate::leanh::lean_dec(v___x_2540_);
    v___x_2542_ = lean_uv_tcp_keepalive(v_s_2535_, v___x_2539_, v___x_2541_);
    return v___x_2542_;
}
pub unsafe fn l_Std_Async_TCP_Socket_Client_keepAlive___redArg___boxed(
    mut v_s_2543_: *mut crate::leanh::LeanObject,
    mut v_enable_2544_: *mut crate::leanh::LeanObject,
    mut v_delay_2545_: *mut crate::leanh::LeanObject,
    mut v_a_2546_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_enable_boxed_2547_: u8 = 0;
    let mut v_res_2548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_enable_boxed_2547_ = (crate::leanh::lean_unbox(v_enable_2544_) as u8);
    v_res_2548_ = l_Std_Async_TCP_Socket_Client_keepAlive___redArg(
        v_s_2543_,
        v_enable_boxed_2547_,
        v_delay_2545_,
    );
    crate::leanh::lean_dec(v_delay_2545_);
    crate::leanh::lean_dec(v_s_2543_);
    return v_res_2548_;
}
pub unsafe fn l_Std_Async_TCP_Socket_Client_keepAlive(
    mut v_s_2549_: *mut crate::leanh::LeanObject,
    mut v_enable_2550_: u8,
    mut v_delay_2551_: *mut crate::leanh::LeanObject,
    mut v_x_2552_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2554_: u8 = 0;
    let mut v___x_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: u32 = 0;
    let mut v___x_2557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2554_ = lean_bool_to_int8(v_enable_2550_);
    v___x_2555_ = l_Int_toNat(v_delay_2551_);
    v___x_2556_ = lean_uint32_of_nat(v___x_2555_);
    crate::leanh::lean_dec(v___x_2555_);
    v___x_2557_ = lean_uv_tcp_keepalive(v_s_2549_, v___x_2554_, v___x_2556_);
    return v___x_2557_;
}
pub unsafe fn l_Std_Async_TCP_Socket_Client_keepAlive___boxed(
    mut v_s_2558_: *mut crate::leanh::LeanObject,
    mut v_enable_2559_: *mut crate::leanh::LeanObject,
    mut v_delay_2560_: *mut crate::leanh::LeanObject,
    mut v_x_2561_: *mut crate::leanh::LeanObject,
    mut v_a_2562_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_enable_boxed_2563_: u8 = 0;
    let mut v_res_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_enable_boxed_2563_ = (crate::leanh::lean_unbox(v_enable_2559_) as u8);
    v_res_2564_ = l_Std_Async_TCP_Socket_Client_keepAlive(
        v_s_2558_,
        v_enable_boxed_2563_,
        v_delay_2560_,
        v_x_2561_,
    );
    crate::leanh::lean_dec(v_delay_2560_);
    crate::leanh::lean_dec(v_s_2558_);
    return v_res_2564_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Async_TCP(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Time(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Internal_UV_TCP(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Async_Select(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Async_TCP(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    l_Std_Async_TCP_Socket_Server_keepAlive___auto__1 =
        _init_l_Std_Async_TCP_Socket_Server_keepAlive___auto__1();
    crate::leanh::lean_mark_persistent(l_Std_Async_TCP_Socket_Server_keepAlive___auto__1);
    l_Std_Async_TCP_Socket_Client_keepAlive___auto__1 =
        _init_l_Std_Async_TCP_Socket_Client_keepAlive___auto__1();
    crate::leanh::lean_mark_persistent(l_Std_Async_TCP_Socket_Client_keepAlive___auto__1);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Async_TCP(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Time(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Internal_UV_TCP(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Async_Select(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Async_TCP(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Async_TCP(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Async_TCP(builtin);
}
