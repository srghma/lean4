// Lean compiler output
// Module: Std.Http.Server
// Imports: Std.Async Std.Async.TCP Std.Sync.CancellationToken Std.Sync.Semaphore Std.Http.Server.Config Std.Http.Server.Handler Std.Http.Server.Connection
use crate::ffi::{
    lean_array_push, lean_io_as_task, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_eq, lean_nat_sub, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
    lean_task_map, lean_uv_tcp_bind, lean_uv_tcp_getpeername, lean_uv_tcp_getsockname,
    lean_uv_tcp_listen, lean_uv_tcp_new, lean_uv_tcp_nodelay,
};
use crate::r#gen::Init::Control::Except::l_Except_map;
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___aux__13___boxed;
use crate::r#gen::Init::Dynamic::l___private_Init_Dynamic_0__Dynamic_typeNameImpl;
use crate::r#gen::Init::Prelude::{
    l_instMonadLiftT___lam__0___boxed, l_instMonadLiftTOfMonadLift___redArg___lam__0,
};
use crate::r#gen::Init::System::Promise::l_IO_Promise_result_x21___redArg;
use crate::r#gen::Init::While::l___private_Init_While_0__whileM_erased___redArg;
use crate::r#gen::Std::Async::Basic::{
    l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask,
    l_Std_Async_BaseAsync_toRawBaseIO___boxed, l_Std_Async_EAsync_tryFinally_x27___redArg,
};
use crate::r#gen::Std::Async::ContextAsync::{
    l_Std_Async_ContextAsync_instMonad, l_Std_Async_ContextAsync_instMonadFinally___lam__1___boxed,
    l_Std_Async_ContextAsync_instMonadLiftBaseIO___lam__0___boxed,
};
use crate::r#gen::Std::Async::Select::l_Std_Async_Selectable_one___redArg;
use crate::r#gen::Std::Async::TCP::{
    initialize_Std_Async_TCP, l_Std_Async_TCP_Socket_Server_acceptSelector,
    runtime_initialize_Std_Async_TCP,
};
use crate::r#gen::Std::Async::{initialize_Std_Async, runtime_initialize_Std_Async};
use crate::r#gen::Std::Data::DTreeMap::Internal::Operations::l_Std_DTreeMap_Internal_Impl_insert___redArg;
use crate::r#gen::Std::Http::Data::Extensions::{
    l_Std_Http_Extensions_compareName___boxed, l_Std_Http_Extensions_empty,
};
use crate::r#gen::Std::Http::Server::Config::{
    initialize_Std_Http_Server_Config, runtime_initialize_Std_Http_Server_Config,
};
use crate::r#gen::Std::Http::Server::Connection::{
    initialize_Std_Http_Server_Connection,
    l_Std_Http_Server_instImpl_00___x40_Std_Http_Server_Connection_3058719504____hygCtx___hyg_8_,
    l_Std_Http_Server_serveConnection___boxed, runtime_initialize_Std_Http_Server_Connection,
};
use crate::r#gen::Std::Http::Server::Handler::{
    initialize_Std_Http_Server_Handler, runtime_initialize_Std_Http_Server_Handler,
};
use crate::r#gen::Std::Http::Transport::l_Std_Http_instTransportClient;
use crate::r#gen::Std::Sync::CancellationContext::{
    l_Std_CancellationContext_cancel, l_Std_CancellationContext_fork, l_Std_CancellationContext_new,
};
use crate::r#gen::Std::Sync::CancellationToken::{
    initialize_Std_Sync_CancellationToken, l_Std_CancellationToken_isCancelled,
    l_Std_CancellationToken_selector, runtime_initialize_Std_Sync_CancellationToken,
};
use crate::r#gen::Std::Sync::Channel::{
    l_Std_Channel_recv___redArg, l_Std_Channel_recvSelector___redArg, l_Std_Channel_send___redArg,
    l_Std_CloseableChannel_new___redArg,
};
use crate::r#gen::Std::Sync::Mutex::{l_Std_Mutex_atomically___redArg, l_Std_Mutex_new___redArg};
use crate::r#gen::Std::Sync::Semaphore::{
    initialize_Std_Sync_Semaphore, l_Std_Semaphore_acquire, l_Std_Semaphore_new,
    l_Std_Semaphore_release, runtime_initialize_Std_Sync_Semaphore,
};
pub static l_Std_Http_Server_waitShutdown___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Http_Server_waitShutdown___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Server_waitShutdown___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Server_waitShutdown___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Server_waitShutdown___closed__1_value: crate::leanh::LeanClosureObject<1> =
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
        m_fun: l_Std_Http_Server_waitShutdown___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_Server_waitShutdown___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Http_Server_waitShutdown___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Server_waitShutdown___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Std_Async_ContextAsync_instMonadLiftBaseIO___lam__0___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__2_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_instMonadLiftT___lam__0___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__3_value: crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2) as u16, other: 0, tag: 245 }, m_fun: l_instMonadLiftTOfMonadLift___redArg___lam__0 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 2, m_objs: [core::ptr::addr_of!(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__1_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__4_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Std_Async_ContextAsync_instMonadFinally___lam__1___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__5_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__1___boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__6_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__5___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__6_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Server_serve___redArg___lam__4___closed__0_value:
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
static mut l_Std_Http_Server_serve___redArg___lam__4___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Server_serve___redArg___lam__4___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Server_serve___redArg___lam__4___closed__1_value:
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
        core::ptr::addr_of!(l_Std_Http_Server_serve___redArg___lam__4___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Http_Server_serve___redArg___lam__4___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Server_serve___redArg___lam__4___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Http_Server_serve___redArg___lam__19___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Server_serve___redArg___lam__19___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Http_Server_serve___redArg___lam__19___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Server_serve___redArg___lam__19___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Http_Server_serve___redArg___lam__19___closed__2_value:
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
    m_fun: l_Std_Http_Extensions_compareName___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Server_serve___redArg___lam__19___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Server_serve___redArg___lam__19___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Server_serve___redArg___lam__28___closed__0_value:
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
    m_fun: l_Std_Http_Server_serve___redArg___lam__10___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Http_Server_serve___redArg___lam__28___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Server_serve___redArg___lam__28___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Server_serve___redArg___lam__28___closed__1_value:
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
    m_fun: l_Std_Http_Server_serve___redArg___lam__6___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Http_Server_serve___redArg___lam__28___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Server_serve___redArg___lam__28___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Server_serve___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Http_Server_serve___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Server_serve___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Server_serve___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Server_serve___redArg___closed__1_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Http_Server_serve___redArg___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Server_serve___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Server_serve___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Server_serve___redArg___closed__2_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Http_Server_serve___redArg___lam__3___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Server_serve___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Server_serve___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Server_serve___redArg___closed__3_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Http_Server_serve___redArg___lam__4___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Server_serve___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Server_serve___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Server_serve___redArg___closed__4_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Http_Server_serve___redArg___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Server_serve___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Server_serve___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Server_serve___redArg___closed__5_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Http_Server_serve___redArg___lam__5___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Server_serve___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Server_serve___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Std_Http_Server_new(
    mut v_config_1714_: *mut crate::leanh::LeanObject,
    mut v_localAddr_1715_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_connectionLimit_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxConnections_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: u8 = 0;
    let mut v___x_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1717_ = l_Std_CancellationContext_new();
                v___x_1718_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1719_ = l_Std_Mutex_new___redArg(v___x_1718_);
                v_maxConnections_1726_ = crate::leanh::lean_ctor_get(v_config_1714_, 0);
                v___x_1727_ = lean_nat_dec_eq(v_maxConnections_1726_, v___x_1718_);
                if v___x_1727_ == 0 {
                    crate::leanh::lean_inc(v_maxConnections_1726_);
                    v___x_1728_ = l_Std_Semaphore_new(v_maxConnections_1726_);
                    v___x_1729_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1729_, 0, v___x_1728_);
                    v_connectionLimit_1721_ = v___x_1729_;
                    state = 1;
                    continue;
                } else {
                    v___x_1730_ = crate::leanh::lean_box(0);
                    v_connectionLimit_1721_ = v___x_1730_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1722_ = crate::leanh::lean_box(0);
                v___x_1723_ = l_Std_CloseableChannel_new___redArg(v___x_1722_);
                v___x_1724_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1724_, 0, v___x_1717_);
                crate::leanh::lean_ctor_set(v___x_1724_, 1, v___x_1719_);
                crate::leanh::lean_ctor_set(v___x_1724_, 2, v_connectionLimit_1721_);
                crate::leanh::lean_ctor_set(v___x_1724_, 3, v___x_1723_);
                crate::leanh::lean_ctor_set(v___x_1724_, 4, v_config_1714_);
                crate::leanh::lean_ctor_set(v___x_1724_, 5, v_localAddr_1715_);
                v___x_1725_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1725_, 0, v___x_1724_);
                return v___x_1725_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Server_new___boxed(
    mut v_config_1731_: *mut crate::leanh::LeanObject,
    mut v_localAddr_1732_: *mut crate::leanh::LeanObject,
    mut v_a_1733_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1734_ = l_Std_Http_Server_new(v_config_1731_, v_localAddr_1732_);
    return v_res_1734_;
}
pub unsafe fn l_Std_Http_Server_shutdown(
    mut v_s_1735_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_context_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_context_1737_ = crate::leanh::lean_ctor_get(v_s_1735_, 0);
    crate::leanh::lean_inc_ref(v_context_1737_);
    crate::leanh::lean_dec_ref(v_s_1735_);
    v___x_1738_ = crate::leanh::lean_box(1);
    v___x_1739_ = l_Std_CancellationContext_cancel(v_context_1737_, v___x_1738_);
    v___x_1740_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1740_, 0, v___x_1739_);
    v___x_1741_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1741_, 0, v___x_1740_);
    return v___x_1741_;
}
pub unsafe fn l_Std_Http_Server_shutdown___boxed(
    mut v_s_1742_: *mut crate::leanh::LeanObject,
    mut v_a_1743_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1744_ = l_Std_Http_Server_shutdown(v_s_1742_);
    return v_res_1744_;
}
pub unsafe fn l_Std_Http_Server_waitShutdown___lam__0(
    mut v_a_1745_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1746_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1746_, 0, v_a_1745_);
    return v___x_1746_;
}
pub unsafe fn l_Std_Http_Server_waitShutdown___lam__1(
    mut v___f_1747_: *mut crate::leanh::LeanObject,
    mut v_x_1748_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1753_: u8 = 0;
    let mut v___x_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1758_: u8 = 0;
    let mut v_a_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: u8 = 0;
    let mut v___x_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1748_) == 0 {
                    crate::leanh::lean_dec_ref(v___f_1747_);
                    v_a_1750_ = crate::leanh::lean_ctor_get(v_x_1748_, 0);
                    v_isSharedCheck_1758_ = (!crate::leanh::lean_is_exclusive(v_x_1748_)) as u8;
                    if v_isSharedCheck_1758_ == 0 {
                        v___x_1752_ = v_x_1748_;
                        v_isShared_1753_ = v_isSharedCheck_1758_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1750_);
                        crate::leanh::lean_dec(v_x_1748_);
                        v___x_1752_ = crate::leanh::lean_box(0);
                        v_isShared_1753_ = v_isSharedCheck_1758_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1759_ = crate::leanh::lean_ctor_get(v_x_1748_, 0);
                    crate::leanh::lean_inc(v_a_1759_);
                    crate::leanh::lean_dec_ref_known(v_x_1748_, 1);
                    v___x_1760_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1761_ = 0;
                    v___x_1762_ = lean_task_map(v___f_1747_, v_a_1759_, v___x_1760_, v___x_1761_);
                    v___x_1763_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1763_, 0, v___x_1762_);
                    return v___x_1763_;
                }
            }
            1 => {
                if v_isShared_1753_ == 0 {
                    v___x_1755_ = v___x_1752_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1757_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1757_, 0, v_a_1750_);
                    v___x_1755_ = v_reuseFailAlloc_1757_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1756_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1756_, 0, v___x_1755_);
                return v___x_1756_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Server_waitShutdown___lam__1___boxed(
    mut v___f_1764_: *mut crate::leanh::LeanObject,
    mut v_x_1765_: *mut crate::leanh::LeanObject,
    mut v___y_1766_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1767_ = l_Std_Http_Server_waitShutdown___lam__1(v___f_1764_, v_x_1765_);
    return v_res_1767_;
}
pub unsafe fn l_Std_Http_Server_waitShutdown(
    mut v_s_1771_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_shutdownPromise_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: u8 = 0;
    let mut v___x_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_shutdownPromise_1773_ = crate::leanh::lean_ctor_get(v_s_1771_, 3);
    crate::leanh::lean_inc_ref(v_shutdownPromise_1773_);
    crate::leanh::lean_dec_ref(v_s_1771_);
    v___x_1774_ = crate::leanh::lean_box(0);
    v___x_1775_ = l_Std_Channel_recv___redArg(v___x_1774_, v_shutdownPromise_1773_);
    v___f_1776_ = l_Std_Http_Server_waitShutdown___closed__1;
    v___x_1777_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1777_, 0, v___x_1775_);
    v___x_1778_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1778_, 0, v___x_1777_);
    v___x_1779_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1780_ = 0;
    v___x_1781_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1779_,
        v___x_1780_,
        v___x_1778_,
        v___f_1776_,
    );
    return v___x_1781_;
}
pub unsafe fn l_Std_Http_Server_waitShutdown___boxed(
    mut v_s_1782_: *mut crate::leanh::LeanObject,
    mut v_a_1783_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1784_ = l_Std_Http_Server_waitShutdown(v_s_1782_);
    return v_res_1784_;
}
pub unsafe fn l_Std_Http_Server_waitShutdownSelector(
    mut v_s_1785_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_shutdownPromise_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_shutdownPromise_1786_ = crate::leanh::lean_ctor_get(v_s_1785_, 3);
    crate::leanh::lean_inc_ref(v_shutdownPromise_1786_);
    crate::leanh::lean_dec_ref(v_s_1785_);
    v___x_1787_ = crate::leanh::lean_box(0);
    v___x_1788_ = l_Std_Channel_recvSelector___redArg(v___x_1787_, v_shutdownPromise_1786_);
    return v___x_1788_;
}
pub unsafe fn l_Std_Http_Server_shutdownAndWait___lam__2(
    mut v_shutdownPromise_1789_: *mut crate::leanh::LeanObject,
    mut v___f_1790_: *mut crate::leanh::LeanObject,
    mut v_x_1791_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1796_: u8 = 0;
    let mut v___x_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: u8 = 0;
    let mut v___x_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1806_: u8 = 0;
    let mut v_unused_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1791_) == 0 {
                    crate::leanh::lean_dec_ref(v___f_1790_);
                    crate::leanh::lean_dec_ref(v_shutdownPromise_1789_);
                    v___x_1793_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1793_, 0, v_x_1791_);
                    return v___x_1793_;
                } else {
                    v_isSharedCheck_1806_ = (!crate::leanh::lean_is_exclusive(v_x_1791_)) as u8;
                    if v_isSharedCheck_1806_ == 0 {
                        v_unused_1807_ = crate::leanh::lean_ctor_get(v_x_1791_, 0);
                        crate::leanh::lean_dec(v_unused_1807_);
                        v___x_1795_ = v_x_1791_;
                        v_isShared_1796_ = v_isSharedCheck_1806_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_x_1791_);
                        v___x_1795_ = crate::leanh::lean_box(0);
                        v_isShared_1796_ = v_isSharedCheck_1806_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1797_ = crate::leanh::lean_box(0);
                v___x_1798_ = l_Std_Channel_recv___redArg(v___x_1797_, v_shutdownPromise_1789_);
                if v_isShared_1796_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1795_, 0, v___x_1798_);
                    v___x_1800_ = v___x_1795_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1805_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1805_, 0, v___x_1798_);
                    v___x_1800_ = v_reuseFailAlloc_1805_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1801_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1801_, 0, v___x_1800_);
                v___x_1802_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1803_ = 0;
                v___x_1804_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_1802_,
                    v___x_1803_,
                    v___x_1801_,
                    v___f_1790_,
                );
                return v___x_1804_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Server_shutdownAndWait___lam__2___boxed(
    mut v_shutdownPromise_1808_: *mut crate::leanh::LeanObject,
    mut v___f_1809_: *mut crate::leanh::LeanObject,
    mut v_x_1810_: *mut crate::leanh::LeanObject,
    mut v___y_1811_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1812_ =
        l_Std_Http_Server_shutdownAndWait___lam__2(v_shutdownPromise_1808_, v___f_1809_, v_x_1810_);
    return v_res_1812_;
}
pub unsafe fn l_Std_Http_Server_shutdownAndWait(
    mut v_s_1813_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_context_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_shutdownPromise_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: u8 = 0;
    let mut v___x_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_context_1815_ = crate::leanh::lean_ctor_get(v_s_1813_, 0);
    crate::leanh::lean_inc_ref(v_context_1815_);
    v_shutdownPromise_1816_ = crate::leanh::lean_ctor_get(v_s_1813_, 3);
    crate::leanh::lean_inc_ref(v_shutdownPromise_1816_);
    crate::leanh::lean_dec_ref(v_s_1813_);
    v___x_1817_ = crate::leanh::lean_box(1);
    v___x_1818_ = l_Std_CancellationContext_cancel(v_context_1815_, v___x_1817_);
    v___f_1819_ = l_Std_Http_Server_waitShutdown___closed__1;
    v___f_1820_ = crate::leanh::lean_alloc_closure(
        l_Std_Http_Server_shutdownAndWait___lam__2___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1820_, 0, v_shutdownPromise_1816_);
    crate::leanh::lean_closure_set(v___f_1820_, 1, v___f_1819_);
    v___x_1821_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1821_, 0, v___x_1818_);
    v___x_1822_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1822_, 0, v___x_1821_);
    v___x_1823_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1824_ = 0;
    v___x_1825_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1823_,
        v___x_1824_,
        v___x_1822_,
        v___f_1820_,
    );
    return v___x_1825_;
}
pub unsafe fn l_Std_Http_Server_shutdownAndWait___boxed(
    mut v_s_1826_: *mut crate::leanh::LeanObject,
    mut v_a_1827_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1828_ = l_Std_Http_Server_shutdownAndWait(v_s_1826_);
    return v_res_1828_;
}
pub unsafe fn l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0(
    mut v___y_1833_: *mut crate::leanh::LeanObject,
    mut v___y_1834_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1836_ = lean_st_ref_take(v___y_1833_);
    v___x_1837_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_1838_ = lean_nat_add(v___x_1836_, v___x_1837_);
    crate::leanh::lean_dec(v___x_1836_);
    v___x_1839_ = lean_st_ref_set(v___y_1833_, v___x_1838_);
    v___x_1840_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__1;
    return v___x_1840_;
}
pub unsafe fn l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___boxed(
    mut v___y_1841_: *mut crate::leanh::LeanObject,
    mut v___y_1842_: *mut crate::leanh::LeanObject,
    mut v___y_1843_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1844_ =
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0(
            v___y_1841_,
            v___y_1842_,
        );
    crate::leanh::lean_dec_ref(v___y_1842_);
    crate::leanh::lean_dec(v___y_1841_);
    return v_res_1844_;
}
pub unsafe fn l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__1(
    mut v___y_1845_: *mut crate::leanh::LeanObject,
    mut v___y_1846_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1848_ = lean_st_ref_take(v___y_1845_);
    v___x_1849_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_1850_ = lean_nat_sub(v___x_1848_, v___x_1849_);
    crate::leanh::lean_dec(v___x_1848_);
    v___x_1851_ = lean_st_ref_set(v___y_1845_, v___x_1850_);
    v___x_1852_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__1;
    return v___x_1852_;
}
pub unsafe fn l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__1___boxed(
    mut v___y_1853_: *mut crate::leanh::LeanObject,
    mut v___y_1854_: *mut crate::leanh::LeanObject,
    mut v___y_1855_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1856_ =
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__1(
            v___y_1853_,
            v___y_1854_,
        );
    crate::leanh::lean_dec_ref(v___y_1854_);
    crate::leanh::lean_dec(v___y_1853_);
    return v_res_1856_;
}
pub unsafe fn l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__2(
    mut v_a_1857_: *mut crate::leanh::LeanObject,
    mut v_shutdownPromise_1858_: *mut crate::leanh::LeanObject,
    mut v_x_1859_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1866_: u8 = 0;
    let mut v___x_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1871_: u8 = 0;
    let mut v_a_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: u8 = 0;
    let mut v___x_1875_: u8 = 0;
    let mut v___x_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1859_) == 0 {
                    crate::leanh::lean_dec_ref(v_shutdownPromise_1858_);
                    v_a_1863_ = crate::leanh::lean_ctor_get(v_x_1859_, 0);
                    v_isSharedCheck_1871_ = (!crate::leanh::lean_is_exclusive(v_x_1859_)) as u8;
                    if v_isSharedCheck_1871_ == 0 {
                        v___x_1865_ = v_x_1859_;
                        v_isShared_1866_ = v_isSharedCheck_1871_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1863_);
                        crate::leanh::lean_dec(v_x_1859_);
                        v___x_1865_ = crate::leanh::lean_box(0);
                        v_isShared_1866_ = v_isSharedCheck_1871_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_1872_ = crate::leanh::lean_ctor_get(v_x_1859_, 0);
                    crate::leanh::lean_inc(v_a_1872_);
                    crate::leanh::lean_dec_ref_known(v_x_1859_, 1);
                    v___x_1873_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1874_ = lean_nat_dec_eq(v_a_1857_, v___x_1873_);
                    if v___x_1874_ == 0 {
                        crate::leanh::lean_dec(v_a_1872_);
                        crate::leanh::lean_dec_ref(v_shutdownPromise_1858_);
                        state = 1;
                        continue;
                    } else {
                        v___x_1875_ = (crate::leanh::lean_unbox(v_a_1872_) as u8);
                        crate::leanh::lean_dec(v_a_1872_);
                        if v___x_1875_ == 0 {
                            crate::leanh::lean_dec_ref(v_shutdownPromise_1858_);
                            state = 1;
                            continue;
                        } else {
                            v___x_1876_ = crate::leanh::lean_box(0);
                            v___x_1877_ =
                                l_Std_Channel_send___redArg(v_shutdownPromise_1858_, v___x_1876_);
                            crate::leanh::lean_dec_ref(v___x_1877_);
                            v___x_1878_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__1;
                            return v___x_1878_;
                        }
                    }
                }
            }
            1 => {
                v___x_1862_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__1;
                return v___x_1862_;
            }
            2 => {
                if v_isShared_1866_ == 0 {
                    v___x_1868_ = v___x_1865_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1870_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1870_, 0, v_a_1863_);
                    v___x_1868_ = v_reuseFailAlloc_1870_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1869_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1869_, 0, v___x_1868_);
                return v___x_1869_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__2___boxed(
    mut v_a_1879_: *mut crate::leanh::LeanObject,
    mut v_shutdownPromise_1880_: *mut crate::leanh::LeanObject,
    mut v_x_1881_: *mut crate::leanh::LeanObject,
    mut v___y_1882_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1883_ =
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__2(
            v_a_1879_,
            v_shutdownPromise_1880_,
            v_x_1881_,
        );
    crate::leanh::lean_dec(v_a_1879_);
    return v_res_1883_;
}
pub unsafe fn l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__3(
    mut v_context_1884_: *mut crate::leanh::LeanObject,
    mut v_shutdownPromise_1885_: *mut crate::leanh::LeanObject,
    mut v_x_1886_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1891_: u8 = 0;
    let mut v___x_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1896_: u8 = 0;
    let mut v_a_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1900_: u8 = 0;
    let mut v_token_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: u8 = 0;
    let mut v___f_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: u8 = 0;
    let mut v___x_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1912_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1886_) == 0 {
                    crate::leanh::lean_dec_ref(v_shutdownPromise_1885_);
                    crate::leanh::lean_dec_ref(v_context_1884_);
                    v_a_1888_ = crate::leanh::lean_ctor_get(v_x_1886_, 0);
                    v_isSharedCheck_1896_ = (!crate::leanh::lean_is_exclusive(v_x_1886_)) as u8;
                    if v_isSharedCheck_1896_ == 0 {
                        v___x_1890_ = v_x_1886_;
                        v_isShared_1891_ = v_isSharedCheck_1896_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1888_);
                        crate::leanh::lean_dec(v_x_1886_);
                        v___x_1890_ = crate::leanh::lean_box(0);
                        v_isShared_1891_ = v_isSharedCheck_1896_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1897_ = crate::leanh::lean_ctor_get(v_x_1886_, 0);
                    v_isSharedCheck_1912_ = (!crate::leanh::lean_is_exclusive(v_x_1886_)) as u8;
                    if v_isSharedCheck_1912_ == 0 {
                        v___x_1899_ = v_x_1886_;
                        v_isShared_1900_ = v_isSharedCheck_1912_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1897_);
                        crate::leanh::lean_dec(v_x_1886_);
                        v___x_1899_ = crate::leanh::lean_box(0);
                        v_isShared_1900_ = v_isSharedCheck_1912_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1891_ == 0 {
                    v___x_1893_ = v___x_1890_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1895_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1895_, 0, v_a_1888_);
                    v___x_1893_ = v_reuseFailAlloc_1895_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1894_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1894_, 0, v___x_1893_);
                return v___x_1894_;
            }
            3 => {
                v_token_1901_ = crate::leanh::lean_ctor_get(v_context_1884_, 1);
                crate::leanh::lean_inc_ref(v_token_1901_);
                crate::leanh::lean_dec_ref(v_context_1884_);
                v___x_1902_ = l_Std_CancellationToken_isCancelled(v_token_1901_);
                v___f_1903_ = crate::leanh::lean_alloc_closure(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__2___boxed as *mut core::ffi::c_void, 4, 2);
                crate::leanh::lean_closure_set(v___f_1903_, 0, v_a_1897_);
                crate::leanh::lean_closure_set(v___f_1903_, 1, v_shutdownPromise_1885_);
                v___x_1904_ = crate::leanh::lean_box((v___x_1902_) as usize);
                if v_isShared_1900_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1899_, 0, v___x_1904_);
                    v___x_1906_ = v___x_1899_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1911_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1911_, 0, v___x_1904_);
                    v___x_1906_ = v_reuseFailAlloc_1911_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1907_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1907_, 0, v___x_1906_);
                v___x_1908_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1909_ = 0;
                v___x_1910_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_1908_,
                    v___x_1909_,
                    v___x_1907_,
                    v___f_1903_,
                );
                return v___x_1910_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__3___boxed(
    mut v_context_1913_: *mut crate::leanh::LeanObject,
    mut v_shutdownPromise_1914_: *mut crate::leanh::LeanObject,
    mut v_x_1915_: *mut crate::leanh::LeanObject,
    mut v___y_1916_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1917_ =
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__3(
            v_context_1913_,
            v_shutdownPromise_1914_,
            v_x_1915_,
        );
    return v_res_1917_;
}
pub unsafe fn l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__4(
    mut v___f_1918_: *mut crate::leanh::LeanObject,
    mut v_____r_1919_: *mut crate::leanh::LeanObject,
    mut v___y_1920_: *mut crate::leanh::LeanObject,
    mut v___y_1921_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: u8 = 0;
    let mut v___x_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1923_ = lean_st_ref_get(v___y_1920_);
    v___x_1924_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1924_, 0, v___x_1923_);
    v___x_1925_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1925_, 0, v___x_1924_);
    v___x_1926_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1927_ = 0;
    v___x_1928_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1926_,
        v___x_1927_,
        v___x_1925_,
        v___f_1918_,
    );
    return v___x_1928_;
}
pub unsafe fn l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__4___boxed(
    mut v___f_1929_: *mut crate::leanh::LeanObject,
    mut v_____r_1930_: *mut crate::leanh::LeanObject,
    mut v___y_1931_: *mut crate::leanh::LeanObject,
    mut v___y_1932_: *mut crate::leanh::LeanObject,
    mut v___y_1933_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1934_ =
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__4(
            v___f_1929_,
            v_____r_1930_,
            v___y_1931_,
            v___y_1932_,
        );
    crate::leanh::lean_dec_ref(v___y_1932_);
    crate::leanh::lean_dec(v___y_1931_);
    return v_res_1934_;
}
pub unsafe fn l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__5(
    mut v_x_1935_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_1936_ = crate::leanh::lean_ctor_get(v_x_1935_, 0);
    crate::leanh::lean_inc(v_fst_1936_);
    return v_fst_1936_;
}
pub unsafe fn l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__5___boxed(
    mut v_x_1937_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1938_ =
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__5(
            v_x_1937_,
        );
    crate::leanh::lean_dec_ref(v_x_1937_);
    return v_res_1938_;
}
pub unsafe fn l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__6(
    mut v___x_1939_: *mut crate::leanh::LeanObject,
    mut v___f_1940_: *mut crate::leanh::LeanObject,
    mut v___f_1941_: *mut crate::leanh::LeanObject,
    mut v___f_1942_: *mut crate::leanh::LeanObject,
    mut v___f_1943_: *mut crate::leanh::LeanObject,
    mut v_activeConnections_1944_: *mut crate::leanh::LeanObject,
    mut v_____r_1945_: *mut crate::leanh::LeanObject,
    mut v___y_1946_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2353__overap_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v___x_1939_);
    v___x_1948_ = crate::leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonad___aux__13___boxed as *mut core::ffi::c_void,
        9,
        8,
    );
    crate::leanh::lean_closure_set(v___x_1948_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1948_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1948_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1948_, 3, v___x_1939_);
    crate::leanh::lean_closure_set(v___x_1948_, 4, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1948_, 5, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1948_, 6, v___f_1940_);
    crate::leanh::lean_closure_set(v___x_1948_, 7, v___f_1941_);
    v___x_2353__overap_1949_ = l_Std_Mutex_atomically___redArg(
        v___x_1939_,
        v___f_1942_,
        v___f_1943_,
        v_activeConnections_1944_,
        v___x_1948_,
    );
    crate::leanh::lean_inc_ref(v___y_1946_);
    v___x_1950_ = crate::leanh::lean_apply_2(
        v___x_2353__overap_1949_,
        v___y_1946_,
        crate::leanh::lean_box(0),
    );
    return v___x_1950_;
}
pub unsafe fn l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__6___boxed(
    mut v___x_1951_: *mut crate::leanh::LeanObject,
    mut v___f_1952_: *mut crate::leanh::LeanObject,
    mut v___f_1953_: *mut crate::leanh::LeanObject,
    mut v___f_1954_: *mut crate::leanh::LeanObject,
    mut v___f_1955_: *mut crate::leanh::LeanObject,
    mut v_activeConnections_1956_: *mut crate::leanh::LeanObject,
    mut v_____r_1957_: *mut crate::leanh::LeanObject,
    mut v___y_1958_: *mut crate::leanh::LeanObject,
    mut v___y_1959_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1960_ =
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__6(
            v___x_1951_,
            v___f_1952_,
            v___f_1953_,
            v___f_1954_,
            v___f_1955_,
            v_activeConnections_1956_,
            v_____r_1957_,
            v___y_1958_,
        );
    crate::leanh::lean_dec_ref(v___y_1958_);
    return v_res_1960_;
}
pub unsafe fn l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__7(
    mut v___f_1961_: *mut crate::leanh::LeanObject,
    mut v_a_1962_: *mut crate::leanh::LeanObject,
    mut v_x_1963_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1963_) == 0 {
        let mut v___x_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v___f_1961_);
        v___x_1965_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1965_, 0, v_x_1963_);
        return v___x_1965_;
    } else {
        let mut v_a_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_1966_ = crate::leanh::lean_ctor_get(v_x_1963_, 0);
        crate::leanh::lean_inc(v_a_1966_);
        crate::leanh::lean_dec_ref_known(v_x_1963_, 1);
        crate::leanh::lean_inc_ref(v_a_1962_);
        v___x_1967_ = crate::leanh::lean_apply_3(
            v___f_1961_,
            v_a_1966_,
            v_a_1962_,
            crate::leanh::lean_box(0),
        );
        return v___x_1967_;
    }
}
pub unsafe fn l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__7___boxed(
    mut v___f_1968_: *mut crate::leanh::LeanObject,
    mut v_a_1969_: *mut crate::leanh::LeanObject,
    mut v_x_1970_: *mut crate::leanh::LeanObject,
    mut v___y_1971_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1972_ =
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__7(
            v___f_1968_,
            v_a_1969_,
            v_x_1970_,
        );
    crate::leanh::lean_dec_ref(v_a_1969_);
    return v_res_1972_;
}
pub unsafe fn l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__8(
    mut v_releaseConnectionPermit_1973_: u8,
    mut v___f_1974_: *mut crate::leanh::LeanObject,
    mut v_a_1975_: *mut crate::leanh::LeanObject,
    mut v_connectionLimit_1976_: *mut crate::leanh::LeanObject,
    mut v___f_1977_: *mut crate::leanh::LeanObject,
    mut v_opt_1978_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1985_: u8 = 0;
    let mut v___x_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: u8 = 0;
    let mut v___x_1992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1994_: u8 = 0;
    let mut v___x_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_releaseConnectionPermit_1973_ == 0 {
                    crate::leanh::lean_dec_ref(v___f_1977_);
                    crate::leanh::lean_dec(v_connectionLimit_1976_);
                    v___x_1980_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc_ref(v_a_1975_);
                    v___x_1981_ = crate::leanh::lean_apply_3(
                        v___f_1974_,
                        v___x_1980_,
                        v_a_1975_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_1981_;
                } else {
                    if crate::leanh::lean_obj_tag(v_connectionLimit_1976_) == 1 {
                        crate::leanh::lean_dec_ref(v___f_1974_);
                        v_val_1982_ = crate::leanh::lean_ctor_get(v_connectionLimit_1976_, 0);
                        v_isSharedCheck_1994_ =
                            (!crate::leanh::lean_is_exclusive(v_connectionLimit_1976_)) as u8;
                        if v_isSharedCheck_1994_ == 0 {
                            v___x_1984_ = v_connectionLimit_1976_;
                            v_isShared_1985_ = v_isSharedCheck_1994_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_1982_);
                            crate::leanh::lean_dec(v_connectionLimit_1976_);
                            v___x_1984_ = crate::leanh::lean_box(0);
                            v_isShared_1985_ = v_isSharedCheck_1994_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___f_1977_);
                        crate::leanh::lean_dec(v_connectionLimit_1976_);
                        v___x_1995_ = crate::leanh::lean_box(0);
                        crate::leanh::lean_inc_ref(v_a_1975_);
                        v___x_1996_ = crate::leanh::lean_apply_3(
                            v___f_1974_,
                            v___x_1995_,
                            v_a_1975_,
                            crate::leanh::lean_box(0),
                        );
                        return v___x_1996_;
                    }
                }
            }
            1 => {
                v___x_1986_ = l_Std_Semaphore_release(v_val_1982_);
                if v_isShared_1985_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1984_, 0, v___x_1986_);
                    v___x_1988_ = v___x_1984_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1993_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1993_, 0, v___x_1986_);
                    v___x_1988_ = v_reuseFailAlloc_1993_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1989_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1989_, 0, v___x_1988_);
                v___x_1990_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1991_ = 0;
                v___x_1992_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_1990_,
                    v___x_1991_,
                    v___x_1989_,
                    v___f_1977_,
                );
                return v___x_1992_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__8___boxed(
    mut v_releaseConnectionPermit_1997_: *mut crate::leanh::LeanObject,
    mut v___f_1998_: *mut crate::leanh::LeanObject,
    mut v_a_1999_: *mut crate::leanh::LeanObject,
    mut v_connectionLimit_2000_: *mut crate::leanh::LeanObject,
    mut v___f_2001_: *mut crate::leanh::LeanObject,
    mut v_opt_2002_: *mut crate::leanh::LeanObject,
    mut v___y_2003_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_releaseConnectionPermit_boxed_2004_: u8 = 0;
    let mut v_res_2005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_releaseConnectionPermit_boxed_2004_ =
        (crate::leanh::lean_unbox(v_releaseConnectionPermit_1997_) as u8);
    v_res_2005_ =
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__8(
            v_releaseConnectionPermit_boxed_2004_,
            v___f_1998_,
            v_a_1999_,
            v_connectionLimit_2000_,
            v___f_2001_,
            v_opt_2002_,
        );
    crate::leanh::lean_dec(v_opt_2002_);
    crate::leanh::lean_dec_ref(v_a_1999_);
    return v_res_2005_;
}
pub unsafe fn l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__9(
    mut v_action_2006_: *mut crate::leanh::LeanObject,
    mut v_a_2007_: *mut crate::leanh::LeanObject,
    mut v___f_2008_: *mut crate::leanh::LeanObject,
    mut v___f_2009_: *mut crate::leanh::LeanObject,
    mut v_x_2010_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2015_: u8 = 0;
    let mut v___x_2017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2020_: u8 = 0;
    let mut v___x_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: u8 = 0;
    let mut v___x_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2032_: u8 = 0;
    let mut v___x_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2036_: u8 = 0;
    let mut v_a_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2040_: u8 = 0;
    let mut v_fst_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2045_: u8 = 0;
    let mut v_a_2046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2049_: u8 = 0;
    let mut v___x_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2055_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2010_) == 0 {
                    crate::leanh::lean_dec(v___f_2009_);
                    crate::leanh::lean_dec_ref(v___f_2008_);
                    crate::leanh::lean_dec_ref(v_action_2006_);
                    v_a_2012_ = crate::leanh::lean_ctor_get(v_x_2010_, 0);
                    v_isSharedCheck_2020_ = (!crate::leanh::lean_is_exclusive(v_x_2010_)) as u8;
                    if v_isSharedCheck_2020_ == 0 {
                        v___x_2014_ = v_x_2010_;
                        v_isShared_2015_ = v_isSharedCheck_2020_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2012_);
                        crate::leanh::lean_dec(v_x_2010_);
                        v___x_2014_ = crate::leanh::lean_box(0);
                        v_isShared_2015_ = v_isSharedCheck_2020_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v_x_2010_, 1);
                    crate::leanh::lean_inc_ref(v_a_2007_);
                    v___x_2021_ = crate::leanh::lean_apply_1(v_action_2006_, v_a_2007_);
                    v___x_2022_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2023_ = 0;
                    v___x_2024_ = l_Std_Async_EAsync_tryFinally_x27___redArg(
                        v___x_2021_,
                        v___f_2008_,
                        v___x_2022_,
                        v___x_2023_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2024_) == 0 {
                        crate::leanh::lean_dec(v___f_2009_);
                        v_a_2028_ = crate::leanh::lean_ctor_get(v___x_2024_, 0);
                        crate::leanh::lean_inc(v_a_2028_);
                        crate::leanh::lean_dec_ref_known(v___x_2024_, 1);
                        if crate::leanh::lean_obj_tag(v_a_2028_) == 0 {
                            v_a_2029_ = crate::leanh::lean_ctor_get(v_a_2028_, 0);
                            v_isSharedCheck_2036_ =
                                (!crate::leanh::lean_is_exclusive(v_a_2028_)) as u8;
                            if v_isSharedCheck_2036_ == 0 {
                                v___x_2031_ = v_a_2028_;
                                v_isShared_2032_ = v_isSharedCheck_2036_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2029_);
                                crate::leanh::lean_dec(v_a_2028_);
                                v___x_2031_ = crate::leanh::lean_box(0);
                                v_isShared_2032_ = v_isSharedCheck_2036_;
                                state = 4;
                                continue;
                            }
                        } else {
                            v_a_2037_ = crate::leanh::lean_ctor_get(v_a_2028_, 0);
                            v_isSharedCheck_2045_ =
                                (!crate::leanh::lean_is_exclusive(v_a_2028_)) as u8;
                            if v_isSharedCheck_2045_ == 0 {
                                v___x_2039_ = v_a_2028_;
                                v_isShared_2040_ = v_isSharedCheck_2045_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2037_);
                                crate::leanh::lean_dec(v_a_2028_);
                                v___x_2039_ = crate::leanh::lean_box(0);
                                v_isShared_2040_ = v_isSharedCheck_2045_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        v_a_2046_ = crate::leanh::lean_ctor_get(v___x_2024_, 0);
                        v_isSharedCheck_2055_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2024_)) as u8;
                        if v_isSharedCheck_2055_ == 0 {
                            v___x_2048_ = v___x_2024_;
                            v_isShared_2049_ = v_isSharedCheck_2055_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2046_);
                            crate::leanh::lean_dec(v___x_2024_);
                            v___x_2048_ = crate::leanh::lean_box(0);
                            v_isShared_2049_ = v_isSharedCheck_2055_;
                            state = 8;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_2015_ == 0 {
                    v___x_2017_ = v___x_2014_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2019_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2019_, 0, v_a_2012_);
                    v___x_2017_ = v_reuseFailAlloc_2019_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2018_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2018_, 0, v___x_2017_);
                return v___x_2018_;
            }
            3 => {
                v___x_2027_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2027_, 0, v___y_2026_);
                return v___x_2027_;
            }
            4 => {
                if v_isShared_2032_ == 0 {
                    v___x_2034_ = v___x_2031_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2035_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_a_2029_);
                    v___x_2034_ = v_reuseFailAlloc_2035_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___y_2026_ = v___x_2034_;
                state = 3;
                continue;
            }
            6 => {
                v_fst_2041_ = crate::leanh::lean_ctor_get(v_a_2037_, 0);
                crate::leanh::lean_inc(v_fst_2041_);
                crate::leanh::lean_dec(v_a_2037_);
                if v_isShared_2040_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2039_, 0, v_fst_2041_);
                    v___x_2043_ = v___x_2039_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2044_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2044_, 0, v_fst_2041_);
                    v___x_2043_ = v_reuseFailAlloc_2044_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_2026_ = v___x_2043_;
                state = 3;
                continue;
            }
            8 => {
                v___x_2050_ =
                    crate::leanh::lean_alloc_closure(l_Except_map as *mut core::ffi::c_void, 5, 4);
                crate::leanh::lean_closure_set(v___x_2050_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_2050_, 1, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_2050_, 2, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_2050_, 3, v___f_2009_);
                v___x_2051_ = lean_task_map(v___x_2050_, v_a_2046_, v___x_2022_, v___x_2023_);
                if v_isShared_2049_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2048_, 0, v___x_2051_);
                    v___x_2053_ = v___x_2048_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2054_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2054_, 0, v___x_2051_);
                    v___x_2053_ = v_reuseFailAlloc_2054_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2053_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__9___boxed(
    mut v_action_2056_: *mut crate::leanh::LeanObject,
    mut v_a_2057_: *mut crate::leanh::LeanObject,
    mut v___f_2058_: *mut crate::leanh::LeanObject,
    mut v___f_2059_: *mut crate::leanh::LeanObject,
    mut v_x_2060_: *mut crate::leanh::LeanObject,
    mut v___y_2061_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2062_ =
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__9(
            v_action_2056_,
            v_a_2057_,
            v___f_2058_,
            v___f_2059_,
            v_x_2060_,
        );
    crate::leanh::lean_dec_ref(v_a_2057_);
    return v_res_2062_;
}
pub unsafe fn l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg(
    mut v_s_2072_: *mut crate::leanh::LeanObject,
    mut v_releaseConnectionPermit_2073_: u8,
    mut v_action_2074_: *mut crate::leanh::LeanObject,
    mut v_a_2075_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_context_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_activeConnections_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_connectionLimit_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_shutdownPromise_2081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520__overap_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: u8 = 0;
    let mut v___x_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2077_ = l_Std_Async_ContextAsync_instMonad;
    v_context_2078_ = crate::leanh::lean_ctor_get(v_s_2072_, 0);
    crate::leanh::lean_inc_ref(v_context_2078_);
    v_activeConnections_2079_ = crate::leanh::lean_ctor_get(v_s_2072_, 1);
    crate::leanh::lean_inc_ref_n(v_activeConnections_2079_, 2);
    v_connectionLimit_2080_ = crate::leanh::lean_ctor_get(v_s_2072_, 2);
    crate::leanh::lean_inc(v_connectionLimit_2080_);
    v_shutdownPromise_2081_ = crate::leanh::lean_ctor_get(v_s_2072_, 3);
    crate::leanh::lean_inc_ref(v_shutdownPromise_2081_);
    crate::leanh::lean_dec_ref(v_s_2072_);
    v___f_2082_ =
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__0;
    v___f_2083_ =
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__3;
    v___f_2084_ =
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__4;
    v___x_1520__overap_2085_ = l_Std_Mutex_atomically___redArg(
        v___x_2077_,
        v___f_2083_,
        v___f_2084_,
        v_activeConnections_2079_,
        v___f_2082_,
    );
    crate::leanh::lean_inc_ref_n(v_a_2075_, 4);
    v___x_2086_ = crate::leanh::lean_apply_2(
        v___x_1520__overap_2085_,
        v_a_2075_,
        crate::leanh::lean_box(0),
    );
    v___f_2087_ =
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__5;
    v___f_2088_ = crate::leanh::lean_alloc_closure(
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__3___boxed
            as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2088_, 0, v_context_2078_);
    crate::leanh::lean_closure_set(v___f_2088_, 1, v_shutdownPromise_2081_);
    v___f_2089_ = crate::leanh::lean_alloc_closure(
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__4___boxed
            as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2089_, 0, v___f_2088_);
    v___f_2090_ =
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__6;
    v___f_2091_ = crate::leanh::lean_alloc_closure(
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__6___boxed
            as *mut core::ffi::c_void,
        9,
        6,
    );
    crate::leanh::lean_closure_set(v___f_2091_, 0, v___x_2077_);
    crate::leanh::lean_closure_set(v___f_2091_, 1, v___f_2087_);
    crate::leanh::lean_closure_set(v___f_2091_, 2, v___f_2089_);
    crate::leanh::lean_closure_set(v___f_2091_, 3, v___f_2083_);
    crate::leanh::lean_closure_set(v___f_2091_, 4, v___f_2084_);
    crate::leanh::lean_closure_set(v___f_2091_, 5, v_activeConnections_2079_);
    crate::leanh::lean_inc_ref(v___f_2091_);
    v___f_2092_ = crate::leanh::lean_alloc_closure(
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__7___boxed
            as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2092_, 0, v___f_2091_);
    crate::leanh::lean_closure_set(v___f_2092_, 1, v_a_2075_);
    v___x_2093_ = crate::leanh::lean_box((v_releaseConnectionPermit_2073_) as usize);
    v___f_2094_ = crate::leanh::lean_alloc_closure(
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__8___boxed
            as *mut core::ffi::c_void,
        7,
        5,
    );
    crate::leanh::lean_closure_set(v___f_2094_, 0, v___x_2093_);
    crate::leanh::lean_closure_set(v___f_2094_, 1, v___f_2091_);
    crate::leanh::lean_closure_set(v___f_2094_, 2, v_a_2075_);
    crate::leanh::lean_closure_set(v___f_2094_, 3, v_connectionLimit_2080_);
    crate::leanh::lean_closure_set(v___f_2094_, 4, v___f_2092_);
    v___f_2095_ = crate::leanh::lean_alloc_closure(
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__9___boxed
            as *mut core::ffi::c_void,
        6,
        4,
    );
    crate::leanh::lean_closure_set(v___f_2095_, 0, v_action_2074_);
    crate::leanh::lean_closure_set(v___f_2095_, 1, v_a_2075_);
    crate::leanh::lean_closure_set(v___f_2095_, 2, v___f_2094_);
    crate::leanh::lean_closure_set(v___f_2095_, 3, v___f_2090_);
    v___x_2096_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2097_ = 0;
    v___x_2098_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2096_,
        v___x_2097_,
        v___x_2086_,
        v___f_2095_,
    );
    return v___x_2098_;
}
pub unsafe fn l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___boxed(
    mut v_s_2099_: *mut crate::leanh::LeanObject,
    mut v_releaseConnectionPermit_2100_: *mut crate::leanh::LeanObject,
    mut v_action_2101_: *mut crate::leanh::LeanObject,
    mut v_a_2102_: *mut crate::leanh::LeanObject,
    mut v_a_2103_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_releaseConnectionPermit_boxed_2104_: u8 = 0;
    let mut v_res_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_releaseConnectionPermit_boxed_2104_ =
        (crate::leanh::lean_unbox(v_releaseConnectionPermit_2100_) as u8);
    v_res_2105_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg(
        v_s_2099_,
        v_releaseConnectionPermit_boxed_2104_,
        v_action_2101_,
        v_a_2102_,
    );
    crate::leanh::lean_dec_ref(v_a_2102_);
    return v_res_2105_;
}
pub unsafe fn l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation(
    mut v_00_u03b1_2106_: *mut crate::leanh::LeanObject,
    mut v_s_2107_: *mut crate::leanh::LeanObject,
    mut v_releaseConnectionPermit_2108_: u8,
    mut v_action_2109_: *mut crate::leanh::LeanObject,
    mut v_a_2110_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_context_2113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_activeConnections_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_connectionLimit_2115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_shutdownPromise_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2130__overap_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: u8 = 0;
    let mut v___x_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2112_ = l_Std_Async_ContextAsync_instMonad;
    v_context_2113_ = crate::leanh::lean_ctor_get(v_s_2107_, 0);
    crate::leanh::lean_inc_ref(v_context_2113_);
    v_activeConnections_2114_ = crate::leanh::lean_ctor_get(v_s_2107_, 1);
    crate::leanh::lean_inc_ref_n(v_activeConnections_2114_, 2);
    v_connectionLimit_2115_ = crate::leanh::lean_ctor_get(v_s_2107_, 2);
    crate::leanh::lean_inc(v_connectionLimit_2115_);
    v_shutdownPromise_2116_ = crate::leanh::lean_ctor_get(v_s_2107_, 3);
    crate::leanh::lean_inc_ref(v_shutdownPromise_2116_);
    crate::leanh::lean_dec_ref(v_s_2107_);
    v___f_2117_ =
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__0;
    v___f_2118_ =
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__3;
    v___f_2119_ =
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__4;
    v___x_2130__overap_2120_ = l_Std_Mutex_atomically___redArg(
        v___x_2112_,
        v___f_2118_,
        v___f_2119_,
        v_activeConnections_2114_,
        v___f_2117_,
    );
    crate::leanh::lean_inc_ref_n(v_a_2110_, 4);
    v___x_2121_ = crate::leanh::lean_apply_2(
        v___x_2130__overap_2120_,
        v_a_2110_,
        crate::leanh::lean_box(0),
    );
    v___f_2122_ =
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__5;
    v___f_2123_ = crate::leanh::lean_alloc_closure(
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__3___boxed
            as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2123_, 0, v_context_2113_);
    crate::leanh::lean_closure_set(v___f_2123_, 1, v_shutdownPromise_2116_);
    v___f_2124_ = crate::leanh::lean_alloc_closure(
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__4___boxed
            as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2124_, 0, v___f_2123_);
    v___f_2125_ =
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__6;
    v___f_2126_ = crate::leanh::lean_alloc_closure(
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__6___boxed
            as *mut core::ffi::c_void,
        9,
        6,
    );
    crate::leanh::lean_closure_set(v___f_2126_, 0, v___x_2112_);
    crate::leanh::lean_closure_set(v___f_2126_, 1, v___f_2122_);
    crate::leanh::lean_closure_set(v___f_2126_, 2, v___f_2124_);
    crate::leanh::lean_closure_set(v___f_2126_, 3, v___f_2118_);
    crate::leanh::lean_closure_set(v___f_2126_, 4, v___f_2119_);
    crate::leanh::lean_closure_set(v___f_2126_, 5, v_activeConnections_2114_);
    crate::leanh::lean_inc_ref(v___f_2126_);
    v___f_2127_ = crate::leanh::lean_alloc_closure(
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__7___boxed
            as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2127_, 0, v___f_2126_);
    crate::leanh::lean_closure_set(v___f_2127_, 1, v_a_2110_);
    v___x_2128_ = crate::leanh::lean_box((v_releaseConnectionPermit_2108_) as usize);
    v___f_2129_ = crate::leanh::lean_alloc_closure(
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__8___boxed
            as *mut core::ffi::c_void,
        7,
        5,
    );
    crate::leanh::lean_closure_set(v___f_2129_, 0, v___x_2128_);
    crate::leanh::lean_closure_set(v___f_2129_, 1, v___f_2126_);
    crate::leanh::lean_closure_set(v___f_2129_, 2, v_a_2110_);
    crate::leanh::lean_closure_set(v___f_2129_, 3, v_connectionLimit_2115_);
    crate::leanh::lean_closure_set(v___f_2129_, 4, v___f_2127_);
    v___f_2130_ = crate::leanh::lean_alloc_closure(
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__9___boxed
            as *mut core::ffi::c_void,
        6,
        4,
    );
    crate::leanh::lean_closure_set(v___f_2130_, 0, v_action_2109_);
    crate::leanh::lean_closure_set(v___f_2130_, 1, v_a_2110_);
    crate::leanh::lean_closure_set(v___f_2130_, 2, v___f_2129_);
    crate::leanh::lean_closure_set(v___f_2130_, 3, v___f_2125_);
    v___x_2131_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2132_ = 0;
    v___x_2133_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2131_,
        v___x_2132_,
        v___x_2121_,
        v___f_2130_,
    );
    return v___x_2133_;
}
pub unsafe fn l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___boxed(
    mut v_00_u03b1_2134_: *mut crate::leanh::LeanObject,
    mut v_s_2135_: *mut crate::leanh::LeanObject,
    mut v_releaseConnectionPermit_2136_: *mut crate::leanh::LeanObject,
    mut v_action_2137_: *mut crate::leanh::LeanObject,
    mut v_a_2138_: *mut crate::leanh::LeanObject,
    mut v_a_2139_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_releaseConnectionPermit_boxed_2140_: u8 = 0;
    let mut v_res_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_releaseConnectionPermit_boxed_2140_ =
        (crate::leanh::lean_unbox(v_releaseConnectionPermit_2136_) as u8);
    v_res_2141_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation(
        v_00_u03b1_2134_,
        v_s_2135_,
        v_releaseConnectionPermit_boxed_2140_,
        v_action_2137_,
        v_a_2138_,
    );
    crate::leanh::lean_dec_ref(v_a_2138_);
    return v_res_2141_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__0(
    mut v_x_2142_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2142_) == 0 {
        let mut v___x_2144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2144_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2144_, 0, v_x_2142_);
        return v___x_2144_;
    } else {
        let mut v___x_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref_known(v_x_2142_, 1);
        v___x_2145_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__1;
        return v___x_2145_;
    }
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__0___boxed(
    mut v_x_2146_: *mut crate::leanh::LeanObject,
    mut v___y_2147_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2148_ = l_Std_Http_Server_serve___redArg___lam__0(v_x_2146_);
    return v_res_2148_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__1(
    mut v_x_2149_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2154_: u8 = 0;
    let mut v___x_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2159_: u8 = 0;
    let mut v_a_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2163_: u8 = 0;
    let mut v_a_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2167_: u8 = 0;
    let mut v___x_2169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2175_: u8 = 0;
    let mut v_a_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2179_: u8 = 0;
    let mut v___x_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2187_: u8 = 0;
    let mut v_isSharedCheck_2188_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2149_) == 0 {
                    v_a_2151_ = crate::leanh::lean_ctor_get(v_x_2149_, 0);
                    v_isSharedCheck_2159_ = (!crate::leanh::lean_is_exclusive(v_x_2149_)) as u8;
                    if v_isSharedCheck_2159_ == 0 {
                        v___x_2153_ = v_x_2149_;
                        v_isShared_2154_ = v_isSharedCheck_2159_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2151_);
                        crate::leanh::lean_dec(v_x_2149_);
                        v___x_2153_ = crate::leanh::lean_box(0);
                        v_isShared_2154_ = v_isSharedCheck_2159_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2160_ = crate::leanh::lean_ctor_get(v_x_2149_, 0);
                    v_isSharedCheck_2188_ = (!crate::leanh::lean_is_exclusive(v_x_2149_)) as u8;
                    if v_isSharedCheck_2188_ == 0 {
                        v___x_2162_ = v_x_2149_;
                        v_isShared_2163_ = v_isSharedCheck_2188_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2160_);
                        crate::leanh::lean_dec(v_x_2149_);
                        v___x_2162_ = crate::leanh::lean_box(0);
                        v_isShared_2163_ = v_isSharedCheck_2188_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2154_ == 0 {
                    v___x_2156_ = v___x_2153_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2158_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2158_, 0, v_a_2151_);
                    v___x_2156_ = v_reuseFailAlloc_2158_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2157_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2157_, 0, v___x_2156_);
                return v___x_2157_;
            }
            3 => {
                if crate::leanh::lean_obj_tag(v_a_2160_) == 0 {
                    v_a_2164_ = crate::leanh::lean_ctor_get(v_a_2160_, 0);
                    v_isSharedCheck_2175_ = (!crate::leanh::lean_is_exclusive(v_a_2160_)) as u8;
                    if v_isSharedCheck_2175_ == 0 {
                        v___x_2166_ = v_a_2160_;
                        v_isShared_2167_ = v_isSharedCheck_2175_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2164_);
                        crate::leanh::lean_dec(v_a_2160_);
                        v___x_2166_ = crate::leanh::lean_box(0);
                        v_isShared_2167_ = v_isSharedCheck_2175_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_a_2176_ = crate::leanh::lean_ctor_get(v_a_2160_, 0);
                    v_isSharedCheck_2187_ = (!crate::leanh::lean_is_exclusive(v_a_2160_)) as u8;
                    if v_isSharedCheck_2187_ == 0 {
                        v___x_2178_ = v_a_2160_;
                        v_isShared_2179_ = v_isSharedCheck_2187_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2176_);
                        crate::leanh::lean_dec(v_a_2160_);
                        v___x_2178_ = crate::leanh::lean_box(0);
                        v_isShared_2179_ = v_isSharedCheck_2187_;
                        state = 7;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_2167_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2166_, 1);
                    v___x_2169_ = v___x_2166_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2174_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2174_, 0, v_a_2164_);
                    v___x_2169_ = v_reuseFailAlloc_2174_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_2163_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2162_, 0, v___x_2169_);
                    v___x_2171_ = v___x_2162_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2173_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2173_, 0, v___x_2169_);
                    v___x_2171_ = v_reuseFailAlloc_2173_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_2172_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2172_, 0, v___x_2171_);
                return v___x_2172_;
            }
            7 => {
                if v_isShared_2179_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2178_, 0);
                    v___x_2181_ = v___x_2178_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2186_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2186_, 0, v_a_2176_);
                    v___x_2181_ = v_reuseFailAlloc_2186_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_2163_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2162_, 0, v___x_2181_);
                    v___x_2183_ = v___x_2162_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2185_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2185_, 0, v___x_2181_);
                    v___x_2183_ = v_reuseFailAlloc_2185_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_2184_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2184_, 0, v___x_2183_);
                return v___x_2184_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__1___boxed(
    mut v_x_2189_: *mut crate::leanh::LeanObject,
    mut v___y_2190_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2191_ = l_Std_Http_Server_serve___redArg___lam__1(v_x_2189_);
    return v_res_2191_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__3(
    mut v_x_2192_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_2193_ = crate::leanh::lean_ctor_get(v_x_2192_, 0);
    crate::leanh::lean_inc(v_fst_2193_);
    return v_fst_2193_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__3___boxed(
    mut v_x_2194_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2195_ = l_Std_Http_Server_serve___redArg___lam__3(v_x_2194_);
    crate::leanh::lean_dec_ref(v_x_2194_);
    return v_res_2195_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__4(
    mut v_x_2200_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2202_ = l_Std_Http_Server_serve___redArg___lam__4___closed__1;
    return v___x_2202_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__4___boxed(
    mut v_x_2203_: *mut crate::leanh::LeanObject,
    mut v___y_2204_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2205_ = l_Std_Http_Server_serve___redArg___lam__4(v_x_2203_);
    return v_res_2205_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__2(
    mut v_x_2206_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2208_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2208_, 0, v_x_2206_);
    v___x_2209_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2209_, 0, v___x_2208_);
    v___x_2210_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2210_, 0, v___x_2209_);
    return v___x_2210_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__2___boxed(
    mut v_x_2211_: *mut crate::leanh::LeanObject,
    mut v___y_2212_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2213_ = l_Std_Http_Server_serve___redArg___lam__2(v_x_2211_);
    return v_res_2213_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__5(
    mut v_x_2214_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2219_: u8 = 0;
    let mut v___x_2221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2224_: u8 = 0;
    let mut v_a_2225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2228_: u8 = 0;
    let mut v_token_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2235_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2214_) == 0 {
                    v_a_2216_ = crate::leanh::lean_ctor_get(v_x_2214_, 0);
                    v_isSharedCheck_2224_ = (!crate::leanh::lean_is_exclusive(v_x_2214_)) as u8;
                    if v_isSharedCheck_2224_ == 0 {
                        v___x_2218_ = v_x_2214_;
                        v_isShared_2219_ = v_isSharedCheck_2224_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2216_);
                        crate::leanh::lean_dec(v_x_2214_);
                        v___x_2218_ = crate::leanh::lean_box(0);
                        v_isShared_2219_ = v_isSharedCheck_2224_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2225_ = crate::leanh::lean_ctor_get(v_x_2214_, 0);
                    v_isSharedCheck_2235_ = (!crate::leanh::lean_is_exclusive(v_x_2214_)) as u8;
                    if v_isSharedCheck_2235_ == 0 {
                        v___x_2227_ = v_x_2214_;
                        v_isShared_2228_ = v_isSharedCheck_2235_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2225_);
                        crate::leanh::lean_dec(v_x_2214_);
                        v___x_2227_ = crate::leanh::lean_box(0);
                        v_isShared_2228_ = v_isSharedCheck_2235_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2219_ == 0 {
                    v___x_2221_ = v___x_2218_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2223_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2223_, 0, v_a_2216_);
                    v___x_2221_ = v_reuseFailAlloc_2223_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2222_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2222_, 0, v___x_2221_);
                return v___x_2222_;
            }
            3 => {
                v_token_2229_ = crate::leanh::lean_ctor_get(v_a_2225_, 1);
                crate::leanh::lean_inc_ref(v_token_2229_);
                crate::leanh::lean_dec(v_a_2225_);
                v___x_2230_ = l_Std_CancellationToken_selector(v_token_2229_);
                if v_isShared_2228_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2227_, 0, v___x_2230_);
                    v___x_2232_ = v___x_2227_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2234_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2234_, 0, v___x_2230_);
                    v___x_2232_ = v_reuseFailAlloc_2234_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2233_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2233_, 0, v___x_2232_);
                return v___x_2233_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__5___boxed(
    mut v_x_2236_: *mut crate::leanh::LeanObject,
    mut v___y_2237_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2238_ = l_Std_Http_Server_serve___redArg___lam__5(v_x_2236_);
    return v_res_2238_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__10(
    mut v___x_2239_: *mut crate::leanh::LeanObject,
    mut v_____r_2240_: *mut crate::leanh::LeanObject,
    mut v___y_2241_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2243_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2243_, 0, v___x_2239_);
    v___x_2244_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2244_, 0, v___x_2243_);
    v___x_2245_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2245_, 0, v___x_2244_);
    return v___x_2245_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__10___boxed(
    mut v___x_2246_: *mut crate::leanh::LeanObject,
    mut v_____r_2247_: *mut crate::leanh::LeanObject,
    mut v___y_2248_: *mut crate::leanh::LeanObject,
    mut v___y_2249_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2250_ =
        l_Std_Http_Server_serve___redArg___lam__10(v___x_2246_, v_____r_2247_, v___y_2248_);
    crate::leanh::lean_dec_ref(v___y_2248_);
    return v_res_2250_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__6(
    mut v___x_2251_: *mut crate::leanh::LeanObject,
    mut v_x_2252_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2257_: u8 = 0;
    let mut v___x_2259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2262_: u8 = 0;
    let mut v___x_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2265_: u8 = 0;
    let mut v___x_2266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2271_: u8 = 0;
    let mut v_unused_2272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2252_) == 0 {
                    v_a_2254_ = crate::leanh::lean_ctor_get(v_x_2252_, 0);
                    v_isSharedCheck_2262_ = (!crate::leanh::lean_is_exclusive(v_x_2252_)) as u8;
                    if v_isSharedCheck_2262_ == 0 {
                        v___x_2256_ = v_x_2252_;
                        v_isShared_2257_ = v_isSharedCheck_2262_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2254_);
                        crate::leanh::lean_dec(v_x_2252_);
                        v___x_2256_ = crate::leanh::lean_box(0);
                        v_isShared_2257_ = v_isSharedCheck_2262_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_isSharedCheck_2271_ = (!crate::leanh::lean_is_exclusive(v_x_2252_)) as u8;
                    if v_isSharedCheck_2271_ == 0 {
                        v_unused_2272_ = crate::leanh::lean_ctor_get(v_x_2252_, 0);
                        crate::leanh::lean_dec(v_unused_2272_);
                        v___x_2264_ = v_x_2252_;
                        v_isShared_2265_ = v_isSharedCheck_2271_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_x_2252_);
                        v___x_2264_ = crate::leanh::lean_box(0);
                        v_isShared_2265_ = v_isSharedCheck_2271_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2257_ == 0 {
                    v___x_2259_ = v___x_2256_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2261_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2261_, 0, v_a_2254_);
                    v___x_2259_ = v_reuseFailAlloc_2261_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2260_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2260_, 0, v___x_2259_);
                return v___x_2260_;
            }
            3 => {
                v___x_2266_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2266_, 0, v___x_2251_);
                if v_isShared_2265_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2264_, 0, v___x_2266_);
                    v___x_2268_ = v___x_2264_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2270_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2270_, 0, v___x_2266_);
                    v___x_2268_ = v_reuseFailAlloc_2270_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2269_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2269_, 0, v___x_2268_);
                return v___x_2269_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__6___boxed(
    mut v___x_2273_: *mut crate::leanh::LeanObject,
    mut v_x_2274_: *mut crate::leanh::LeanObject,
    mut v___y_2275_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2276_ = l_Std_Http_Server_serve___redArg___lam__6(v___x_2273_, v_x_2274_);
    return v_res_2276_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__7(
    mut v___f_2277_: *mut crate::leanh::LeanObject,
    mut v___y_2278_: *mut crate::leanh::LeanObject,
    mut v_x_2279_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2284_: u8 = 0;
    let mut v___x_2286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2289_: u8 = 0;
    let mut v_a_2290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2279_) == 0 {
                    crate::leanh::lean_dec_ref(v___f_2277_);
                    v_a_2281_ = crate::leanh::lean_ctor_get(v_x_2279_, 0);
                    v_isSharedCheck_2289_ = (!crate::leanh::lean_is_exclusive(v_x_2279_)) as u8;
                    if v_isSharedCheck_2289_ == 0 {
                        v___x_2283_ = v_x_2279_;
                        v_isShared_2284_ = v_isSharedCheck_2289_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2281_);
                        crate::leanh::lean_dec(v_x_2279_);
                        v___x_2283_ = crate::leanh::lean_box(0);
                        v_isShared_2284_ = v_isSharedCheck_2289_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2290_ = crate::leanh::lean_ctor_get(v_x_2279_, 0);
                    crate::leanh::lean_inc(v_a_2290_);
                    crate::leanh::lean_dec_ref_known(v_x_2279_, 1);
                    crate::leanh::lean_inc_ref(v___y_2278_);
                    v___x_2291_ = crate::leanh::lean_apply_3(
                        v___f_2277_,
                        v_a_2290_,
                        v___y_2278_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_2291_;
                }
            }
            1 => {
                if v_isShared_2284_ == 0 {
                    v___x_2286_ = v___x_2283_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2288_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2288_, 0, v_a_2281_);
                    v___x_2286_ = v_reuseFailAlloc_2288_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2287_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2287_, 0, v___x_2286_);
                return v___x_2287_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__7___boxed(
    mut v___f_2292_: *mut crate::leanh::LeanObject,
    mut v___y_2293_: *mut crate::leanh::LeanObject,
    mut v_x_2294_: *mut crate::leanh::LeanObject,
    mut v___y_2295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2296_ = l_Std_Http_Server_serve___redArg___lam__7(v___f_2292_, v___y_2293_, v_x_2294_);
    crate::leanh::lean_dec_ref(v___y_2293_);
    return v_res_2296_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__8(
    mut v_a_2297_: *mut crate::leanh::LeanObject,
    mut v_x_2298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2303_: u8 = 0;
    let mut v___x_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2310_: u8 = 0;
    let mut v_unused_2311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2298_) == 0 {
                    crate::leanh::lean_dec_ref(v_a_2297_);
                    v___x_2300_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2300_, 0, v_x_2298_);
                    return v___x_2300_;
                } else {
                    v_isSharedCheck_2310_ = (!crate::leanh::lean_is_exclusive(v_x_2298_)) as u8;
                    if v_isSharedCheck_2310_ == 0 {
                        v_unused_2311_ = crate::leanh::lean_ctor_get(v_x_2298_, 0);
                        crate::leanh::lean_dec(v_unused_2311_);
                        v___x_2302_ = v_x_2298_;
                        v_isShared_2303_ = v_isSharedCheck_2310_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_x_2298_);
                        v___x_2302_ = crate::leanh::lean_box(0);
                        v_isShared_2303_ = v_isSharedCheck_2310_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2304_ = crate::leanh::lean_box(2);
                v___x_2305_ = l_Std_CancellationContext_cancel(v_a_2297_, v___x_2304_);
                if v_isShared_2303_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2302_, 0, v___x_2305_);
                    v___x_2307_ = v___x_2302_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2309_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2309_, 0, v___x_2305_);
                    v___x_2307_ = v_reuseFailAlloc_2309_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2308_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2308_, 0, v___x_2307_);
                return v___x_2308_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__8___boxed(
    mut v_a_2312_: *mut crate::leanh::LeanObject,
    mut v_x_2313_: *mut crate::leanh::LeanObject,
    mut v___y_2314_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2315_ = l_Std_Http_Server_serve___redArg___lam__8(v_a_2312_, v_x_2313_);
    return v_res_2315_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__11(
    mut v___f_2316_: *mut crate::leanh::LeanObject,
    mut v_a_2317_: *mut crate::leanh::LeanObject,
    mut v_x_2318_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2318_) == 0 {
        let mut v___x_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_a_2317_);
        crate::leanh::lean_dec_ref(v___f_2316_);
        v___x_2320_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2320_, 0, v_x_2318_);
        return v___x_2320_;
    } else {
        let mut v_a_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_2321_ = crate::leanh::lean_ctor_get(v_x_2318_, 0);
        crate::leanh::lean_inc(v_a_2321_);
        crate::leanh::lean_dec_ref_known(v_x_2318_, 1);
        v___x_2322_ = crate::leanh::lean_apply_3(
            v___f_2316_,
            v_a_2321_,
            v_a_2317_,
            crate::leanh::lean_box(0),
        );
        return v___x_2322_;
    }
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__11___boxed(
    mut v___f_2323_: *mut crate::leanh::LeanObject,
    mut v_a_2324_: *mut crate::leanh::LeanObject,
    mut v_x_2325_: *mut crate::leanh::LeanObject,
    mut v___y_2326_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2327_ = l_Std_Http_Server_serve___redArg___lam__11(v___f_2323_, v_a_2324_, v_x_2325_);
    return v_res_2327_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__9(
    mut v_permitAcquired_2328_: u8,
    mut v___f_2329_: *mut crate::leanh::LeanObject,
    mut v___x_2330_: *mut crate::leanh::LeanObject,
    mut v_a_2331_: *mut crate::leanh::LeanObject,
    mut v_connectionLimit_2332_: *mut crate::leanh::LeanObject,
    mut v___x_2333_: *mut crate::leanh::LeanObject,
    mut v___x_2334_: u8,
    mut v___f_2335_: *mut crate::leanh::LeanObject,
    mut v_opt_2336_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2342_: u8 = 0;
    let mut v___x_2343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2349_: u8 = 0;
    let mut v___x_2350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_permitAcquired_2328_ == 0 {
                    crate::leanh::lean_dec_ref(v___f_2335_);
                    crate::leanh::lean_dec(v___x_2333_);
                    crate::leanh::lean_dec(v_connectionLimit_2332_);
                    v___x_2338_ = crate::leanh::lean_apply_3(
                        v___f_2329_,
                        v___x_2330_,
                        v_a_2331_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_2338_;
                } else {
                    if crate::leanh::lean_obj_tag(v_connectionLimit_2332_) == 1 {
                        crate::leanh::lean_dec_ref(v_a_2331_);
                        crate::leanh::lean_dec_ref(v___f_2329_);
                        v_val_2339_ = crate::leanh::lean_ctor_get(v_connectionLimit_2332_, 0);
                        v_isSharedCheck_2349_ =
                            (!crate::leanh::lean_is_exclusive(v_connectionLimit_2332_)) as u8;
                        if v_isSharedCheck_2349_ == 0 {
                            v___x_2341_ = v_connectionLimit_2332_;
                            v_isShared_2342_ = v_isSharedCheck_2349_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_2339_);
                            crate::leanh::lean_dec(v_connectionLimit_2332_);
                            v___x_2341_ = crate::leanh::lean_box(0);
                            v_isShared_2342_ = v_isSharedCheck_2349_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___f_2335_);
                        crate::leanh::lean_dec(v___x_2333_);
                        crate::leanh::lean_dec(v_connectionLimit_2332_);
                        v___x_2350_ = crate::leanh::lean_apply_3(
                            v___f_2329_,
                            v___x_2330_,
                            v_a_2331_,
                            crate::leanh::lean_box(0),
                        );
                        return v___x_2350_;
                    }
                }
            }
            1 => {
                v___x_2343_ = l_Std_Semaphore_release(v_val_2339_);
                if v_isShared_2342_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2341_, 0, v___x_2343_);
                    v___x_2345_ = v___x_2341_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2348_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2348_, 0, v___x_2343_);
                    v___x_2345_ = v_reuseFailAlloc_2348_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2346_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2346_, 0, v___x_2345_);
                v___x_2347_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_2333_,
                    v___x_2334_,
                    v___x_2346_,
                    v___f_2335_,
                );
                return v___x_2347_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__9___boxed(
    mut v_permitAcquired_2351_: *mut crate::leanh::LeanObject,
    mut v___f_2352_: *mut crate::leanh::LeanObject,
    mut v___x_2353_: *mut crate::leanh::LeanObject,
    mut v_a_2354_: *mut crate::leanh::LeanObject,
    mut v_connectionLimit_2355_: *mut crate::leanh::LeanObject,
    mut v___x_2356_: *mut crate::leanh::LeanObject,
    mut v___x_2357_: *mut crate::leanh::LeanObject,
    mut v___f_2358_: *mut crate::leanh::LeanObject,
    mut v_opt_2359_: *mut crate::leanh::LeanObject,
    mut v___y_2360_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_permitAcquired_boxed_2361_: u8 = 0;
    let mut v___x_13775__boxed_2362_: u8 = 0;
    let mut v_res_2363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_permitAcquired_boxed_2361_ = (crate::leanh::lean_unbox(v_permitAcquired_2351_) as u8);
    v___x_13775__boxed_2362_ = (crate::leanh::lean_unbox(v___x_2357_) as u8);
    v_res_2363_ = l_Std_Http_Server_serve___redArg___lam__9(
        v_permitAcquired_boxed_2361_,
        v___f_2352_,
        v___x_2353_,
        v_a_2354_,
        v_connectionLimit_2355_,
        v___x_2356_,
        v___x_13775__boxed_2362_,
        v___f_2358_,
        v_opt_2359_,
    );
    crate::leanh::lean_dec(v_opt_2359_);
    return v_res_2363_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__12(
    mut v___x_2364_: *mut crate::leanh::LeanObject,
    mut v_inst_2365_: *mut crate::leanh::LeanObject,
    mut v_val_2366_: *mut crate::leanh::LeanObject,
    mut v_handler_2367_: *mut crate::leanh::LeanObject,
    mut v_config_2368_: *mut crate::leanh::LeanObject,
    mut v_extensions_2369_: *mut crate::leanh::LeanObject,
    mut v_a_2370_: *mut crate::leanh::LeanObject,
    mut v___f_2371_: *mut crate::leanh::LeanObject,
    mut v___x_2372_: *mut crate::leanh::LeanObject,
    mut v___x_2373_: u8,
    mut v___f_2374_: *mut crate::leanh::LeanObject,
    mut v_x_2375_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2380_: u8 = 0;
    let mut v___x_2381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2392_: u8 = 0;
    let mut v___x_2394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2396_: u8 = 0;
    let mut v_a_2397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2400_: u8 = 0;
    let mut v_fst_2401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2405_: u8 = 0;
    let mut v_a_2406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2409_: u8 = 0;
    let mut v___x_2410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2415_: u8 = 0;
    let mut v_isSharedCheck_2416_: u8 = 0;
    let mut v_unused_2417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2375_) == 0 {
                    crate::leanh::lean_dec_ref(v___f_2374_);
                    crate::leanh::lean_dec(v___x_2372_);
                    crate::leanh::lean_dec_ref(v___f_2371_);
                    crate::leanh::lean_dec_ref(v_a_2370_);
                    crate::leanh::lean_dec(v_extensions_2369_);
                    crate::leanh::lean_dec_ref(v_config_2368_);
                    crate::leanh::lean_dec(v_handler_2367_);
                    crate::leanh::lean_dec(v_val_2366_);
                    crate::leanh::lean_dec_ref(v_inst_2365_);
                    crate::leanh::lean_dec_ref(v___x_2364_);
                    v___x_2377_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2377_, 0, v_x_2375_);
                    return v___x_2377_;
                } else {
                    v_isSharedCheck_2416_ = (!crate::leanh::lean_is_exclusive(v_x_2375_)) as u8;
                    if v_isSharedCheck_2416_ == 0 {
                        v_unused_2417_ = crate::leanh::lean_ctor_get(v_x_2375_, 0);
                        crate::leanh::lean_dec(v_unused_2417_);
                        v___x_2379_ = v_x_2375_;
                        v_isShared_2380_ = v_isSharedCheck_2416_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_x_2375_);
                        v___x_2379_ = crate::leanh::lean_box(0);
                        v_isShared_2380_ = v_isSharedCheck_2416_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2381_ = crate::leanh::lean_alloc_closure(
                    l_Std_Http_Server_serveConnection___boxed as *mut core::ffi::c_void,
                    10,
                    9,
                );
                crate::leanh::lean_closure_set(v___x_2381_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_2381_, 1, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_2381_, 2, v___x_2364_);
                crate::leanh::lean_closure_set(v___x_2381_, 3, v_inst_2365_);
                crate::leanh::lean_closure_set(v___x_2381_, 4, v_val_2366_);
                crate::leanh::lean_closure_set(v___x_2381_, 5, v_handler_2367_);
                crate::leanh::lean_closure_set(v___x_2381_, 6, v_config_2368_);
                crate::leanh::lean_closure_set(v___x_2381_, 7, v_extensions_2369_);
                crate::leanh::lean_closure_set(v___x_2381_, 8, v_a_2370_);
                crate::leanh::lean_inc(v___x_2372_);
                v___x_2382_ = l_Std_Async_EAsync_tryFinally_x27___redArg(
                    v___x_2381_,
                    v___f_2371_,
                    v___x_2372_,
                    v___x_2373_,
                );
                if crate::leanh::lean_obj_tag(v___x_2382_) == 0 {
                    crate::leanh::lean_dec_ref(v___f_2374_);
                    crate::leanh::lean_dec(v___x_2372_);
                    v_a_2388_ = crate::leanh::lean_ctor_get(v___x_2382_, 0);
                    crate::leanh::lean_inc(v_a_2388_);
                    crate::leanh::lean_dec_ref_known(v___x_2382_, 1);
                    if crate::leanh::lean_obj_tag(v_a_2388_) == 0 {
                        v_a_2389_ = crate::leanh::lean_ctor_get(v_a_2388_, 0);
                        v_isSharedCheck_2396_ = (!crate::leanh::lean_is_exclusive(v_a_2388_)) as u8;
                        if v_isSharedCheck_2396_ == 0 {
                            v___x_2391_ = v_a_2388_;
                            v_isShared_2392_ = v_isSharedCheck_2396_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2389_);
                            crate::leanh::lean_dec(v_a_2388_);
                            v___x_2391_ = crate::leanh::lean_box(0);
                            v_isShared_2392_ = v_isSharedCheck_2396_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v_a_2397_ = crate::leanh::lean_ctor_get(v_a_2388_, 0);
                        v_isSharedCheck_2405_ = (!crate::leanh::lean_is_exclusive(v_a_2388_)) as u8;
                        if v_isSharedCheck_2405_ == 0 {
                            v___x_2399_ = v_a_2388_;
                            v_isShared_2400_ = v_isSharedCheck_2405_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2397_);
                            crate::leanh::lean_dec(v_a_2388_);
                            v___x_2399_ = crate::leanh::lean_box(0);
                            v_isShared_2400_ = v_isSharedCheck_2405_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2379_);
                    v_a_2406_ = crate::leanh::lean_ctor_get(v___x_2382_, 0);
                    v_isSharedCheck_2415_ = (!crate::leanh::lean_is_exclusive(v___x_2382_)) as u8;
                    if v_isSharedCheck_2415_ == 0 {
                        v___x_2408_ = v___x_2382_;
                        v_isShared_2409_ = v_isSharedCheck_2415_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2406_);
                        crate::leanh::lean_dec(v___x_2382_);
                        v___x_2408_ = crate::leanh::lean_box(0);
                        v_isShared_2409_ = v_isSharedCheck_2415_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2380_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2379_, 0);
                    crate::leanh::lean_ctor_set(v___x_2379_, 0, v___y_2384_);
                    v___x_2386_ = v___x_2379_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2387_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2387_, 0, v___y_2384_);
                    v___x_2386_ = v_reuseFailAlloc_2387_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2386_;
            }
            4 => {
                if v_isShared_2392_ == 0 {
                    v___x_2394_ = v___x_2391_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2395_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2395_, 0, v_a_2389_);
                    v___x_2394_ = v_reuseFailAlloc_2395_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___y_2384_ = v___x_2394_;
                state = 2;
                continue;
            }
            6 => {
                v_fst_2401_ = crate::leanh::lean_ctor_get(v_a_2397_, 0);
                crate::leanh::lean_inc(v_fst_2401_);
                crate::leanh::lean_dec(v_a_2397_);
                if v_isShared_2400_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2399_, 0, v_fst_2401_);
                    v___x_2403_ = v___x_2399_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2404_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2404_, 0, v_fst_2401_);
                    v___x_2403_ = v_reuseFailAlloc_2404_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_2384_ = v___x_2403_;
                state = 2;
                continue;
            }
            8 => {
                v___x_2410_ =
                    crate::leanh::lean_alloc_closure(l_Except_map as *mut core::ffi::c_void, 5, 4);
                crate::leanh::lean_closure_set(v___x_2410_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_2410_, 1, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_2410_, 2, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_2410_, 3, v___f_2374_);
                v___x_2411_ = lean_task_map(v___x_2410_, v_a_2406_, v___x_2372_, v___x_2373_);
                if v_isShared_2409_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2408_, 0, v___x_2411_);
                    v___x_2413_ = v___x_2408_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2414_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2414_, 0, v___x_2411_);
                    v___x_2413_ = v_reuseFailAlloc_2414_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2413_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__12___boxed(
    mut v___x_2418_: *mut crate::leanh::LeanObject,
    mut v_inst_2419_: *mut crate::leanh::LeanObject,
    mut v_val_2420_: *mut crate::leanh::LeanObject,
    mut v_handler_2421_: *mut crate::leanh::LeanObject,
    mut v_config_2422_: *mut crate::leanh::LeanObject,
    mut v_extensions_2423_: *mut crate::leanh::LeanObject,
    mut v_a_2424_: *mut crate::leanh::LeanObject,
    mut v___f_2425_: *mut crate::leanh::LeanObject,
    mut v___x_2426_: *mut crate::leanh::LeanObject,
    mut v___x_2427_: *mut crate::leanh::LeanObject,
    mut v___f_2428_: *mut crate::leanh::LeanObject,
    mut v_x_2429_: *mut crate::leanh::LeanObject,
    mut v___y_2430_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_13824__boxed_2431_: u8 = 0;
    let mut v_res_2432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_13824__boxed_2431_ = (crate::leanh::lean_unbox(v___x_2427_) as u8);
    v_res_2432_ = l_Std_Http_Server_serve___redArg___lam__12(
        v___x_2418_,
        v_inst_2419_,
        v_val_2420_,
        v_handler_2421_,
        v_config_2422_,
        v_extensions_2423_,
        v_a_2424_,
        v___f_2425_,
        v___x_2426_,
        v___x_13824__boxed_2431_,
        v___f_2428_,
        v_x_2429_,
    );
    return v_res_2432_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__13(
    mut v___x_2433_: *mut crate::leanh::LeanObject,
    mut v_activeConnections_2434_: *mut crate::leanh::LeanObject,
    mut v___f_2435_: *mut crate::leanh::LeanObject,
    mut v_a_2436_: *mut crate::leanh::LeanObject,
    mut v___f_2437_: *mut crate::leanh::LeanObject,
    mut v___f_2438_: *mut crate::leanh::LeanObject,
    mut v_permitAcquired_2439_: u8,
    mut v___x_2440_: *mut crate::leanh::LeanObject,
    mut v_connectionLimit_2441_: *mut crate::leanh::LeanObject,
    mut v___x_2442_: *mut crate::leanh::LeanObject,
    mut v___x_2443_: u8,
    mut v___x_2444_: *mut crate::leanh::LeanObject,
    mut v_inst_2445_: *mut crate::leanh::LeanObject,
    mut v_val_2446_: *mut crate::leanh::LeanObject,
    mut v_handler_2447_: *mut crate::leanh::LeanObject,
    mut v_config_2448_: *mut crate::leanh::LeanObject,
    mut v_extensions_2449_: *mut crate::leanh::LeanObject,
    mut v___f_2450_: *mut crate::leanh::LeanObject,
    mut v___f_2451_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_12955__overap_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2453_ =
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__3;
    v___f_2454_ =
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__4;
    crate::leanh::lean_inc_ref(v_activeConnections_2434_);
    crate::leanh::lean_inc_ref(v___x_2433_);
    v___x_12955__overap_2455_ = l_Std_Mutex_atomically___redArg(
        v___x_2433_,
        v___f_2453_,
        v___f_2454_,
        v_activeConnections_2434_,
        v___f_2435_,
    );
    crate::leanh::lean_inc_ref_n(v_a_2436_, 3);
    v___x_2456_ = crate::leanh::lean_apply_2(
        v___x_12955__overap_2455_,
        v_a_2436_,
        crate::leanh::lean_box(0),
    );
    v___f_2457_ = crate::leanh::lean_alloc_closure(
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__6___boxed
            as *mut core::ffi::c_void,
        9,
        6,
    );
    crate::leanh::lean_closure_set(v___f_2457_, 0, v___x_2433_);
    crate::leanh::lean_closure_set(v___f_2457_, 1, v___f_2437_);
    crate::leanh::lean_closure_set(v___f_2457_, 2, v___f_2438_);
    crate::leanh::lean_closure_set(v___f_2457_, 3, v___f_2453_);
    crate::leanh::lean_closure_set(v___f_2457_, 4, v___f_2454_);
    crate::leanh::lean_closure_set(v___f_2457_, 5, v_activeConnections_2434_);
    crate::leanh::lean_inc_ref(v___f_2457_);
    v___f_2458_ = crate::leanh::lean_alloc_closure(
        l_Std_Http_Server_serve___redArg___lam__11___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2458_, 0, v___f_2457_);
    crate::leanh::lean_closure_set(v___f_2458_, 1, v_a_2436_);
    v___x_2459_ = crate::leanh::lean_box((v_permitAcquired_2439_) as usize);
    v___x_2460_ = crate::leanh::lean_box((v___x_2443_) as usize);
    crate::leanh::lean_inc_n(v___x_2442_, 3);
    v___f_2461_ = crate::leanh::lean_alloc_closure(
        l_Std_Http_Server_serve___redArg___lam__9___boxed as *mut core::ffi::c_void,
        10,
        8,
    );
    crate::leanh::lean_closure_set(v___f_2461_, 0, v___x_2459_);
    crate::leanh::lean_closure_set(v___f_2461_, 1, v___f_2457_);
    crate::leanh::lean_closure_set(v___f_2461_, 2, v___x_2440_);
    crate::leanh::lean_closure_set(v___f_2461_, 3, v_a_2436_);
    crate::leanh::lean_closure_set(v___f_2461_, 4, v_connectionLimit_2441_);
    crate::leanh::lean_closure_set(v___f_2461_, 5, v___x_2442_);
    crate::leanh::lean_closure_set(v___f_2461_, 6, v___x_2460_);
    crate::leanh::lean_closure_set(v___f_2461_, 7, v___f_2458_);
    v___x_2462_ = crate::leanh::lean_box((v___x_2443_) as usize);
    v___f_2463_ = crate::leanh::lean_alloc_closure(
        l_Std_Http_Server_serve___redArg___lam__12___boxed as *mut core::ffi::c_void,
        13,
        11,
    );
    crate::leanh::lean_closure_set(v___f_2463_, 0, v___x_2444_);
    crate::leanh::lean_closure_set(v___f_2463_, 1, v_inst_2445_);
    crate::leanh::lean_closure_set(v___f_2463_, 2, v_val_2446_);
    crate::leanh::lean_closure_set(v___f_2463_, 3, v_handler_2447_);
    crate::leanh::lean_closure_set(v___f_2463_, 4, v_config_2448_);
    crate::leanh::lean_closure_set(v___f_2463_, 5, v_extensions_2449_);
    crate::leanh::lean_closure_set(v___f_2463_, 6, v_a_2436_);
    crate::leanh::lean_closure_set(v___f_2463_, 7, v___f_2461_);
    crate::leanh::lean_closure_set(v___f_2463_, 8, v___x_2442_);
    crate::leanh::lean_closure_set(v___f_2463_, 9, v___x_2462_);
    crate::leanh::lean_closure_set(v___f_2463_, 10, v___f_2450_);
    v___x_2464_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2442_,
        v___x_2443_,
        v___x_2456_,
        v___f_2463_,
    );
    v___x_2465_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2442_,
        v___x_2443_,
        v___x_2464_,
        v___f_2451_,
    );
    return v___x_2465_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__13___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2466_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_activeConnections_2467_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v___f_2468_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_a_2469_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v___f_2470_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___f_2471_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_permitAcquired_2472_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___x_2473_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_connectionLimit_2474_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___x_2475_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___x_2476_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___x_2477_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_inst_2478_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_val_2479_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_handler_2480_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v_config_2481_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v_extensions_2482_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___f_2483_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___f_2484_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v___y_2485_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v_permitAcquired_boxed_2486_: u8 = 0;
    let mut v___x_13943__boxed_2487_: u8 = 0;
    let mut v_res_2488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_permitAcquired_boxed_2486_ = (crate::leanh::lean_unbox(v_permitAcquired_2472_) as u8);
    v___x_13943__boxed_2487_ = (crate::leanh::lean_unbox(v___x_2476_) as u8);
    v_res_2488_ = l_Std_Http_Server_serve___redArg___lam__13(
        v___x_2466_,
        v_activeConnections_2467_,
        v___f_2468_,
        v_a_2469_,
        v___f_2470_,
        v___f_2471_,
        v_permitAcquired_boxed_2486_,
        v___x_2473_,
        v_connectionLimit_2474_,
        v___x_2475_,
        v___x_13943__boxed_2487_,
        v___x_2477_,
        v_inst_2478_,
        v_val_2479_,
        v_handler_2480_,
        v_config_2481_,
        v_extensions_2482_,
        v___f_2483_,
        v___f_2484_,
    );
    return v_res_2488_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__14(
    mut v___x_2489_: *mut crate::leanh::LeanObject,
    mut v_activeConnections_2490_: *mut crate::leanh::LeanObject,
    mut v___f_2491_: *mut crate::leanh::LeanObject,
    mut v___f_2492_: *mut crate::leanh::LeanObject,
    mut v___f_2493_: *mut crate::leanh::LeanObject,
    mut v_permitAcquired_2494_: u8,
    mut v___x_2495_: *mut crate::leanh::LeanObject,
    mut v_connectionLimit_2496_: *mut crate::leanh::LeanObject,
    mut v___x_2497_: *mut crate::leanh::LeanObject,
    mut v___x_2498_: u8,
    mut v___x_2499_: *mut crate::leanh::LeanObject,
    mut v_inst_2500_: *mut crate::leanh::LeanObject,
    mut v_val_2501_: *mut crate::leanh::LeanObject,
    mut v_handler_2502_: *mut crate::leanh::LeanObject,
    mut v_config_2503_: *mut crate::leanh::LeanObject,
    mut v_extensions_2504_: *mut crate::leanh::LeanObject,
    mut v___f_2505_: *mut crate::leanh::LeanObject,
    mut v_x_2506_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2511_: u8 = 0;
    let mut v___x_2513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2516_: u8 = 0;
    let mut v_a_2517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2520_: u8 = 0;
    let mut v___f_2521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2531_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2506_) == 0 {
                    crate::leanh::lean_dec_ref(v___f_2505_);
                    crate::leanh::lean_dec(v_extensions_2504_);
                    crate::leanh::lean_dec_ref(v_config_2503_);
                    crate::leanh::lean_dec(v_handler_2502_);
                    crate::leanh::lean_dec(v_val_2501_);
                    crate::leanh::lean_dec_ref(v_inst_2500_);
                    crate::leanh::lean_dec_ref(v___x_2499_);
                    crate::leanh::lean_dec(v___x_2497_);
                    crate::leanh::lean_dec(v_connectionLimit_2496_);
                    crate::leanh::lean_dec_ref(v___f_2493_);
                    crate::leanh::lean_dec_ref(v___f_2492_);
                    crate::leanh::lean_dec_ref(v___f_2491_);
                    crate::leanh::lean_dec_ref(v_activeConnections_2490_);
                    crate::leanh::lean_dec_ref(v___x_2489_);
                    v_a_2508_ = crate::leanh::lean_ctor_get(v_x_2506_, 0);
                    v_isSharedCheck_2516_ = (!crate::leanh::lean_is_exclusive(v_x_2506_)) as u8;
                    if v_isSharedCheck_2516_ == 0 {
                        v___x_2510_ = v_x_2506_;
                        v_isShared_2511_ = v_isSharedCheck_2516_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2508_);
                        crate::leanh::lean_dec(v_x_2506_);
                        v___x_2510_ = crate::leanh::lean_box(0);
                        v_isShared_2511_ = v_isSharedCheck_2516_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2517_ = crate::leanh::lean_ctor_get(v_x_2506_, 0);
                    v_isSharedCheck_2531_ = (!crate::leanh::lean_is_exclusive(v_x_2506_)) as u8;
                    if v_isSharedCheck_2531_ == 0 {
                        v___x_2519_ = v_x_2506_;
                        v_isShared_2520_ = v_isSharedCheck_2531_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2517_);
                        crate::leanh::lean_dec(v_x_2506_);
                        v___x_2519_ = crate::leanh::lean_box(0);
                        v_isShared_2520_ = v_isSharedCheck_2531_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2511_ == 0 {
                    v___x_2513_ = v___x_2510_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2515_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2515_, 0, v_a_2508_);
                    v___x_2513_ = v_reuseFailAlloc_2515_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2514_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2514_, 0, v___x_2513_);
                return v___x_2514_;
            }
            3 => {
                crate::leanh::lean_inc(v_a_2517_);
                v___f_2521_ = crate::leanh::lean_alloc_closure(
                    l_Std_Http_Server_serve___redArg___lam__8___boxed as *mut core::ffi::c_void,
                    3,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2521_, 0, v_a_2517_);
                v___x_2522_ = crate::leanh::lean_box((v_permitAcquired_2494_) as usize);
                v___x_2523_ = crate::leanh::lean_box((v___x_2498_) as usize);
                crate::leanh::lean_inc(v___x_2497_);
                v___f_2524_ = crate::leanh::lean_alloc_closure(
                    l_Std_Http_Server_serve___redArg___lam__13___boxed as *mut core::ffi::c_void,
                    20,
                    19,
                );
                crate::leanh::lean_closure_set(v___f_2524_, 0, v___x_2489_);
                crate::leanh::lean_closure_set(v___f_2524_, 1, v_activeConnections_2490_);
                crate::leanh::lean_closure_set(v___f_2524_, 2, v___f_2491_);
                crate::leanh::lean_closure_set(v___f_2524_, 3, v_a_2517_);
                crate::leanh::lean_closure_set(v___f_2524_, 4, v___f_2492_);
                crate::leanh::lean_closure_set(v___f_2524_, 5, v___f_2493_);
                crate::leanh::lean_closure_set(v___f_2524_, 6, v___x_2522_);
                crate::leanh::lean_closure_set(v___f_2524_, 7, v___x_2495_);
                crate::leanh::lean_closure_set(v___f_2524_, 8, v_connectionLimit_2496_);
                crate::leanh::lean_closure_set(v___f_2524_, 9, v___x_2497_);
                crate::leanh::lean_closure_set(v___f_2524_, 10, v___x_2523_);
                crate::leanh::lean_closure_set(v___f_2524_, 11, v___x_2499_);
                crate::leanh::lean_closure_set(v___f_2524_, 12, v_inst_2500_);
                crate::leanh::lean_closure_set(v___f_2524_, 13, v_val_2501_);
                crate::leanh::lean_closure_set(v___f_2524_, 14, v_handler_2502_);
                crate::leanh::lean_closure_set(v___f_2524_, 15, v_config_2503_);
                crate::leanh::lean_closure_set(v___f_2524_, 16, v_extensions_2504_);
                crate::leanh::lean_closure_set(v___f_2524_, 17, v___f_2505_);
                crate::leanh::lean_closure_set(v___f_2524_, 18, v___f_2521_);
                v___x_2525_ = crate::leanh::lean_alloc_closure(
                    l_Std_Async_BaseAsync_toRawBaseIO___boxed as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___x_2525_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_2525_, 1, v___f_2524_);
                v___x_2526_ = lean_io_as_task(v___x_2525_, v___x_2497_);
                crate::leanh::lean_dec_ref(v___x_2526_);
                if v_isShared_2520_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2519_, 0, v___x_2495_);
                    v___x_2528_ = v___x_2519_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2530_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2530_, 0, v___x_2495_);
                    v___x_2528_ = v_reuseFailAlloc_2530_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2529_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2529_, 0, v___x_2528_);
                return v___x_2529_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__14___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2532_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_activeConnections_2533_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v___f_2534_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v___f_2535_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v___f_2536_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_permitAcquired_2537_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___x_2538_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_connectionLimit_2539_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___x_2540_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___x_2541_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___x_2542_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_inst_2543_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_val_2544_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_handler_2545_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_config_2546_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v_extensions_2547_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___f_2548_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_x_2549_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___y_2550_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v_permitAcquired_boxed_2551_: u8 = 0;
    let mut v___x_14010__boxed_2552_: u8 = 0;
    let mut v_res_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_permitAcquired_boxed_2551_ = (crate::leanh::lean_unbox(v_permitAcquired_2537_) as u8);
    v___x_14010__boxed_2552_ = (crate::leanh::lean_unbox(v___x_2541_) as u8);
    v_res_2553_ = l_Std_Http_Server_serve___redArg___lam__14(
        v___x_2532_,
        v_activeConnections_2533_,
        v___f_2534_,
        v___f_2535_,
        v___f_2536_,
        v_permitAcquired_boxed_2551_,
        v___x_2538_,
        v_connectionLimit_2539_,
        v___x_2540_,
        v___x_14010__boxed_2552_,
        v___x_2542_,
        v_inst_2543_,
        v_val_2544_,
        v_handler_2545_,
        v_config_2546_,
        v_extensions_2547_,
        v___f_2548_,
        v_x_2549_,
    );
    return v_res_2553_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__15(
    mut v___x_2554_: *mut crate::leanh::LeanObject,
    mut v___x_2555_: u8,
    mut v___f_2556_: *mut crate::leanh::LeanObject,
    mut v_x_2557_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2562_: u8 = 0;
    let mut v___x_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2567_: u8 = 0;
    let mut v_a_2568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2571_: u8 = 0;
    let mut v___x_2572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2578_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2557_) == 0 {
                    crate::leanh::lean_dec_ref(v___f_2556_);
                    crate::leanh::lean_dec(v___x_2554_);
                    v_a_2559_ = crate::leanh::lean_ctor_get(v_x_2557_, 0);
                    v_isSharedCheck_2567_ = (!crate::leanh::lean_is_exclusive(v_x_2557_)) as u8;
                    if v_isSharedCheck_2567_ == 0 {
                        v___x_2561_ = v_x_2557_;
                        v_isShared_2562_ = v_isSharedCheck_2567_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2559_);
                        crate::leanh::lean_dec(v_x_2557_);
                        v___x_2561_ = crate::leanh::lean_box(0);
                        v_isShared_2562_ = v_isSharedCheck_2567_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2568_ = crate::leanh::lean_ctor_get(v_x_2557_, 0);
                    v_isSharedCheck_2578_ = (!crate::leanh::lean_is_exclusive(v_x_2557_)) as u8;
                    if v_isSharedCheck_2578_ == 0 {
                        v___x_2570_ = v_x_2557_;
                        v_isShared_2571_ = v_isSharedCheck_2578_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2568_);
                        crate::leanh::lean_dec(v_x_2557_);
                        v___x_2570_ = crate::leanh::lean_box(0);
                        v_isShared_2571_ = v_isSharedCheck_2578_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2562_ == 0 {
                    v___x_2564_ = v___x_2561_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2566_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2566_, 0, v_a_2559_);
                    v___x_2564_ = v_reuseFailAlloc_2566_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2565_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2565_, 0, v___x_2564_);
                return v___x_2565_;
            }
            3 => {
                v___x_2572_ = l_Std_CancellationContext_fork(v_a_2568_);
                if v_isShared_2571_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2570_, 0, v___x_2572_);
                    v___x_2574_ = v___x_2570_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2577_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2577_, 0, v___x_2572_);
                    v___x_2574_ = v_reuseFailAlloc_2577_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2575_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2575_, 0, v___x_2574_);
                v___x_2576_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_2554_,
                    v___x_2555_,
                    v___x_2575_,
                    v___f_2556_,
                );
                return v___x_2576_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__15___boxed(
    mut v___x_2579_: *mut crate::leanh::LeanObject,
    mut v___x_2580_: *mut crate::leanh::LeanObject,
    mut v___f_2581_: *mut crate::leanh::LeanObject,
    mut v_x_2582_: *mut crate::leanh::LeanObject,
    mut v___y_2583_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_14092__boxed_2584_: u8 = 0;
    let mut v_res_2585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_14092__boxed_2584_ = (crate::leanh::lean_unbox(v___x_2580_) as u8);
    v_res_2585_ = l_Std_Http_Server_serve___redArg___lam__15(
        v___x_2579_,
        v___x_14092__boxed_2584_,
        v___f_2581_,
        v_x_2582_,
    );
    return v_res_2585_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__16(
    mut v___x_2586_: *mut crate::leanh::LeanObject,
    mut v_activeConnections_2587_: *mut crate::leanh::LeanObject,
    mut v___f_2588_: *mut crate::leanh::LeanObject,
    mut v___f_2589_: *mut crate::leanh::LeanObject,
    mut v___f_2590_: *mut crate::leanh::LeanObject,
    mut v_permitAcquired_2591_: u8,
    mut v___x_2592_: *mut crate::leanh::LeanObject,
    mut v_connectionLimit_2593_: *mut crate::leanh::LeanObject,
    mut v___x_2594_: u8,
    mut v_inst_2595_: *mut crate::leanh::LeanObject,
    mut v_val_2596_: *mut crate::leanh::LeanObject,
    mut v_handler_2597_: *mut crate::leanh::LeanObject,
    mut v_config_2598_: *mut crate::leanh::LeanObject,
    mut v___f_2599_: *mut crate::leanh::LeanObject,
    mut v___f_2600_: *mut crate::leanh::LeanObject,
    mut v_extensions_2601_: *mut crate::leanh::LeanObject,
    mut v___y_2602_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2604_ = l_Std_Http_instTransportClient;
    v___x_2605_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2606_ = crate::leanh::lean_box((v_permitAcquired_2591_) as usize);
    v___x_2607_ = crate::leanh::lean_box((v___x_2594_) as usize);
    v___f_2608_ = crate::leanh::lean_alloc_closure(
        l_Std_Http_Server_serve___redArg___lam__14___boxed as *mut core::ffi::c_void,
        19,
        17,
    );
    crate::leanh::lean_closure_set(v___f_2608_, 0, v___x_2586_);
    crate::leanh::lean_closure_set(v___f_2608_, 1, v_activeConnections_2587_);
    crate::leanh::lean_closure_set(v___f_2608_, 2, v___f_2588_);
    crate::leanh::lean_closure_set(v___f_2608_, 3, v___f_2589_);
    crate::leanh::lean_closure_set(v___f_2608_, 4, v___f_2590_);
    crate::leanh::lean_closure_set(v___f_2608_, 5, v___x_2606_);
    crate::leanh::lean_closure_set(v___f_2608_, 6, v___x_2592_);
    crate::leanh::lean_closure_set(v___f_2608_, 7, v_connectionLimit_2593_);
    crate::leanh::lean_closure_set(v___f_2608_, 8, v___x_2605_);
    crate::leanh::lean_closure_set(v___f_2608_, 9, v___x_2607_);
    crate::leanh::lean_closure_set(v___f_2608_, 10, v___x_2604_);
    crate::leanh::lean_closure_set(v___f_2608_, 11, v_inst_2595_);
    crate::leanh::lean_closure_set(v___f_2608_, 12, v_val_2596_);
    crate::leanh::lean_closure_set(v___f_2608_, 13, v_handler_2597_);
    crate::leanh::lean_closure_set(v___f_2608_, 14, v_config_2598_);
    crate::leanh::lean_closure_set(v___f_2608_, 15, v_extensions_2601_);
    crate::leanh::lean_closure_set(v___f_2608_, 16, v___f_2599_);
    v___x_2609_ = crate::leanh::lean_box((v___x_2594_) as usize);
    v___f_2610_ = crate::leanh::lean_alloc_closure(
        l_Std_Http_Server_serve___redArg___lam__15___boxed as *mut core::ffi::c_void,
        5,
        3,
    );
    crate::leanh::lean_closure_set(v___f_2610_, 0, v___x_2605_);
    crate::leanh::lean_closure_set(v___f_2610_, 1, v___x_2609_);
    crate::leanh::lean_closure_set(v___f_2610_, 2, v___f_2608_);
    crate::leanh::lean_inc_ref(v___y_2602_);
    v___x_2611_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2611_, 0, v___y_2602_);
    v___x_2612_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2612_, 0, v___x_2611_);
    v___x_2613_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2605_,
        v___x_2594_,
        v___x_2612_,
        v___f_2610_,
    );
    v___x_2614_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2605_,
        v___x_2594_,
        v___x_2613_,
        v___f_2600_,
    );
    return v___x_2614_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__16___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2615_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_activeConnections_2616_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v___f_2617_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v___f_2618_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v___f_2619_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_permitAcquired_2620_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___x_2621_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_connectionLimit_2622_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___x_2623_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_inst_2624_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_val_2625_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_handler_2626_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_config_2627_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___f_2628_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___f_2629_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v_extensions_2630_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_2631_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_2632_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_permitAcquired_boxed_2633_: u8 = 0;
    let mut v___x_14151__boxed_2634_: u8 = 0;
    let mut v_res_2635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_permitAcquired_boxed_2633_ = (crate::leanh::lean_unbox(v_permitAcquired_2620_) as u8);
    v___x_14151__boxed_2634_ = (crate::leanh::lean_unbox(v___x_2623_) as u8);
    v_res_2635_ = l_Std_Http_Server_serve___redArg___lam__16(
        v___x_2615_,
        v_activeConnections_2616_,
        v___f_2617_,
        v___f_2618_,
        v___f_2619_,
        v_permitAcquired_boxed_2633_,
        v___x_2621_,
        v_connectionLimit_2622_,
        v___x_14151__boxed_2634_,
        v_inst_2624_,
        v_val_2625_,
        v_handler_2626_,
        v_config_2627_,
        v___f_2628_,
        v___f_2629_,
        v_extensions_2630_,
        v___y_2631_,
    );
    crate::leanh::lean_dec_ref(v___y_2631_);
    return v_res_2635_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__17(
    mut v___f_2636_: *mut crate::leanh::LeanObject,
    mut v___y_2637_: *mut crate::leanh::LeanObject,
    mut v_x_2638_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2643_: u8 = 0;
    let mut v___x_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2648_: u8 = 0;
    let mut v_a_2649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2638_) == 0 {
                    crate::leanh::lean_dec_ref(v___f_2636_);
                    v_a_2640_ = crate::leanh::lean_ctor_get(v_x_2638_, 0);
                    v_isSharedCheck_2648_ = (!crate::leanh::lean_is_exclusive(v_x_2638_)) as u8;
                    if v_isSharedCheck_2648_ == 0 {
                        v___x_2642_ = v_x_2638_;
                        v_isShared_2643_ = v_isSharedCheck_2648_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2640_);
                        crate::leanh::lean_dec(v_x_2638_);
                        v___x_2642_ = crate::leanh::lean_box(0);
                        v_isShared_2643_ = v_isSharedCheck_2648_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2649_ = crate::leanh::lean_ctor_get(v_x_2638_, 0);
                    crate::leanh::lean_inc(v_a_2649_);
                    crate::leanh::lean_dec_ref_known(v_x_2638_, 1);
                    crate::leanh::lean_inc_ref(v___y_2637_);
                    v___x_2650_ = crate::leanh::lean_apply_3(
                        v___f_2636_,
                        v_a_2649_,
                        v___y_2637_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_2650_;
                }
            }
            1 => {
                if v_isShared_2643_ == 0 {
                    v___x_2645_ = v___x_2642_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2647_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2647_, 0, v_a_2640_);
                    v___x_2645_ = v_reuseFailAlloc_2647_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2646_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2646_, 0, v___x_2645_);
                return v___x_2646_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__17___boxed(
    mut v___f_2651_: *mut crate::leanh::LeanObject,
    mut v___y_2652_: *mut crate::leanh::LeanObject,
    mut v_x_2653_: *mut crate::leanh::LeanObject,
    mut v___y_2654_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2655_ = l_Std_Http_Server_serve___redArg___lam__17(v___f_2651_, v___y_2652_, v_x_2653_);
    crate::leanh::lean_dec_ref(v___y_2652_);
    return v_res_2655_;
}
pub unsafe fn _init_l_Std_Http_Server_serve___redArg___lam__19___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2656_ = l_Std_Http_Extensions_empty;
    v___x_2657_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2657_, 0, v___x_2656_);
    return v___x_2657_;
}
pub unsafe fn _init_l_Std_Http_Server_serve___redArg___lam__19___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2658_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Server_serve___redArg___lam__19___closed__0),
        core::ptr::addr_of_mut!(l_Std_Http_Server_serve___redArg___lam__19___closed__0_once),
        _init_l_Std_Http_Server_serve___redArg___lam__19___closed__0,
    );
    v___x_2659_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2659_, 0, v___x_2658_);
    return v___x_2659_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__19(
    mut v___x_2661_: u8,
    mut v___f_2662_: *mut crate::leanh::LeanObject,
    mut v___f_2663_: *mut crate::leanh::LeanObject,
    mut v_x_2664_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2669_: u8 = 0;
    let mut v___x_2671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2674_: u8 = 0;
    let mut v_a_2675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2682_: u8 = 0;
    let mut v___x_2683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dyn_2685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2695_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2664_) == 0 {
                    crate::leanh::lean_dec_ref(v___f_2663_);
                    crate::leanh::lean_dec_ref(v___f_2662_);
                    v_a_2666_ = crate::leanh::lean_ctor_get(v_x_2664_, 0);
                    v_isSharedCheck_2674_ = (!crate::leanh::lean_is_exclusive(v_x_2664_)) as u8;
                    if v_isSharedCheck_2674_ == 0 {
                        v___x_2668_ = v_x_2664_;
                        v_isShared_2669_ = v_isSharedCheck_2674_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2666_);
                        crate::leanh::lean_dec(v_x_2664_);
                        v___x_2668_ = crate::leanh::lean_box(0);
                        v_isShared_2669_ = v_isSharedCheck_2674_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2675_ = crate::leanh::lean_ctor_get(v_x_2664_, 0);
                    crate::leanh::lean_inc(v_a_2675_);
                    crate::leanh::lean_dec_ref_known(v_x_2664_, 1);
                    if crate::leanh::lean_obj_tag(v_a_2675_) == 0 {
                        crate::leanh::lean_dec_ref_known(v_a_2675_, 1);
                        crate::leanh::lean_dec_ref(v___f_2663_);
                        v___x_2676_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Server_serve___redArg___lam__19___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Server_serve___redArg___lam__19___closed__1_once
                            ),
                            _init_l_Std_Http_Server_serve___redArg___lam__19___closed__1,
                        );
                        v___x_2677_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_2678_ =
                            l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                                crate::leanh::lean_box(0),
                                crate::leanh::lean_box(0),
                                v___x_2677_,
                                v___x_2661_,
                                v___x_2676_,
                                v___f_2662_,
                            );
                        return v___x_2678_;
                    } else {
                        crate::leanh::lean_dec_ref(v___f_2662_);
                        v_a_2679_ = crate::leanh::lean_ctor_get(v_a_2675_, 0);
                        v_isSharedCheck_2695_ = (!crate::leanh::lean_is_exclusive(v_a_2675_)) as u8;
                        if v_isSharedCheck_2695_ == 0 {
                            v___x_2681_ = v_a_2675_;
                            v_isShared_2682_ = v_isSharedCheck_2695_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2679_);
                            crate::leanh::lean_dec(v_a_2675_);
                            v___x_2681_ = crate::leanh::lean_box(0);
                            v_isShared_2682_ = v_isSharedCheck_2695_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_2669_ == 0 {
                    v___x_2671_ = v___x_2668_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2673_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2673_, 0, v_a_2666_);
                    v___x_2671_ = v_reuseFailAlloc_2673_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2672_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2672_, 0, v___x_2671_);
                return v___x_2672_;
            }
            3 => {
                v___x_2683_ = l_Std_Http_Extensions_empty;
                v___x_2684_ = l_Std_Http_Server_instImpl_00___x40_Std_Http_Server_Connection_3058719504____hygCtx___hyg_8_;
                v_dyn_2685_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v_dyn_2685_, 0, v___x_2684_);
                crate::leanh::lean_ctor_set(v_dyn_2685_, 1, v_a_2679_);
                v___x_2686_ = l_Std_Http_Server_serve___redArg___lam__19___closed__2;
                v___x_2687_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_dyn_2685_);
                v___x_2688_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
                    v___x_2686_,
                    v___x_2687_,
                    v_dyn_2685_,
                    v___x_2683_,
                );
                if v_isShared_2682_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2681_, 0, v___x_2688_);
                    v___x_2690_ = v___x_2681_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2694_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2694_, 0, v___x_2688_);
                    v___x_2690_ = v_reuseFailAlloc_2694_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2691_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2691_, 0, v___x_2690_);
                v___x_2692_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2693_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_2692_,
                    v___x_2661_,
                    v___x_2691_,
                    v___f_2663_,
                );
                return v___x_2693_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__19___boxed(
    mut v___x_2696_: *mut crate::leanh::LeanObject,
    mut v___f_2697_: *mut crate::leanh::LeanObject,
    mut v___f_2698_: *mut crate::leanh::LeanObject,
    mut v_x_2699_: *mut crate::leanh::LeanObject,
    mut v___y_2700_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_14248__boxed_2701_: u8 = 0;
    let mut v_res_2702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_14248__boxed_2701_ = (crate::leanh::lean_unbox(v___x_2696_) as u8);
    v_res_2702_ = l_Std_Http_Server_serve___redArg___lam__19(
        v___x_14248__boxed_2701_,
        v___f_2697_,
        v___f_2698_,
        v_x_2699_,
    );
    return v_res_2702_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__18(
    mut v_permitAcquired_2703_: u8,
    mut v___f_2704_: *mut crate::leanh::LeanObject,
    mut v___x_2705_: *mut crate::leanh::LeanObject,
    mut v___y_2706_: *mut crate::leanh::LeanObject,
    mut v_connectionLimit_2707_: *mut crate::leanh::LeanObject,
    mut v___x_2708_: u8,
    mut v___f_2709_: *mut crate::leanh::LeanObject,
    mut v___x_2710_: *mut crate::leanh::LeanObject,
    mut v_activeConnections_2711_: *mut crate::leanh::LeanObject,
    mut v___f_2712_: *mut crate::leanh::LeanObject,
    mut v___f_2713_: *mut crate::leanh::LeanObject,
    mut v___f_2714_: *mut crate::leanh::LeanObject,
    mut v_inst_2715_: *mut crate::leanh::LeanObject,
    mut v_handler_2716_: *mut crate::leanh::LeanObject,
    mut v_config_2717_: *mut crate::leanh::LeanObject,
    mut v___f_2718_: *mut crate::leanh::LeanObject,
    mut v___f_2719_: *mut crate::leanh::LeanObject,
    mut v_x_2720_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2725_: u8 = 0;
    let mut v___x_2727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2730_: u8 = 0;
    let mut v_a_2731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2734_: u8 = 0;
    let mut v___x_2735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2739_: u8 = 0;
    let mut v___x_2740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2749_: u8 = 0;
    let mut v___x_2750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2754_: u8 = 0;
    let mut v___x_2755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2775_: u8 = 0;
    let mut v___x_2777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2779_: u8 = 0;
    let mut v_a_2780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2783_: u8 = 0;
    let mut v___x_2785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2787_: u8 = 0;
    let mut v_isSharedCheck_2788_: u8 = 0;
    let mut v_isSharedCheck_2789_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2720_) == 0 {
                    crate::leanh::lean_dec_ref(v___f_2719_);
                    crate::leanh::lean_dec_ref(v___f_2718_);
                    crate::leanh::lean_dec_ref(v_config_2717_);
                    crate::leanh::lean_dec(v_handler_2716_);
                    crate::leanh::lean_dec_ref(v_inst_2715_);
                    crate::leanh::lean_dec_ref(v___f_2714_);
                    crate::leanh::lean_dec_ref(v___f_2713_);
                    crate::leanh::lean_dec_ref(v___f_2712_);
                    crate::leanh::lean_dec_ref(v_activeConnections_2711_);
                    crate::leanh::lean_dec_ref(v___x_2710_);
                    crate::leanh::lean_dec_ref(v___f_2709_);
                    crate::leanh::lean_dec(v_connectionLimit_2707_);
                    crate::leanh::lean_dec_ref(v___f_2704_);
                    v_a_2722_ = crate::leanh::lean_ctor_get(v_x_2720_, 0);
                    v_isSharedCheck_2730_ = (!crate::leanh::lean_is_exclusive(v_x_2720_)) as u8;
                    if v_isSharedCheck_2730_ == 0 {
                        v___x_2724_ = v_x_2720_;
                        v_isShared_2725_ = v_isSharedCheck_2730_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2722_);
                        crate::leanh::lean_dec(v_x_2720_);
                        v___x_2724_ = crate::leanh::lean_box(0);
                        v_isShared_2725_ = v_isSharedCheck_2730_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2731_ = crate::leanh::lean_ctor_get(v_x_2720_, 0);
                    v_isSharedCheck_2789_ = (!crate::leanh::lean_is_exclusive(v_x_2720_)) as u8;
                    if v_isSharedCheck_2789_ == 0 {
                        v___x_2733_ = v_x_2720_;
                        v_isShared_2734_ = v_isSharedCheck_2789_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2731_);
                        crate::leanh::lean_dec(v_x_2720_);
                        v___x_2733_ = crate::leanh::lean_box(0);
                        v_isShared_2734_ = v_isSharedCheck_2789_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2725_ == 0 {
                    v___x_2727_ = v___x_2724_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2729_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2729_, 0, v_a_2722_);
                    v___x_2727_ = v_reuseFailAlloc_2729_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2728_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2728_, 0, v___x_2727_);
                return v___x_2728_;
            }
            3 => {
                if crate::leanh::lean_obj_tag(v_a_2731_) == 0 {
                    crate::leanh::lean_dec_ref(v___f_2719_);
                    crate::leanh::lean_dec_ref(v___f_2718_);
                    crate::leanh::lean_dec_ref(v_config_2717_);
                    crate::leanh::lean_dec(v_handler_2716_);
                    crate::leanh::lean_dec_ref(v_inst_2715_);
                    crate::leanh::lean_dec_ref(v___f_2714_);
                    crate::leanh::lean_dec_ref(v___f_2713_);
                    crate::leanh::lean_dec_ref(v___f_2712_);
                    crate::leanh::lean_dec_ref(v_activeConnections_2711_);
                    crate::leanh::lean_dec_ref(v___x_2710_);
                    if v_permitAcquired_2703_ == 0 {
                        crate::leanh::lean_del_object(v___x_2733_);
                        crate::leanh::lean_dec_ref(v___f_2709_);
                        crate::leanh::lean_dec(v_connectionLimit_2707_);
                        crate::leanh::lean_inc_ref(v___y_2706_);
                        v___x_2735_ = crate::leanh::lean_apply_3(
                            v___f_2704_,
                            v___x_2705_,
                            v___y_2706_,
                            crate::leanh::lean_box(0),
                        );
                        return v___x_2735_;
                    } else {
                        if crate::leanh::lean_obj_tag(v_connectionLimit_2707_) == 1 {
                            crate::leanh::lean_dec_ref(v___f_2704_);
                            v_val_2736_ = crate::leanh::lean_ctor_get(v_connectionLimit_2707_, 0);
                            v_isSharedCheck_2749_ =
                                (!crate::leanh::lean_is_exclusive(v_connectionLimit_2707_)) as u8;
                            if v_isSharedCheck_2749_ == 0 {
                                v___x_2738_ = v_connectionLimit_2707_;
                                v_isShared_2739_ = v_isSharedCheck_2749_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_val_2736_);
                                crate::leanh::lean_dec(v_connectionLimit_2707_);
                                v___x_2738_ = crate::leanh::lean_box(0);
                                v_isShared_2739_ = v_isSharedCheck_2749_;
                                state = 4;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_2733_);
                            crate::leanh::lean_dec_ref(v___f_2709_);
                            crate::leanh::lean_dec(v_connectionLimit_2707_);
                            crate::leanh::lean_inc_ref(v___y_2706_);
                            v___x_2750_ = crate::leanh::lean_apply_3(
                                v___f_2704_,
                                v___x_2705_,
                                v___y_2706_,
                                crate::leanh::lean_box(0),
                            );
                            return v___x_2750_;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___f_2709_);
                    crate::leanh::lean_dec_ref(v___f_2704_);
                    v_val_2751_ = crate::leanh::lean_ctor_get(v_a_2731_, 0);
                    v_isSharedCheck_2788_ = (!crate::leanh::lean_is_exclusive(v_a_2731_)) as u8;
                    if v_isSharedCheck_2788_ == 0 {
                        v___x_2753_ = v_a_2731_;
                        v_isShared_2754_ = v_isSharedCheck_2788_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2751_);
                        crate::leanh::lean_dec(v_a_2731_);
                        v___x_2753_ = crate::leanh::lean_box(0);
                        v_isShared_2754_ = v_isSharedCheck_2788_;
                        state = 7;
                        continue;
                    }
                }
            }
            4 => {
                v___x_2740_ = l_Std_Semaphore_release(v_val_2736_);
                if v_isShared_2734_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2733_, 0, v___x_2740_);
                    v___x_2742_ = v___x_2733_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2748_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2748_, 0, v___x_2740_);
                    v___x_2742_ = v_reuseFailAlloc_2748_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_2739_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2738_, 0);
                    crate::leanh::lean_ctor_set(v___x_2738_, 0, v___x_2742_);
                    v___x_2744_ = v___x_2738_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2747_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2747_, 0, v___x_2742_);
                    v___x_2744_ = v_reuseFailAlloc_2747_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_2745_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2746_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_2745_,
                    v___x_2708_,
                    v___x_2744_,
                    v___f_2709_,
                );
                return v___x_2746_;
            }
            7 => {
                v___x_2755_ = crate::leanh::lean_box((v_permitAcquired_2703_) as usize);
                v___x_2756_ = crate::leanh::lean_box((v___x_2708_) as usize);
                crate::leanh::lean_inc(v_val_2751_);
                v___f_2757_ = crate::leanh::lean_alloc_closure(
                    l_Std_Http_Server_serve___redArg___lam__16___boxed as *mut core::ffi::c_void,
                    18,
                    15,
                );
                crate::leanh::lean_closure_set(v___f_2757_, 0, v___x_2710_);
                crate::leanh::lean_closure_set(v___f_2757_, 1, v_activeConnections_2711_);
                crate::leanh::lean_closure_set(v___f_2757_, 2, v___f_2712_);
                crate::leanh::lean_closure_set(v___f_2757_, 3, v___f_2713_);
                crate::leanh::lean_closure_set(v___f_2757_, 4, v___f_2714_);
                crate::leanh::lean_closure_set(v___f_2757_, 5, v___x_2755_);
                crate::leanh::lean_closure_set(v___f_2757_, 6, v___x_2705_);
                crate::leanh::lean_closure_set(v___f_2757_, 7, v_connectionLimit_2707_);
                crate::leanh::lean_closure_set(v___f_2757_, 8, v___x_2756_);
                crate::leanh::lean_closure_set(v___f_2757_, 9, v_inst_2715_);
                crate::leanh::lean_closure_set(v___f_2757_, 10, v_val_2751_);
                crate::leanh::lean_closure_set(v___f_2757_, 11, v_handler_2716_);
                crate::leanh::lean_closure_set(v___f_2757_, 12, v_config_2717_);
                crate::leanh::lean_closure_set(v___f_2757_, 13, v___f_2718_);
                crate::leanh::lean_closure_set(v___f_2757_, 14, v___f_2719_);
                crate::leanh::lean_inc_ref(v___y_2706_);
                v___f_2758_ = crate::leanh::lean_alloc_closure(
                    l_Std_Http_Server_serve___redArg___lam__17___boxed as *mut core::ffi::c_void,
                    4,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_2758_, 0, v___f_2757_);
                crate::leanh::lean_closure_set(v___f_2758_, 1, v___y_2706_);
                v___x_2759_ = crate::leanh::lean_box((v___x_2708_) as usize);
                crate::leanh::lean_inc_ref(v___f_2758_);
                v___f_2760_ = crate::leanh::lean_alloc_closure(
                    l_Std_Http_Server_serve___redArg___lam__19___boxed as *mut core::ffi::c_void,
                    5,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_2760_, 0, v___x_2759_);
                crate::leanh::lean_closure_set(v___f_2760_, 1, v___f_2758_);
                crate::leanh::lean_closure_set(v___f_2760_, 2, v___f_2758_);
                v___x_2771_ = lean_uv_tcp_getpeername(v_val_2751_);
                crate::leanh::lean_dec(v_val_2751_);
                if crate::leanh::lean_obj_tag(v___x_2771_) == 0 {
                    v_a_2772_ = crate::leanh::lean_ctor_get(v___x_2771_, 0);
                    v_isSharedCheck_2779_ = (!crate::leanh::lean_is_exclusive(v___x_2771_)) as u8;
                    if v_isSharedCheck_2779_ == 0 {
                        v___x_2774_ = v___x_2771_;
                        v_isShared_2775_ = v_isSharedCheck_2779_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2772_);
                        crate::leanh::lean_dec(v___x_2771_);
                        v___x_2774_ = crate::leanh::lean_box(0);
                        v_isShared_2775_ = v_isSharedCheck_2779_;
                        state = 11;
                        continue;
                    }
                } else {
                    v_a_2780_ = crate::leanh::lean_ctor_get(v___x_2771_, 0);
                    v_isSharedCheck_2787_ = (!crate::leanh::lean_is_exclusive(v___x_2771_)) as u8;
                    if v_isSharedCheck_2787_ == 0 {
                        v___x_2782_ = v___x_2771_;
                        v_isShared_2783_ = v_isSharedCheck_2787_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2780_);
                        crate::leanh::lean_dec(v___x_2771_);
                        v___x_2782_ = crate::leanh::lean_box(0);
                        v_isShared_2783_ = v_isSharedCheck_2787_;
                        state = 13;
                        continue;
                    }
                }
            }
            8 => {
                if v_isShared_2734_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2733_, 0, v_val_2762_);
                    v___x_2764_ = v___x_2733_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2770_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2770_, 0, v_val_2762_);
                    v___x_2764_ = v_reuseFailAlloc_2770_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_2754_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2753_, 0);
                    crate::leanh::lean_ctor_set(v___x_2753_, 0, v___x_2764_);
                    v___x_2766_ = v___x_2753_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2769_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2769_, 0, v___x_2764_);
                    v___x_2766_ = v_reuseFailAlloc_2769_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_2767_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2768_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_2767_,
                    v___x_2708_,
                    v___x_2766_,
                    v___f_2760_,
                );
                return v___x_2768_;
            }
            11 => {
                if v_isShared_2775_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2774_, 1);
                    v___x_2777_ = v___x_2774_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2778_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2778_, 0, v_a_2772_);
                    v___x_2777_ = v_reuseFailAlloc_2778_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v_val_2762_ = v___x_2777_;
                state = 8;
                continue;
            }
            13 => {
                if v_isShared_2783_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2782_, 0);
                    v___x_2785_ = v___x_2782_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2786_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2786_, 0, v_a_2780_);
                    v___x_2785_ = v_reuseFailAlloc_2786_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v_val_2762_ = v___x_2785_;
                state = 8;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__18___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_permitAcquired_2790_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v___f_2791_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v___x_2792_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v___y_2793_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_connectionLimit_2794_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___x_2795_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___f_2796_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___x_2797_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_activeConnections_2798_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___f_2799_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___f_2800_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___f_2801_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_inst_2802_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_handler_2803_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_config_2804_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___f_2805_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___f_2806_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_x_2807_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___y_2808_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v_permitAcquired_boxed_2809_: u8 = 0;
    let mut v___x_14330__boxed_2810_: u8 = 0;
    let mut v_res_2811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_permitAcquired_boxed_2809_ = (crate::leanh::lean_unbox(v_permitAcquired_2790_) as u8);
    v___x_14330__boxed_2810_ = (crate::leanh::lean_unbox(v___x_2795_) as u8);
    v_res_2811_ = l_Std_Http_Server_serve___redArg___lam__18(
        v_permitAcquired_boxed_2809_,
        v___f_2791_,
        v___x_2792_,
        v___y_2793_,
        v_connectionLimit_2794_,
        v___x_14330__boxed_2810_,
        v___f_2796_,
        v___x_2797_,
        v_activeConnections_2798_,
        v___f_2799_,
        v___f_2800_,
        v___f_2801_,
        v_inst_2802_,
        v_handler_2803_,
        v_config_2804_,
        v___f_2805_,
        v___f_2806_,
        v_x_2807_,
    );
    crate::leanh::lean_dec_ref(v___y_2793_);
    return v_res_2811_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__20(
    mut v_a_2812_: *mut crate::leanh::LeanObject,
    mut v___f_2813_: *mut crate::leanh::LeanObject,
    mut v___f_2814_: *mut crate::leanh::LeanObject,
    mut v___x_2815_: u8,
    mut v___f_2816_: *mut crate::leanh::LeanObject,
    mut v_x_2817_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2822_: u8 = 0;
    let mut v___x_2824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2827_: u8 = 0;
    let mut v_a_2828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2817_) == 0 {
                    crate::leanh::lean_dec_ref(v___f_2816_);
                    crate::leanh::lean_dec_ref(v___f_2814_);
                    crate::leanh::lean_dec_ref(v___f_2813_);
                    crate::leanh::lean_dec(v_a_2812_);
                    v_a_2819_ = crate::leanh::lean_ctor_get(v_x_2817_, 0);
                    v_isSharedCheck_2827_ = (!crate::leanh::lean_is_exclusive(v_x_2817_)) as u8;
                    if v_isSharedCheck_2827_ == 0 {
                        v___x_2821_ = v_x_2817_;
                        v_isShared_2822_ = v_isSharedCheck_2827_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2819_);
                        crate::leanh::lean_dec(v_x_2817_);
                        v___x_2821_ = crate::leanh::lean_box(0);
                        v_isShared_2822_ = v_isSharedCheck_2827_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2828_ = crate::leanh::lean_ctor_get(v_x_2817_, 0);
                    crate::leanh::lean_inc(v_a_2828_);
                    crate::leanh::lean_dec_ref_known(v_x_2817_, 1);
                    v___x_2829_ = l_Std_Async_TCP_Socket_Server_acceptSelector(v_a_2812_);
                    v___x_2830_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2830_, 0, v___x_2829_);
                    crate::leanh::lean_ctor_set(v___x_2830_, 1, v___f_2813_);
                    v___x_2831_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2831_, 0, v_a_2828_);
                    crate::leanh::lean_ctor_set(v___x_2831_, 1, v___f_2814_);
                    v___x_2832_ = crate::leanh::lean_unsigned_to_nat(2);
                    v___x_2833_ = lean_mk_empty_array_with_capacity(v___x_2832_);
                    v___x_2834_ = lean_array_push(v___x_2833_, v___x_2830_);
                    v___x_2835_ = lean_array_push(v___x_2834_, v___x_2831_);
                    v___x_2836_ = l_Std_Async_Selectable_one___redArg(v___x_2835_);
                    v___x_2837_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2838_ =
                        l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v___x_2837_,
                            v___x_2815_,
                            v___x_2836_,
                            v___f_2816_,
                        );
                    return v___x_2838_;
                }
            }
            1 => {
                if v_isShared_2822_ == 0 {
                    v___x_2824_ = v___x_2821_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2826_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2826_, 0, v_a_2819_);
                    v___x_2824_ = v_reuseFailAlloc_2826_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2825_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2825_, 0, v___x_2824_);
                return v___x_2825_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__20___boxed(
    mut v_a_2839_: *mut crate::leanh::LeanObject,
    mut v___f_2840_: *mut crate::leanh::LeanObject,
    mut v___f_2841_: *mut crate::leanh::LeanObject,
    mut v___x_2842_: *mut crate::leanh::LeanObject,
    mut v___f_2843_: *mut crate::leanh::LeanObject,
    mut v_x_2844_: *mut crate::leanh::LeanObject,
    mut v___y_2845_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_14508__boxed_2846_: u8 = 0;
    let mut v_res_2847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_14508__boxed_2846_ = (crate::leanh::lean_unbox(v___x_2842_) as u8);
    v_res_2847_ = l_Std_Http_Server_serve___redArg___lam__20(
        v_a_2839_,
        v___f_2840_,
        v___f_2841_,
        v___x_14508__boxed_2846_,
        v___f_2843_,
        v_x_2844_,
    );
    return v_res_2847_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__21(
    mut v___x_2848_: u8,
    mut v___f_2849_: *mut crate::leanh::LeanObject,
    mut v___f_2850_: *mut crate::leanh::LeanObject,
    mut v___x_2851_: *mut crate::leanh::LeanObject,
    mut v_connectionLimit_2852_: *mut crate::leanh::LeanObject,
    mut v___x_2853_: *mut crate::leanh::LeanObject,
    mut v_activeConnections_2854_: *mut crate::leanh::LeanObject,
    mut v___f_2855_: *mut crate::leanh::LeanObject,
    mut v___f_2856_: *mut crate::leanh::LeanObject,
    mut v___f_2857_: *mut crate::leanh::LeanObject,
    mut v_inst_2858_: *mut crate::leanh::LeanObject,
    mut v_handler_2859_: *mut crate::leanh::LeanObject,
    mut v_config_2860_: *mut crate::leanh::LeanObject,
    mut v___f_2861_: *mut crate::leanh::LeanObject,
    mut v___f_2862_: *mut crate::leanh::LeanObject,
    mut v_a_2863_: *mut crate::leanh::LeanObject,
    mut v___f_2864_: *mut crate::leanh::LeanObject,
    mut v___f_2865_: *mut crate::leanh::LeanObject,
    mut v_permitAcquired_2866_: u8,
    mut v___y_2867_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref_n(v___y_2867_, 3);
    v___x_2869_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2869_, 0, v___y_2867_);
    v___x_2870_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2870_, 0, v___x_2869_);
    v___x_2871_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2872_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2871_,
        v___x_2848_,
        v___x_2870_,
        v___f_2849_,
    );
    crate::leanh::lean_inc_ref(v___f_2850_);
    v___f_2873_ = crate::leanh::lean_alloc_closure(
        l_Std_Http_Server_serve___redArg___lam__7___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2873_, 0, v___f_2850_);
    crate::leanh::lean_closure_set(v___f_2873_, 1, v___y_2867_);
    v___x_2874_ = crate::leanh::lean_box((v_permitAcquired_2866_) as usize);
    v___x_2875_ = crate::leanh::lean_box((v___x_2848_) as usize);
    v___f_2876_ = crate::leanh::lean_alloc_closure(
        l_Std_Http_Server_serve___redArg___lam__18___boxed as *mut core::ffi::c_void,
        19,
        17,
    );
    crate::leanh::lean_closure_set(v___f_2876_, 0, v___x_2874_);
    crate::leanh::lean_closure_set(v___f_2876_, 1, v___f_2850_);
    crate::leanh::lean_closure_set(v___f_2876_, 2, v___x_2851_);
    crate::leanh::lean_closure_set(v___f_2876_, 3, v___y_2867_);
    crate::leanh::lean_closure_set(v___f_2876_, 4, v_connectionLimit_2852_);
    crate::leanh::lean_closure_set(v___f_2876_, 5, v___x_2875_);
    crate::leanh::lean_closure_set(v___f_2876_, 6, v___f_2873_);
    crate::leanh::lean_closure_set(v___f_2876_, 7, v___x_2853_);
    crate::leanh::lean_closure_set(v___f_2876_, 8, v_activeConnections_2854_);
    crate::leanh::lean_closure_set(v___f_2876_, 9, v___f_2855_);
    crate::leanh::lean_closure_set(v___f_2876_, 10, v___f_2856_);
    crate::leanh::lean_closure_set(v___f_2876_, 11, v___f_2857_);
    crate::leanh::lean_closure_set(v___f_2876_, 12, v_inst_2858_);
    crate::leanh::lean_closure_set(v___f_2876_, 13, v_handler_2859_);
    crate::leanh::lean_closure_set(v___f_2876_, 14, v_config_2860_);
    crate::leanh::lean_closure_set(v___f_2876_, 15, v___f_2861_);
    crate::leanh::lean_closure_set(v___f_2876_, 16, v___f_2862_);
    v___x_2877_ = crate::leanh::lean_box((v___x_2848_) as usize);
    v___f_2878_ = crate::leanh::lean_alloc_closure(
        l_Std_Http_Server_serve___redArg___lam__20___boxed as *mut core::ffi::c_void,
        7,
        5,
    );
    crate::leanh::lean_closure_set(v___f_2878_, 0, v_a_2863_);
    crate::leanh::lean_closure_set(v___f_2878_, 1, v___f_2864_);
    crate::leanh::lean_closure_set(v___f_2878_, 2, v___f_2865_);
    crate::leanh::lean_closure_set(v___f_2878_, 3, v___x_2877_);
    crate::leanh::lean_closure_set(v___f_2878_, 4, v___f_2876_);
    v___x_2879_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2871_,
        v___x_2848_,
        v___x_2872_,
        v___f_2878_,
    );
    return v___x_2879_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__21___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2880_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v___f_2881_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v___f_2882_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v___x_2883_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_connectionLimit_2884_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___x_2885_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_activeConnections_2886_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___f_2887_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___f_2888_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___f_2889_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_inst_2890_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_handler_2891_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_config_2892_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___f_2893_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___f_2894_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v_a_2895_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___f_2896_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___f_2897_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_permitAcquired_2898_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v___y_2899_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v___y_2900_: *mut crate::leanh::LeanObject = *_args.add(20);
    let mut v___x_14566__boxed_2901_: u8 = 0;
    let mut v_permitAcquired_boxed_2902_: u8 = 0;
    let mut v_res_2903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_14566__boxed_2901_ = (crate::leanh::lean_unbox(v___x_2880_) as u8);
    v_permitAcquired_boxed_2902_ = (crate::leanh::lean_unbox(v_permitAcquired_2898_) as u8);
    v_res_2903_ = l_Std_Http_Server_serve___redArg___lam__21(
        v___x_14566__boxed_2901_,
        v___f_2881_,
        v___f_2882_,
        v___x_2883_,
        v_connectionLimit_2884_,
        v___x_2885_,
        v_activeConnections_2886_,
        v___f_2887_,
        v___f_2888_,
        v___f_2889_,
        v_inst_2890_,
        v_handler_2891_,
        v_config_2892_,
        v___f_2893_,
        v___f_2894_,
        v_a_2895_,
        v___f_2896_,
        v___f_2897_,
        v_permitAcquired_boxed_2902_,
        v___y_2899_,
    );
    crate::leanh::lean_dec_ref(v___y_2899_);
    return v_res_2903_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__22(
    mut v___f_2904_: *mut crate::leanh::LeanObject,
    mut v___y_2905_: *mut crate::leanh::LeanObject,
    mut v_x_2906_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2911_: u8 = 0;
    let mut v___x_2913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2916_: u8 = 0;
    let mut v_a_2917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2906_) == 0 {
                    crate::leanh::lean_dec_ref(v___f_2904_);
                    v_a_2908_ = crate::leanh::lean_ctor_get(v_x_2906_, 0);
                    v_isSharedCheck_2916_ = (!crate::leanh::lean_is_exclusive(v_x_2906_)) as u8;
                    if v_isSharedCheck_2916_ == 0 {
                        v___x_2910_ = v_x_2906_;
                        v_isShared_2911_ = v_isSharedCheck_2916_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2908_);
                        crate::leanh::lean_dec(v_x_2906_);
                        v___x_2910_ = crate::leanh::lean_box(0);
                        v_isShared_2911_ = v_isSharedCheck_2916_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2917_ = crate::leanh::lean_ctor_get(v_x_2906_, 0);
                    crate::leanh::lean_inc(v_a_2917_);
                    crate::leanh::lean_dec_ref_known(v_x_2906_, 1);
                    crate::leanh::lean_inc_ref(v___y_2905_);
                    v___x_2918_ = crate::leanh::lean_apply_3(
                        v___f_2904_,
                        v_a_2917_,
                        v___y_2905_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_2918_;
                }
            }
            1 => {
                if v_isShared_2911_ == 0 {
                    v___x_2913_ = v___x_2910_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2915_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2915_, 0, v_a_2908_);
                    v___x_2913_ = v_reuseFailAlloc_2915_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2914_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2914_, 0, v___x_2913_);
                return v___x_2914_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__22___boxed(
    mut v___f_2919_: *mut crate::leanh::LeanObject,
    mut v___y_2920_: *mut crate::leanh::LeanObject,
    mut v_x_2921_: *mut crate::leanh::LeanObject,
    mut v___y_2922_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2923_ = l_Std_Http_Server_serve___redArg___lam__22(v___f_2919_, v___y_2920_, v_x_2921_);
    crate::leanh::lean_dec_ref(v___y_2920_);
    return v_res_2923_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__23(
    mut v___x_2924_: u8,
    mut v___x_2925_: u8,
    mut v___f_2926_: *mut crate::leanh::LeanObject,
    mut v_x_2927_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2932_: u8 = 0;
    let mut v___x_2934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2937_: u8 = 0;
    let mut v___x_2939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2940_: u8 = 0;
    let mut v___x_2941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2948_: u8 = 0;
    let mut v_unused_2949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2927_) == 0 {
                    crate::leanh::lean_dec_ref(v___f_2926_);
                    v_a_2929_ = crate::leanh::lean_ctor_get(v_x_2927_, 0);
                    v_isSharedCheck_2937_ = (!crate::leanh::lean_is_exclusive(v_x_2927_)) as u8;
                    if v_isSharedCheck_2937_ == 0 {
                        v___x_2931_ = v_x_2927_;
                        v_isShared_2932_ = v_isSharedCheck_2937_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2929_);
                        crate::leanh::lean_dec(v_x_2927_);
                        v___x_2931_ = crate::leanh::lean_box(0);
                        v_isShared_2932_ = v_isSharedCheck_2937_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_isSharedCheck_2948_ = (!crate::leanh::lean_is_exclusive(v_x_2927_)) as u8;
                    if v_isSharedCheck_2948_ == 0 {
                        v_unused_2949_ = crate::leanh::lean_ctor_get(v_x_2927_, 0);
                        crate::leanh::lean_dec(v_unused_2949_);
                        v___x_2939_ = v_x_2927_;
                        v_isShared_2940_ = v_isSharedCheck_2948_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_x_2927_);
                        v___x_2939_ = crate::leanh::lean_box(0);
                        v_isShared_2940_ = v_isSharedCheck_2948_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2932_ == 0 {
                    v___x_2934_ = v___x_2931_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2936_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2936_, 0, v_a_2929_);
                    v___x_2934_ = v_reuseFailAlloc_2936_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2935_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2935_, 0, v___x_2934_);
                return v___x_2935_;
            }
            3 => {
                v___x_2941_ = crate::leanh::lean_box((v___x_2924_) as usize);
                if v_isShared_2940_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2939_, 0, v___x_2941_);
                    v___x_2943_ = v___x_2939_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2947_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2947_, 0, v___x_2941_);
                    v___x_2943_ = v_reuseFailAlloc_2947_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2944_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2944_, 0, v___x_2943_);
                v___x_2945_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2946_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_2945_,
                    v___x_2925_,
                    v___x_2944_,
                    v___f_2926_,
                );
                return v___x_2946_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__23___boxed(
    mut v___x_2950_: *mut crate::leanh::LeanObject,
    mut v___x_2951_: *mut crate::leanh::LeanObject,
    mut v___f_2952_: *mut crate::leanh::LeanObject,
    mut v_x_2953_: *mut crate::leanh::LeanObject,
    mut v___y_2954_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_14670__boxed_2955_: u8 = 0;
    let mut v___x_14671__boxed_2956_: u8 = 0;
    let mut v_res_2957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_14670__boxed_2955_ = (crate::leanh::lean_unbox(v___x_2950_) as u8);
    v___x_14671__boxed_2956_ = (crate::leanh::lean_unbox(v___x_2951_) as u8);
    v_res_2957_ = l_Std_Http_Server_serve___redArg___lam__23(
        v___x_14670__boxed_2955_,
        v___x_14671__boxed_2956_,
        v___f_2952_,
        v_x_2953_,
    );
    return v_res_2957_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__24(
    mut v___f_2958_: *mut crate::leanh::LeanObject,
    mut v___x_2959_: u8,
    mut v___f_2960_: *mut crate::leanh::LeanObject,
    mut v_x_2961_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2966_: u8 = 0;
    let mut v___x_2968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2971_: u8 = 0;
    let mut v_a_2972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2961_) == 0 {
                    crate::leanh::lean_dec_ref(v___f_2960_);
                    crate::leanh::lean_dec_ref(v___f_2958_);
                    v_a_2963_ = crate::leanh::lean_ctor_get(v_x_2961_, 0);
                    v_isSharedCheck_2971_ = (!crate::leanh::lean_is_exclusive(v_x_2961_)) as u8;
                    if v_isSharedCheck_2971_ == 0 {
                        v___x_2965_ = v_x_2961_;
                        v_isShared_2966_ = v_isSharedCheck_2971_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2963_);
                        crate::leanh::lean_dec(v_x_2961_);
                        v___x_2965_ = crate::leanh::lean_box(0);
                        v_isShared_2966_ = v_isSharedCheck_2971_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2972_ = crate::leanh::lean_ctor_get(v_x_2961_, 0);
                    crate::leanh::lean_inc(v_a_2972_);
                    crate::leanh::lean_dec_ref_known(v_x_2961_, 1);
                    v___x_2973_ = l_IO_Promise_result_x21___redArg(v_a_2972_);
                    crate::leanh::lean_dec(v_a_2972_);
                    v___x_2974_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2975_ = lean_task_map(v___f_2958_, v___x_2973_, v___x_2974_, v___x_2959_);
                    v___x_2976_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2976_, 0, v___x_2975_);
                    v___x_2977_ =
                        l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v___x_2974_,
                            v___x_2959_,
                            v___x_2976_,
                            v___f_2960_,
                        );
                    return v___x_2977_;
                }
            }
            1 => {
                if v_isShared_2966_ == 0 {
                    v___x_2968_ = v___x_2965_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2970_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2970_, 0, v_a_2963_);
                    v___x_2968_ = v_reuseFailAlloc_2970_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2969_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2969_, 0, v___x_2968_);
                return v___x_2969_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__24___boxed(
    mut v___f_2978_: *mut crate::leanh::LeanObject,
    mut v___x_2979_: *mut crate::leanh::LeanObject,
    mut v___f_2980_: *mut crate::leanh::LeanObject,
    mut v_x_2981_: *mut crate::leanh::LeanObject,
    mut v___y_2982_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_14729__boxed_2983_: u8 = 0;
    let mut v_res_2984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_14729__boxed_2983_ = (crate::leanh::lean_unbox(v___x_2979_) as u8);
    v_res_2984_ = l_Std_Http_Server_serve___redArg___lam__24(
        v___f_2978_,
        v___x_14729__boxed_2983_,
        v___f_2980_,
        v_x_2981_,
    );
    return v_res_2984_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__26(
    mut v___x_2985_: u8,
    mut v___f_2986_: *mut crate::leanh::LeanObject,
    mut v_connectionLimit_2987_: *mut crate::leanh::LeanObject,
    mut v___f_2988_: *mut crate::leanh::LeanObject,
    mut v___f_2989_: *mut crate::leanh::LeanObject,
    mut v_b_2990_: *mut crate::leanh::LeanObject,
    mut v___y_2991_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3000_: u8 = 0;
    let mut v___x_3001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3003_: u8 = 0;
    let mut v___x_3004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3015_: u8 = 0;
    let mut v___f_3016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_connectionLimit_2987_) == 1 {
                    v_val_2997_ = crate::leanh::lean_ctor_get(v_connectionLimit_2987_, 0);
                    v_isSharedCheck_3015_ =
                        (!crate::leanh::lean_is_exclusive(v_connectionLimit_2987_)) as u8;
                    if v_isSharedCheck_3015_ == 0 {
                        v___x_2999_ = v_connectionLimit_2987_;
                        v_isShared_3000_ = v_isSharedCheck_3015_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2997_);
                        crate::leanh::lean_dec(v_connectionLimit_2987_);
                        v___x_2999_ = crate::leanh::lean_box(0);
                        v_isShared_3000_ = v_isSharedCheck_3015_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___f_2989_);
                    crate::leanh::lean_dec(v_connectionLimit_2987_);
                    crate::leanh::lean_inc_ref(v___y_2991_);
                    v___f_3016_ = crate::leanh::lean_alloc_closure(
                        l_Std_Http_Server_serve___redArg___lam__22___boxed
                            as *mut core::ffi::c_void,
                        4,
                        2,
                    );
                    crate::leanh::lean_closure_set(v___f_3016_, 0, v___f_2988_);
                    crate::leanh::lean_closure_set(v___f_3016_, 1, v___y_2991_);
                    v___x_3017_ = crate::leanh::lean_box((v___x_2985_) as usize);
                    v___x_3018_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3018_, 0, v___x_3017_);
                    v___x_3019_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3019_, 0, v___x_3018_);
                    v___x_3020_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3021_ =
                        l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v___x_3020_,
                            v___x_2985_,
                            v___x_3019_,
                            v___f_3016_,
                        );
                    v___y_2994_ = v___x_3021_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2995_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2996_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_2995_,
                    v___x_2985_,
                    v___y_2994_,
                    v___f_2986_,
                );
                return v___x_2996_;
            }
            2 => {
                v___x_3001_ = l_Std_Semaphore_acquire(v_val_2997_);
                crate::leanh::lean_inc_ref(v___y_2991_);
                v___f_3002_ = crate::leanh::lean_alloc_closure(
                    l_Std_Http_Server_serve___redArg___lam__22___boxed as *mut core::ffi::c_void,
                    4,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_3002_, 0, v___f_2988_);
                crate::leanh::lean_closure_set(v___f_3002_, 1, v___y_2991_);
                v___x_3003_ = 1;
                v___x_3004_ = crate::leanh::lean_box((v___x_3003_) as usize);
                v___x_3005_ = crate::leanh::lean_box((v___x_2985_) as usize);
                v___f_3006_ = crate::leanh::lean_alloc_closure(
                    l_Std_Http_Server_serve___redArg___lam__23___boxed as *mut core::ffi::c_void,
                    5,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_3006_, 0, v___x_3004_);
                crate::leanh::lean_closure_set(v___f_3006_, 1, v___x_3005_);
                crate::leanh::lean_closure_set(v___f_3006_, 2, v___f_3002_);
                v___x_3007_ = crate::leanh::lean_box((v___x_2985_) as usize);
                v___f_3008_ = crate::leanh::lean_alloc_closure(
                    l_Std_Http_Server_serve___redArg___lam__24___boxed as *mut core::ffi::c_void,
                    5,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_3008_, 0, v___f_2989_);
                crate::leanh::lean_closure_set(v___f_3008_, 1, v___x_3007_);
                crate::leanh::lean_closure_set(v___f_3008_, 2, v___f_3006_);
                if v_isShared_3000_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2999_, 0, v___x_3001_);
                    v___x_3010_ = v___x_2999_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3014_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3014_, 0, v___x_3001_);
                    v___x_3010_ = v_reuseFailAlloc_3014_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3011_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3011_, 0, v___x_3010_);
                v___x_3012_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3013_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_3012_,
                    v___x_2985_,
                    v___x_3011_,
                    v___f_3008_,
                );
                v___y_2994_ = v___x_3013_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__26___boxed(
    mut v___x_3022_: *mut crate::leanh::LeanObject,
    mut v___f_3023_: *mut crate::leanh::LeanObject,
    mut v_connectionLimit_3024_: *mut crate::leanh::LeanObject,
    mut v___f_3025_: *mut crate::leanh::LeanObject,
    mut v___f_3026_: *mut crate::leanh::LeanObject,
    mut v_b_3027_: *mut crate::leanh::LeanObject,
    mut v___y_3028_: *mut crate::leanh::LeanObject,
    mut v___y_3029_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_14773__boxed_3030_: u8 = 0;
    let mut v_res_3031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_14773__boxed_3030_ = (crate::leanh::lean_unbox(v___x_3022_) as u8);
    v_res_3031_ = l_Std_Http_Server_serve___redArg___lam__26(
        v___x_14773__boxed_3030_,
        v___f_3023_,
        v_connectionLimit_3024_,
        v___f_3025_,
        v___f_3026_,
        v_b_3027_,
        v___y_3028_,
    );
    crate::leanh::lean_dec_ref(v___y_3028_);
    return v_res_3031_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__25(
    mut v___x_3032_: *mut crate::leanh::LeanObject,
    mut v___f_3033_: *mut crate::leanh::LeanObject,
    mut v___x_3034_: *mut crate::leanh::LeanObject,
    mut v___x_3035_: u8,
    mut v___f_3036_: *mut crate::leanh::LeanObject,
    mut v___y_3037_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_13260__overap_3039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_13260__overap_3039_ =
        l___private_Init_While_0__whileM_erased___redArg(v___x_3032_, v___f_3033_, v___x_3034_);
    v___x_3040_ = crate::leanh::lean_apply_2(
        v___x_13260__overap_3039_,
        v___y_3037_,
        crate::leanh::lean_box(0),
    );
    v___x_3041_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3042_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3041_,
        v___x_3035_,
        v___x_3040_,
        v___f_3036_,
    );
    return v___x_3042_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__25___boxed(
    mut v___x_3043_: *mut crate::leanh::LeanObject,
    mut v___f_3044_: *mut crate::leanh::LeanObject,
    mut v___x_3045_: *mut crate::leanh::LeanObject,
    mut v___x_3046_: *mut crate::leanh::LeanObject,
    mut v___f_3047_: *mut crate::leanh::LeanObject,
    mut v___y_3048_: *mut crate::leanh::LeanObject,
    mut v___y_3049_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_14852__boxed_3050_: u8 = 0;
    let mut v_res_3051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_14852__boxed_3050_ = (crate::leanh::lean_unbox(v___x_3046_) as u8);
    v_res_3051_ = l_Std_Http_Server_serve___redArg___lam__25(
        v___x_3043_,
        v___f_3044_,
        v___x_3045_,
        v___x_14852__boxed_3050_,
        v___f_3047_,
        v___y_3048_,
    );
    return v_res_3051_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__27(
    mut v_x_3052_: *mut crate::leanh::LeanObject,
    mut v_x_3053_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3058_: u8 = 0;
    let mut v___x_3060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3063_: u8 = 0;
    let mut v___x_3064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3053_) == 0 {
                    crate::leanh::lean_dec_ref(v_x_3052_);
                    v_a_3055_ = crate::leanh::lean_ctor_get(v_x_3053_, 0);
                    v_isSharedCheck_3063_ = (!crate::leanh::lean_is_exclusive(v_x_3053_)) as u8;
                    if v_isSharedCheck_3063_ == 0 {
                        v___x_3057_ = v_x_3053_;
                        v_isShared_3058_ = v_isSharedCheck_3063_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3055_);
                        crate::leanh::lean_dec(v_x_3053_);
                        v___x_3057_ = crate::leanh::lean_box(0);
                        v_isShared_3058_ = v_isSharedCheck_3063_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v_x_3053_, 1);
                    v___x_3064_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3064_, 0, v_x_3052_);
                    return v___x_3064_;
                }
            }
            1 => {
                if v_isShared_3058_ == 0 {
                    v___x_3060_ = v___x_3057_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3062_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3062_, 0, v_a_3055_);
                    v___x_3060_ = v_reuseFailAlloc_3062_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3061_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3061_, 0, v___x_3060_);
                return v___x_3061_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__27___boxed(
    mut v_x_3065_: *mut crate::leanh::LeanObject,
    mut v_x_3066_: *mut crate::leanh::LeanObject,
    mut v___y_3067_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3068_ = l_Std_Http_Server_serve___redArg___lam__27(v_x_3065_, v_x_3066_);
    return v_res_3068_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__28(
    mut v___f_3073_: *mut crate::leanh::LeanObject,
    mut v___x_3074_: *mut crate::leanh::LeanObject,
    mut v___f_3075_: *mut crate::leanh::LeanObject,
    mut v___f_3076_: *mut crate::leanh::LeanObject,
    mut v_inst_3077_: *mut crate::leanh::LeanObject,
    mut v_handler_3078_: *mut crate::leanh::LeanObject,
    mut v_config_3079_: *mut crate::leanh::LeanObject,
    mut v___f_3080_: *mut crate::leanh::LeanObject,
    mut v_a_3081_: *mut crate::leanh::LeanObject,
    mut v___f_3082_: *mut crate::leanh::LeanObject,
    mut v___f_3083_: *mut crate::leanh::LeanObject,
    mut v___f_3084_: *mut crate::leanh::LeanObject,
    mut v___f_3085_: *mut crate::leanh::LeanObject,
    mut v___f_3086_: *mut crate::leanh::LeanObject,
    mut v_x_3087_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_3087_) == 0 {
        let mut v___x_3089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v___f_3086_);
        crate::leanh::lean_dec_ref(v___f_3085_);
        crate::leanh::lean_dec_ref(v___f_3084_);
        crate::leanh::lean_dec_ref(v___f_3083_);
        crate::leanh::lean_dec_ref(v___f_3082_);
        crate::leanh::lean_dec(v_a_3081_);
        crate::leanh::lean_dec_ref(v___f_3080_);
        crate::leanh::lean_dec_ref(v_config_3079_);
        crate::leanh::lean_dec(v_handler_3078_);
        crate::leanh::lean_dec_ref(v_inst_3077_);
        crate::leanh::lean_dec_ref(v___f_3076_);
        crate::leanh::lean_dec_ref(v___f_3075_);
        crate::leanh::lean_dec_ref(v___x_3074_);
        crate::leanh::lean_dec_ref(v___f_3073_);
        v___x_3089_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3089_, 0, v_x_3087_);
        return v___x_3089_;
    } else {
        let mut v_a_3090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_context_3091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_activeConnections_3092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_connectionLimit_3093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_shutdownPromise_3094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3097_: u8 = 0;
        let mut v___x_3098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_3090_ = crate::leanh::lean_ctor_get(v_x_3087_, 0);
        v_context_3091_ = crate::leanh::lean_ctor_get(v_a_3090_, 0);
        v_activeConnections_3092_ = crate::leanh::lean_ctor_get(v_a_3090_, 1);
        v_connectionLimit_3093_ = crate::leanh::lean_ctor_get(v_a_3090_, 2);
        v_shutdownPromise_3094_ = crate::leanh::lean_ctor_get(v_a_3090_, 3);
        crate::leanh::lean_inc_ref(v_shutdownPromise_3094_);
        crate::leanh::lean_inc_ref_n(v_context_3091_, 2);
        v___f_3095_ = crate::leanh::lean_alloc_closure(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__3___boxed as *mut core::ffi::c_void, 4, 2);
        crate::leanh::lean_closure_set(v___f_3095_, 0, v_context_3091_);
        crate::leanh::lean_closure_set(v___f_3095_, 1, v_shutdownPromise_3094_);
        v___f_3096_ = crate::leanh::lean_alloc_closure(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__4___boxed as *mut core::ffi::c_void, 5, 1);
        crate::leanh::lean_closure_set(v___f_3096_, 0, v___f_3095_);
        v___x_3097_ = 0;
        v___x_3098_ = crate::leanh::lean_box(0);
        v___f_3099_ = l_Std_Http_Server_serve___redArg___lam__28___closed__0;
        v___f_3100_ = l_Std_Http_Server_serve___redArg___lam__28___closed__1;
        v___x_3101_ = crate::leanh::lean_box((v___x_3097_) as usize);
        crate::leanh::lean_inc_ref(v_activeConnections_3092_);
        crate::leanh::lean_inc_ref(v___x_3074_);
        crate::leanh::lean_inc_n(v_connectionLimit_3093_, 2);
        v___f_3102_ = crate::leanh::lean_alloc_closure(
            l_Std_Http_Server_serve___redArg___lam__21___boxed as *mut core::ffi::c_void,
            21,
            18,
        );
        crate::leanh::lean_closure_set(v___f_3102_, 0, v___x_3101_);
        crate::leanh::lean_closure_set(v___f_3102_, 1, v___f_3073_);
        crate::leanh::lean_closure_set(v___f_3102_, 2, v___f_3099_);
        crate::leanh::lean_closure_set(v___f_3102_, 3, v___x_3098_);
        crate::leanh::lean_closure_set(v___f_3102_, 4, v_connectionLimit_3093_);
        crate::leanh::lean_closure_set(v___f_3102_, 5, v___x_3074_);
        crate::leanh::lean_closure_set(v___f_3102_, 6, v_activeConnections_3092_);
        crate::leanh::lean_closure_set(v___f_3102_, 7, v___f_3075_);
        crate::leanh::lean_closure_set(v___f_3102_, 8, v___f_3076_);
        crate::leanh::lean_closure_set(v___f_3102_, 9, v___f_3096_);
        crate::leanh::lean_closure_set(v___f_3102_, 10, v_inst_3077_);
        crate::leanh::lean_closure_set(v___f_3102_, 11, v_handler_3078_);
        crate::leanh::lean_closure_set(v___f_3102_, 12, v_config_3079_);
        crate::leanh::lean_closure_set(v___f_3102_, 13, v___f_3080_);
        crate::leanh::lean_closure_set(v___f_3102_, 14, v___f_3100_);
        crate::leanh::lean_closure_set(v___f_3102_, 15, v_a_3081_);
        crate::leanh::lean_closure_set(v___f_3102_, 16, v___f_3082_);
        crate::leanh::lean_closure_set(v___f_3102_, 17, v___f_3083_);
        v___x_3103_ = crate::leanh::lean_box((v___x_3097_) as usize);
        v___f_3104_ = crate::leanh::lean_alloc_closure(
            l_Std_Http_Server_serve___redArg___lam__26___boxed as *mut core::ffi::c_void,
            8,
            5,
        );
        crate::leanh::lean_closure_set(v___f_3104_, 0, v___x_3103_);
        crate::leanh::lean_closure_set(v___f_3104_, 1, v___f_3084_);
        crate::leanh::lean_closure_set(v___f_3104_, 2, v_connectionLimit_3093_);
        crate::leanh::lean_closure_set(v___f_3104_, 3, v___f_3102_);
        crate::leanh::lean_closure_set(v___f_3104_, 4, v___f_3085_);
        v___x_3105_ = crate::leanh::lean_box((v___x_3097_) as usize);
        v___f_3106_ = crate::leanh::lean_alloc_closure(
            l_Std_Http_Server_serve___redArg___lam__25___boxed as *mut core::ffi::c_void,
            7,
            5,
        );
        crate::leanh::lean_closure_set(v___f_3106_, 0, v___x_3074_);
        crate::leanh::lean_closure_set(v___f_3106_, 1, v___f_3104_);
        crate::leanh::lean_closure_set(v___f_3106_, 2, v___x_3098_);
        crate::leanh::lean_closure_set(v___f_3106_, 3, v___x_3105_);
        crate::leanh::lean_closure_set(v___f_3106_, 4, v___f_3086_);
        v___x_3107_ = crate::leanh::lean_box((v___x_3097_) as usize);
        crate::leanh::lean_inc(v_a_3090_);
        v___x_3108_ = crate::leanh::lean_alloc_closure(
            l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___boxed
                as *mut core::ffi::c_void,
            6,
            5,
        );
        crate::leanh::lean_closure_set(v___x_3108_, 0, crate::leanh::lean_box(0));
        crate::leanh::lean_closure_set(v___x_3108_, 1, v_a_3090_);
        crate::leanh::lean_closure_set(v___x_3108_, 2, v___x_3107_);
        crate::leanh::lean_closure_set(v___x_3108_, 3, v___f_3106_);
        crate::leanh::lean_closure_set(v___x_3108_, 4, v_context_3091_);
        v___x_3109_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_3110_ = crate::leanh::lean_alloc_closure(
            l_Std_Async_BaseAsync_toRawBaseIO___boxed as *mut core::ffi::c_void,
            3,
            2,
        );
        crate::leanh::lean_closure_set(v___x_3110_, 0, crate::leanh::lean_box(0));
        crate::leanh::lean_closure_set(v___x_3110_, 1, v___x_3108_);
        v___x_3111_ = lean_io_as_task(v___x_3110_, v___x_3109_);
        crate::leanh::lean_dec_ref(v___x_3111_);
        v___f_3112_ = crate::leanh::lean_alloc_closure(
            l_Std_Http_Server_serve___redArg___lam__27___boxed as *mut core::ffi::c_void,
            3,
            1,
        );
        crate::leanh::lean_closure_set(v___f_3112_, 0, v_x_3087_);
        v___x_3113_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__1;
        v___x_3114_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_3109_,
            v___x_3097_,
            v___x_3113_,
            v___f_3112_,
        );
        return v___x_3114_;
    }
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__28___boxed(
    mut v___f_3115_: *mut crate::leanh::LeanObject,
    mut v___x_3116_: *mut crate::leanh::LeanObject,
    mut v___f_3117_: *mut crate::leanh::LeanObject,
    mut v___f_3118_: *mut crate::leanh::LeanObject,
    mut v_inst_3119_: *mut crate::leanh::LeanObject,
    mut v_handler_3120_: *mut crate::leanh::LeanObject,
    mut v_config_3121_: *mut crate::leanh::LeanObject,
    mut v___f_3122_: *mut crate::leanh::LeanObject,
    mut v_a_3123_: *mut crate::leanh::LeanObject,
    mut v___f_3124_: *mut crate::leanh::LeanObject,
    mut v___f_3125_: *mut crate::leanh::LeanObject,
    mut v___f_3126_: *mut crate::leanh::LeanObject,
    mut v___f_3127_: *mut crate::leanh::LeanObject,
    mut v___f_3128_: *mut crate::leanh::LeanObject,
    mut v_x_3129_: *mut crate::leanh::LeanObject,
    mut v___y_3130_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3131_ = l_Std_Http_Server_serve___redArg___lam__28(
        v___f_3115_,
        v___x_3116_,
        v___f_3117_,
        v___f_3118_,
        v_inst_3119_,
        v_handler_3120_,
        v_config_3121_,
        v___f_3122_,
        v_a_3123_,
        v___f_3124_,
        v___f_3125_,
        v___f_3126_,
        v___f_3127_,
        v___f_3128_,
        v_x_3129_,
    );
    return v_res_3131_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__29(
    mut v___f_3132_: *mut crate::leanh::LeanObject,
    mut v_config_3133_: *mut crate::leanh::LeanObject,
    mut v_x_3134_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_3137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3140_: u8 = 0;
    let mut v___x_3141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3145_: u8 = 0;
    let mut v___x_3147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3150_: u8 = 0;
    let mut v_a_3151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3154_: u8 = 0;
    let mut v___x_3155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3161_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3134_) == 0 {
                    crate::leanh::lean_dec_ref(v_config_3133_);
                    crate::leanh::lean_dec_ref(v___f_3132_);
                    v_a_3142_ = crate::leanh::lean_ctor_get(v_x_3134_, 0);
                    v_isSharedCheck_3150_ = (!crate::leanh::lean_is_exclusive(v_x_3134_)) as u8;
                    if v_isSharedCheck_3150_ == 0 {
                        v___x_3144_ = v_x_3134_;
                        v_isShared_3145_ = v_isSharedCheck_3150_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3142_);
                        crate::leanh::lean_dec(v_x_3134_);
                        v___x_3144_ = crate::leanh::lean_box(0);
                        v_isShared_3145_ = v_isSharedCheck_3150_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_3151_ = crate::leanh::lean_ctor_get(v_x_3134_, 0);
                    v_isSharedCheck_3161_ = (!crate::leanh::lean_is_exclusive(v_x_3134_)) as u8;
                    if v_isSharedCheck_3161_ == 0 {
                        v___x_3153_ = v_x_3134_;
                        v_isShared_3154_ = v_isSharedCheck_3161_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3151_);
                        crate::leanh::lean_dec(v_x_3134_);
                        v___x_3153_ = crate::leanh::lean_box(0);
                        v_isShared_3154_ = v_isSharedCheck_3161_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3138_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3138_, 0, v_val_3137_);
                v___x_3139_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3140_ = 0;
                v___x_3141_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_3139_,
                    v___x_3140_,
                    v___x_3138_,
                    v___f_3132_,
                );
                return v___x_3141_;
            }
            2 => {
                if v_isShared_3145_ == 0 {
                    v___x_3147_ = v___x_3144_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3149_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3149_, 0, v_a_3142_);
                    v___x_3147_ = v_reuseFailAlloc_3149_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3148_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3148_, 0, v___x_3147_);
                return v___x_3148_;
            }
            4 => {
                v___x_3155_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3155_, 0, v_a_3151_);
                v___x_3156_ = l_Std_Http_Server_new(v_config_3133_, v___x_3155_);
                v_a_3157_ = crate::leanh::lean_ctor_get(v___x_3156_, 0);
                crate::leanh::lean_inc(v_a_3157_);
                crate::leanh::lean_dec_ref(v___x_3156_);
                if v_isShared_3154_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3153_, 0, v_a_3157_);
                    v___x_3159_ = v___x_3153_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3160_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3160_, 0, v_a_3157_);
                    v___x_3159_ = v_reuseFailAlloc_3160_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_val_3137_ = v___x_3159_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__29___boxed(
    mut v___f_3162_: *mut crate::leanh::LeanObject,
    mut v_config_3163_: *mut crate::leanh::LeanObject,
    mut v_x_3164_: *mut crate::leanh::LeanObject,
    mut v___y_3165_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3166_ =
        l_Std_Http_Server_serve___redArg___lam__29(v___f_3162_, v_config_3163_, v_x_3164_);
    return v_res_3166_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__30(
    mut v___f_3167_: *mut crate::leanh::LeanObject,
    mut v_a_3168_: *mut crate::leanh::LeanObject,
    mut v_x_3169_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_3172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: u8 = 0;
    let mut v___x_3176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3180_: u8 = 0;
    let mut v___x_3182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3185_: u8 = 0;
    let mut v___x_3187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3188_: u8 = 0;
    let mut v___x_3189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3198_: u8 = 0;
    let mut v_unused_3199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3169_) == 0 {
                    crate::leanh::lean_dec_ref(v___f_3167_);
                    v_a_3177_ = crate::leanh::lean_ctor_get(v_x_3169_, 0);
                    v_isSharedCheck_3185_ = (!crate::leanh::lean_is_exclusive(v_x_3169_)) as u8;
                    if v_isSharedCheck_3185_ == 0 {
                        v___x_3179_ = v_x_3169_;
                        v_isShared_3180_ = v_isSharedCheck_3185_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3177_);
                        crate::leanh::lean_dec(v_x_3169_);
                        v___x_3179_ = crate::leanh::lean_box(0);
                        v_isShared_3180_ = v_isSharedCheck_3185_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_isSharedCheck_3198_ = (!crate::leanh::lean_is_exclusive(v_x_3169_)) as u8;
                    if v_isSharedCheck_3198_ == 0 {
                        v_unused_3199_ = crate::leanh::lean_ctor_get(v_x_3169_, 0);
                        crate::leanh::lean_dec(v_unused_3199_);
                        v___x_3187_ = v_x_3169_;
                        v_isShared_3188_ = v_isSharedCheck_3198_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_x_3169_);
                        v___x_3187_ = crate::leanh::lean_box(0);
                        v_isShared_3188_ = v_isSharedCheck_3198_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3173_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3173_, 0, v_val_3172_);
                v___x_3174_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3175_ = 0;
                v___x_3176_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_3174_,
                    v___x_3175_,
                    v___x_3173_,
                    v___f_3167_,
                );
                return v___x_3176_;
            }
            2 => {
                if v_isShared_3180_ == 0 {
                    v___x_3182_ = v___x_3179_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3184_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3184_, 0, v_a_3177_);
                    v___x_3182_ = v_reuseFailAlloc_3184_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3183_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3183_, 0, v___x_3182_);
                return v___x_3183_;
            }
            4 => {
                v___x_3189_ = lean_uv_tcp_getsockname(v_a_3168_);
                if crate::leanh::lean_obj_tag(v___x_3189_) == 0 {
                    v_a_3190_ = crate::leanh::lean_ctor_get(v___x_3189_, 0);
                    crate::leanh::lean_inc(v_a_3190_);
                    crate::leanh::lean_dec_ref_known(v___x_3189_, 1);
                    if v_isShared_3188_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3187_, 0, v_a_3190_);
                        v___x_3192_ = v___x_3187_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3193_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3193_, 0, v_a_3190_);
                        v___x_3192_ = v_reuseFailAlloc_3193_;
                        state = 5;
                        continue;
                    }
                } else {
                    v_a_3194_ = crate::leanh::lean_ctor_get(v___x_3189_, 0);
                    crate::leanh::lean_inc(v_a_3194_);
                    crate::leanh::lean_dec_ref_known(v___x_3189_, 1);
                    if v_isShared_3188_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_3187_, 0);
                        crate::leanh::lean_ctor_set(v___x_3187_, 0, v_a_3194_);
                        v___x_3196_ = v___x_3187_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_3197_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3197_, 0, v_a_3194_);
                        v___x_3196_ = v_reuseFailAlloc_3197_;
                        state = 6;
                        continue;
                    }
                }
            }
            5 => {
                v_val_3172_ = v___x_3192_;
                state = 1;
                continue;
            }
            6 => {
                v_val_3172_ = v___x_3196_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__30___boxed(
    mut v___f_3200_: *mut crate::leanh::LeanObject,
    mut v_a_3201_: *mut crate::leanh::LeanObject,
    mut v_x_3202_: *mut crate::leanh::LeanObject,
    mut v___y_3203_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3204_ = l_Std_Http_Server_serve___redArg___lam__30(v___f_3200_, v_a_3201_, v_x_3202_);
    crate::leanh::lean_dec(v_a_3201_);
    return v_res_3204_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__31(
    mut v___f_3205_: *mut crate::leanh::LeanObject,
    mut v_a_3206_: *mut crate::leanh::LeanObject,
    mut v_x_3207_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_3210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: u8 = 0;
    let mut v___x_3214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3218_: u8 = 0;
    let mut v___x_3220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3223_: u8 = 0;
    let mut v___x_3225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3226_: u8 = 0;
    let mut v___x_3227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3236_: u8 = 0;
    let mut v_unused_3237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3207_) == 0 {
                    crate::leanh::lean_dec_ref(v___f_3205_);
                    v_a_3215_ = crate::leanh::lean_ctor_get(v_x_3207_, 0);
                    v_isSharedCheck_3223_ = (!crate::leanh::lean_is_exclusive(v_x_3207_)) as u8;
                    if v_isSharedCheck_3223_ == 0 {
                        v___x_3217_ = v_x_3207_;
                        v_isShared_3218_ = v_isSharedCheck_3223_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3215_);
                        crate::leanh::lean_dec(v_x_3207_);
                        v___x_3217_ = crate::leanh::lean_box(0);
                        v_isShared_3218_ = v_isSharedCheck_3223_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_isSharedCheck_3236_ = (!crate::leanh::lean_is_exclusive(v_x_3207_)) as u8;
                    if v_isSharedCheck_3236_ == 0 {
                        v_unused_3237_ = crate::leanh::lean_ctor_get(v_x_3207_, 0);
                        crate::leanh::lean_dec(v_unused_3237_);
                        v___x_3225_ = v_x_3207_;
                        v_isShared_3226_ = v_isSharedCheck_3236_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_x_3207_);
                        v___x_3225_ = crate::leanh::lean_box(0);
                        v_isShared_3226_ = v_isSharedCheck_3236_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3211_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3211_, 0, v_val_3210_);
                v___x_3212_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3213_ = 0;
                v___x_3214_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_3212_,
                    v___x_3213_,
                    v___x_3211_,
                    v___f_3205_,
                );
                return v___x_3214_;
            }
            2 => {
                if v_isShared_3218_ == 0 {
                    v___x_3220_ = v___x_3217_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3222_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3222_, 0, v_a_3215_);
                    v___x_3220_ = v_reuseFailAlloc_3222_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3221_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3221_, 0, v___x_3220_);
                return v___x_3221_;
            }
            4 => {
                v___x_3227_ = lean_uv_tcp_nodelay(v_a_3206_);
                if crate::leanh::lean_obj_tag(v___x_3227_) == 0 {
                    v_a_3228_ = crate::leanh::lean_ctor_get(v___x_3227_, 0);
                    crate::leanh::lean_inc(v_a_3228_);
                    crate::leanh::lean_dec_ref_known(v___x_3227_, 1);
                    if v_isShared_3226_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3225_, 0, v_a_3228_);
                        v___x_3230_ = v___x_3225_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3231_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3231_, 0, v_a_3228_);
                        v___x_3230_ = v_reuseFailAlloc_3231_;
                        state = 5;
                        continue;
                    }
                } else {
                    v_a_3232_ = crate::leanh::lean_ctor_get(v___x_3227_, 0);
                    crate::leanh::lean_inc(v_a_3232_);
                    crate::leanh::lean_dec_ref_known(v___x_3227_, 1);
                    if v_isShared_3226_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_3225_, 0);
                        crate::leanh::lean_ctor_set(v___x_3225_, 0, v_a_3232_);
                        v___x_3234_ = v___x_3225_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_3235_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3235_, 0, v_a_3232_);
                        v___x_3234_ = v_reuseFailAlloc_3235_;
                        state = 6;
                        continue;
                    }
                }
            }
            5 => {
                v_val_3210_ = v___x_3230_;
                state = 1;
                continue;
            }
            6 => {
                v_val_3210_ = v___x_3234_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__31___boxed(
    mut v___f_3238_: *mut crate::leanh::LeanObject,
    mut v_a_3239_: *mut crate::leanh::LeanObject,
    mut v_x_3240_: *mut crate::leanh::LeanObject,
    mut v___y_3241_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3242_ = l_Std_Http_Server_serve___redArg___lam__31(v___f_3238_, v_a_3239_, v_x_3240_);
    crate::leanh::lean_dec(v_a_3239_);
    return v_res_3242_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__32(
    mut v___f_3243_: *mut crate::leanh::LeanObject,
    mut v_a_3244_: *mut crate::leanh::LeanObject,
    mut v_backlog_3245_: u32,
    mut v_x_3246_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_3249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3252_: u8 = 0;
    let mut v___x_3253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3257_: u8 = 0;
    let mut v___x_3259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3262_: u8 = 0;
    let mut v___x_3264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3265_: u8 = 0;
    let mut v___x_3266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3275_: u8 = 0;
    let mut v_unused_3276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3246_) == 0 {
                    crate::leanh::lean_dec_ref(v___f_3243_);
                    v_a_3254_ = crate::leanh::lean_ctor_get(v_x_3246_, 0);
                    v_isSharedCheck_3262_ = (!crate::leanh::lean_is_exclusive(v_x_3246_)) as u8;
                    if v_isSharedCheck_3262_ == 0 {
                        v___x_3256_ = v_x_3246_;
                        v_isShared_3257_ = v_isSharedCheck_3262_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3254_);
                        crate::leanh::lean_dec(v_x_3246_);
                        v___x_3256_ = crate::leanh::lean_box(0);
                        v_isShared_3257_ = v_isSharedCheck_3262_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_isSharedCheck_3275_ = (!crate::leanh::lean_is_exclusive(v_x_3246_)) as u8;
                    if v_isSharedCheck_3275_ == 0 {
                        v_unused_3276_ = crate::leanh::lean_ctor_get(v_x_3246_, 0);
                        crate::leanh::lean_dec(v_unused_3276_);
                        v___x_3264_ = v_x_3246_;
                        v_isShared_3265_ = v_isSharedCheck_3275_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_x_3246_);
                        v___x_3264_ = crate::leanh::lean_box(0);
                        v_isShared_3265_ = v_isSharedCheck_3275_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3250_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3250_, 0, v_val_3249_);
                v___x_3251_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3252_ = 0;
                v___x_3253_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_3251_,
                    v___x_3252_,
                    v___x_3250_,
                    v___f_3243_,
                );
                return v___x_3253_;
            }
            2 => {
                if v_isShared_3257_ == 0 {
                    v___x_3259_ = v___x_3256_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3261_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3261_, 0, v_a_3254_);
                    v___x_3259_ = v_reuseFailAlloc_3261_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3260_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3260_, 0, v___x_3259_);
                return v___x_3260_;
            }
            4 => {
                v___x_3266_ = lean_uv_tcp_listen(v_a_3244_, v_backlog_3245_);
                if crate::leanh::lean_obj_tag(v___x_3266_) == 0 {
                    v_a_3267_ = crate::leanh::lean_ctor_get(v___x_3266_, 0);
                    crate::leanh::lean_inc(v_a_3267_);
                    crate::leanh::lean_dec_ref_known(v___x_3266_, 1);
                    if v_isShared_3265_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3264_, 0, v_a_3267_);
                        v___x_3269_ = v___x_3264_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3270_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3270_, 0, v_a_3267_);
                        v___x_3269_ = v_reuseFailAlloc_3270_;
                        state = 5;
                        continue;
                    }
                } else {
                    v_a_3271_ = crate::leanh::lean_ctor_get(v___x_3266_, 0);
                    crate::leanh::lean_inc(v_a_3271_);
                    crate::leanh::lean_dec_ref_known(v___x_3266_, 1);
                    if v_isShared_3265_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_3264_, 0);
                        crate::leanh::lean_ctor_set(v___x_3264_, 0, v_a_3271_);
                        v___x_3273_ = v___x_3264_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_3274_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3274_, 0, v_a_3271_);
                        v___x_3273_ = v_reuseFailAlloc_3274_;
                        state = 6;
                        continue;
                    }
                }
            }
            5 => {
                v_val_3249_ = v___x_3269_;
                state = 1;
                continue;
            }
            6 => {
                v_val_3249_ = v___x_3273_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__32___boxed(
    mut v___f_3277_: *mut crate::leanh::LeanObject,
    mut v_a_3278_: *mut crate::leanh::LeanObject,
    mut v_backlog_3279_: *mut crate::leanh::LeanObject,
    mut v_x_3280_: *mut crate::leanh::LeanObject,
    mut v___y_3281_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_backlog_boxed_3282_: u32 = 0;
    let mut v_res_3283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_backlog_boxed_3282_ = crate::leanh::lean_unbox_uint32(v_backlog_3279_);
    crate::leanh::lean_dec(v_backlog_3279_);
    v_res_3283_ = l_Std_Http_Server_serve___redArg___lam__32(
        v___f_3277_,
        v_a_3278_,
        v_backlog_boxed_3282_,
        v_x_3280_,
    );
    crate::leanh::lean_dec(v_a_3278_);
    return v_res_3283_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__33(
    mut v___f_3284_: *mut crate::leanh::LeanObject,
    mut v___x_3285_: *mut crate::leanh::LeanObject,
    mut v___f_3286_: *mut crate::leanh::LeanObject,
    mut v___f_3287_: *mut crate::leanh::LeanObject,
    mut v_inst_3288_: *mut crate::leanh::LeanObject,
    mut v_handler_3289_: *mut crate::leanh::LeanObject,
    mut v_config_3290_: *mut crate::leanh::LeanObject,
    mut v___f_3291_: *mut crate::leanh::LeanObject,
    mut v___f_3292_: *mut crate::leanh::LeanObject,
    mut v___f_3293_: *mut crate::leanh::LeanObject,
    mut v___f_3294_: *mut crate::leanh::LeanObject,
    mut v___f_3295_: *mut crate::leanh::LeanObject,
    mut v___f_3296_: *mut crate::leanh::LeanObject,
    mut v_backlog_3297_: u32,
    mut v_addr_3298_: *mut crate::leanh::LeanObject,
    mut v_x_3299_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3304_: u8 = 0;
    let mut v___x_3306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3309_: u8 = 0;
    let mut v_a_3310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3313_: u8 = 0;
    let mut v___f_3314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: u8 = 0;
    let mut v___x_3325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3335_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3299_) == 0 {
                    crate::leanh::lean_dec_ref(v___f_3296_);
                    crate::leanh::lean_dec_ref(v___f_3295_);
                    crate::leanh::lean_dec_ref(v___f_3294_);
                    crate::leanh::lean_dec_ref(v___f_3293_);
                    crate::leanh::lean_dec_ref(v___f_3292_);
                    crate::leanh::lean_dec_ref(v___f_3291_);
                    crate::leanh::lean_dec_ref(v_config_3290_);
                    crate::leanh::lean_dec(v_handler_3289_);
                    crate::leanh::lean_dec_ref(v_inst_3288_);
                    crate::leanh::lean_dec_ref(v___f_3287_);
                    crate::leanh::lean_dec_ref(v___f_3286_);
                    crate::leanh::lean_dec_ref(v___x_3285_);
                    crate::leanh::lean_dec_ref(v___f_3284_);
                    v_a_3301_ = crate::leanh::lean_ctor_get(v_x_3299_, 0);
                    v_isSharedCheck_3309_ = (!crate::leanh::lean_is_exclusive(v_x_3299_)) as u8;
                    if v_isSharedCheck_3309_ == 0 {
                        v___x_3303_ = v_x_3299_;
                        v_isShared_3304_ = v_isSharedCheck_3309_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3301_);
                        crate::leanh::lean_dec(v_x_3299_);
                        v___x_3303_ = crate::leanh::lean_box(0);
                        v_isShared_3304_ = v_isSharedCheck_3309_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3310_ = crate::leanh::lean_ctor_get(v_x_3299_, 0);
                    v_isSharedCheck_3335_ = (!crate::leanh::lean_is_exclusive(v_x_3299_)) as u8;
                    if v_isSharedCheck_3335_ == 0 {
                        v___x_3312_ = v_x_3299_;
                        v_isShared_3313_ = v_isSharedCheck_3335_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3310_);
                        crate::leanh::lean_dec(v_x_3299_);
                        v___x_3312_ = crate::leanh::lean_box(0);
                        v_isShared_3313_ = v_isSharedCheck_3335_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3304_ == 0 {
                    v___x_3306_ = v___x_3303_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3308_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3308_, 0, v_a_3301_);
                    v___x_3306_ = v_reuseFailAlloc_3308_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3307_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3307_, 0, v___x_3306_);
                return v___x_3307_;
            }
            3 => {
                crate::leanh::lean_inc_n(v_a_3310_, 4);
                crate::leanh::lean_inc_ref(v_config_3290_);
                v___f_3314_ = crate::leanh::lean_alloc_closure(
                    l_Std_Http_Server_serve___redArg___lam__28___boxed as *mut core::ffi::c_void,
                    16,
                    14,
                );
                crate::leanh::lean_closure_set(v___f_3314_, 0, v___f_3284_);
                crate::leanh::lean_closure_set(v___f_3314_, 1, v___x_3285_);
                crate::leanh::lean_closure_set(v___f_3314_, 2, v___f_3286_);
                crate::leanh::lean_closure_set(v___f_3314_, 3, v___f_3287_);
                crate::leanh::lean_closure_set(v___f_3314_, 4, v_inst_3288_);
                crate::leanh::lean_closure_set(v___f_3314_, 5, v_handler_3289_);
                crate::leanh::lean_closure_set(v___f_3314_, 6, v_config_3290_);
                crate::leanh::lean_closure_set(v___f_3314_, 7, v___f_3291_);
                crate::leanh::lean_closure_set(v___f_3314_, 8, v_a_3310_);
                crate::leanh::lean_closure_set(v___f_3314_, 9, v___f_3292_);
                crate::leanh::lean_closure_set(v___f_3314_, 10, v___f_3293_);
                crate::leanh::lean_closure_set(v___f_3314_, 11, v___f_3294_);
                crate::leanh::lean_closure_set(v___f_3314_, 12, v___f_3295_);
                crate::leanh::lean_closure_set(v___f_3314_, 13, v___f_3296_);
                v___f_3315_ = crate::leanh::lean_alloc_closure(
                    l_Std_Http_Server_serve___redArg___lam__29___boxed as *mut core::ffi::c_void,
                    4,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_3315_, 0, v___f_3314_);
                crate::leanh::lean_closure_set(v___f_3315_, 1, v_config_3290_);
                v___f_3316_ = crate::leanh::lean_alloc_closure(
                    l_Std_Http_Server_serve___redArg___lam__30___boxed as *mut core::ffi::c_void,
                    4,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_3316_, 0, v___f_3315_);
                crate::leanh::lean_closure_set(v___f_3316_, 1, v_a_3310_);
                v___f_3317_ = crate::leanh::lean_alloc_closure(
                    l_Std_Http_Server_serve___redArg___lam__31___boxed as *mut core::ffi::c_void,
                    4,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_3317_, 0, v___f_3316_);
                crate::leanh::lean_closure_set(v___f_3317_, 1, v_a_3310_);
                v___x_3318_ = crate::leanh::lean_box_uint32(v_backlog_3297_);
                v___f_3319_ = crate::leanh::lean_alloc_closure(
                    l_Std_Http_Server_serve___redArg___lam__32___boxed as *mut core::ffi::c_void,
                    5,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_3319_, 0, v___f_3317_);
                crate::leanh::lean_closure_set(v___f_3319_, 1, v_a_3310_);
                crate::leanh::lean_closure_set(v___f_3319_, 2, v___x_3318_);
                v___x_3326_ = lean_uv_tcp_bind(v_a_3310_, v_addr_3298_);
                crate::leanh::lean_dec(v_a_3310_);
                if crate::leanh::lean_obj_tag(v___x_3326_) == 0 {
                    v_a_3327_ = crate::leanh::lean_ctor_get(v___x_3326_, 0);
                    crate::leanh::lean_inc(v_a_3327_);
                    crate::leanh::lean_dec_ref_known(v___x_3326_, 1);
                    if v_isShared_3313_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3312_, 0, v_a_3327_);
                        v___x_3329_ = v___x_3312_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3330_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3330_, 0, v_a_3327_);
                        v___x_3329_ = v_reuseFailAlloc_3330_;
                        state = 5;
                        continue;
                    }
                } else {
                    v_a_3331_ = crate::leanh::lean_ctor_get(v___x_3326_, 0);
                    crate::leanh::lean_inc(v_a_3331_);
                    crate::leanh::lean_dec_ref_known(v___x_3326_, 1);
                    if v_isShared_3313_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_3312_, 0);
                        crate::leanh::lean_ctor_set(v___x_3312_, 0, v_a_3331_);
                        v___x_3333_ = v___x_3312_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_3334_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3334_, 0, v_a_3331_);
                        v___x_3333_ = v_reuseFailAlloc_3334_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                v___x_3322_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3322_, 0, v_val_3321_);
                v___x_3323_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3324_ = 0;
                v___x_3325_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_3323_,
                    v___x_3324_,
                    v___x_3322_,
                    v___f_3319_,
                );
                return v___x_3325_;
            }
            5 => {
                v_val_3321_ = v___x_3329_;
                state = 4;
                continue;
            }
            6 => {
                v_val_3321_ = v___x_3333_;
                state = 4;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__33___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3336_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v___x_3337_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v___f_3338_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v___f_3339_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_inst_3340_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_handler_3341_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_config_3342_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___f_3343_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___f_3344_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___f_3345_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___f_3346_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___f_3347_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___f_3348_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_backlog_3349_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_addr_3350_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v_x_3351_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_3352_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_backlog_boxed_3353_: u32 = 0;
    let mut v_res_3354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_backlog_boxed_3353_ = crate::leanh::lean_unbox_uint32(v_backlog_3349_);
    crate::leanh::lean_dec(v_backlog_3349_);
    v_res_3354_ = l_Std_Http_Server_serve___redArg___lam__33(
        v___f_3336_,
        v___x_3337_,
        v___f_3338_,
        v___f_3339_,
        v_inst_3340_,
        v_handler_3341_,
        v_config_3342_,
        v___f_3343_,
        v___f_3344_,
        v___f_3345_,
        v___f_3346_,
        v___f_3347_,
        v___f_3348_,
        v_backlog_boxed_3353_,
        v_addr_3350_,
        v_x_3351_,
    );
    crate::leanh::lean_dec_ref(v_addr_3350_);
    return v_res_3354_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg(
    mut v_inst_3361_: *mut crate::leanh::LeanObject,
    mut v_addr_3362_: *mut crate::leanh::LeanObject,
    mut v_handler_3363_: *mut crate::leanh::LeanObject,
    mut v_config_3364_: *mut crate::leanh::LeanObject,
    mut v_backlog_3365_: u32,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3383_: u8 = 0;
    let mut v___x_3384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3389_: u8 = 0;
    let mut v___x_3391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3393_: u8 = 0;
    let mut v_a_3394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3397_: u8 = 0;
    let mut v___x_3399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3401_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_3367_ = l_Std_Http_Server_serve___redArg___closed__0;
                v___f_3368_ = l_Std_Http_Server_serve___redArg___closed__1;
                v___f_3369_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__0;
                v___f_3370_ = l_Std_Http_Server_serve___redArg___closed__2;
                v___f_3371_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__5;
                v___f_3372_ = l_Std_Http_Server_serve___redArg___closed__3;
                v___f_3373_ = l_Std_Http_Server_serve___redArg___closed__4;
                v___f_3374_ = l_Std_Http_Server_serve___redArg___closed__5;
                v___f_3375_ = l_Std_Http_Server_waitShutdown___closed__0;
                v___x_3376_ = l_Std_Async_ContextAsync_instMonad;
                v___x_3377_ = crate::leanh::lean_box_uint32(v_backlog_3365_);
                v___f_3378_ = crate::leanh::lean_alloc_closure(
                    l_Std_Http_Server_serve___redArg___lam__33___boxed as *mut core::ffi::c_void,
                    17,
                    15,
                );
                crate::leanh::lean_closure_set(v___f_3378_, 0, v___f_3374_);
                crate::leanh::lean_closure_set(v___f_3378_, 1, v___x_3376_);
                crate::leanh::lean_closure_set(v___f_3378_, 2, v___f_3369_);
                crate::leanh::lean_closure_set(v___f_3378_, 3, v___f_3371_);
                crate::leanh::lean_closure_set(v___f_3378_, 4, v_inst_3361_);
                crate::leanh::lean_closure_set(v___f_3378_, 5, v_handler_3363_);
                crate::leanh::lean_closure_set(v___f_3378_, 6, v_config_3364_);
                crate::leanh::lean_closure_set(v___f_3378_, 7, v___f_3370_);
                crate::leanh::lean_closure_set(v___f_3378_, 8, v___f_3373_);
                crate::leanh::lean_closure_set(v___f_3378_, 9, v___f_3372_);
                crate::leanh::lean_closure_set(v___f_3378_, 10, v___f_3368_);
                crate::leanh::lean_closure_set(v___f_3378_, 11, v___f_3375_);
                crate::leanh::lean_closure_set(v___f_3378_, 12, v___f_3367_);
                crate::leanh::lean_closure_set(v___f_3378_, 13, v___x_3377_);
                crate::leanh::lean_closure_set(v___f_3378_, 14, v_addr_3362_);
                v___x_3385_ = lean_uv_tcp_new();
                if crate::leanh::lean_obj_tag(v___x_3385_) == 0 {
                    v_a_3386_ = crate::leanh::lean_ctor_get(v___x_3385_, 0);
                    v_isSharedCheck_3393_ = (!crate::leanh::lean_is_exclusive(v___x_3385_)) as u8;
                    if v_isSharedCheck_3393_ == 0 {
                        v___x_3388_ = v___x_3385_;
                        v_isShared_3389_ = v_isSharedCheck_3393_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3386_);
                        crate::leanh::lean_dec(v___x_3385_);
                        v___x_3388_ = crate::leanh::lean_box(0);
                        v_isShared_3389_ = v_isSharedCheck_3393_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_3394_ = crate::leanh::lean_ctor_get(v___x_3385_, 0);
                    v_isSharedCheck_3401_ = (!crate::leanh::lean_is_exclusive(v___x_3385_)) as u8;
                    if v_isSharedCheck_3401_ == 0 {
                        v___x_3396_ = v___x_3385_;
                        v_isShared_3397_ = v_isSharedCheck_3401_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3394_);
                        crate::leanh::lean_dec(v___x_3385_);
                        v___x_3396_ = crate::leanh::lean_box(0);
                        v_isShared_3397_ = v_isSharedCheck_3401_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3381_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3381_, 0, v_val_3380_);
                v___x_3382_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3383_ = 0;
                v___x_3384_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_3382_,
                    v___x_3383_,
                    v___x_3381_,
                    v___f_3378_,
                );
                return v___x_3384_;
            }
            2 => {
                if v_isShared_3389_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3388_, 1);
                    v___x_3391_ = v___x_3388_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3392_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3392_, 0, v_a_3386_);
                    v___x_3391_ = v_reuseFailAlloc_3392_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_val_3380_ = v___x_3391_;
                state = 1;
                continue;
            }
            4 => {
                if v_isShared_3397_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3396_, 0);
                    v___x_3399_ = v___x_3396_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3400_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3400_, 0, v_a_3394_);
                    v___x_3399_ = v_reuseFailAlloc_3400_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_val_3380_ = v___x_3399_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Server_serve___redArg___boxed(
    mut v_inst_3402_: *mut crate::leanh::LeanObject,
    mut v_addr_3403_: *mut crate::leanh::LeanObject,
    mut v_handler_3404_: *mut crate::leanh::LeanObject,
    mut v_config_3405_: *mut crate::leanh::LeanObject,
    mut v_backlog_3406_: *mut crate::leanh::LeanObject,
    mut v_a_3407_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_backlog_boxed_3408_: u32 = 0;
    let mut v_res_3409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_backlog_boxed_3408_ = crate::leanh::lean_unbox_uint32(v_backlog_3406_);
    crate::leanh::lean_dec(v_backlog_3406_);
    v_res_3409_ = l_Std_Http_Server_serve___redArg(
        v_inst_3402_,
        v_addr_3403_,
        v_handler_3404_,
        v_config_3405_,
        v_backlog_boxed_3408_,
    );
    return v_res_3409_;
}
pub unsafe fn l_Std_Http_Server_serve(
    mut v_00_u03c3_3410_: *mut crate::leanh::LeanObject,
    mut v_inst_3411_: *mut crate::leanh::LeanObject,
    mut v_addr_3412_: *mut crate::leanh::LeanObject,
    mut v_handler_3413_: *mut crate::leanh::LeanObject,
    mut v_config_3414_: *mut crate::leanh::LeanObject,
    mut v_backlog_3415_: u32,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3417_ = l_Std_Http_Server_serve___redArg(
        v_inst_3411_,
        v_addr_3412_,
        v_handler_3413_,
        v_config_3414_,
        v_backlog_3415_,
    );
    return v___x_3417_;
}
pub unsafe fn l_Std_Http_Server_serve___boxed(
    mut v_00_u03c3_3418_: *mut crate::leanh::LeanObject,
    mut v_inst_3419_: *mut crate::leanh::LeanObject,
    mut v_addr_3420_: *mut crate::leanh::LeanObject,
    mut v_handler_3421_: *mut crate::leanh::LeanObject,
    mut v_config_3422_: *mut crate::leanh::LeanObject,
    mut v_backlog_3423_: *mut crate::leanh::LeanObject,
    mut v_a_3424_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_backlog_boxed_3425_: u32 = 0;
    let mut v_res_3426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_backlog_boxed_3425_ = crate::leanh::lean_unbox_uint32(v_backlog_3423_);
    crate::leanh::lean_dec(v_backlog_3423_);
    v_res_3426_ = l_Std_Http_Server_serve(
        v_00_u03c3_3418_,
        v_inst_3419_,
        v_addr_3420_,
        v_handler_3421_,
        v_config_3422_,
        v_backlog_boxed_3425_,
    );
    return v_res_3426_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Http_Server(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Async(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Async_TCP(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Sync_CancellationToken(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Sync_Semaphore(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Server_Config(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Server_Handler(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Server_Connection(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Http_Server(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Http_Server(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Async(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Async_TCP(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Sync_CancellationToken(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Sync_Semaphore(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Http_Server_Config(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Http_Server_Handler(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Http_Server_Connection(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Server(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Http_Server(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Http_Server(builtin);
}
