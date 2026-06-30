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
pub static l_Std_Http_Server_waitShutdown___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Http_Server_waitShutdown___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Server_waitShutdown___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Server_waitShutdown___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Server_waitShutdown___closed__1_value: leanh::LeanClosureObject<1> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Http_Server_waitShutdown___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_Server_waitShutdown___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Http_Server_waitShutdown___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Server_waitShutdown___closed__1_value)
        as *mut leanh::LeanObject;
pub static l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__0_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__1_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__0_value) as *mut leanh::LeanObject] };
static mut l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__1_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Std_Async_ContextAsync_instMonadLiftBaseIO___lam__0___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__1_value
) as *mut leanh::LeanObject;
pub static l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__2_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_instMonadLiftT___lam__0___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__2_value
) as *mut leanh::LeanObject;
pub static l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__3_value: leanh::LeanClosureObject<2> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*2) as u16, other: 0, tag: 245 }, m_fun: l_instMonadLiftTOfMonadLift___redArg___lam__0 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 2, m_objs: [core::ptr::addr_of!(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__2_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__1_value) as *mut leanh::LeanObject] };
static mut l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__3_value
) as *mut leanh::LeanObject;
pub static l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__4_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Std_Async_ContextAsync_instMonadFinally___lam__1___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__4_value
) as *mut leanh::LeanObject;
pub static l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__5_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__1___boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__5_value
) as *mut leanh::LeanObject;
pub static l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__6_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__5___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__6_value
) as *mut leanh::LeanObject;
pub static l_Std_Http_Server_serve___redArg___lam__4___closed__0_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l_Std_Http_Server_serve___redArg___lam__4___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Server_serve___redArg___lam__4___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Server_serve___redArg___lam__4___closed__1_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_Server_serve___redArg___lam__4___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_Server_serve___redArg___lam__4___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Server_serve___redArg___lam__4___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Std_Http_Server_serve___redArg___lam__19___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Server_serve___redArg___lam__19___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Http_Server_serve___redArg___lam__19___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Server_serve___redArg___lam__19___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Http_Server_serve___redArg___lam__19___closed__2_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_Extensions_compareName___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Server_serve___redArg___lam__19___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Server_serve___redArg___lam__19___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Server_serve___redArg___lam__28___closed__0_value:
    leanh::LeanClosureObject<1> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_Server_serve___redArg___lam__10___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l_Std_Http_Server_serve___redArg___lam__28___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Server_serve___redArg___lam__28___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Server_serve___redArg___lam__28___closed__1_value:
    leanh::LeanClosureObject<1> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_Server_serve___redArg___lam__6___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l_Std_Http_Server_serve___redArg___lam__28___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Server_serve___redArg___lam__28___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Server_serve___redArg___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Http_Server_serve___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Server_serve___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Server_serve___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Server_serve___redArg___closed__1_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Http_Server_serve___redArg___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Server_serve___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Server_serve___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Server_serve___redArg___closed__2_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Http_Server_serve___redArg___lam__3___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Server_serve___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Server_serve___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Server_serve___redArg___closed__3_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Http_Server_serve___redArg___lam__4___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Server_serve___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Server_serve___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Server_serve___redArg___closed__4_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Http_Server_serve___redArg___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Server_serve___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Server_serve___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Server_serve___redArg___closed__5_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Http_Server_serve___redArg___lam__5___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Server_serve___redArg___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Server_serve___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Std_Http_Server_new(
    mut v_config_1714_: *mut leanh::LeanObject,
    mut v_localAddr_1715_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_connectionLimit_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxConnections_1726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: u8 = 0;
    let mut v___x_1728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1717_ = l_Std_CancellationContext_new();
                v___x_1718_ = leanh::lean_unsigned_to_nat(0);
                v___x_1719_ = l_Std_Mutex_new___redArg(v___x_1718_);
                v_maxConnections_1726_ = leanh::lean_ctor_get(v_config_1714_, 0);
                v___x_1727_ = lean_nat_dec_eq(v_maxConnections_1726_, v___x_1718_);
                if v___x_1727_ == 0 {
                    leanh::lean_inc(v_maxConnections_1726_);
                    v___x_1728_ = l_Std_Semaphore_new(v_maxConnections_1726_);
                    v___x_1729_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1729_, 0, v___x_1728_);
                    v_connectionLimit_1721_ = v___x_1729_;
                    state = 1;
                    continue;
                } else {
                    v___x_1730_ = leanh::lean_box(0);
                    v_connectionLimit_1721_ = v___x_1730_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1722_ = leanh::lean_box(0);
                v___x_1723_ = l_Std_CloseableChannel_new___redArg(v___x_1722_);
                v___x_1724_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
                leanh::lean_ctor_set(v___x_1724_, 0, v___x_1717_);
                leanh::lean_ctor_set(v___x_1724_, 1, v___x_1719_);
                leanh::lean_ctor_set(v___x_1724_, 2, v_connectionLimit_1721_);
                leanh::lean_ctor_set(v___x_1724_, 3, v___x_1723_);
                leanh::lean_ctor_set(v___x_1724_, 4, v_config_1714_);
                leanh::lean_ctor_set(v___x_1724_, 5, v_localAddr_1715_);
                v___x_1725_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1725_, 0, v___x_1724_);
                return v___x_1725_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Server_new___boxed(
    mut v_config_1731_: *mut leanh::LeanObject,
    mut v_localAddr_1732_: *mut leanh::LeanObject,
    mut v_a_1733_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1734_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1734_ = l_Std_Http_Server_new(v_config_1731_, v_localAddr_1732_);
    return v_res_1734_;
}
pub unsafe fn l_Std_Http_Server_shutdown(
    mut v_s_1735_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_context_1737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_context_1737_ = leanh::lean_ctor_get(v_s_1735_, 0);
    leanh::lean_inc_ref(v_context_1737_);
    leanh::lean_dec_ref(v_s_1735_);
    v___x_1738_ = leanh::lean_box(1);
    v___x_1739_ = l_Std_CancellationContext_cancel(v_context_1737_, v___x_1738_);
    v___x_1740_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1740_, 0, v___x_1739_);
    v___x_1741_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1741_, 0, v___x_1740_);
    return v___x_1741_;
}
pub unsafe fn l_Std_Http_Server_shutdown___boxed(
    mut v_s_1742_: *mut leanh::LeanObject,
    mut v_a_1743_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1744_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1744_ = l_Std_Http_Server_shutdown(v_s_1742_);
    return v_res_1744_;
}
pub unsafe fn l_Std_Http_Server_waitShutdown___lam__0(
    mut v_a_1745_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1746_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1746_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1746_, 0, v_a_1745_);
    return v___x_1746_;
}
pub unsafe fn l_Std_Http_Server_waitShutdown___lam__1(
    mut v___f_1747_: *mut leanh::LeanObject,
    mut v_x_1748_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1753_: u8 = 0;
    let mut v___x_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1758_: u8 = 0;
    let mut v_a_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: u8 = 0;
    let mut v___x_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1748_) == 0 {
                    leanh::lean_dec_ref(v___f_1747_);
                    v_a_1750_ = leanh::lean_ctor_get(v_x_1748_, 0);
                    v_isSharedCheck_1758_ = (!leanh::lean_is_exclusive(v_x_1748_)) as u8;
                    if v_isSharedCheck_1758_ == 0 {
                        v___x_1752_ = v_x_1748_;
                        v_isShared_1753_ = v_isSharedCheck_1758_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1750_);
                        leanh::lean_dec(v_x_1748_);
                        v___x_1752_ = leanh::lean_box(0);
                        v_isShared_1753_ = v_isSharedCheck_1758_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1759_ = leanh::lean_ctor_get(v_x_1748_, 0);
                    leanh::lean_inc(v_a_1759_);
                    leanh::lean_dec_ref_known(v_x_1748_, 1);
                    v___x_1760_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1761_ = 0;
                    v___x_1762_ = lean_task_map(v___f_1747_, v_a_1759_, v___x_1760_, v___x_1761_);
                    v___x_1763_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1763_, 0, v___x_1762_);
                    return v___x_1763_;
                }
            }
            1 => {
                if v_isShared_1753_ == 0 {
                    v___x_1755_ = v___x_1752_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1757_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1757_, 0, v_a_1750_);
                    v___x_1755_ = v_reuseFailAlloc_1757_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1756_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1756_, 0, v___x_1755_);
                return v___x_1756_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Server_waitShutdown___lam__1___boxed(
    mut v___f_1764_: *mut leanh::LeanObject,
    mut v_x_1765_: *mut leanh::LeanObject,
    mut v___y_1766_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1767_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1767_ = l_Std_Http_Server_waitShutdown___lam__1(v___f_1764_, v_x_1765_);
    return v_res_1767_;
}
pub unsafe fn l_Std_Http_Server_waitShutdown(
    mut v_s_1771_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_shutdownPromise_1773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: u8 = 0;
    let mut v___x_1781_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_shutdownPromise_1773_ = leanh::lean_ctor_get(v_s_1771_, 3);
    leanh::lean_inc_ref(v_shutdownPromise_1773_);
    leanh::lean_dec_ref(v_s_1771_);
    v___x_1774_ = leanh::lean_box(0);
    v___x_1775_ = l_Std_Channel_recv___redArg(v___x_1774_, v_shutdownPromise_1773_);
    v___f_1776_ = l_Std_Http_Server_waitShutdown___closed__1;
    v___x_1777_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1777_, 0, v___x_1775_);
    v___x_1778_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1778_, 0, v___x_1777_);
    v___x_1779_ = leanh::lean_unsigned_to_nat(0);
    v___x_1780_ = 0;
    v___x_1781_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1779_,
        v___x_1780_,
        v___x_1778_,
        v___f_1776_,
    );
    return v___x_1781_;
}
pub unsafe fn l_Std_Http_Server_waitShutdown___boxed(
    mut v_s_1782_: *mut leanh::LeanObject,
    mut v_a_1783_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1784_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1784_ = l_Std_Http_Server_waitShutdown(v_s_1782_);
    return v_res_1784_;
}
pub unsafe fn l_Std_Http_Server_waitShutdownSelector(
    mut v_s_1785_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_shutdownPromise_1786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_shutdownPromise_1786_ = leanh::lean_ctor_get(v_s_1785_, 3);
    leanh::lean_inc_ref(v_shutdownPromise_1786_);
    leanh::lean_dec_ref(v_s_1785_);
    v___x_1787_ = leanh::lean_box(0);
    v___x_1788_ = l_Std_Channel_recvSelector___redArg(v___x_1787_, v_shutdownPromise_1786_);
    return v___x_1788_;
}
pub unsafe fn l_Std_Http_Server_shutdownAndWait___lam__2(
    mut v_shutdownPromise_1789_: *mut leanh::LeanObject,
    mut v___f_1790_: *mut leanh::LeanObject,
    mut v_x_1791_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1796_: u8 = 0;
    let mut v___x_1797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: u8 = 0;
    let mut v___x_1804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1806_: u8 = 0;
    let mut v_unused_1807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1791_) == 0 {
                    leanh::lean_dec_ref(v___f_1790_);
                    leanh::lean_dec_ref(v_shutdownPromise_1789_);
                    v___x_1793_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1793_, 0, v_x_1791_);
                    return v___x_1793_;
                } else {
                    v_isSharedCheck_1806_ = (!leanh::lean_is_exclusive(v_x_1791_)) as u8;
                    if v_isSharedCheck_1806_ == 0 {
                        v_unused_1807_ = leanh::lean_ctor_get(v_x_1791_, 0);
                        leanh::lean_dec(v_unused_1807_);
                        v___x_1795_ = v_x_1791_;
                        v_isShared_1796_ = v_isSharedCheck_1806_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_x_1791_);
                        v___x_1795_ = leanh::lean_box(0);
                        v_isShared_1796_ = v_isSharedCheck_1806_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1797_ = leanh::lean_box(0);
                v___x_1798_ = l_Std_Channel_recv___redArg(v___x_1797_, v_shutdownPromise_1789_);
                if v_isShared_1796_ == 0 {
                    leanh::lean_ctor_set(v___x_1795_, 0, v___x_1798_);
                    v___x_1800_ = v___x_1795_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1805_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1805_, 0, v___x_1798_);
                    v___x_1800_ = v_reuseFailAlloc_1805_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1801_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1801_, 0, v___x_1800_);
                v___x_1802_ = leanh::lean_unsigned_to_nat(0);
                v___x_1803_ = 0;
                v___x_1804_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
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
    mut v_shutdownPromise_1808_: *mut leanh::LeanObject,
    mut v___f_1809_: *mut leanh::LeanObject,
    mut v_x_1810_: *mut leanh::LeanObject,
    mut v___y_1811_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1812_ =
        l_Std_Http_Server_shutdownAndWait___lam__2(v_shutdownPromise_1808_, v___f_1809_, v_x_1810_);
    return v_res_1812_;
}
pub unsafe fn l_Std_Http_Server_shutdownAndWait(
    mut v_s_1813_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_context_1815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_shutdownPromise_1816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: u8 = 0;
    let mut v___x_1825_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_context_1815_ = leanh::lean_ctor_get(v_s_1813_, 0);
    leanh::lean_inc_ref(v_context_1815_);
    v_shutdownPromise_1816_ = leanh::lean_ctor_get(v_s_1813_, 3);
    leanh::lean_inc_ref(v_shutdownPromise_1816_);
    leanh::lean_dec_ref(v_s_1813_);
    v___x_1817_ = leanh::lean_box(1);
    v___x_1818_ = l_Std_CancellationContext_cancel(v_context_1815_, v___x_1817_);
    v___f_1819_ = l_Std_Http_Server_waitShutdown___closed__1;
    v___f_1820_ = leanh::lean_alloc_closure(
        l_Std_Http_Server_shutdownAndWait___lam__2___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_1820_, 0, v_shutdownPromise_1816_);
    leanh::lean_closure_set(v___f_1820_, 1, v___f_1819_);
    v___x_1821_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1821_, 0, v___x_1818_);
    v___x_1822_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1822_, 0, v___x_1821_);
    v___x_1823_ = leanh::lean_unsigned_to_nat(0);
    v___x_1824_ = 0;
    v___x_1825_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1823_,
        v___x_1824_,
        v___x_1822_,
        v___f_1820_,
    );
    return v___x_1825_;
}
pub unsafe fn l_Std_Http_Server_shutdownAndWait___boxed(
    mut v_s_1826_: *mut leanh::LeanObject,
    mut v_a_1827_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1828_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1828_ = l_Std_Http_Server_shutdownAndWait(v_s_1826_);
    return v_res_1828_;
}
pub unsafe fn l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0(
    mut v___y_1833_: *mut leanh::LeanObject,
    mut v___y_1834_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1836_ = lean_st_ref_take(v___y_1833_);
    v___x_1837_ = leanh::lean_unsigned_to_nat(1);
    v___x_1838_ = lean_nat_add(v___x_1836_, v___x_1837_);
    leanh::lean_dec(v___x_1836_);
    v___x_1839_ = lean_st_ref_set(v___y_1833_, v___x_1838_);
    v___x_1840_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__1;
    return v___x_1840_;
}
pub unsafe fn l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___boxed(
    mut v___y_1841_: *mut leanh::LeanObject,
    mut v___y_1842_: *mut leanh::LeanObject,
    mut v___y_1843_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1844_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1844_ =
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0(
            v___y_1841_,
            v___y_1842_,
        );
    leanh::lean_dec_ref(v___y_1842_);
    leanh::lean_dec(v___y_1841_);
    return v_res_1844_;
}
pub unsafe fn l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__1(
    mut v___y_1845_: *mut leanh::LeanObject,
    mut v___y_1846_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1848_ = lean_st_ref_take(v___y_1845_);
    v___x_1849_ = leanh::lean_unsigned_to_nat(1);
    v___x_1850_ = lean_nat_sub(v___x_1848_, v___x_1849_);
    leanh::lean_dec(v___x_1848_);
    v___x_1851_ = lean_st_ref_set(v___y_1845_, v___x_1850_);
    v___x_1852_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__1;
    return v___x_1852_;
}
pub unsafe fn l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__1___boxed(
    mut v___y_1853_: *mut leanh::LeanObject,
    mut v___y_1854_: *mut leanh::LeanObject,
    mut v___y_1855_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1856_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1856_ =
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__1(
            v___y_1853_,
            v___y_1854_,
        );
    leanh::lean_dec_ref(v___y_1854_);
    leanh::lean_dec(v___y_1853_);
    return v_res_1856_;
}
pub unsafe fn l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__2(
    mut v_a_1857_: *mut leanh::LeanObject,
    mut v_shutdownPromise_1858_: *mut leanh::LeanObject,
    mut v_x_1859_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1866_: u8 = 0;
    let mut v___x_1868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1871_: u8 = 0;
    let mut v_a_1872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: u8 = 0;
    let mut v___x_1875_: u8 = 0;
    let mut v___x_1876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1859_) == 0 {
                    leanh::lean_dec_ref(v_shutdownPromise_1858_);
                    v_a_1863_ = leanh::lean_ctor_get(v_x_1859_, 0);
                    v_isSharedCheck_1871_ = (!leanh::lean_is_exclusive(v_x_1859_)) as u8;
                    if v_isSharedCheck_1871_ == 0 {
                        v___x_1865_ = v_x_1859_;
                        v_isShared_1866_ = v_isSharedCheck_1871_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1863_);
                        leanh::lean_dec(v_x_1859_);
                        v___x_1865_ = leanh::lean_box(0);
                        v_isShared_1866_ = v_isSharedCheck_1871_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_1872_ = leanh::lean_ctor_get(v_x_1859_, 0);
                    leanh::lean_inc(v_a_1872_);
                    leanh::lean_dec_ref_known(v_x_1859_, 1);
                    v___x_1873_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1874_ = lean_nat_dec_eq(v_a_1857_, v___x_1873_);
                    if v___x_1874_ == 0 {
                        leanh::lean_dec(v_a_1872_);
                        leanh::lean_dec_ref(v_shutdownPromise_1858_);
                        state = 1;
                        continue;
                    } else {
                        v___x_1875_ = (leanh::lean_unbox(v_a_1872_) as u8);
                        leanh::lean_dec(v_a_1872_);
                        if v___x_1875_ == 0 {
                            leanh::lean_dec_ref(v_shutdownPromise_1858_);
                            state = 1;
                            continue;
                        } else {
                            v___x_1876_ = leanh::lean_box(0);
                            v___x_1877_ =
                                l_Std_Channel_send___redArg(v_shutdownPromise_1858_, v___x_1876_);
                            leanh::lean_dec_ref(v___x_1877_);
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
                    v_reuseFailAlloc_1870_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1870_, 0, v_a_1863_);
                    v___x_1868_ = v_reuseFailAlloc_1870_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1869_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1869_, 0, v___x_1868_);
                return v___x_1869_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__2___boxed(
    mut v_a_1879_: *mut leanh::LeanObject,
    mut v_shutdownPromise_1880_: *mut leanh::LeanObject,
    mut v_x_1881_: *mut leanh::LeanObject,
    mut v___y_1882_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1883_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1883_ =
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__2(
            v_a_1879_,
            v_shutdownPromise_1880_,
            v_x_1881_,
        );
    leanh::lean_dec(v_a_1879_);
    return v_res_1883_;
}
pub unsafe fn l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__3(
    mut v_context_1884_: *mut leanh::LeanObject,
    mut v_shutdownPromise_1885_: *mut leanh::LeanObject,
    mut v_x_1886_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1891_: u8 = 0;
    let mut v___x_1893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1896_: u8 = 0;
    let mut v_a_1897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1900_: u8 = 0;
    let mut v_token_1901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: u8 = 0;
    let mut v___f_1903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: u8 = 0;
    let mut v___x_1910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1912_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1886_) == 0 {
                    leanh::lean_dec_ref(v_shutdownPromise_1885_);
                    leanh::lean_dec_ref(v_context_1884_);
                    v_a_1888_ = leanh::lean_ctor_get(v_x_1886_, 0);
                    v_isSharedCheck_1896_ = (!leanh::lean_is_exclusive(v_x_1886_)) as u8;
                    if v_isSharedCheck_1896_ == 0 {
                        v___x_1890_ = v_x_1886_;
                        v_isShared_1891_ = v_isSharedCheck_1896_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1888_);
                        leanh::lean_dec(v_x_1886_);
                        v___x_1890_ = leanh::lean_box(0);
                        v_isShared_1891_ = v_isSharedCheck_1896_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1897_ = leanh::lean_ctor_get(v_x_1886_, 0);
                    v_isSharedCheck_1912_ = (!leanh::lean_is_exclusive(v_x_1886_)) as u8;
                    if v_isSharedCheck_1912_ == 0 {
                        v___x_1899_ = v_x_1886_;
                        v_isShared_1900_ = v_isSharedCheck_1912_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1897_);
                        leanh::lean_dec(v_x_1886_);
                        v___x_1899_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_1895_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1895_, 0, v_a_1888_);
                    v___x_1893_ = v_reuseFailAlloc_1895_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1894_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1894_, 0, v___x_1893_);
                return v___x_1894_;
            }
            3 => {
                v_token_1901_ = leanh::lean_ctor_get(v_context_1884_, 1);
                leanh::lean_inc_ref(v_token_1901_);
                leanh::lean_dec_ref(v_context_1884_);
                v___x_1902_ = l_Std_CancellationToken_isCancelled(v_token_1901_);
                v___f_1903_ = leanh::lean_alloc_closure(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__2___boxed as *mut core::ffi::c_void, 4, 2);
                leanh::lean_closure_set(v___f_1903_, 0, v_a_1897_);
                leanh::lean_closure_set(v___f_1903_, 1, v_shutdownPromise_1885_);
                v___x_1904_ = leanh::lean_box((v___x_1902_) as usize);
                if v_isShared_1900_ == 0 {
                    leanh::lean_ctor_set(v___x_1899_, 0, v___x_1904_);
                    v___x_1906_ = v___x_1899_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1911_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1911_, 0, v___x_1904_);
                    v___x_1906_ = v_reuseFailAlloc_1911_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1907_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1907_, 0, v___x_1906_);
                v___x_1908_ = leanh::lean_unsigned_to_nat(0);
                v___x_1909_ = 0;
                v___x_1910_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
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
    mut v_context_1913_: *mut leanh::LeanObject,
    mut v_shutdownPromise_1914_: *mut leanh::LeanObject,
    mut v_x_1915_: *mut leanh::LeanObject,
    mut v___y_1916_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1917_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1917_ =
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__3(
            v_context_1913_,
            v_shutdownPromise_1914_,
            v_x_1915_,
        );
    return v_res_1917_;
}
pub unsafe fn l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__4(
    mut v___f_1918_: *mut leanh::LeanObject,
    mut v_____r_1919_: *mut leanh::LeanObject,
    mut v___y_1920_: *mut leanh::LeanObject,
    mut v___y_1921_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: u8 = 0;
    let mut v___x_1928_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1923_ = lean_st_ref_get(v___y_1920_);
    v___x_1924_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1924_, 0, v___x_1923_);
    v___x_1925_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1925_, 0, v___x_1924_);
    v___x_1926_ = leanh::lean_unsigned_to_nat(0);
    v___x_1927_ = 0;
    v___x_1928_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1926_,
        v___x_1927_,
        v___x_1925_,
        v___f_1918_,
    );
    return v___x_1928_;
}
pub unsafe fn l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__4___boxed(
    mut v___f_1929_: *mut leanh::LeanObject,
    mut v_____r_1930_: *mut leanh::LeanObject,
    mut v___y_1931_: *mut leanh::LeanObject,
    mut v___y_1932_: *mut leanh::LeanObject,
    mut v___y_1933_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1934_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1934_ =
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__4(
            v___f_1929_,
            v_____r_1930_,
            v___y_1931_,
            v___y_1932_,
        );
    leanh::lean_dec_ref(v___y_1932_);
    leanh::lean_dec(v___y_1931_);
    return v_res_1934_;
}
pub unsafe fn l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__5(
    mut v_x_1935_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_1936_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_1936_ = leanh::lean_ctor_get(v_x_1935_, 0);
    leanh::lean_inc(v_fst_1936_);
    return v_fst_1936_;
}
pub unsafe fn l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__5___boxed(
    mut v_x_1937_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1938_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1938_ =
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__5(
            v_x_1937_,
        );
    leanh::lean_dec_ref(v_x_1937_);
    return v_res_1938_;
}
pub unsafe fn l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__6(
    mut v___x_1939_: *mut leanh::LeanObject,
    mut v___f_1940_: *mut leanh::LeanObject,
    mut v___f_1941_: *mut leanh::LeanObject,
    mut v___f_1942_: *mut leanh::LeanObject,
    mut v___f_1943_: *mut leanh::LeanObject,
    mut v_activeConnections_1944_: *mut leanh::LeanObject,
    mut v_____r_1945_: *mut leanh::LeanObject,
    mut v___y_1946_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2353__overap_1949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v___x_1939_);
    v___x_1948_ = leanh::lean_alloc_closure(
        l_StateRefT_x27_instMonad___aux__13___boxed as *mut core::ffi::c_void,
        9,
        8,
    );
    leanh::lean_closure_set(v___x_1948_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1948_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1948_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1948_, 3, v___x_1939_);
    leanh::lean_closure_set(v___x_1948_, 4, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1948_, 5, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1948_, 6, v___f_1940_);
    leanh::lean_closure_set(v___x_1948_, 7, v___f_1941_);
    v___x_2353__overap_1949_ = l_Std_Mutex_atomically___redArg(
        v___x_1939_,
        v___f_1942_,
        v___f_1943_,
        v_activeConnections_1944_,
        v___x_1948_,
    );
    leanh::lean_inc_ref(v___y_1946_);
    v___x_1950_ = leanh::lean_apply_2(
        v___x_2353__overap_1949_,
        v___y_1946_,
        leanh::lean_box(0),
    );
    return v___x_1950_;
}
pub unsafe fn l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__6___boxed(
    mut v___x_1951_: *mut leanh::LeanObject,
    mut v___f_1952_: *mut leanh::LeanObject,
    mut v___f_1953_: *mut leanh::LeanObject,
    mut v___f_1954_: *mut leanh::LeanObject,
    mut v___f_1955_: *mut leanh::LeanObject,
    mut v_activeConnections_1956_: *mut leanh::LeanObject,
    mut v_____r_1957_: *mut leanh::LeanObject,
    mut v___y_1958_: *mut leanh::LeanObject,
    mut v___y_1959_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1960_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec_ref(v___y_1958_);
    return v_res_1960_;
}
pub unsafe fn l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__7(
    mut v___f_1961_: *mut leanh::LeanObject,
    mut v_a_1962_: *mut leanh::LeanObject,
    mut v_x_1963_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1963_) == 0 {
        let mut v___x_1965_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v___f_1961_);
        v___x_1965_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1965_, 0, v_x_1963_);
        return v___x_1965_;
    } else {
        let mut v_a_1966_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1967_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_1966_ = leanh::lean_ctor_get(v_x_1963_, 0);
        leanh::lean_inc(v_a_1966_);
        leanh::lean_dec_ref_known(v_x_1963_, 1);
        leanh::lean_inc_ref(v_a_1962_);
        v___x_1967_ = leanh::lean_apply_3(
            v___f_1961_,
            v_a_1966_,
            v_a_1962_,
            leanh::lean_box(0),
        );
        return v___x_1967_;
    }
}
pub unsafe fn l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__7___boxed(
    mut v___f_1968_: *mut leanh::LeanObject,
    mut v_a_1969_: *mut leanh::LeanObject,
    mut v_x_1970_: *mut leanh::LeanObject,
    mut v___y_1971_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1972_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1972_ =
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__7(
            v___f_1968_,
            v_a_1969_,
            v_x_1970_,
        );
    leanh::lean_dec_ref(v_a_1969_);
    return v_res_1972_;
}
pub unsafe fn l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__8(
    mut v_releaseConnectionPermit_1973_: u8,
    mut v___f_1974_: *mut leanh::LeanObject,
    mut v_a_1975_: *mut leanh::LeanObject,
    mut v_connectionLimit_1976_: *mut leanh::LeanObject,
    mut v___f_1977_: *mut leanh::LeanObject,
    mut v_opt_1978_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1985_: u8 = 0;
    let mut v___x_1986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: u8 = 0;
    let mut v___x_1992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1994_: u8 = 0;
    let mut v___x_1995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_releaseConnectionPermit_1973_ == 0 {
                    leanh::lean_dec_ref(v___f_1977_);
                    leanh::lean_dec(v_connectionLimit_1976_);
                    v___x_1980_ = leanh::lean_box(0);
                    leanh::lean_inc_ref(v_a_1975_);
                    v___x_1981_ = leanh::lean_apply_3(
                        v___f_1974_,
                        v___x_1980_,
                        v_a_1975_,
                        leanh::lean_box(0),
                    );
                    return v___x_1981_;
                } else {
                    if leanh::lean_obj_tag(v_connectionLimit_1976_) == 1 {
                        leanh::lean_dec_ref(v___f_1974_);
                        v_val_1982_ = leanh::lean_ctor_get(v_connectionLimit_1976_, 0);
                        v_isSharedCheck_1994_ =
                            (!leanh::lean_is_exclusive(v_connectionLimit_1976_)) as u8;
                        if v_isSharedCheck_1994_ == 0 {
                            v___x_1984_ = v_connectionLimit_1976_;
                            v_isShared_1985_ = v_isSharedCheck_1994_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_1982_);
                            leanh::lean_dec(v_connectionLimit_1976_);
                            v___x_1984_ = leanh::lean_box(0);
                            v_isShared_1985_ = v_isSharedCheck_1994_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v___f_1977_);
                        leanh::lean_dec(v_connectionLimit_1976_);
                        v___x_1995_ = leanh::lean_box(0);
                        leanh::lean_inc_ref(v_a_1975_);
                        v___x_1996_ = leanh::lean_apply_3(
                            v___f_1974_,
                            v___x_1995_,
                            v_a_1975_,
                            leanh::lean_box(0),
                        );
                        return v___x_1996_;
                    }
                }
            }
            1 => {
                v___x_1986_ = l_Std_Semaphore_release(v_val_1982_);
                if v_isShared_1985_ == 0 {
                    leanh::lean_ctor_set(v___x_1984_, 0, v___x_1986_);
                    v___x_1988_ = v___x_1984_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1993_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1993_, 0, v___x_1986_);
                    v___x_1988_ = v_reuseFailAlloc_1993_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1989_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1989_, 0, v___x_1988_);
                v___x_1990_ = leanh::lean_unsigned_to_nat(0);
                v___x_1991_ = 0;
                v___x_1992_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
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
    mut v_releaseConnectionPermit_1997_: *mut leanh::LeanObject,
    mut v___f_1998_: *mut leanh::LeanObject,
    mut v_a_1999_: *mut leanh::LeanObject,
    mut v_connectionLimit_2000_: *mut leanh::LeanObject,
    mut v___f_2001_: *mut leanh::LeanObject,
    mut v_opt_2002_: *mut leanh::LeanObject,
    mut v___y_2003_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_releaseConnectionPermit_boxed_2004_: u8 = 0;
    let mut v_res_2005_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_releaseConnectionPermit_boxed_2004_ =
        (leanh::lean_unbox(v_releaseConnectionPermit_1997_) as u8);
    v_res_2005_ =
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__8(
            v_releaseConnectionPermit_boxed_2004_,
            v___f_1998_,
            v_a_1999_,
            v_connectionLimit_2000_,
            v___f_2001_,
            v_opt_2002_,
        );
    leanh::lean_dec(v_opt_2002_);
    leanh::lean_dec_ref(v_a_1999_);
    return v_res_2005_;
}
pub unsafe fn l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__9(
    mut v_action_2006_: *mut leanh::LeanObject,
    mut v_a_2007_: *mut leanh::LeanObject,
    mut v___f_2008_: *mut leanh::LeanObject,
    mut v___f_2009_: *mut leanh::LeanObject,
    mut v_x_2010_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_2012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2015_: u8 = 0;
    let mut v___x_2017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2020_: u8 = 0;
    let mut v___x_2021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: u8 = 0;
    let mut v___x_2024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2032_: u8 = 0;
    let mut v___x_2034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2036_: u8 = 0;
    let mut v_a_2037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2040_: u8 = 0;
    let mut v_fst_2041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2045_: u8 = 0;
    let mut v_a_2046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2049_: u8 = 0;
    let mut v___x_2050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2055_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2010_) == 0 {
                    leanh::lean_dec(v___f_2009_);
                    leanh::lean_dec_ref(v___f_2008_);
                    leanh::lean_dec_ref(v_action_2006_);
                    v_a_2012_ = leanh::lean_ctor_get(v_x_2010_, 0);
                    v_isSharedCheck_2020_ = (!leanh::lean_is_exclusive(v_x_2010_)) as u8;
                    if v_isSharedCheck_2020_ == 0 {
                        v___x_2014_ = v_x_2010_;
                        v_isShared_2015_ = v_isSharedCheck_2020_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2012_);
                        leanh::lean_dec(v_x_2010_);
                        v___x_2014_ = leanh::lean_box(0);
                        v_isShared_2015_ = v_isSharedCheck_2020_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref_known(v_x_2010_, 1);
                    leanh::lean_inc_ref(v_a_2007_);
                    v___x_2021_ = leanh::lean_apply_1(v_action_2006_, v_a_2007_);
                    v___x_2022_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2023_ = 0;
                    v___x_2024_ = l_Std_Async_EAsync_tryFinally_x27___redArg(
                        v___x_2021_,
                        v___f_2008_,
                        v___x_2022_,
                        v___x_2023_,
                    );
                    if leanh::lean_obj_tag(v___x_2024_) == 0 {
                        leanh::lean_dec(v___f_2009_);
                        v_a_2028_ = leanh::lean_ctor_get(v___x_2024_, 0);
                        leanh::lean_inc(v_a_2028_);
                        leanh::lean_dec_ref_known(v___x_2024_, 1);
                        if leanh::lean_obj_tag(v_a_2028_) == 0 {
                            v_a_2029_ = leanh::lean_ctor_get(v_a_2028_, 0);
                            v_isSharedCheck_2036_ =
                                (!leanh::lean_is_exclusive(v_a_2028_)) as u8;
                            if v_isSharedCheck_2036_ == 0 {
                                v___x_2031_ = v_a_2028_;
                                v_isShared_2032_ = v_isSharedCheck_2036_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2029_);
                                leanh::lean_dec(v_a_2028_);
                                v___x_2031_ = leanh::lean_box(0);
                                v_isShared_2032_ = v_isSharedCheck_2036_;
                                state = 4;
                                continue;
                            }
                        } else {
                            v_a_2037_ = leanh::lean_ctor_get(v_a_2028_, 0);
                            v_isSharedCheck_2045_ =
                                (!leanh::lean_is_exclusive(v_a_2028_)) as u8;
                            if v_isSharedCheck_2045_ == 0 {
                                v___x_2039_ = v_a_2028_;
                                v_isShared_2040_ = v_isSharedCheck_2045_;
                                state = 6;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2037_);
                                leanh::lean_dec(v_a_2028_);
                                v___x_2039_ = leanh::lean_box(0);
                                v_isShared_2040_ = v_isSharedCheck_2045_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        v_a_2046_ = leanh::lean_ctor_get(v___x_2024_, 0);
                        v_isSharedCheck_2055_ =
                            (!leanh::lean_is_exclusive(v___x_2024_)) as u8;
                        if v_isSharedCheck_2055_ == 0 {
                            v___x_2048_ = v___x_2024_;
                            v_isShared_2049_ = v_isSharedCheck_2055_;
                            state = 8;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2046_);
                            leanh::lean_dec(v___x_2024_);
                            v___x_2048_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2019_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2019_, 0, v_a_2012_);
                    v___x_2017_ = v_reuseFailAlloc_2019_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2018_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2018_, 0, v___x_2017_);
                return v___x_2018_;
            }
            3 => {
                v___x_2027_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2027_, 0, v___y_2026_);
                return v___x_2027_;
            }
            4 => {
                if v_isShared_2032_ == 0 {
                    v___x_2034_ = v___x_2031_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2035_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_a_2029_);
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
                v_fst_2041_ = leanh::lean_ctor_get(v_a_2037_, 0);
                leanh::lean_inc(v_fst_2041_);
                leanh::lean_dec(v_a_2037_);
                if v_isShared_2040_ == 0 {
                    leanh::lean_ctor_set(v___x_2039_, 0, v_fst_2041_);
                    v___x_2043_ = v___x_2039_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2044_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2044_, 0, v_fst_2041_);
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
                    leanh::lean_alloc_closure(l_Except_map as *mut core::ffi::c_void, 5, 4);
                leanh::lean_closure_set(v___x_2050_, 0, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_2050_, 1, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_2050_, 2, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_2050_, 3, v___f_2009_);
                v___x_2051_ = lean_task_map(v___x_2050_, v_a_2046_, v___x_2022_, v___x_2023_);
                if v_isShared_2049_ == 0 {
                    leanh::lean_ctor_set(v___x_2048_, 0, v___x_2051_);
                    v___x_2053_ = v___x_2048_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2054_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2054_, 0, v___x_2051_);
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
    mut v_action_2056_: *mut leanh::LeanObject,
    mut v_a_2057_: *mut leanh::LeanObject,
    mut v___f_2058_: *mut leanh::LeanObject,
    mut v___f_2059_: *mut leanh::LeanObject,
    mut v_x_2060_: *mut leanh::LeanObject,
    mut v___y_2061_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2062_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2062_ =
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__9(
            v_action_2056_,
            v_a_2057_,
            v___f_2058_,
            v___f_2059_,
            v_x_2060_,
        );
    leanh::lean_dec_ref(v_a_2057_);
    return v_res_2062_;
}
pub unsafe fn l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg(
    mut v_s_2072_: *mut leanh::LeanObject,
    mut v_releaseConnectionPermit_2073_: u8,
    mut v_action_2074_: *mut leanh::LeanObject,
    mut v_a_2075_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_context_2078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_activeConnections_2079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_connectionLimit_2080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_shutdownPromise_2081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520__overap_2085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: u8 = 0;
    let mut v___x_2098_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2077_ = l_Std_Async_ContextAsync_instMonad;
    v_context_2078_ = leanh::lean_ctor_get(v_s_2072_, 0);
    leanh::lean_inc_ref(v_context_2078_);
    v_activeConnections_2079_ = leanh::lean_ctor_get(v_s_2072_, 1);
    leanh::lean_inc_ref_n(v_activeConnections_2079_, 2);
    v_connectionLimit_2080_ = leanh::lean_ctor_get(v_s_2072_, 2);
    leanh::lean_inc(v_connectionLimit_2080_);
    v_shutdownPromise_2081_ = leanh::lean_ctor_get(v_s_2072_, 3);
    leanh::lean_inc_ref(v_shutdownPromise_2081_);
    leanh::lean_dec_ref(v_s_2072_);
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
    leanh::lean_inc_ref_n(v_a_2075_, 4);
    v___x_2086_ = leanh::lean_apply_2(
        v___x_1520__overap_2085_,
        v_a_2075_,
        leanh::lean_box(0),
    );
    v___f_2087_ =
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__5;
    v___f_2088_ = leanh::lean_alloc_closure(
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__3___boxed
            as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_2088_, 0, v_context_2078_);
    leanh::lean_closure_set(v___f_2088_, 1, v_shutdownPromise_2081_);
    v___f_2089_ = leanh::lean_alloc_closure(
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__4___boxed
            as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_2089_, 0, v___f_2088_);
    v___f_2090_ =
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__6;
    v___f_2091_ = leanh::lean_alloc_closure(
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__6___boxed
            as *mut core::ffi::c_void,
        9,
        6,
    );
    leanh::lean_closure_set(v___f_2091_, 0, v___x_2077_);
    leanh::lean_closure_set(v___f_2091_, 1, v___f_2087_);
    leanh::lean_closure_set(v___f_2091_, 2, v___f_2089_);
    leanh::lean_closure_set(v___f_2091_, 3, v___f_2083_);
    leanh::lean_closure_set(v___f_2091_, 4, v___f_2084_);
    leanh::lean_closure_set(v___f_2091_, 5, v_activeConnections_2079_);
    leanh::lean_inc_ref(v___f_2091_);
    v___f_2092_ = leanh::lean_alloc_closure(
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__7___boxed
            as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_2092_, 0, v___f_2091_);
    leanh::lean_closure_set(v___f_2092_, 1, v_a_2075_);
    v___x_2093_ = leanh::lean_box((v_releaseConnectionPermit_2073_) as usize);
    v___f_2094_ = leanh::lean_alloc_closure(
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__8___boxed
            as *mut core::ffi::c_void,
        7,
        5,
    );
    leanh::lean_closure_set(v___f_2094_, 0, v___x_2093_);
    leanh::lean_closure_set(v___f_2094_, 1, v___f_2091_);
    leanh::lean_closure_set(v___f_2094_, 2, v_a_2075_);
    leanh::lean_closure_set(v___f_2094_, 3, v_connectionLimit_2080_);
    leanh::lean_closure_set(v___f_2094_, 4, v___f_2092_);
    v___f_2095_ = leanh::lean_alloc_closure(
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__9___boxed
            as *mut core::ffi::c_void,
        6,
        4,
    );
    leanh::lean_closure_set(v___f_2095_, 0, v_action_2074_);
    leanh::lean_closure_set(v___f_2095_, 1, v_a_2075_);
    leanh::lean_closure_set(v___f_2095_, 2, v___f_2094_);
    leanh::lean_closure_set(v___f_2095_, 3, v___f_2090_);
    v___x_2096_ = leanh::lean_unsigned_to_nat(0);
    v___x_2097_ = 0;
    v___x_2098_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2096_,
        v___x_2097_,
        v___x_2086_,
        v___f_2095_,
    );
    return v___x_2098_;
}
pub unsafe fn l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___boxed(
    mut v_s_2099_: *mut leanh::LeanObject,
    mut v_releaseConnectionPermit_2100_: *mut leanh::LeanObject,
    mut v_action_2101_: *mut leanh::LeanObject,
    mut v_a_2102_: *mut leanh::LeanObject,
    mut v_a_2103_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_releaseConnectionPermit_boxed_2104_: u8 = 0;
    let mut v_res_2105_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_releaseConnectionPermit_boxed_2104_ =
        (leanh::lean_unbox(v_releaseConnectionPermit_2100_) as u8);
    v_res_2105_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg(
        v_s_2099_,
        v_releaseConnectionPermit_boxed_2104_,
        v_action_2101_,
        v_a_2102_,
    );
    leanh::lean_dec_ref(v_a_2102_);
    return v_res_2105_;
}
pub unsafe fn l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation(
    mut v_00_u03b1_2106_: *mut leanh::LeanObject,
    mut v_s_2107_: *mut leanh::LeanObject,
    mut v_releaseConnectionPermit_2108_: u8,
    mut v_action_2109_: *mut leanh::LeanObject,
    mut v_a_2110_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_context_2113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_activeConnections_2114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_connectionLimit_2115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_shutdownPromise_2116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2130__overap_2120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: u8 = 0;
    let mut v___x_2133_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2112_ = l_Std_Async_ContextAsync_instMonad;
    v_context_2113_ = leanh::lean_ctor_get(v_s_2107_, 0);
    leanh::lean_inc_ref(v_context_2113_);
    v_activeConnections_2114_ = leanh::lean_ctor_get(v_s_2107_, 1);
    leanh::lean_inc_ref_n(v_activeConnections_2114_, 2);
    v_connectionLimit_2115_ = leanh::lean_ctor_get(v_s_2107_, 2);
    leanh::lean_inc(v_connectionLimit_2115_);
    v_shutdownPromise_2116_ = leanh::lean_ctor_get(v_s_2107_, 3);
    leanh::lean_inc_ref(v_shutdownPromise_2116_);
    leanh::lean_dec_ref(v_s_2107_);
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
    leanh::lean_inc_ref_n(v_a_2110_, 4);
    v___x_2121_ = leanh::lean_apply_2(
        v___x_2130__overap_2120_,
        v_a_2110_,
        leanh::lean_box(0),
    );
    v___f_2122_ =
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__5;
    v___f_2123_ = leanh::lean_alloc_closure(
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__3___boxed
            as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_2123_, 0, v_context_2113_);
    leanh::lean_closure_set(v___f_2123_, 1, v_shutdownPromise_2116_);
    v___f_2124_ = leanh::lean_alloc_closure(
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__4___boxed
            as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_2124_, 0, v___f_2123_);
    v___f_2125_ =
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__6;
    v___f_2126_ = leanh::lean_alloc_closure(
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__6___boxed
            as *mut core::ffi::c_void,
        9,
        6,
    );
    leanh::lean_closure_set(v___f_2126_, 0, v___x_2112_);
    leanh::lean_closure_set(v___f_2126_, 1, v___f_2122_);
    leanh::lean_closure_set(v___f_2126_, 2, v___f_2124_);
    leanh::lean_closure_set(v___f_2126_, 3, v___f_2118_);
    leanh::lean_closure_set(v___f_2126_, 4, v___f_2119_);
    leanh::lean_closure_set(v___f_2126_, 5, v_activeConnections_2114_);
    leanh::lean_inc_ref(v___f_2126_);
    v___f_2127_ = leanh::lean_alloc_closure(
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__7___boxed
            as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_2127_, 0, v___f_2126_);
    leanh::lean_closure_set(v___f_2127_, 1, v_a_2110_);
    v___x_2128_ = leanh::lean_box((v_releaseConnectionPermit_2108_) as usize);
    v___f_2129_ = leanh::lean_alloc_closure(
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__8___boxed
            as *mut core::ffi::c_void,
        7,
        5,
    );
    leanh::lean_closure_set(v___f_2129_, 0, v___x_2128_);
    leanh::lean_closure_set(v___f_2129_, 1, v___f_2126_);
    leanh::lean_closure_set(v___f_2129_, 2, v_a_2110_);
    leanh::lean_closure_set(v___f_2129_, 3, v_connectionLimit_2115_);
    leanh::lean_closure_set(v___f_2129_, 4, v___f_2127_);
    v___f_2130_ = leanh::lean_alloc_closure(
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__9___boxed
            as *mut core::ffi::c_void,
        6,
        4,
    );
    leanh::lean_closure_set(v___f_2130_, 0, v_action_2109_);
    leanh::lean_closure_set(v___f_2130_, 1, v_a_2110_);
    leanh::lean_closure_set(v___f_2130_, 2, v___f_2129_);
    leanh::lean_closure_set(v___f_2130_, 3, v___f_2125_);
    v___x_2131_ = leanh::lean_unsigned_to_nat(0);
    v___x_2132_ = 0;
    v___x_2133_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2131_,
        v___x_2132_,
        v___x_2121_,
        v___f_2130_,
    );
    return v___x_2133_;
}
pub unsafe fn l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___boxed(
    mut v_00_u03b1_2134_: *mut leanh::LeanObject,
    mut v_s_2135_: *mut leanh::LeanObject,
    mut v_releaseConnectionPermit_2136_: *mut leanh::LeanObject,
    mut v_action_2137_: *mut leanh::LeanObject,
    mut v_a_2138_: *mut leanh::LeanObject,
    mut v_a_2139_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_releaseConnectionPermit_boxed_2140_: u8 = 0;
    let mut v_res_2141_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_releaseConnectionPermit_boxed_2140_ =
        (leanh::lean_unbox(v_releaseConnectionPermit_2136_) as u8);
    v_res_2141_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation(
        v_00_u03b1_2134_,
        v_s_2135_,
        v_releaseConnectionPermit_boxed_2140_,
        v_action_2137_,
        v_a_2138_,
    );
    leanh::lean_dec_ref(v_a_2138_);
    return v_res_2141_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__0(
    mut v_x_2142_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_2142_) == 0 {
        let mut v___x_2144_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2144_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_2144_, 0, v_x_2142_);
        return v___x_2144_;
    } else {
        let mut v___x_2145_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref_known(v_x_2142_, 1);
        v___x_2145_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__1;
        return v___x_2145_;
    }
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__0___boxed(
    mut v_x_2146_: *mut leanh::LeanObject,
    mut v___y_2147_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2148_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2148_ = l_Std_Http_Server_serve___redArg___lam__0(v_x_2146_);
    return v_res_2148_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__1(
    mut v_x_2149_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_2151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2154_: u8 = 0;
    let mut v___x_2156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2159_: u8 = 0;
    let mut v_a_2160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2163_: u8 = 0;
    let mut v_a_2164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2167_: u8 = 0;
    let mut v___x_2169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2175_: u8 = 0;
    let mut v_a_2176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2179_: u8 = 0;
    let mut v___x_2181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2187_: u8 = 0;
    let mut v_isSharedCheck_2188_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2149_) == 0 {
                    v_a_2151_ = leanh::lean_ctor_get(v_x_2149_, 0);
                    v_isSharedCheck_2159_ = (!leanh::lean_is_exclusive(v_x_2149_)) as u8;
                    if v_isSharedCheck_2159_ == 0 {
                        v___x_2153_ = v_x_2149_;
                        v_isShared_2154_ = v_isSharedCheck_2159_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2151_);
                        leanh::lean_dec(v_x_2149_);
                        v___x_2153_ = leanh::lean_box(0);
                        v_isShared_2154_ = v_isSharedCheck_2159_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2160_ = leanh::lean_ctor_get(v_x_2149_, 0);
                    v_isSharedCheck_2188_ = (!leanh::lean_is_exclusive(v_x_2149_)) as u8;
                    if v_isSharedCheck_2188_ == 0 {
                        v___x_2162_ = v_x_2149_;
                        v_isShared_2163_ = v_isSharedCheck_2188_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2160_);
                        leanh::lean_dec(v_x_2149_);
                        v___x_2162_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2158_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2158_, 0, v_a_2151_);
                    v___x_2156_ = v_reuseFailAlloc_2158_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2157_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2157_, 0, v___x_2156_);
                return v___x_2157_;
            }
            3 => {
                if leanh::lean_obj_tag(v_a_2160_) == 0 {
                    v_a_2164_ = leanh::lean_ctor_get(v_a_2160_, 0);
                    v_isSharedCheck_2175_ = (!leanh::lean_is_exclusive(v_a_2160_)) as u8;
                    if v_isSharedCheck_2175_ == 0 {
                        v___x_2166_ = v_a_2160_;
                        v_isShared_2167_ = v_isSharedCheck_2175_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2164_);
                        leanh::lean_dec(v_a_2160_);
                        v___x_2166_ = leanh::lean_box(0);
                        v_isShared_2167_ = v_isSharedCheck_2175_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_a_2176_ = leanh::lean_ctor_get(v_a_2160_, 0);
                    v_isSharedCheck_2187_ = (!leanh::lean_is_exclusive(v_a_2160_)) as u8;
                    if v_isSharedCheck_2187_ == 0 {
                        v___x_2178_ = v_a_2160_;
                        v_isShared_2179_ = v_isSharedCheck_2187_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2176_);
                        leanh::lean_dec(v_a_2160_);
                        v___x_2178_ = leanh::lean_box(0);
                        v_isShared_2179_ = v_isSharedCheck_2187_;
                        state = 7;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_2167_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2166_, 1);
                    v___x_2169_ = v___x_2166_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2174_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2174_, 0, v_a_2164_);
                    v___x_2169_ = v_reuseFailAlloc_2174_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_2163_ == 0 {
                    leanh::lean_ctor_set(v___x_2162_, 0, v___x_2169_);
                    v___x_2171_ = v___x_2162_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2173_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2173_, 0, v___x_2169_);
                    v___x_2171_ = v_reuseFailAlloc_2173_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_2172_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2172_, 0, v___x_2171_);
                return v___x_2172_;
            }
            7 => {
                if v_isShared_2179_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2178_, 0);
                    v___x_2181_ = v___x_2178_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2186_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2186_, 0, v_a_2176_);
                    v___x_2181_ = v_reuseFailAlloc_2186_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_2163_ == 0 {
                    leanh::lean_ctor_set(v___x_2162_, 0, v___x_2181_);
                    v___x_2183_ = v___x_2162_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2185_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2185_, 0, v___x_2181_);
                    v___x_2183_ = v_reuseFailAlloc_2185_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_2184_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2184_, 0, v___x_2183_);
                return v___x_2184_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__1___boxed(
    mut v_x_2189_: *mut leanh::LeanObject,
    mut v___y_2190_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2191_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2191_ = l_Std_Http_Server_serve___redArg___lam__1(v_x_2189_);
    return v_res_2191_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__3(
    mut v_x_2192_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2193_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_2193_ = leanh::lean_ctor_get(v_x_2192_, 0);
    leanh::lean_inc(v_fst_2193_);
    return v_fst_2193_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__3___boxed(
    mut v_x_2194_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2195_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2195_ = l_Std_Http_Server_serve___redArg___lam__3(v_x_2194_);
    leanh::lean_dec_ref(v_x_2194_);
    return v_res_2195_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__4(
    mut v_x_2200_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2202_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2202_ = l_Std_Http_Server_serve___redArg___lam__4___closed__1;
    return v___x_2202_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__4___boxed(
    mut v_x_2203_: *mut leanh::LeanObject,
    mut v___y_2204_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2205_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2205_ = l_Std_Http_Server_serve___redArg___lam__4(v_x_2203_);
    return v_res_2205_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__2(
    mut v_x_2206_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2208_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2208_, 0, v_x_2206_);
    v___x_2209_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2209_, 0, v___x_2208_);
    v___x_2210_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2210_, 0, v___x_2209_);
    return v___x_2210_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__2___boxed(
    mut v_x_2211_: *mut leanh::LeanObject,
    mut v___y_2212_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2213_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2213_ = l_Std_Http_Server_serve___redArg___lam__2(v_x_2211_);
    return v_res_2213_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__5(
    mut v_x_2214_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_2216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2219_: u8 = 0;
    let mut v___x_2221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2224_: u8 = 0;
    let mut v_a_2225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2228_: u8 = 0;
    let mut v_token_2229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2235_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2214_) == 0 {
                    v_a_2216_ = leanh::lean_ctor_get(v_x_2214_, 0);
                    v_isSharedCheck_2224_ = (!leanh::lean_is_exclusive(v_x_2214_)) as u8;
                    if v_isSharedCheck_2224_ == 0 {
                        v___x_2218_ = v_x_2214_;
                        v_isShared_2219_ = v_isSharedCheck_2224_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2216_);
                        leanh::lean_dec(v_x_2214_);
                        v___x_2218_ = leanh::lean_box(0);
                        v_isShared_2219_ = v_isSharedCheck_2224_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2225_ = leanh::lean_ctor_get(v_x_2214_, 0);
                    v_isSharedCheck_2235_ = (!leanh::lean_is_exclusive(v_x_2214_)) as u8;
                    if v_isSharedCheck_2235_ == 0 {
                        v___x_2227_ = v_x_2214_;
                        v_isShared_2228_ = v_isSharedCheck_2235_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2225_);
                        leanh::lean_dec(v_x_2214_);
                        v___x_2227_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2223_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2223_, 0, v_a_2216_);
                    v___x_2221_ = v_reuseFailAlloc_2223_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2222_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2222_, 0, v___x_2221_);
                return v___x_2222_;
            }
            3 => {
                v_token_2229_ = leanh::lean_ctor_get(v_a_2225_, 1);
                leanh::lean_inc_ref(v_token_2229_);
                leanh::lean_dec(v_a_2225_);
                v___x_2230_ = l_Std_CancellationToken_selector(v_token_2229_);
                if v_isShared_2228_ == 0 {
                    leanh::lean_ctor_set(v___x_2227_, 0, v___x_2230_);
                    v___x_2232_ = v___x_2227_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2234_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2234_, 0, v___x_2230_);
                    v___x_2232_ = v_reuseFailAlloc_2234_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2233_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2233_, 0, v___x_2232_);
                return v___x_2233_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__5___boxed(
    mut v_x_2236_: *mut leanh::LeanObject,
    mut v___y_2237_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2238_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2238_ = l_Std_Http_Server_serve___redArg___lam__5(v_x_2236_);
    return v_res_2238_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__10(
    mut v___x_2239_: *mut leanh::LeanObject,
    mut v_____r_2240_: *mut leanh::LeanObject,
    mut v___y_2241_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2243_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2243_, 0, v___x_2239_);
    v___x_2244_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2244_, 0, v___x_2243_);
    v___x_2245_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2245_, 0, v___x_2244_);
    return v___x_2245_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__10___boxed(
    mut v___x_2246_: *mut leanh::LeanObject,
    mut v_____r_2247_: *mut leanh::LeanObject,
    mut v___y_2248_: *mut leanh::LeanObject,
    mut v___y_2249_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2250_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2250_ =
        l_Std_Http_Server_serve___redArg___lam__10(v___x_2246_, v_____r_2247_, v___y_2248_);
    leanh::lean_dec_ref(v___y_2248_);
    return v_res_2250_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__6(
    mut v___x_2251_: *mut leanh::LeanObject,
    mut v_x_2252_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_2254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2257_: u8 = 0;
    let mut v___x_2259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2262_: u8 = 0;
    let mut v___x_2264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2265_: u8 = 0;
    let mut v___x_2266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2271_: u8 = 0;
    let mut v_unused_2272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2252_) == 0 {
                    v_a_2254_ = leanh::lean_ctor_get(v_x_2252_, 0);
                    v_isSharedCheck_2262_ = (!leanh::lean_is_exclusive(v_x_2252_)) as u8;
                    if v_isSharedCheck_2262_ == 0 {
                        v___x_2256_ = v_x_2252_;
                        v_isShared_2257_ = v_isSharedCheck_2262_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2254_);
                        leanh::lean_dec(v_x_2252_);
                        v___x_2256_ = leanh::lean_box(0);
                        v_isShared_2257_ = v_isSharedCheck_2262_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_isSharedCheck_2271_ = (!leanh::lean_is_exclusive(v_x_2252_)) as u8;
                    if v_isSharedCheck_2271_ == 0 {
                        v_unused_2272_ = leanh::lean_ctor_get(v_x_2252_, 0);
                        leanh::lean_dec(v_unused_2272_);
                        v___x_2264_ = v_x_2252_;
                        v_isShared_2265_ = v_isSharedCheck_2271_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_dec(v_x_2252_);
                        v___x_2264_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2261_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2261_, 0, v_a_2254_);
                    v___x_2259_ = v_reuseFailAlloc_2261_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2260_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2260_, 0, v___x_2259_);
                return v___x_2260_;
            }
            3 => {
                v___x_2266_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2266_, 0, v___x_2251_);
                if v_isShared_2265_ == 0 {
                    leanh::lean_ctor_set(v___x_2264_, 0, v___x_2266_);
                    v___x_2268_ = v___x_2264_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2270_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2270_, 0, v___x_2266_);
                    v___x_2268_ = v_reuseFailAlloc_2270_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2269_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2269_, 0, v___x_2268_);
                return v___x_2269_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__6___boxed(
    mut v___x_2273_: *mut leanh::LeanObject,
    mut v_x_2274_: *mut leanh::LeanObject,
    mut v___y_2275_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2276_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2276_ = l_Std_Http_Server_serve___redArg___lam__6(v___x_2273_, v_x_2274_);
    return v_res_2276_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__7(
    mut v___f_2277_: *mut leanh::LeanObject,
    mut v___y_2278_: *mut leanh::LeanObject,
    mut v_x_2279_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_2281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2284_: u8 = 0;
    let mut v___x_2286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2289_: u8 = 0;
    let mut v_a_2290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2279_) == 0 {
                    leanh::lean_dec_ref(v___f_2277_);
                    v_a_2281_ = leanh::lean_ctor_get(v_x_2279_, 0);
                    v_isSharedCheck_2289_ = (!leanh::lean_is_exclusive(v_x_2279_)) as u8;
                    if v_isSharedCheck_2289_ == 0 {
                        v___x_2283_ = v_x_2279_;
                        v_isShared_2284_ = v_isSharedCheck_2289_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2281_);
                        leanh::lean_dec(v_x_2279_);
                        v___x_2283_ = leanh::lean_box(0);
                        v_isShared_2284_ = v_isSharedCheck_2289_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2290_ = leanh::lean_ctor_get(v_x_2279_, 0);
                    leanh::lean_inc(v_a_2290_);
                    leanh::lean_dec_ref_known(v_x_2279_, 1);
                    leanh::lean_inc_ref(v___y_2278_);
                    v___x_2291_ = leanh::lean_apply_3(
                        v___f_2277_,
                        v_a_2290_,
                        v___y_2278_,
                        leanh::lean_box(0),
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
                    v_reuseFailAlloc_2288_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2288_, 0, v_a_2281_);
                    v___x_2286_ = v_reuseFailAlloc_2288_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2287_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2287_, 0, v___x_2286_);
                return v___x_2287_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__7___boxed(
    mut v___f_2292_: *mut leanh::LeanObject,
    mut v___y_2293_: *mut leanh::LeanObject,
    mut v_x_2294_: *mut leanh::LeanObject,
    mut v___y_2295_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2296_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2296_ = l_Std_Http_Server_serve___redArg___lam__7(v___f_2292_, v___y_2293_, v_x_2294_);
    leanh::lean_dec_ref(v___y_2293_);
    return v_res_2296_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__8(
    mut v_a_2297_: *mut leanh::LeanObject,
    mut v_x_2298_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2303_: u8 = 0;
    let mut v___x_2304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2310_: u8 = 0;
    let mut v_unused_2311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2298_) == 0 {
                    leanh::lean_dec_ref(v_a_2297_);
                    v___x_2300_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2300_, 0, v_x_2298_);
                    return v___x_2300_;
                } else {
                    v_isSharedCheck_2310_ = (!leanh::lean_is_exclusive(v_x_2298_)) as u8;
                    if v_isSharedCheck_2310_ == 0 {
                        v_unused_2311_ = leanh::lean_ctor_get(v_x_2298_, 0);
                        leanh::lean_dec(v_unused_2311_);
                        v___x_2302_ = v_x_2298_;
                        v_isShared_2303_ = v_isSharedCheck_2310_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_x_2298_);
                        v___x_2302_ = leanh::lean_box(0);
                        v_isShared_2303_ = v_isSharedCheck_2310_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2304_ = leanh::lean_box(2);
                v___x_2305_ = l_Std_CancellationContext_cancel(v_a_2297_, v___x_2304_);
                if v_isShared_2303_ == 0 {
                    leanh::lean_ctor_set(v___x_2302_, 0, v___x_2305_);
                    v___x_2307_ = v___x_2302_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2309_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2309_, 0, v___x_2305_);
                    v___x_2307_ = v_reuseFailAlloc_2309_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2308_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2308_, 0, v___x_2307_);
                return v___x_2308_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__8___boxed(
    mut v_a_2312_: *mut leanh::LeanObject,
    mut v_x_2313_: *mut leanh::LeanObject,
    mut v___y_2314_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2315_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2315_ = l_Std_Http_Server_serve___redArg___lam__8(v_a_2312_, v_x_2313_);
    return v_res_2315_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__11(
    mut v___f_2316_: *mut leanh::LeanObject,
    mut v_a_2317_: *mut leanh::LeanObject,
    mut v_x_2318_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_2318_) == 0 {
        let mut v___x_2320_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_a_2317_);
        leanh::lean_dec_ref(v___f_2316_);
        v___x_2320_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_2320_, 0, v_x_2318_);
        return v___x_2320_;
    } else {
        let mut v_a_2321_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2322_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_2321_ = leanh::lean_ctor_get(v_x_2318_, 0);
        leanh::lean_inc(v_a_2321_);
        leanh::lean_dec_ref_known(v_x_2318_, 1);
        v___x_2322_ = leanh::lean_apply_3(
            v___f_2316_,
            v_a_2321_,
            v_a_2317_,
            leanh::lean_box(0),
        );
        return v___x_2322_;
    }
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__11___boxed(
    mut v___f_2323_: *mut leanh::LeanObject,
    mut v_a_2324_: *mut leanh::LeanObject,
    mut v_x_2325_: *mut leanh::LeanObject,
    mut v___y_2326_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2327_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2327_ = l_Std_Http_Server_serve___redArg___lam__11(v___f_2323_, v_a_2324_, v_x_2325_);
    return v_res_2327_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__9(
    mut v_permitAcquired_2328_: u8,
    mut v___f_2329_: *mut leanh::LeanObject,
    mut v___x_2330_: *mut leanh::LeanObject,
    mut v_a_2331_: *mut leanh::LeanObject,
    mut v_connectionLimit_2332_: *mut leanh::LeanObject,
    mut v___x_2333_: *mut leanh::LeanObject,
    mut v___x_2334_: u8,
    mut v___f_2335_: *mut leanh::LeanObject,
    mut v_opt_2336_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2342_: u8 = 0;
    let mut v___x_2343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2349_: u8 = 0;
    let mut v___x_2350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_permitAcquired_2328_ == 0 {
                    leanh::lean_dec_ref(v___f_2335_);
                    leanh::lean_dec(v___x_2333_);
                    leanh::lean_dec(v_connectionLimit_2332_);
                    v___x_2338_ = leanh::lean_apply_3(
                        v___f_2329_,
                        v___x_2330_,
                        v_a_2331_,
                        leanh::lean_box(0),
                    );
                    return v___x_2338_;
                } else {
                    if leanh::lean_obj_tag(v_connectionLimit_2332_) == 1 {
                        leanh::lean_dec_ref(v_a_2331_);
                        leanh::lean_dec_ref(v___f_2329_);
                        v_val_2339_ = leanh::lean_ctor_get(v_connectionLimit_2332_, 0);
                        v_isSharedCheck_2349_ =
                            (!leanh::lean_is_exclusive(v_connectionLimit_2332_)) as u8;
                        if v_isSharedCheck_2349_ == 0 {
                            v___x_2341_ = v_connectionLimit_2332_;
                            v_isShared_2342_ = v_isSharedCheck_2349_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_2339_);
                            leanh::lean_dec(v_connectionLimit_2332_);
                            v___x_2341_ = leanh::lean_box(0);
                            v_isShared_2342_ = v_isSharedCheck_2349_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v___f_2335_);
                        leanh::lean_dec(v___x_2333_);
                        leanh::lean_dec(v_connectionLimit_2332_);
                        v___x_2350_ = leanh::lean_apply_3(
                            v___f_2329_,
                            v___x_2330_,
                            v_a_2331_,
                            leanh::lean_box(0),
                        );
                        return v___x_2350_;
                    }
                }
            }
            1 => {
                v___x_2343_ = l_Std_Semaphore_release(v_val_2339_);
                if v_isShared_2342_ == 0 {
                    leanh::lean_ctor_set(v___x_2341_, 0, v___x_2343_);
                    v___x_2345_ = v___x_2341_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2348_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2348_, 0, v___x_2343_);
                    v___x_2345_ = v_reuseFailAlloc_2348_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2346_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2346_, 0, v___x_2345_);
                v___x_2347_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
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
    mut v_permitAcquired_2351_: *mut leanh::LeanObject,
    mut v___f_2352_: *mut leanh::LeanObject,
    mut v___x_2353_: *mut leanh::LeanObject,
    mut v_a_2354_: *mut leanh::LeanObject,
    mut v_connectionLimit_2355_: *mut leanh::LeanObject,
    mut v___x_2356_: *mut leanh::LeanObject,
    mut v___x_2357_: *mut leanh::LeanObject,
    mut v___f_2358_: *mut leanh::LeanObject,
    mut v_opt_2359_: *mut leanh::LeanObject,
    mut v___y_2360_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_permitAcquired_boxed_2361_: u8 = 0;
    let mut v___x_13775__boxed_2362_: u8 = 0;
    let mut v_res_2363_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_permitAcquired_boxed_2361_ = (leanh::lean_unbox(v_permitAcquired_2351_) as u8);
    v___x_13775__boxed_2362_ = (leanh::lean_unbox(v___x_2357_) as u8);
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
    leanh::lean_dec(v_opt_2359_);
    return v_res_2363_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__12(
    mut v___x_2364_: *mut leanh::LeanObject,
    mut v_inst_2365_: *mut leanh::LeanObject,
    mut v_val_2366_: *mut leanh::LeanObject,
    mut v_handler_2367_: *mut leanh::LeanObject,
    mut v_config_2368_: *mut leanh::LeanObject,
    mut v_extensions_2369_: *mut leanh::LeanObject,
    mut v_a_2370_: *mut leanh::LeanObject,
    mut v___f_2371_: *mut leanh::LeanObject,
    mut v___x_2372_: *mut leanh::LeanObject,
    mut v___x_2373_: u8,
    mut v___f_2374_: *mut leanh::LeanObject,
    mut v_x_2375_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2380_: u8 = 0;
    let mut v___x_2381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2392_: u8 = 0;
    let mut v___x_2394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2396_: u8 = 0;
    let mut v_a_2397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2400_: u8 = 0;
    let mut v_fst_2401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2405_: u8 = 0;
    let mut v_a_2406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2409_: u8 = 0;
    let mut v___x_2410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2415_: u8 = 0;
    let mut v_isSharedCheck_2416_: u8 = 0;
    let mut v_unused_2417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2375_) == 0 {
                    leanh::lean_dec_ref(v___f_2374_);
                    leanh::lean_dec(v___x_2372_);
                    leanh::lean_dec_ref(v___f_2371_);
                    leanh::lean_dec_ref(v_a_2370_);
                    leanh::lean_dec(v_extensions_2369_);
                    leanh::lean_dec_ref(v_config_2368_);
                    leanh::lean_dec(v_handler_2367_);
                    leanh::lean_dec(v_val_2366_);
                    leanh::lean_dec_ref(v_inst_2365_);
                    leanh::lean_dec_ref(v___x_2364_);
                    v___x_2377_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2377_, 0, v_x_2375_);
                    return v___x_2377_;
                } else {
                    v_isSharedCheck_2416_ = (!leanh::lean_is_exclusive(v_x_2375_)) as u8;
                    if v_isSharedCheck_2416_ == 0 {
                        v_unused_2417_ = leanh::lean_ctor_get(v_x_2375_, 0);
                        leanh::lean_dec(v_unused_2417_);
                        v___x_2379_ = v_x_2375_;
                        v_isShared_2380_ = v_isSharedCheck_2416_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_x_2375_);
                        v___x_2379_ = leanh::lean_box(0);
                        v_isShared_2380_ = v_isSharedCheck_2416_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2381_ = leanh::lean_alloc_closure(
                    l_Std_Http_Server_serveConnection___boxed as *mut core::ffi::c_void,
                    10,
                    9,
                );
                leanh::lean_closure_set(v___x_2381_, 0, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_2381_, 1, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_2381_, 2, v___x_2364_);
                leanh::lean_closure_set(v___x_2381_, 3, v_inst_2365_);
                leanh::lean_closure_set(v___x_2381_, 4, v_val_2366_);
                leanh::lean_closure_set(v___x_2381_, 5, v_handler_2367_);
                leanh::lean_closure_set(v___x_2381_, 6, v_config_2368_);
                leanh::lean_closure_set(v___x_2381_, 7, v_extensions_2369_);
                leanh::lean_closure_set(v___x_2381_, 8, v_a_2370_);
                leanh::lean_inc(v___x_2372_);
                v___x_2382_ = l_Std_Async_EAsync_tryFinally_x27___redArg(
                    v___x_2381_,
                    v___f_2371_,
                    v___x_2372_,
                    v___x_2373_,
                );
                if leanh::lean_obj_tag(v___x_2382_) == 0 {
                    leanh::lean_dec_ref(v___f_2374_);
                    leanh::lean_dec(v___x_2372_);
                    v_a_2388_ = leanh::lean_ctor_get(v___x_2382_, 0);
                    leanh::lean_inc(v_a_2388_);
                    leanh::lean_dec_ref_known(v___x_2382_, 1);
                    if leanh::lean_obj_tag(v_a_2388_) == 0 {
                        v_a_2389_ = leanh::lean_ctor_get(v_a_2388_, 0);
                        v_isSharedCheck_2396_ = (!leanh::lean_is_exclusive(v_a_2388_)) as u8;
                        if v_isSharedCheck_2396_ == 0 {
                            v___x_2391_ = v_a_2388_;
                            v_isShared_2392_ = v_isSharedCheck_2396_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2389_);
                            leanh::lean_dec(v_a_2388_);
                            v___x_2391_ = leanh::lean_box(0);
                            v_isShared_2392_ = v_isSharedCheck_2396_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v_a_2397_ = leanh::lean_ctor_get(v_a_2388_, 0);
                        v_isSharedCheck_2405_ = (!leanh::lean_is_exclusive(v_a_2388_)) as u8;
                        if v_isSharedCheck_2405_ == 0 {
                            v___x_2399_ = v_a_2388_;
                            v_isShared_2400_ = v_isSharedCheck_2405_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2397_);
                            leanh::lean_dec(v_a_2388_);
                            v___x_2399_ = leanh::lean_box(0);
                            v_isShared_2400_ = v_isSharedCheck_2405_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_2379_);
                    v_a_2406_ = leanh::lean_ctor_get(v___x_2382_, 0);
                    v_isSharedCheck_2415_ = (!leanh::lean_is_exclusive(v___x_2382_)) as u8;
                    if v_isSharedCheck_2415_ == 0 {
                        v___x_2408_ = v___x_2382_;
                        v_isShared_2409_ = v_isSharedCheck_2415_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2406_);
                        leanh::lean_dec(v___x_2382_);
                        v___x_2408_ = leanh::lean_box(0);
                        v_isShared_2409_ = v_isSharedCheck_2415_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2380_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2379_, 0);
                    leanh::lean_ctor_set(v___x_2379_, 0, v___y_2384_);
                    v___x_2386_ = v___x_2379_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2387_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2387_, 0, v___y_2384_);
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
                    v_reuseFailAlloc_2395_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2395_, 0, v_a_2389_);
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
                v_fst_2401_ = leanh::lean_ctor_get(v_a_2397_, 0);
                leanh::lean_inc(v_fst_2401_);
                leanh::lean_dec(v_a_2397_);
                if v_isShared_2400_ == 0 {
                    leanh::lean_ctor_set(v___x_2399_, 0, v_fst_2401_);
                    v___x_2403_ = v___x_2399_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2404_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2404_, 0, v_fst_2401_);
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
                    leanh::lean_alloc_closure(l_Except_map as *mut core::ffi::c_void, 5, 4);
                leanh::lean_closure_set(v___x_2410_, 0, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_2410_, 1, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_2410_, 2, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_2410_, 3, v___f_2374_);
                v___x_2411_ = lean_task_map(v___x_2410_, v_a_2406_, v___x_2372_, v___x_2373_);
                if v_isShared_2409_ == 0 {
                    leanh::lean_ctor_set(v___x_2408_, 0, v___x_2411_);
                    v___x_2413_ = v___x_2408_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2414_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2414_, 0, v___x_2411_);
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
    mut v___x_2418_: *mut leanh::LeanObject,
    mut v_inst_2419_: *mut leanh::LeanObject,
    mut v_val_2420_: *mut leanh::LeanObject,
    mut v_handler_2421_: *mut leanh::LeanObject,
    mut v_config_2422_: *mut leanh::LeanObject,
    mut v_extensions_2423_: *mut leanh::LeanObject,
    mut v_a_2424_: *mut leanh::LeanObject,
    mut v___f_2425_: *mut leanh::LeanObject,
    mut v___x_2426_: *mut leanh::LeanObject,
    mut v___x_2427_: *mut leanh::LeanObject,
    mut v___f_2428_: *mut leanh::LeanObject,
    mut v_x_2429_: *mut leanh::LeanObject,
    mut v___y_2430_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_13824__boxed_2431_: u8 = 0;
    let mut v_res_2432_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_13824__boxed_2431_ = (leanh::lean_unbox(v___x_2427_) as u8);
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
    mut v___x_2433_: *mut leanh::LeanObject,
    mut v_activeConnections_2434_: *mut leanh::LeanObject,
    mut v___f_2435_: *mut leanh::LeanObject,
    mut v_a_2436_: *mut leanh::LeanObject,
    mut v___f_2437_: *mut leanh::LeanObject,
    mut v___f_2438_: *mut leanh::LeanObject,
    mut v_permitAcquired_2439_: u8,
    mut v___x_2440_: *mut leanh::LeanObject,
    mut v_connectionLimit_2441_: *mut leanh::LeanObject,
    mut v___x_2442_: *mut leanh::LeanObject,
    mut v___x_2443_: u8,
    mut v___x_2444_: *mut leanh::LeanObject,
    mut v_inst_2445_: *mut leanh::LeanObject,
    mut v_val_2446_: *mut leanh::LeanObject,
    mut v_handler_2447_: *mut leanh::LeanObject,
    mut v_config_2448_: *mut leanh::LeanObject,
    mut v_extensions_2449_: *mut leanh::LeanObject,
    mut v___f_2450_: *mut leanh::LeanObject,
    mut v___f_2451_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_12955__overap_2455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2453_ =
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__3;
    v___f_2454_ =
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__4;
    leanh::lean_inc_ref(v_activeConnections_2434_);
    leanh::lean_inc_ref(v___x_2433_);
    v___x_12955__overap_2455_ = l_Std_Mutex_atomically___redArg(
        v___x_2433_,
        v___f_2453_,
        v___f_2454_,
        v_activeConnections_2434_,
        v___f_2435_,
    );
    leanh::lean_inc_ref_n(v_a_2436_, 3);
    v___x_2456_ = leanh::lean_apply_2(
        v___x_12955__overap_2455_,
        v_a_2436_,
        leanh::lean_box(0),
    );
    v___f_2457_ = leanh::lean_alloc_closure(
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__6___boxed
            as *mut core::ffi::c_void,
        9,
        6,
    );
    leanh::lean_closure_set(v___f_2457_, 0, v___x_2433_);
    leanh::lean_closure_set(v___f_2457_, 1, v___f_2437_);
    leanh::lean_closure_set(v___f_2457_, 2, v___f_2438_);
    leanh::lean_closure_set(v___f_2457_, 3, v___f_2453_);
    leanh::lean_closure_set(v___f_2457_, 4, v___f_2454_);
    leanh::lean_closure_set(v___f_2457_, 5, v_activeConnections_2434_);
    leanh::lean_inc_ref(v___f_2457_);
    v___f_2458_ = leanh::lean_alloc_closure(
        l_Std_Http_Server_serve___redArg___lam__11___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_2458_, 0, v___f_2457_);
    leanh::lean_closure_set(v___f_2458_, 1, v_a_2436_);
    v___x_2459_ = leanh::lean_box((v_permitAcquired_2439_) as usize);
    v___x_2460_ = leanh::lean_box((v___x_2443_) as usize);
    leanh::lean_inc_n(v___x_2442_, 3);
    v___f_2461_ = leanh::lean_alloc_closure(
        l_Std_Http_Server_serve___redArg___lam__9___boxed as *mut core::ffi::c_void,
        10,
        8,
    );
    leanh::lean_closure_set(v___f_2461_, 0, v___x_2459_);
    leanh::lean_closure_set(v___f_2461_, 1, v___f_2457_);
    leanh::lean_closure_set(v___f_2461_, 2, v___x_2440_);
    leanh::lean_closure_set(v___f_2461_, 3, v_a_2436_);
    leanh::lean_closure_set(v___f_2461_, 4, v_connectionLimit_2441_);
    leanh::lean_closure_set(v___f_2461_, 5, v___x_2442_);
    leanh::lean_closure_set(v___f_2461_, 6, v___x_2460_);
    leanh::lean_closure_set(v___f_2461_, 7, v___f_2458_);
    v___x_2462_ = leanh::lean_box((v___x_2443_) as usize);
    v___f_2463_ = leanh::lean_alloc_closure(
        l_Std_Http_Server_serve___redArg___lam__12___boxed as *mut core::ffi::c_void,
        13,
        11,
    );
    leanh::lean_closure_set(v___f_2463_, 0, v___x_2444_);
    leanh::lean_closure_set(v___f_2463_, 1, v_inst_2445_);
    leanh::lean_closure_set(v___f_2463_, 2, v_val_2446_);
    leanh::lean_closure_set(v___f_2463_, 3, v_handler_2447_);
    leanh::lean_closure_set(v___f_2463_, 4, v_config_2448_);
    leanh::lean_closure_set(v___f_2463_, 5, v_extensions_2449_);
    leanh::lean_closure_set(v___f_2463_, 6, v_a_2436_);
    leanh::lean_closure_set(v___f_2463_, 7, v___f_2461_);
    leanh::lean_closure_set(v___f_2463_, 8, v___x_2442_);
    leanh::lean_closure_set(v___f_2463_, 9, v___x_2462_);
    leanh::lean_closure_set(v___f_2463_, 10, v___f_2450_);
    v___x_2464_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2442_,
        v___x_2443_,
        v___x_2456_,
        v___f_2463_,
    );
    v___x_2465_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2442_,
        v___x_2443_,
        v___x_2464_,
        v___f_2451_,
    );
    return v___x_2465_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__13___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2466_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_activeConnections_2467_: *mut leanh::LeanObject = *_args.add(1);
    let mut v___f_2468_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_a_2469_: *mut leanh::LeanObject = *_args.add(3);
    let mut v___f_2470_: *mut leanh::LeanObject = *_args.add(4);
    let mut v___f_2471_: *mut leanh::LeanObject = *_args.add(5);
    let mut v_permitAcquired_2472_: *mut leanh::LeanObject = *_args.add(6);
    let mut v___x_2473_: *mut leanh::LeanObject = *_args.add(7);
    let mut v_connectionLimit_2474_: *mut leanh::LeanObject = *_args.add(8);
    let mut v___x_2475_: *mut leanh::LeanObject = *_args.add(9);
    let mut v___x_2476_: *mut leanh::LeanObject = *_args.add(10);
    let mut v___x_2477_: *mut leanh::LeanObject = *_args.add(11);
    let mut v_inst_2478_: *mut leanh::LeanObject = *_args.add(12);
    let mut v_val_2479_: *mut leanh::LeanObject = *_args.add(13);
    let mut v_handler_2480_: *mut leanh::LeanObject = *_args.add(14);
    let mut v_config_2481_: *mut leanh::LeanObject = *_args.add(15);
    let mut v_extensions_2482_: *mut leanh::LeanObject = *_args.add(16);
    let mut v___f_2483_: *mut leanh::LeanObject = *_args.add(17);
    let mut v___f_2484_: *mut leanh::LeanObject = *_args.add(18);
    let mut v___y_2485_: *mut leanh::LeanObject = *_args.add(19);
    let mut v_permitAcquired_boxed_2486_: u8 = 0;
    let mut v___x_13943__boxed_2487_: u8 = 0;
    let mut v_res_2488_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_permitAcquired_boxed_2486_ = (leanh::lean_unbox(v_permitAcquired_2472_) as u8);
    v___x_13943__boxed_2487_ = (leanh::lean_unbox(v___x_2476_) as u8);
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
    mut v___x_2489_: *mut leanh::LeanObject,
    mut v_activeConnections_2490_: *mut leanh::LeanObject,
    mut v___f_2491_: *mut leanh::LeanObject,
    mut v___f_2492_: *mut leanh::LeanObject,
    mut v___f_2493_: *mut leanh::LeanObject,
    mut v_permitAcquired_2494_: u8,
    mut v___x_2495_: *mut leanh::LeanObject,
    mut v_connectionLimit_2496_: *mut leanh::LeanObject,
    mut v___x_2497_: *mut leanh::LeanObject,
    mut v___x_2498_: u8,
    mut v___x_2499_: *mut leanh::LeanObject,
    mut v_inst_2500_: *mut leanh::LeanObject,
    mut v_val_2501_: *mut leanh::LeanObject,
    mut v_handler_2502_: *mut leanh::LeanObject,
    mut v_config_2503_: *mut leanh::LeanObject,
    mut v_extensions_2504_: *mut leanh::LeanObject,
    mut v___f_2505_: *mut leanh::LeanObject,
    mut v_x_2506_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_2508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2511_: u8 = 0;
    let mut v___x_2513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2516_: u8 = 0;
    let mut v_a_2517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2520_: u8 = 0;
    let mut v___f_2521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2531_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2506_) == 0 {
                    leanh::lean_dec_ref(v___f_2505_);
                    leanh::lean_dec(v_extensions_2504_);
                    leanh::lean_dec_ref(v_config_2503_);
                    leanh::lean_dec(v_handler_2502_);
                    leanh::lean_dec(v_val_2501_);
                    leanh::lean_dec_ref(v_inst_2500_);
                    leanh::lean_dec_ref(v___x_2499_);
                    leanh::lean_dec(v___x_2497_);
                    leanh::lean_dec(v_connectionLimit_2496_);
                    leanh::lean_dec_ref(v___f_2493_);
                    leanh::lean_dec_ref(v___f_2492_);
                    leanh::lean_dec_ref(v___f_2491_);
                    leanh::lean_dec_ref(v_activeConnections_2490_);
                    leanh::lean_dec_ref(v___x_2489_);
                    v_a_2508_ = leanh::lean_ctor_get(v_x_2506_, 0);
                    v_isSharedCheck_2516_ = (!leanh::lean_is_exclusive(v_x_2506_)) as u8;
                    if v_isSharedCheck_2516_ == 0 {
                        v___x_2510_ = v_x_2506_;
                        v_isShared_2511_ = v_isSharedCheck_2516_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2508_);
                        leanh::lean_dec(v_x_2506_);
                        v___x_2510_ = leanh::lean_box(0);
                        v_isShared_2511_ = v_isSharedCheck_2516_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2517_ = leanh::lean_ctor_get(v_x_2506_, 0);
                    v_isSharedCheck_2531_ = (!leanh::lean_is_exclusive(v_x_2506_)) as u8;
                    if v_isSharedCheck_2531_ == 0 {
                        v___x_2519_ = v_x_2506_;
                        v_isShared_2520_ = v_isSharedCheck_2531_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2517_);
                        leanh::lean_dec(v_x_2506_);
                        v___x_2519_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2515_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2515_, 0, v_a_2508_);
                    v___x_2513_ = v_reuseFailAlloc_2515_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2514_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2514_, 0, v___x_2513_);
                return v___x_2514_;
            }
            3 => {
                leanh::lean_inc(v_a_2517_);
                v___f_2521_ = leanh::lean_alloc_closure(
                    l_Std_Http_Server_serve___redArg___lam__8___boxed as *mut core::ffi::c_void,
                    3,
                    1,
                );
                leanh::lean_closure_set(v___f_2521_, 0, v_a_2517_);
                v___x_2522_ = leanh::lean_box((v_permitAcquired_2494_) as usize);
                v___x_2523_ = leanh::lean_box((v___x_2498_) as usize);
                leanh::lean_inc(v___x_2497_);
                v___f_2524_ = leanh::lean_alloc_closure(
                    l_Std_Http_Server_serve___redArg___lam__13___boxed as *mut core::ffi::c_void,
                    20,
                    19,
                );
                leanh::lean_closure_set(v___f_2524_, 0, v___x_2489_);
                leanh::lean_closure_set(v___f_2524_, 1, v_activeConnections_2490_);
                leanh::lean_closure_set(v___f_2524_, 2, v___f_2491_);
                leanh::lean_closure_set(v___f_2524_, 3, v_a_2517_);
                leanh::lean_closure_set(v___f_2524_, 4, v___f_2492_);
                leanh::lean_closure_set(v___f_2524_, 5, v___f_2493_);
                leanh::lean_closure_set(v___f_2524_, 6, v___x_2522_);
                leanh::lean_closure_set(v___f_2524_, 7, v___x_2495_);
                leanh::lean_closure_set(v___f_2524_, 8, v_connectionLimit_2496_);
                leanh::lean_closure_set(v___f_2524_, 9, v___x_2497_);
                leanh::lean_closure_set(v___f_2524_, 10, v___x_2523_);
                leanh::lean_closure_set(v___f_2524_, 11, v___x_2499_);
                leanh::lean_closure_set(v___f_2524_, 12, v_inst_2500_);
                leanh::lean_closure_set(v___f_2524_, 13, v_val_2501_);
                leanh::lean_closure_set(v___f_2524_, 14, v_handler_2502_);
                leanh::lean_closure_set(v___f_2524_, 15, v_config_2503_);
                leanh::lean_closure_set(v___f_2524_, 16, v_extensions_2504_);
                leanh::lean_closure_set(v___f_2524_, 17, v___f_2505_);
                leanh::lean_closure_set(v___f_2524_, 18, v___f_2521_);
                v___x_2525_ = leanh::lean_alloc_closure(
                    l_Std_Async_BaseAsync_toRawBaseIO___boxed as *mut core::ffi::c_void,
                    3,
                    2,
                );
                leanh::lean_closure_set(v___x_2525_, 0, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_2525_, 1, v___f_2524_);
                v___x_2526_ = lean_io_as_task(v___x_2525_, v___x_2497_);
                leanh::lean_dec_ref(v___x_2526_);
                if v_isShared_2520_ == 0 {
                    leanh::lean_ctor_set(v___x_2519_, 0, v___x_2495_);
                    v___x_2528_ = v___x_2519_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2530_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2530_, 0, v___x_2495_);
                    v___x_2528_ = v_reuseFailAlloc_2530_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2529_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2529_, 0, v___x_2528_);
                return v___x_2529_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__14___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2532_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_activeConnections_2533_: *mut leanh::LeanObject = *_args.add(1);
    let mut v___f_2534_: *mut leanh::LeanObject = *_args.add(2);
    let mut v___f_2535_: *mut leanh::LeanObject = *_args.add(3);
    let mut v___f_2536_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_permitAcquired_2537_: *mut leanh::LeanObject = *_args.add(5);
    let mut v___x_2538_: *mut leanh::LeanObject = *_args.add(6);
    let mut v_connectionLimit_2539_: *mut leanh::LeanObject = *_args.add(7);
    let mut v___x_2540_: *mut leanh::LeanObject = *_args.add(8);
    let mut v___x_2541_: *mut leanh::LeanObject = *_args.add(9);
    let mut v___x_2542_: *mut leanh::LeanObject = *_args.add(10);
    let mut v_inst_2543_: *mut leanh::LeanObject = *_args.add(11);
    let mut v_val_2544_: *mut leanh::LeanObject = *_args.add(12);
    let mut v_handler_2545_: *mut leanh::LeanObject = *_args.add(13);
    let mut v_config_2546_: *mut leanh::LeanObject = *_args.add(14);
    let mut v_extensions_2547_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___f_2548_: *mut leanh::LeanObject = *_args.add(16);
    let mut v_x_2549_: *mut leanh::LeanObject = *_args.add(17);
    let mut v___y_2550_: *mut leanh::LeanObject = *_args.add(18);
    let mut v_permitAcquired_boxed_2551_: u8 = 0;
    let mut v___x_14010__boxed_2552_: u8 = 0;
    let mut v_res_2553_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_permitAcquired_boxed_2551_ = (leanh::lean_unbox(v_permitAcquired_2537_) as u8);
    v___x_14010__boxed_2552_ = (leanh::lean_unbox(v___x_2541_) as u8);
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
    mut v___x_2554_: *mut leanh::LeanObject,
    mut v___x_2555_: u8,
    mut v___f_2556_: *mut leanh::LeanObject,
    mut v_x_2557_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_2559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2562_: u8 = 0;
    let mut v___x_2564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2567_: u8 = 0;
    let mut v_a_2568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2571_: u8 = 0;
    let mut v___x_2572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2578_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2557_) == 0 {
                    leanh::lean_dec_ref(v___f_2556_);
                    leanh::lean_dec(v___x_2554_);
                    v_a_2559_ = leanh::lean_ctor_get(v_x_2557_, 0);
                    v_isSharedCheck_2567_ = (!leanh::lean_is_exclusive(v_x_2557_)) as u8;
                    if v_isSharedCheck_2567_ == 0 {
                        v___x_2561_ = v_x_2557_;
                        v_isShared_2562_ = v_isSharedCheck_2567_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2559_);
                        leanh::lean_dec(v_x_2557_);
                        v___x_2561_ = leanh::lean_box(0);
                        v_isShared_2562_ = v_isSharedCheck_2567_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2568_ = leanh::lean_ctor_get(v_x_2557_, 0);
                    v_isSharedCheck_2578_ = (!leanh::lean_is_exclusive(v_x_2557_)) as u8;
                    if v_isSharedCheck_2578_ == 0 {
                        v___x_2570_ = v_x_2557_;
                        v_isShared_2571_ = v_isSharedCheck_2578_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2568_);
                        leanh::lean_dec(v_x_2557_);
                        v___x_2570_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2566_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2566_, 0, v_a_2559_);
                    v___x_2564_ = v_reuseFailAlloc_2566_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2565_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2565_, 0, v___x_2564_);
                return v___x_2565_;
            }
            3 => {
                v___x_2572_ = l_Std_CancellationContext_fork(v_a_2568_);
                if v_isShared_2571_ == 0 {
                    leanh::lean_ctor_set(v___x_2570_, 0, v___x_2572_);
                    v___x_2574_ = v___x_2570_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2577_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2577_, 0, v___x_2572_);
                    v___x_2574_ = v_reuseFailAlloc_2577_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2575_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2575_, 0, v___x_2574_);
                v___x_2576_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
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
    mut v___x_2579_: *mut leanh::LeanObject,
    mut v___x_2580_: *mut leanh::LeanObject,
    mut v___f_2581_: *mut leanh::LeanObject,
    mut v_x_2582_: *mut leanh::LeanObject,
    mut v___y_2583_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_14092__boxed_2584_: u8 = 0;
    let mut v_res_2585_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_14092__boxed_2584_ = (leanh::lean_unbox(v___x_2580_) as u8);
    v_res_2585_ = l_Std_Http_Server_serve___redArg___lam__15(
        v___x_2579_,
        v___x_14092__boxed_2584_,
        v___f_2581_,
        v_x_2582_,
    );
    return v_res_2585_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__16(
    mut v___x_2586_: *mut leanh::LeanObject,
    mut v_activeConnections_2587_: *mut leanh::LeanObject,
    mut v___f_2588_: *mut leanh::LeanObject,
    mut v___f_2589_: *mut leanh::LeanObject,
    mut v___f_2590_: *mut leanh::LeanObject,
    mut v_permitAcquired_2591_: u8,
    mut v___x_2592_: *mut leanh::LeanObject,
    mut v_connectionLimit_2593_: *mut leanh::LeanObject,
    mut v___x_2594_: u8,
    mut v_inst_2595_: *mut leanh::LeanObject,
    mut v_val_2596_: *mut leanh::LeanObject,
    mut v_handler_2597_: *mut leanh::LeanObject,
    mut v_config_2598_: *mut leanh::LeanObject,
    mut v___f_2599_: *mut leanh::LeanObject,
    mut v___f_2600_: *mut leanh::LeanObject,
    mut v_extensions_2601_: *mut leanh::LeanObject,
    mut v___y_2602_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2604_ = l_Std_Http_instTransportClient;
    v___x_2605_ = leanh::lean_unsigned_to_nat(0);
    v___x_2606_ = leanh::lean_box((v_permitAcquired_2591_) as usize);
    v___x_2607_ = leanh::lean_box((v___x_2594_) as usize);
    v___f_2608_ = leanh::lean_alloc_closure(
        l_Std_Http_Server_serve___redArg___lam__14___boxed as *mut core::ffi::c_void,
        19,
        17,
    );
    leanh::lean_closure_set(v___f_2608_, 0, v___x_2586_);
    leanh::lean_closure_set(v___f_2608_, 1, v_activeConnections_2587_);
    leanh::lean_closure_set(v___f_2608_, 2, v___f_2588_);
    leanh::lean_closure_set(v___f_2608_, 3, v___f_2589_);
    leanh::lean_closure_set(v___f_2608_, 4, v___f_2590_);
    leanh::lean_closure_set(v___f_2608_, 5, v___x_2606_);
    leanh::lean_closure_set(v___f_2608_, 6, v___x_2592_);
    leanh::lean_closure_set(v___f_2608_, 7, v_connectionLimit_2593_);
    leanh::lean_closure_set(v___f_2608_, 8, v___x_2605_);
    leanh::lean_closure_set(v___f_2608_, 9, v___x_2607_);
    leanh::lean_closure_set(v___f_2608_, 10, v___x_2604_);
    leanh::lean_closure_set(v___f_2608_, 11, v_inst_2595_);
    leanh::lean_closure_set(v___f_2608_, 12, v_val_2596_);
    leanh::lean_closure_set(v___f_2608_, 13, v_handler_2597_);
    leanh::lean_closure_set(v___f_2608_, 14, v_config_2598_);
    leanh::lean_closure_set(v___f_2608_, 15, v_extensions_2601_);
    leanh::lean_closure_set(v___f_2608_, 16, v___f_2599_);
    v___x_2609_ = leanh::lean_box((v___x_2594_) as usize);
    v___f_2610_ = leanh::lean_alloc_closure(
        l_Std_Http_Server_serve___redArg___lam__15___boxed as *mut core::ffi::c_void,
        5,
        3,
    );
    leanh::lean_closure_set(v___f_2610_, 0, v___x_2605_);
    leanh::lean_closure_set(v___f_2610_, 1, v___x_2609_);
    leanh::lean_closure_set(v___f_2610_, 2, v___f_2608_);
    leanh::lean_inc_ref(v___y_2602_);
    v___x_2611_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2611_, 0, v___y_2602_);
    v___x_2612_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2612_, 0, v___x_2611_);
    v___x_2613_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2605_,
        v___x_2594_,
        v___x_2612_,
        v___f_2610_,
    );
    v___x_2614_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2605_,
        v___x_2594_,
        v___x_2613_,
        v___f_2600_,
    );
    return v___x_2614_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__16___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2615_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_activeConnections_2616_: *mut leanh::LeanObject = *_args.add(1);
    let mut v___f_2617_: *mut leanh::LeanObject = *_args.add(2);
    let mut v___f_2618_: *mut leanh::LeanObject = *_args.add(3);
    let mut v___f_2619_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_permitAcquired_2620_: *mut leanh::LeanObject = *_args.add(5);
    let mut v___x_2621_: *mut leanh::LeanObject = *_args.add(6);
    let mut v_connectionLimit_2622_: *mut leanh::LeanObject = *_args.add(7);
    let mut v___x_2623_: *mut leanh::LeanObject = *_args.add(8);
    let mut v_inst_2624_: *mut leanh::LeanObject = *_args.add(9);
    let mut v_val_2625_: *mut leanh::LeanObject = *_args.add(10);
    let mut v_handler_2626_: *mut leanh::LeanObject = *_args.add(11);
    let mut v_config_2627_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___f_2628_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___f_2629_: *mut leanh::LeanObject = *_args.add(14);
    let mut v_extensions_2630_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_2631_: *mut leanh::LeanObject = *_args.add(16);
    let mut v___y_2632_: *mut leanh::LeanObject = *_args.add(17);
    let mut v_permitAcquired_boxed_2633_: u8 = 0;
    let mut v___x_14151__boxed_2634_: u8 = 0;
    let mut v_res_2635_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_permitAcquired_boxed_2633_ = (leanh::lean_unbox(v_permitAcquired_2620_) as u8);
    v___x_14151__boxed_2634_ = (leanh::lean_unbox(v___x_2623_) as u8);
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
    leanh::lean_dec_ref(v___y_2631_);
    return v_res_2635_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__17(
    mut v___f_2636_: *mut leanh::LeanObject,
    mut v___y_2637_: *mut leanh::LeanObject,
    mut v_x_2638_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_2640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2643_: u8 = 0;
    let mut v___x_2645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2648_: u8 = 0;
    let mut v_a_2649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2638_) == 0 {
                    leanh::lean_dec_ref(v___f_2636_);
                    v_a_2640_ = leanh::lean_ctor_get(v_x_2638_, 0);
                    v_isSharedCheck_2648_ = (!leanh::lean_is_exclusive(v_x_2638_)) as u8;
                    if v_isSharedCheck_2648_ == 0 {
                        v___x_2642_ = v_x_2638_;
                        v_isShared_2643_ = v_isSharedCheck_2648_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2640_);
                        leanh::lean_dec(v_x_2638_);
                        v___x_2642_ = leanh::lean_box(0);
                        v_isShared_2643_ = v_isSharedCheck_2648_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2649_ = leanh::lean_ctor_get(v_x_2638_, 0);
                    leanh::lean_inc(v_a_2649_);
                    leanh::lean_dec_ref_known(v_x_2638_, 1);
                    leanh::lean_inc_ref(v___y_2637_);
                    v___x_2650_ = leanh::lean_apply_3(
                        v___f_2636_,
                        v_a_2649_,
                        v___y_2637_,
                        leanh::lean_box(0),
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
                    v_reuseFailAlloc_2647_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2647_, 0, v_a_2640_);
                    v___x_2645_ = v_reuseFailAlloc_2647_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2646_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2646_, 0, v___x_2645_);
                return v___x_2646_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__17___boxed(
    mut v___f_2651_: *mut leanh::LeanObject,
    mut v___y_2652_: *mut leanh::LeanObject,
    mut v_x_2653_: *mut leanh::LeanObject,
    mut v___y_2654_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2655_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2655_ = l_Std_Http_Server_serve___redArg___lam__17(v___f_2651_, v___y_2652_, v_x_2653_);
    leanh::lean_dec_ref(v___y_2652_);
    return v_res_2655_;
}
pub unsafe fn _init_l_Std_Http_Server_serve___redArg___lam__19___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2657_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2656_ = l_Std_Http_Extensions_empty;
    v___x_2657_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2657_, 0, v___x_2656_);
    return v___x_2657_;
}
pub unsafe fn _init_l_Std_Http_Server_serve___redArg___lam__19___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2658_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Server_serve___redArg___lam__19___closed__0),
        core::ptr::addr_of_mut!(l_Std_Http_Server_serve___redArg___lam__19___closed__0_once),
        _init_l_Std_Http_Server_serve___redArg___lam__19___closed__0,
    );
    v___x_2659_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2659_, 0, v___x_2658_);
    return v___x_2659_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__19(
    mut v___x_2661_: u8,
    mut v___f_2662_: *mut leanh::LeanObject,
    mut v___f_2663_: *mut leanh::LeanObject,
    mut v_x_2664_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_2666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2669_: u8 = 0;
    let mut v___x_2671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2674_: u8 = 0;
    let mut v_a_2675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2682_: u8 = 0;
    let mut v___x_2683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dyn_2685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2695_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2664_) == 0 {
                    leanh::lean_dec_ref(v___f_2663_);
                    leanh::lean_dec_ref(v___f_2662_);
                    v_a_2666_ = leanh::lean_ctor_get(v_x_2664_, 0);
                    v_isSharedCheck_2674_ = (!leanh::lean_is_exclusive(v_x_2664_)) as u8;
                    if v_isSharedCheck_2674_ == 0 {
                        v___x_2668_ = v_x_2664_;
                        v_isShared_2669_ = v_isSharedCheck_2674_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2666_);
                        leanh::lean_dec(v_x_2664_);
                        v___x_2668_ = leanh::lean_box(0);
                        v_isShared_2669_ = v_isSharedCheck_2674_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2675_ = leanh::lean_ctor_get(v_x_2664_, 0);
                    leanh::lean_inc(v_a_2675_);
                    leanh::lean_dec_ref_known(v_x_2664_, 1);
                    if leanh::lean_obj_tag(v_a_2675_) == 0 {
                        leanh::lean_dec_ref_known(v_a_2675_, 1);
                        leanh::lean_dec_ref(v___f_2663_);
                        v___x_2676_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Server_serve___redArg___lam__19___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Server_serve___redArg___lam__19___closed__1_once
                            ),
                            _init_l_Std_Http_Server_serve___redArg___lam__19___closed__1,
                        );
                        v___x_2677_ = leanh::lean_unsigned_to_nat(0);
                        v___x_2678_ =
                            l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                                leanh::lean_box(0),
                                leanh::lean_box(0),
                                v___x_2677_,
                                v___x_2661_,
                                v___x_2676_,
                                v___f_2662_,
                            );
                        return v___x_2678_;
                    } else {
                        leanh::lean_dec_ref(v___f_2662_);
                        v_a_2679_ = leanh::lean_ctor_get(v_a_2675_, 0);
                        v_isSharedCheck_2695_ = (!leanh::lean_is_exclusive(v_a_2675_)) as u8;
                        if v_isSharedCheck_2695_ == 0 {
                            v___x_2681_ = v_a_2675_;
                            v_isShared_2682_ = v_isSharedCheck_2695_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2679_);
                            leanh::lean_dec(v_a_2675_);
                            v___x_2681_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2673_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2673_, 0, v_a_2666_);
                    v___x_2671_ = v_reuseFailAlloc_2673_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2672_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2672_, 0, v___x_2671_);
                return v___x_2672_;
            }
            3 => {
                v___x_2683_ = l_Std_Http_Extensions_empty;
                v___x_2684_ = l_Std_Http_Server_instImpl_00___x40_Std_Http_Server_Connection_3058719504____hygCtx___hyg_8_;
                v_dyn_2685_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v_dyn_2685_, 0, v___x_2684_);
                leanh::lean_ctor_set(v_dyn_2685_, 1, v_a_2679_);
                v___x_2686_ = l_Std_Http_Server_serve___redArg___lam__19___closed__2;
                v___x_2687_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_dyn_2685_);
                v___x_2688_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
                    v___x_2686_,
                    v___x_2687_,
                    v_dyn_2685_,
                    v___x_2683_,
                );
                if v_isShared_2682_ == 0 {
                    leanh::lean_ctor_set(v___x_2681_, 0, v___x_2688_);
                    v___x_2690_ = v___x_2681_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2694_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2694_, 0, v___x_2688_);
                    v___x_2690_ = v_reuseFailAlloc_2694_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2691_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2691_, 0, v___x_2690_);
                v___x_2692_ = leanh::lean_unsigned_to_nat(0);
                v___x_2693_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
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
    mut v___x_2696_: *mut leanh::LeanObject,
    mut v___f_2697_: *mut leanh::LeanObject,
    mut v___f_2698_: *mut leanh::LeanObject,
    mut v_x_2699_: *mut leanh::LeanObject,
    mut v___y_2700_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_14248__boxed_2701_: u8 = 0;
    let mut v_res_2702_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_14248__boxed_2701_ = (leanh::lean_unbox(v___x_2696_) as u8);
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
    mut v___f_2704_: *mut leanh::LeanObject,
    mut v___x_2705_: *mut leanh::LeanObject,
    mut v___y_2706_: *mut leanh::LeanObject,
    mut v_connectionLimit_2707_: *mut leanh::LeanObject,
    mut v___x_2708_: u8,
    mut v___f_2709_: *mut leanh::LeanObject,
    mut v___x_2710_: *mut leanh::LeanObject,
    mut v_activeConnections_2711_: *mut leanh::LeanObject,
    mut v___f_2712_: *mut leanh::LeanObject,
    mut v___f_2713_: *mut leanh::LeanObject,
    mut v___f_2714_: *mut leanh::LeanObject,
    mut v_inst_2715_: *mut leanh::LeanObject,
    mut v_handler_2716_: *mut leanh::LeanObject,
    mut v_config_2717_: *mut leanh::LeanObject,
    mut v___f_2718_: *mut leanh::LeanObject,
    mut v___f_2719_: *mut leanh::LeanObject,
    mut v_x_2720_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_2722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2725_: u8 = 0;
    let mut v___x_2727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2730_: u8 = 0;
    let mut v_a_2731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2734_: u8 = 0;
    let mut v___x_2735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2739_: u8 = 0;
    let mut v___x_2740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2749_: u8 = 0;
    let mut v___x_2750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2754_: u8 = 0;
    let mut v___x_2755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2775_: u8 = 0;
    let mut v___x_2777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2779_: u8 = 0;
    let mut v_a_2780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2783_: u8 = 0;
    let mut v___x_2785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2787_: u8 = 0;
    let mut v_isSharedCheck_2788_: u8 = 0;
    let mut v_isSharedCheck_2789_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2720_) == 0 {
                    leanh::lean_dec_ref(v___f_2719_);
                    leanh::lean_dec_ref(v___f_2718_);
                    leanh::lean_dec_ref(v_config_2717_);
                    leanh::lean_dec(v_handler_2716_);
                    leanh::lean_dec_ref(v_inst_2715_);
                    leanh::lean_dec_ref(v___f_2714_);
                    leanh::lean_dec_ref(v___f_2713_);
                    leanh::lean_dec_ref(v___f_2712_);
                    leanh::lean_dec_ref(v_activeConnections_2711_);
                    leanh::lean_dec_ref(v___x_2710_);
                    leanh::lean_dec_ref(v___f_2709_);
                    leanh::lean_dec(v_connectionLimit_2707_);
                    leanh::lean_dec_ref(v___f_2704_);
                    v_a_2722_ = leanh::lean_ctor_get(v_x_2720_, 0);
                    v_isSharedCheck_2730_ = (!leanh::lean_is_exclusive(v_x_2720_)) as u8;
                    if v_isSharedCheck_2730_ == 0 {
                        v___x_2724_ = v_x_2720_;
                        v_isShared_2725_ = v_isSharedCheck_2730_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2722_);
                        leanh::lean_dec(v_x_2720_);
                        v___x_2724_ = leanh::lean_box(0);
                        v_isShared_2725_ = v_isSharedCheck_2730_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2731_ = leanh::lean_ctor_get(v_x_2720_, 0);
                    v_isSharedCheck_2789_ = (!leanh::lean_is_exclusive(v_x_2720_)) as u8;
                    if v_isSharedCheck_2789_ == 0 {
                        v___x_2733_ = v_x_2720_;
                        v_isShared_2734_ = v_isSharedCheck_2789_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2731_);
                        leanh::lean_dec(v_x_2720_);
                        v___x_2733_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2729_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2729_, 0, v_a_2722_);
                    v___x_2727_ = v_reuseFailAlloc_2729_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2728_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2728_, 0, v___x_2727_);
                return v___x_2728_;
            }
            3 => {
                if leanh::lean_obj_tag(v_a_2731_) == 0 {
                    leanh::lean_dec_ref(v___f_2719_);
                    leanh::lean_dec_ref(v___f_2718_);
                    leanh::lean_dec_ref(v_config_2717_);
                    leanh::lean_dec(v_handler_2716_);
                    leanh::lean_dec_ref(v_inst_2715_);
                    leanh::lean_dec_ref(v___f_2714_);
                    leanh::lean_dec_ref(v___f_2713_);
                    leanh::lean_dec_ref(v___f_2712_);
                    leanh::lean_dec_ref(v_activeConnections_2711_);
                    leanh::lean_dec_ref(v___x_2710_);
                    if v_permitAcquired_2703_ == 0 {
                        leanh::lean_del_object(v___x_2733_);
                        leanh::lean_dec_ref(v___f_2709_);
                        leanh::lean_dec(v_connectionLimit_2707_);
                        leanh::lean_inc_ref(v___y_2706_);
                        v___x_2735_ = leanh::lean_apply_3(
                            v___f_2704_,
                            v___x_2705_,
                            v___y_2706_,
                            leanh::lean_box(0),
                        );
                        return v___x_2735_;
                    } else {
                        if leanh::lean_obj_tag(v_connectionLimit_2707_) == 1 {
                            leanh::lean_dec_ref(v___f_2704_);
                            v_val_2736_ = leanh::lean_ctor_get(v_connectionLimit_2707_, 0);
                            v_isSharedCheck_2749_ =
                                (!leanh::lean_is_exclusive(v_connectionLimit_2707_)) as u8;
                            if v_isSharedCheck_2749_ == 0 {
                                v___x_2738_ = v_connectionLimit_2707_;
                                v_isShared_2739_ = v_isSharedCheck_2749_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_inc(v_val_2736_);
                                leanh::lean_dec(v_connectionLimit_2707_);
                                v___x_2738_ = leanh::lean_box(0);
                                v_isShared_2739_ = v_isSharedCheck_2749_;
                                state = 4;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_2733_);
                            leanh::lean_dec_ref(v___f_2709_);
                            leanh::lean_dec(v_connectionLimit_2707_);
                            leanh::lean_inc_ref(v___y_2706_);
                            v___x_2750_ = leanh::lean_apply_3(
                                v___f_2704_,
                                v___x_2705_,
                                v___y_2706_,
                                leanh::lean_box(0),
                            );
                            return v___x_2750_;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___f_2709_);
                    leanh::lean_dec_ref(v___f_2704_);
                    v_val_2751_ = leanh::lean_ctor_get(v_a_2731_, 0);
                    v_isSharedCheck_2788_ = (!leanh::lean_is_exclusive(v_a_2731_)) as u8;
                    if v_isSharedCheck_2788_ == 0 {
                        v___x_2753_ = v_a_2731_;
                        v_isShared_2754_ = v_isSharedCheck_2788_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2751_);
                        leanh::lean_dec(v_a_2731_);
                        v___x_2753_ = leanh::lean_box(0);
                        v_isShared_2754_ = v_isSharedCheck_2788_;
                        state = 7;
                        continue;
                    }
                }
            }
            4 => {
                v___x_2740_ = l_Std_Semaphore_release(v_val_2736_);
                if v_isShared_2734_ == 0 {
                    leanh::lean_ctor_set(v___x_2733_, 0, v___x_2740_);
                    v___x_2742_ = v___x_2733_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2748_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2748_, 0, v___x_2740_);
                    v___x_2742_ = v_reuseFailAlloc_2748_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_2739_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2738_, 0);
                    leanh::lean_ctor_set(v___x_2738_, 0, v___x_2742_);
                    v___x_2744_ = v___x_2738_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2747_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2747_, 0, v___x_2742_);
                    v___x_2744_ = v_reuseFailAlloc_2747_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_2745_ = leanh::lean_unsigned_to_nat(0);
                v___x_2746_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_2745_,
                    v___x_2708_,
                    v___x_2744_,
                    v___f_2709_,
                );
                return v___x_2746_;
            }
            7 => {
                v___x_2755_ = leanh::lean_box((v_permitAcquired_2703_) as usize);
                v___x_2756_ = leanh::lean_box((v___x_2708_) as usize);
                leanh::lean_inc(v_val_2751_);
                v___f_2757_ = leanh::lean_alloc_closure(
                    l_Std_Http_Server_serve___redArg___lam__16___boxed as *mut core::ffi::c_void,
                    18,
                    15,
                );
                leanh::lean_closure_set(v___f_2757_, 0, v___x_2710_);
                leanh::lean_closure_set(v___f_2757_, 1, v_activeConnections_2711_);
                leanh::lean_closure_set(v___f_2757_, 2, v___f_2712_);
                leanh::lean_closure_set(v___f_2757_, 3, v___f_2713_);
                leanh::lean_closure_set(v___f_2757_, 4, v___f_2714_);
                leanh::lean_closure_set(v___f_2757_, 5, v___x_2755_);
                leanh::lean_closure_set(v___f_2757_, 6, v___x_2705_);
                leanh::lean_closure_set(v___f_2757_, 7, v_connectionLimit_2707_);
                leanh::lean_closure_set(v___f_2757_, 8, v___x_2756_);
                leanh::lean_closure_set(v___f_2757_, 9, v_inst_2715_);
                leanh::lean_closure_set(v___f_2757_, 10, v_val_2751_);
                leanh::lean_closure_set(v___f_2757_, 11, v_handler_2716_);
                leanh::lean_closure_set(v___f_2757_, 12, v_config_2717_);
                leanh::lean_closure_set(v___f_2757_, 13, v___f_2718_);
                leanh::lean_closure_set(v___f_2757_, 14, v___f_2719_);
                leanh::lean_inc_ref(v___y_2706_);
                v___f_2758_ = leanh::lean_alloc_closure(
                    l_Std_Http_Server_serve___redArg___lam__17___boxed as *mut core::ffi::c_void,
                    4,
                    2,
                );
                leanh::lean_closure_set(v___f_2758_, 0, v___f_2757_);
                leanh::lean_closure_set(v___f_2758_, 1, v___y_2706_);
                v___x_2759_ = leanh::lean_box((v___x_2708_) as usize);
                leanh::lean_inc_ref(v___f_2758_);
                v___f_2760_ = leanh::lean_alloc_closure(
                    l_Std_Http_Server_serve___redArg___lam__19___boxed as *mut core::ffi::c_void,
                    5,
                    3,
                );
                leanh::lean_closure_set(v___f_2760_, 0, v___x_2759_);
                leanh::lean_closure_set(v___f_2760_, 1, v___f_2758_);
                leanh::lean_closure_set(v___f_2760_, 2, v___f_2758_);
                v___x_2771_ = lean_uv_tcp_getpeername(v_val_2751_);
                leanh::lean_dec(v_val_2751_);
                if leanh::lean_obj_tag(v___x_2771_) == 0 {
                    v_a_2772_ = leanh::lean_ctor_get(v___x_2771_, 0);
                    v_isSharedCheck_2779_ = (!leanh::lean_is_exclusive(v___x_2771_)) as u8;
                    if v_isSharedCheck_2779_ == 0 {
                        v___x_2774_ = v___x_2771_;
                        v_isShared_2775_ = v_isSharedCheck_2779_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2772_);
                        leanh::lean_dec(v___x_2771_);
                        v___x_2774_ = leanh::lean_box(0);
                        v_isShared_2775_ = v_isSharedCheck_2779_;
                        state = 11;
                        continue;
                    }
                } else {
                    v_a_2780_ = leanh::lean_ctor_get(v___x_2771_, 0);
                    v_isSharedCheck_2787_ = (!leanh::lean_is_exclusive(v___x_2771_)) as u8;
                    if v_isSharedCheck_2787_ == 0 {
                        v___x_2782_ = v___x_2771_;
                        v_isShared_2783_ = v_isSharedCheck_2787_;
                        state = 13;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2780_);
                        leanh::lean_dec(v___x_2771_);
                        v___x_2782_ = leanh::lean_box(0);
                        v_isShared_2783_ = v_isSharedCheck_2787_;
                        state = 13;
                        continue;
                    }
                }
            }
            8 => {
                if v_isShared_2734_ == 0 {
                    leanh::lean_ctor_set(v___x_2733_, 0, v_val_2762_);
                    v___x_2764_ = v___x_2733_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2770_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2770_, 0, v_val_2762_);
                    v___x_2764_ = v_reuseFailAlloc_2770_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_2754_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2753_, 0);
                    leanh::lean_ctor_set(v___x_2753_, 0, v___x_2764_);
                    v___x_2766_ = v___x_2753_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2769_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2769_, 0, v___x_2764_);
                    v___x_2766_ = v_reuseFailAlloc_2769_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_2767_ = leanh::lean_unsigned_to_nat(0);
                v___x_2768_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_2767_,
                    v___x_2708_,
                    v___x_2766_,
                    v___f_2760_,
                );
                return v___x_2768_;
            }
            11 => {
                if v_isShared_2775_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2774_, 1);
                    v___x_2777_ = v___x_2774_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2778_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2778_, 0, v_a_2772_);
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
                    leanh::lean_ctor_set_tag(v___x_2782_, 0);
                    v___x_2785_ = v___x_2782_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2786_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2786_, 0, v_a_2780_);
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
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_permitAcquired_2790_: *mut leanh::LeanObject = *_args.add(0);
    let mut v___f_2791_: *mut leanh::LeanObject = *_args.add(1);
    let mut v___x_2792_: *mut leanh::LeanObject = *_args.add(2);
    let mut v___y_2793_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_connectionLimit_2794_: *mut leanh::LeanObject = *_args.add(4);
    let mut v___x_2795_: *mut leanh::LeanObject = *_args.add(5);
    let mut v___f_2796_: *mut leanh::LeanObject = *_args.add(6);
    let mut v___x_2797_: *mut leanh::LeanObject = *_args.add(7);
    let mut v_activeConnections_2798_: *mut leanh::LeanObject = *_args.add(8);
    let mut v___f_2799_: *mut leanh::LeanObject = *_args.add(9);
    let mut v___f_2800_: *mut leanh::LeanObject = *_args.add(10);
    let mut v___f_2801_: *mut leanh::LeanObject = *_args.add(11);
    let mut v_inst_2802_: *mut leanh::LeanObject = *_args.add(12);
    let mut v_handler_2803_: *mut leanh::LeanObject = *_args.add(13);
    let mut v_config_2804_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___f_2805_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___f_2806_: *mut leanh::LeanObject = *_args.add(16);
    let mut v_x_2807_: *mut leanh::LeanObject = *_args.add(17);
    let mut v___y_2808_: *mut leanh::LeanObject = *_args.add(18);
    let mut v_permitAcquired_boxed_2809_: u8 = 0;
    let mut v___x_14330__boxed_2810_: u8 = 0;
    let mut v_res_2811_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_permitAcquired_boxed_2809_ = (leanh::lean_unbox(v_permitAcquired_2790_) as u8);
    v___x_14330__boxed_2810_ = (leanh::lean_unbox(v___x_2795_) as u8);
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
    leanh::lean_dec_ref(v___y_2793_);
    return v_res_2811_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__20(
    mut v_a_2812_: *mut leanh::LeanObject,
    mut v___f_2813_: *mut leanh::LeanObject,
    mut v___f_2814_: *mut leanh::LeanObject,
    mut v___x_2815_: u8,
    mut v___f_2816_: *mut leanh::LeanObject,
    mut v_x_2817_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_2819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2822_: u8 = 0;
    let mut v___x_2824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2827_: u8 = 0;
    let mut v_a_2828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2817_) == 0 {
                    leanh::lean_dec_ref(v___f_2816_);
                    leanh::lean_dec_ref(v___f_2814_);
                    leanh::lean_dec_ref(v___f_2813_);
                    leanh::lean_dec(v_a_2812_);
                    v_a_2819_ = leanh::lean_ctor_get(v_x_2817_, 0);
                    v_isSharedCheck_2827_ = (!leanh::lean_is_exclusive(v_x_2817_)) as u8;
                    if v_isSharedCheck_2827_ == 0 {
                        v___x_2821_ = v_x_2817_;
                        v_isShared_2822_ = v_isSharedCheck_2827_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2819_);
                        leanh::lean_dec(v_x_2817_);
                        v___x_2821_ = leanh::lean_box(0);
                        v_isShared_2822_ = v_isSharedCheck_2827_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2828_ = leanh::lean_ctor_get(v_x_2817_, 0);
                    leanh::lean_inc(v_a_2828_);
                    leanh::lean_dec_ref_known(v_x_2817_, 1);
                    v___x_2829_ = l_Std_Async_TCP_Socket_Server_acceptSelector(v_a_2812_);
                    v___x_2830_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2830_, 0, v___x_2829_);
                    leanh::lean_ctor_set(v___x_2830_, 1, v___f_2813_);
                    v___x_2831_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2831_, 0, v_a_2828_);
                    leanh::lean_ctor_set(v___x_2831_, 1, v___f_2814_);
                    v___x_2832_ = leanh::lean_unsigned_to_nat(2);
                    v___x_2833_ = lean_mk_empty_array_with_capacity(v___x_2832_);
                    v___x_2834_ = lean_array_push(v___x_2833_, v___x_2830_);
                    v___x_2835_ = lean_array_push(v___x_2834_, v___x_2831_);
                    v___x_2836_ = l_Std_Async_Selectable_one___redArg(v___x_2835_);
                    v___x_2837_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2838_ =
                        l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                            leanh::lean_box(0),
                            leanh::lean_box(0),
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
                    v_reuseFailAlloc_2826_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2826_, 0, v_a_2819_);
                    v___x_2824_ = v_reuseFailAlloc_2826_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2825_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2825_, 0, v___x_2824_);
                return v___x_2825_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__20___boxed(
    mut v_a_2839_: *mut leanh::LeanObject,
    mut v___f_2840_: *mut leanh::LeanObject,
    mut v___f_2841_: *mut leanh::LeanObject,
    mut v___x_2842_: *mut leanh::LeanObject,
    mut v___f_2843_: *mut leanh::LeanObject,
    mut v_x_2844_: *mut leanh::LeanObject,
    mut v___y_2845_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_14508__boxed_2846_: u8 = 0;
    let mut v_res_2847_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_14508__boxed_2846_ = (leanh::lean_unbox(v___x_2842_) as u8);
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
    mut v___f_2849_: *mut leanh::LeanObject,
    mut v___f_2850_: *mut leanh::LeanObject,
    mut v___x_2851_: *mut leanh::LeanObject,
    mut v_connectionLimit_2852_: *mut leanh::LeanObject,
    mut v___x_2853_: *mut leanh::LeanObject,
    mut v_activeConnections_2854_: *mut leanh::LeanObject,
    mut v___f_2855_: *mut leanh::LeanObject,
    mut v___f_2856_: *mut leanh::LeanObject,
    mut v___f_2857_: *mut leanh::LeanObject,
    mut v_inst_2858_: *mut leanh::LeanObject,
    mut v_handler_2859_: *mut leanh::LeanObject,
    mut v_config_2860_: *mut leanh::LeanObject,
    mut v___f_2861_: *mut leanh::LeanObject,
    mut v___f_2862_: *mut leanh::LeanObject,
    mut v_a_2863_: *mut leanh::LeanObject,
    mut v___f_2864_: *mut leanh::LeanObject,
    mut v___f_2865_: *mut leanh::LeanObject,
    mut v_permitAcquired_2866_: u8,
    mut v___y_2867_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2879_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref_n(v___y_2867_, 3);
    v___x_2869_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2869_, 0, v___y_2867_);
    v___x_2870_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2870_, 0, v___x_2869_);
    v___x_2871_ = leanh::lean_unsigned_to_nat(0);
    v___x_2872_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2871_,
        v___x_2848_,
        v___x_2870_,
        v___f_2849_,
    );
    leanh::lean_inc_ref(v___f_2850_);
    v___f_2873_ = leanh::lean_alloc_closure(
        l_Std_Http_Server_serve___redArg___lam__7___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_2873_, 0, v___f_2850_);
    leanh::lean_closure_set(v___f_2873_, 1, v___y_2867_);
    v___x_2874_ = leanh::lean_box((v_permitAcquired_2866_) as usize);
    v___x_2875_ = leanh::lean_box((v___x_2848_) as usize);
    v___f_2876_ = leanh::lean_alloc_closure(
        l_Std_Http_Server_serve___redArg___lam__18___boxed as *mut core::ffi::c_void,
        19,
        17,
    );
    leanh::lean_closure_set(v___f_2876_, 0, v___x_2874_);
    leanh::lean_closure_set(v___f_2876_, 1, v___f_2850_);
    leanh::lean_closure_set(v___f_2876_, 2, v___x_2851_);
    leanh::lean_closure_set(v___f_2876_, 3, v___y_2867_);
    leanh::lean_closure_set(v___f_2876_, 4, v_connectionLimit_2852_);
    leanh::lean_closure_set(v___f_2876_, 5, v___x_2875_);
    leanh::lean_closure_set(v___f_2876_, 6, v___f_2873_);
    leanh::lean_closure_set(v___f_2876_, 7, v___x_2853_);
    leanh::lean_closure_set(v___f_2876_, 8, v_activeConnections_2854_);
    leanh::lean_closure_set(v___f_2876_, 9, v___f_2855_);
    leanh::lean_closure_set(v___f_2876_, 10, v___f_2856_);
    leanh::lean_closure_set(v___f_2876_, 11, v___f_2857_);
    leanh::lean_closure_set(v___f_2876_, 12, v_inst_2858_);
    leanh::lean_closure_set(v___f_2876_, 13, v_handler_2859_);
    leanh::lean_closure_set(v___f_2876_, 14, v_config_2860_);
    leanh::lean_closure_set(v___f_2876_, 15, v___f_2861_);
    leanh::lean_closure_set(v___f_2876_, 16, v___f_2862_);
    v___x_2877_ = leanh::lean_box((v___x_2848_) as usize);
    v___f_2878_ = leanh::lean_alloc_closure(
        l_Std_Http_Server_serve___redArg___lam__20___boxed as *mut core::ffi::c_void,
        7,
        5,
    );
    leanh::lean_closure_set(v___f_2878_, 0, v_a_2863_);
    leanh::lean_closure_set(v___f_2878_, 1, v___f_2864_);
    leanh::lean_closure_set(v___f_2878_, 2, v___f_2865_);
    leanh::lean_closure_set(v___f_2878_, 3, v___x_2877_);
    leanh::lean_closure_set(v___f_2878_, 4, v___f_2876_);
    v___x_2879_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2871_,
        v___x_2848_,
        v___x_2872_,
        v___f_2878_,
    );
    return v___x_2879_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__21___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2880_: *mut leanh::LeanObject = *_args.add(0);
    let mut v___f_2881_: *mut leanh::LeanObject = *_args.add(1);
    let mut v___f_2882_: *mut leanh::LeanObject = *_args.add(2);
    let mut v___x_2883_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_connectionLimit_2884_: *mut leanh::LeanObject = *_args.add(4);
    let mut v___x_2885_: *mut leanh::LeanObject = *_args.add(5);
    let mut v_activeConnections_2886_: *mut leanh::LeanObject = *_args.add(6);
    let mut v___f_2887_: *mut leanh::LeanObject = *_args.add(7);
    let mut v___f_2888_: *mut leanh::LeanObject = *_args.add(8);
    let mut v___f_2889_: *mut leanh::LeanObject = *_args.add(9);
    let mut v_inst_2890_: *mut leanh::LeanObject = *_args.add(10);
    let mut v_handler_2891_: *mut leanh::LeanObject = *_args.add(11);
    let mut v_config_2892_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___f_2893_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___f_2894_: *mut leanh::LeanObject = *_args.add(14);
    let mut v_a_2895_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___f_2896_: *mut leanh::LeanObject = *_args.add(16);
    let mut v___f_2897_: *mut leanh::LeanObject = *_args.add(17);
    let mut v_permitAcquired_2898_: *mut leanh::LeanObject = *_args.add(18);
    let mut v___y_2899_: *mut leanh::LeanObject = *_args.add(19);
    let mut v___y_2900_: *mut leanh::LeanObject = *_args.add(20);
    let mut v___x_14566__boxed_2901_: u8 = 0;
    let mut v_permitAcquired_boxed_2902_: u8 = 0;
    let mut v_res_2903_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_14566__boxed_2901_ = (leanh::lean_unbox(v___x_2880_) as u8);
    v_permitAcquired_boxed_2902_ = (leanh::lean_unbox(v_permitAcquired_2898_) as u8);
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
    leanh::lean_dec_ref(v___y_2899_);
    return v_res_2903_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__22(
    mut v___f_2904_: *mut leanh::LeanObject,
    mut v___y_2905_: *mut leanh::LeanObject,
    mut v_x_2906_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_2908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2911_: u8 = 0;
    let mut v___x_2913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2916_: u8 = 0;
    let mut v_a_2917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2906_) == 0 {
                    leanh::lean_dec_ref(v___f_2904_);
                    v_a_2908_ = leanh::lean_ctor_get(v_x_2906_, 0);
                    v_isSharedCheck_2916_ = (!leanh::lean_is_exclusive(v_x_2906_)) as u8;
                    if v_isSharedCheck_2916_ == 0 {
                        v___x_2910_ = v_x_2906_;
                        v_isShared_2911_ = v_isSharedCheck_2916_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2908_);
                        leanh::lean_dec(v_x_2906_);
                        v___x_2910_ = leanh::lean_box(0);
                        v_isShared_2911_ = v_isSharedCheck_2916_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2917_ = leanh::lean_ctor_get(v_x_2906_, 0);
                    leanh::lean_inc(v_a_2917_);
                    leanh::lean_dec_ref_known(v_x_2906_, 1);
                    leanh::lean_inc_ref(v___y_2905_);
                    v___x_2918_ = leanh::lean_apply_3(
                        v___f_2904_,
                        v_a_2917_,
                        v___y_2905_,
                        leanh::lean_box(0),
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
                    v_reuseFailAlloc_2915_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2915_, 0, v_a_2908_);
                    v___x_2913_ = v_reuseFailAlloc_2915_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2914_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2914_, 0, v___x_2913_);
                return v___x_2914_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__22___boxed(
    mut v___f_2919_: *mut leanh::LeanObject,
    mut v___y_2920_: *mut leanh::LeanObject,
    mut v_x_2921_: *mut leanh::LeanObject,
    mut v___y_2922_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2923_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2923_ = l_Std_Http_Server_serve___redArg___lam__22(v___f_2919_, v___y_2920_, v_x_2921_);
    leanh::lean_dec_ref(v___y_2920_);
    return v_res_2923_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__23(
    mut v___x_2924_: u8,
    mut v___x_2925_: u8,
    mut v___f_2926_: *mut leanh::LeanObject,
    mut v_x_2927_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_2929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2932_: u8 = 0;
    let mut v___x_2934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2937_: u8 = 0;
    let mut v___x_2939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2940_: u8 = 0;
    let mut v___x_2941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2948_: u8 = 0;
    let mut v_unused_2949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2927_) == 0 {
                    leanh::lean_dec_ref(v___f_2926_);
                    v_a_2929_ = leanh::lean_ctor_get(v_x_2927_, 0);
                    v_isSharedCheck_2937_ = (!leanh::lean_is_exclusive(v_x_2927_)) as u8;
                    if v_isSharedCheck_2937_ == 0 {
                        v___x_2931_ = v_x_2927_;
                        v_isShared_2932_ = v_isSharedCheck_2937_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2929_);
                        leanh::lean_dec(v_x_2927_);
                        v___x_2931_ = leanh::lean_box(0);
                        v_isShared_2932_ = v_isSharedCheck_2937_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_isSharedCheck_2948_ = (!leanh::lean_is_exclusive(v_x_2927_)) as u8;
                    if v_isSharedCheck_2948_ == 0 {
                        v_unused_2949_ = leanh::lean_ctor_get(v_x_2927_, 0);
                        leanh::lean_dec(v_unused_2949_);
                        v___x_2939_ = v_x_2927_;
                        v_isShared_2940_ = v_isSharedCheck_2948_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_dec(v_x_2927_);
                        v___x_2939_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2936_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2936_, 0, v_a_2929_);
                    v___x_2934_ = v_reuseFailAlloc_2936_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2935_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2935_, 0, v___x_2934_);
                return v___x_2935_;
            }
            3 => {
                v___x_2941_ = leanh::lean_box((v___x_2924_) as usize);
                if v_isShared_2940_ == 0 {
                    leanh::lean_ctor_set(v___x_2939_, 0, v___x_2941_);
                    v___x_2943_ = v___x_2939_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2947_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2947_, 0, v___x_2941_);
                    v___x_2943_ = v_reuseFailAlloc_2947_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2944_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2944_, 0, v___x_2943_);
                v___x_2945_ = leanh::lean_unsigned_to_nat(0);
                v___x_2946_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
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
    mut v___x_2950_: *mut leanh::LeanObject,
    mut v___x_2951_: *mut leanh::LeanObject,
    mut v___f_2952_: *mut leanh::LeanObject,
    mut v_x_2953_: *mut leanh::LeanObject,
    mut v___y_2954_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_14670__boxed_2955_: u8 = 0;
    let mut v___x_14671__boxed_2956_: u8 = 0;
    let mut v_res_2957_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_14670__boxed_2955_ = (leanh::lean_unbox(v___x_2950_) as u8);
    v___x_14671__boxed_2956_ = (leanh::lean_unbox(v___x_2951_) as u8);
    v_res_2957_ = l_Std_Http_Server_serve___redArg___lam__23(
        v___x_14670__boxed_2955_,
        v___x_14671__boxed_2956_,
        v___f_2952_,
        v_x_2953_,
    );
    return v_res_2957_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__24(
    mut v___f_2958_: *mut leanh::LeanObject,
    mut v___x_2959_: u8,
    mut v___f_2960_: *mut leanh::LeanObject,
    mut v_x_2961_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_2963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2966_: u8 = 0;
    let mut v___x_2968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2971_: u8 = 0;
    let mut v_a_2972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2961_) == 0 {
                    leanh::lean_dec_ref(v___f_2960_);
                    leanh::lean_dec_ref(v___f_2958_);
                    v_a_2963_ = leanh::lean_ctor_get(v_x_2961_, 0);
                    v_isSharedCheck_2971_ = (!leanh::lean_is_exclusive(v_x_2961_)) as u8;
                    if v_isSharedCheck_2971_ == 0 {
                        v___x_2965_ = v_x_2961_;
                        v_isShared_2966_ = v_isSharedCheck_2971_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2963_);
                        leanh::lean_dec(v_x_2961_);
                        v___x_2965_ = leanh::lean_box(0);
                        v_isShared_2966_ = v_isSharedCheck_2971_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2972_ = leanh::lean_ctor_get(v_x_2961_, 0);
                    leanh::lean_inc(v_a_2972_);
                    leanh::lean_dec_ref_known(v_x_2961_, 1);
                    v___x_2973_ = l_IO_Promise_result_x21___redArg(v_a_2972_);
                    leanh::lean_dec(v_a_2972_);
                    v___x_2974_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2975_ = lean_task_map(v___f_2958_, v___x_2973_, v___x_2974_, v___x_2959_);
                    v___x_2976_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2976_, 0, v___x_2975_);
                    v___x_2977_ =
                        l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                            leanh::lean_box(0),
                            leanh::lean_box(0),
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
                    v_reuseFailAlloc_2970_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2970_, 0, v_a_2963_);
                    v___x_2968_ = v_reuseFailAlloc_2970_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2969_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2969_, 0, v___x_2968_);
                return v___x_2969_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__24___boxed(
    mut v___f_2978_: *mut leanh::LeanObject,
    mut v___x_2979_: *mut leanh::LeanObject,
    mut v___f_2980_: *mut leanh::LeanObject,
    mut v_x_2981_: *mut leanh::LeanObject,
    mut v___y_2982_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_14729__boxed_2983_: u8 = 0;
    let mut v_res_2984_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_14729__boxed_2983_ = (leanh::lean_unbox(v___x_2979_) as u8);
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
    mut v___f_2986_: *mut leanh::LeanObject,
    mut v_connectionLimit_2987_: *mut leanh::LeanObject,
    mut v___f_2988_: *mut leanh::LeanObject,
    mut v___f_2989_: *mut leanh::LeanObject,
    mut v_b_2990_: *mut leanh::LeanObject,
    mut v___y_2991_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3000_: u8 = 0;
    let mut v___x_3001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3003_: u8 = 0;
    let mut v___x_3004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3015_: u8 = 0;
    let mut v___f_3016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_connectionLimit_2987_) == 1 {
                    v_val_2997_ = leanh::lean_ctor_get(v_connectionLimit_2987_, 0);
                    v_isSharedCheck_3015_ =
                        (!leanh::lean_is_exclusive(v_connectionLimit_2987_)) as u8;
                    if v_isSharedCheck_3015_ == 0 {
                        v___x_2999_ = v_connectionLimit_2987_;
                        v_isShared_3000_ = v_isSharedCheck_3015_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2997_);
                        leanh::lean_dec(v_connectionLimit_2987_);
                        v___x_2999_ = leanh::lean_box(0);
                        v_isShared_3000_ = v_isSharedCheck_3015_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v___f_2989_);
                    leanh::lean_dec(v_connectionLimit_2987_);
                    leanh::lean_inc_ref(v___y_2991_);
                    v___f_3016_ = leanh::lean_alloc_closure(
                        l_Std_Http_Server_serve___redArg___lam__22___boxed
                            as *mut core::ffi::c_void,
                        4,
                        2,
                    );
                    leanh::lean_closure_set(v___f_3016_, 0, v___f_2988_);
                    leanh::lean_closure_set(v___f_3016_, 1, v___y_2991_);
                    v___x_3017_ = leanh::lean_box((v___x_2985_) as usize);
                    v___x_3018_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3018_, 0, v___x_3017_);
                    v___x_3019_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3019_, 0, v___x_3018_);
                    v___x_3020_ = leanh::lean_unsigned_to_nat(0);
                    v___x_3021_ =
                        l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                            leanh::lean_box(0),
                            leanh::lean_box(0),
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
                v___x_2995_ = leanh::lean_unsigned_to_nat(0);
                v___x_2996_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_2995_,
                    v___x_2985_,
                    v___y_2994_,
                    v___f_2986_,
                );
                return v___x_2996_;
            }
            2 => {
                v___x_3001_ = l_Std_Semaphore_acquire(v_val_2997_);
                leanh::lean_inc_ref(v___y_2991_);
                v___f_3002_ = leanh::lean_alloc_closure(
                    l_Std_Http_Server_serve___redArg___lam__22___boxed as *mut core::ffi::c_void,
                    4,
                    2,
                );
                leanh::lean_closure_set(v___f_3002_, 0, v___f_2988_);
                leanh::lean_closure_set(v___f_3002_, 1, v___y_2991_);
                v___x_3003_ = 1;
                v___x_3004_ = leanh::lean_box((v___x_3003_) as usize);
                v___x_3005_ = leanh::lean_box((v___x_2985_) as usize);
                v___f_3006_ = leanh::lean_alloc_closure(
                    l_Std_Http_Server_serve___redArg___lam__23___boxed as *mut core::ffi::c_void,
                    5,
                    3,
                );
                leanh::lean_closure_set(v___f_3006_, 0, v___x_3004_);
                leanh::lean_closure_set(v___f_3006_, 1, v___x_3005_);
                leanh::lean_closure_set(v___f_3006_, 2, v___f_3002_);
                v___x_3007_ = leanh::lean_box((v___x_2985_) as usize);
                v___f_3008_ = leanh::lean_alloc_closure(
                    l_Std_Http_Server_serve___redArg___lam__24___boxed as *mut core::ffi::c_void,
                    5,
                    3,
                );
                leanh::lean_closure_set(v___f_3008_, 0, v___f_2989_);
                leanh::lean_closure_set(v___f_3008_, 1, v___x_3007_);
                leanh::lean_closure_set(v___f_3008_, 2, v___f_3006_);
                if v_isShared_3000_ == 0 {
                    leanh::lean_ctor_set(v___x_2999_, 0, v___x_3001_);
                    v___x_3010_ = v___x_2999_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3014_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3014_, 0, v___x_3001_);
                    v___x_3010_ = v_reuseFailAlloc_3014_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3011_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3011_, 0, v___x_3010_);
                v___x_3012_ = leanh::lean_unsigned_to_nat(0);
                v___x_3013_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
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
    mut v___x_3022_: *mut leanh::LeanObject,
    mut v___f_3023_: *mut leanh::LeanObject,
    mut v_connectionLimit_3024_: *mut leanh::LeanObject,
    mut v___f_3025_: *mut leanh::LeanObject,
    mut v___f_3026_: *mut leanh::LeanObject,
    mut v_b_3027_: *mut leanh::LeanObject,
    mut v___y_3028_: *mut leanh::LeanObject,
    mut v___y_3029_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_14773__boxed_3030_: u8 = 0;
    let mut v_res_3031_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_14773__boxed_3030_ = (leanh::lean_unbox(v___x_3022_) as u8);
    v_res_3031_ = l_Std_Http_Server_serve___redArg___lam__26(
        v___x_14773__boxed_3030_,
        v___f_3023_,
        v_connectionLimit_3024_,
        v___f_3025_,
        v___f_3026_,
        v_b_3027_,
        v___y_3028_,
    );
    leanh::lean_dec_ref(v___y_3028_);
    return v_res_3031_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__25(
    mut v___x_3032_: *mut leanh::LeanObject,
    mut v___f_3033_: *mut leanh::LeanObject,
    mut v___x_3034_: *mut leanh::LeanObject,
    mut v___x_3035_: u8,
    mut v___f_3036_: *mut leanh::LeanObject,
    mut v___y_3037_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_13260__overap_3039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3042_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_13260__overap_3039_ =
        l___private_Init_While_0__whileM_erased___redArg(v___x_3032_, v___f_3033_, v___x_3034_);
    v___x_3040_ = leanh::lean_apply_2(
        v___x_13260__overap_3039_,
        v___y_3037_,
        leanh::lean_box(0),
    );
    v___x_3041_ = leanh::lean_unsigned_to_nat(0);
    v___x_3042_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_3041_,
        v___x_3035_,
        v___x_3040_,
        v___f_3036_,
    );
    return v___x_3042_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__25___boxed(
    mut v___x_3043_: *mut leanh::LeanObject,
    mut v___f_3044_: *mut leanh::LeanObject,
    mut v___x_3045_: *mut leanh::LeanObject,
    mut v___x_3046_: *mut leanh::LeanObject,
    mut v___f_3047_: *mut leanh::LeanObject,
    mut v___y_3048_: *mut leanh::LeanObject,
    mut v___y_3049_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_14852__boxed_3050_: u8 = 0;
    let mut v_res_3051_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_14852__boxed_3050_ = (leanh::lean_unbox(v___x_3046_) as u8);
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
    mut v_x_3052_: *mut leanh::LeanObject,
    mut v_x_3053_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_3055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3058_: u8 = 0;
    let mut v___x_3060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3063_: u8 = 0;
    let mut v___x_3064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3053_) == 0 {
                    leanh::lean_dec_ref(v_x_3052_);
                    v_a_3055_ = leanh::lean_ctor_get(v_x_3053_, 0);
                    v_isSharedCheck_3063_ = (!leanh::lean_is_exclusive(v_x_3053_)) as u8;
                    if v_isSharedCheck_3063_ == 0 {
                        v___x_3057_ = v_x_3053_;
                        v_isShared_3058_ = v_isSharedCheck_3063_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3055_);
                        leanh::lean_dec(v_x_3053_);
                        v___x_3057_ = leanh::lean_box(0);
                        v_isShared_3058_ = v_isSharedCheck_3063_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref_known(v_x_3053_, 1);
                    v___x_3064_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3064_, 0, v_x_3052_);
                    return v___x_3064_;
                }
            }
            1 => {
                if v_isShared_3058_ == 0 {
                    v___x_3060_ = v___x_3057_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3062_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3062_, 0, v_a_3055_);
                    v___x_3060_ = v_reuseFailAlloc_3062_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3061_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3061_, 0, v___x_3060_);
                return v___x_3061_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__27___boxed(
    mut v_x_3065_: *mut leanh::LeanObject,
    mut v_x_3066_: *mut leanh::LeanObject,
    mut v___y_3067_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3068_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3068_ = l_Std_Http_Server_serve___redArg___lam__27(v_x_3065_, v_x_3066_);
    return v_res_3068_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__28(
    mut v___f_3073_: *mut leanh::LeanObject,
    mut v___x_3074_: *mut leanh::LeanObject,
    mut v___f_3075_: *mut leanh::LeanObject,
    mut v___f_3076_: *mut leanh::LeanObject,
    mut v_inst_3077_: *mut leanh::LeanObject,
    mut v_handler_3078_: *mut leanh::LeanObject,
    mut v_config_3079_: *mut leanh::LeanObject,
    mut v___f_3080_: *mut leanh::LeanObject,
    mut v_a_3081_: *mut leanh::LeanObject,
    mut v___f_3082_: *mut leanh::LeanObject,
    mut v___f_3083_: *mut leanh::LeanObject,
    mut v___f_3084_: *mut leanh::LeanObject,
    mut v___f_3085_: *mut leanh::LeanObject,
    mut v___f_3086_: *mut leanh::LeanObject,
    mut v_x_3087_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_3087_) == 0 {
        let mut v___x_3089_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v___f_3086_);
        leanh::lean_dec_ref(v___f_3085_);
        leanh::lean_dec_ref(v___f_3084_);
        leanh::lean_dec_ref(v___f_3083_);
        leanh::lean_dec_ref(v___f_3082_);
        leanh::lean_dec(v_a_3081_);
        leanh::lean_dec_ref(v___f_3080_);
        leanh::lean_dec_ref(v_config_3079_);
        leanh::lean_dec(v_handler_3078_);
        leanh::lean_dec_ref(v_inst_3077_);
        leanh::lean_dec_ref(v___f_3076_);
        leanh::lean_dec_ref(v___f_3075_);
        leanh::lean_dec_ref(v___x_3074_);
        leanh::lean_dec_ref(v___f_3073_);
        v___x_3089_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_3089_, 0, v_x_3087_);
        return v___x_3089_;
    } else {
        let mut v_a_3090_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_context_3091_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_activeConnections_3092_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_connectionLimit_3093_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_shutdownPromise_3094_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3095_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3096_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3097_: u8 = 0;
        let mut v___x_3098_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3099_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3100_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3101_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3102_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3103_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3104_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3105_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3106_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3107_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3108_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3109_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3110_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3111_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3112_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3113_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3114_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_3090_ = leanh::lean_ctor_get(v_x_3087_, 0);
        v_context_3091_ = leanh::lean_ctor_get(v_a_3090_, 0);
        v_activeConnections_3092_ = leanh::lean_ctor_get(v_a_3090_, 1);
        v_connectionLimit_3093_ = leanh::lean_ctor_get(v_a_3090_, 2);
        v_shutdownPromise_3094_ = leanh::lean_ctor_get(v_a_3090_, 3);
        leanh::lean_inc_ref(v_shutdownPromise_3094_);
        leanh::lean_inc_ref_n(v_context_3091_, 2);
        v___f_3095_ = leanh::lean_alloc_closure(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__3___boxed as *mut core::ffi::c_void, 4, 2);
        leanh::lean_closure_set(v___f_3095_, 0, v_context_3091_);
        leanh::lean_closure_set(v___f_3095_, 1, v_shutdownPromise_3094_);
        v___f_3096_ = leanh::lean_alloc_closure(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__4___boxed as *mut core::ffi::c_void, 5, 1);
        leanh::lean_closure_set(v___f_3096_, 0, v___f_3095_);
        v___x_3097_ = 0;
        v___x_3098_ = leanh::lean_box(0);
        v___f_3099_ = l_Std_Http_Server_serve___redArg___lam__28___closed__0;
        v___f_3100_ = l_Std_Http_Server_serve___redArg___lam__28___closed__1;
        v___x_3101_ = leanh::lean_box((v___x_3097_) as usize);
        leanh::lean_inc_ref(v_activeConnections_3092_);
        leanh::lean_inc_ref(v___x_3074_);
        leanh::lean_inc_n(v_connectionLimit_3093_, 2);
        v___f_3102_ = leanh::lean_alloc_closure(
            l_Std_Http_Server_serve___redArg___lam__21___boxed as *mut core::ffi::c_void,
            21,
            18,
        );
        leanh::lean_closure_set(v___f_3102_, 0, v___x_3101_);
        leanh::lean_closure_set(v___f_3102_, 1, v___f_3073_);
        leanh::lean_closure_set(v___f_3102_, 2, v___f_3099_);
        leanh::lean_closure_set(v___f_3102_, 3, v___x_3098_);
        leanh::lean_closure_set(v___f_3102_, 4, v_connectionLimit_3093_);
        leanh::lean_closure_set(v___f_3102_, 5, v___x_3074_);
        leanh::lean_closure_set(v___f_3102_, 6, v_activeConnections_3092_);
        leanh::lean_closure_set(v___f_3102_, 7, v___f_3075_);
        leanh::lean_closure_set(v___f_3102_, 8, v___f_3076_);
        leanh::lean_closure_set(v___f_3102_, 9, v___f_3096_);
        leanh::lean_closure_set(v___f_3102_, 10, v_inst_3077_);
        leanh::lean_closure_set(v___f_3102_, 11, v_handler_3078_);
        leanh::lean_closure_set(v___f_3102_, 12, v_config_3079_);
        leanh::lean_closure_set(v___f_3102_, 13, v___f_3080_);
        leanh::lean_closure_set(v___f_3102_, 14, v___f_3100_);
        leanh::lean_closure_set(v___f_3102_, 15, v_a_3081_);
        leanh::lean_closure_set(v___f_3102_, 16, v___f_3082_);
        leanh::lean_closure_set(v___f_3102_, 17, v___f_3083_);
        v___x_3103_ = leanh::lean_box((v___x_3097_) as usize);
        v___f_3104_ = leanh::lean_alloc_closure(
            l_Std_Http_Server_serve___redArg___lam__26___boxed as *mut core::ffi::c_void,
            8,
            5,
        );
        leanh::lean_closure_set(v___f_3104_, 0, v___x_3103_);
        leanh::lean_closure_set(v___f_3104_, 1, v___f_3084_);
        leanh::lean_closure_set(v___f_3104_, 2, v_connectionLimit_3093_);
        leanh::lean_closure_set(v___f_3104_, 3, v___f_3102_);
        leanh::lean_closure_set(v___f_3104_, 4, v___f_3085_);
        v___x_3105_ = leanh::lean_box((v___x_3097_) as usize);
        v___f_3106_ = leanh::lean_alloc_closure(
            l_Std_Http_Server_serve___redArg___lam__25___boxed as *mut core::ffi::c_void,
            7,
            5,
        );
        leanh::lean_closure_set(v___f_3106_, 0, v___x_3074_);
        leanh::lean_closure_set(v___f_3106_, 1, v___f_3104_);
        leanh::lean_closure_set(v___f_3106_, 2, v___x_3098_);
        leanh::lean_closure_set(v___f_3106_, 3, v___x_3105_);
        leanh::lean_closure_set(v___f_3106_, 4, v___f_3086_);
        v___x_3107_ = leanh::lean_box((v___x_3097_) as usize);
        leanh::lean_inc(v_a_3090_);
        v___x_3108_ = leanh::lean_alloc_closure(
            l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___boxed
                as *mut core::ffi::c_void,
            6,
            5,
        );
        leanh::lean_closure_set(v___x_3108_, 0, leanh::lean_box(0));
        leanh::lean_closure_set(v___x_3108_, 1, v_a_3090_);
        leanh::lean_closure_set(v___x_3108_, 2, v___x_3107_);
        leanh::lean_closure_set(v___x_3108_, 3, v___f_3106_);
        leanh::lean_closure_set(v___x_3108_, 4, v_context_3091_);
        v___x_3109_ = leanh::lean_unsigned_to_nat(0);
        v___x_3110_ = leanh::lean_alloc_closure(
            l_Std_Async_BaseAsync_toRawBaseIO___boxed as *mut core::ffi::c_void,
            3,
            2,
        );
        leanh::lean_closure_set(v___x_3110_, 0, leanh::lean_box(0));
        leanh::lean_closure_set(v___x_3110_, 1, v___x_3108_);
        v___x_3111_ = lean_io_as_task(v___x_3110_, v___x_3109_);
        leanh::lean_dec_ref(v___x_3111_);
        v___f_3112_ = leanh::lean_alloc_closure(
            l_Std_Http_Server_serve___redArg___lam__27___boxed as *mut core::ffi::c_void,
            3,
            1,
        );
        leanh::lean_closure_set(v___f_3112_, 0, v_x_3087_);
        v___x_3113_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__1;
        v___x_3114_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_3109_,
            v___x_3097_,
            v___x_3113_,
            v___f_3112_,
        );
        return v___x_3114_;
    }
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__28___boxed(
    mut v___f_3115_: *mut leanh::LeanObject,
    mut v___x_3116_: *mut leanh::LeanObject,
    mut v___f_3117_: *mut leanh::LeanObject,
    mut v___f_3118_: *mut leanh::LeanObject,
    mut v_inst_3119_: *mut leanh::LeanObject,
    mut v_handler_3120_: *mut leanh::LeanObject,
    mut v_config_3121_: *mut leanh::LeanObject,
    mut v___f_3122_: *mut leanh::LeanObject,
    mut v_a_3123_: *mut leanh::LeanObject,
    mut v___f_3124_: *mut leanh::LeanObject,
    mut v___f_3125_: *mut leanh::LeanObject,
    mut v___f_3126_: *mut leanh::LeanObject,
    mut v___f_3127_: *mut leanh::LeanObject,
    mut v___f_3128_: *mut leanh::LeanObject,
    mut v_x_3129_: *mut leanh::LeanObject,
    mut v___y_3130_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3131_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v___f_3132_: *mut leanh::LeanObject,
    mut v_config_3133_: *mut leanh::LeanObject,
    mut v_x_3134_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_val_3137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3140_: u8 = 0;
    let mut v___x_3141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3145_: u8 = 0;
    let mut v___x_3147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3150_: u8 = 0;
    let mut v_a_3151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3154_: u8 = 0;
    let mut v___x_3155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3161_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3134_) == 0 {
                    leanh::lean_dec_ref(v_config_3133_);
                    leanh::lean_dec_ref(v___f_3132_);
                    v_a_3142_ = leanh::lean_ctor_get(v_x_3134_, 0);
                    v_isSharedCheck_3150_ = (!leanh::lean_is_exclusive(v_x_3134_)) as u8;
                    if v_isSharedCheck_3150_ == 0 {
                        v___x_3144_ = v_x_3134_;
                        v_isShared_3145_ = v_isSharedCheck_3150_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3142_);
                        leanh::lean_dec(v_x_3134_);
                        v___x_3144_ = leanh::lean_box(0);
                        v_isShared_3145_ = v_isSharedCheck_3150_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_3151_ = leanh::lean_ctor_get(v_x_3134_, 0);
                    v_isSharedCheck_3161_ = (!leanh::lean_is_exclusive(v_x_3134_)) as u8;
                    if v_isSharedCheck_3161_ == 0 {
                        v___x_3153_ = v_x_3134_;
                        v_isShared_3154_ = v_isSharedCheck_3161_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3151_);
                        leanh::lean_dec(v_x_3134_);
                        v___x_3153_ = leanh::lean_box(0);
                        v_isShared_3154_ = v_isSharedCheck_3161_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3138_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3138_, 0, v_val_3137_);
                v___x_3139_ = leanh::lean_unsigned_to_nat(0);
                v___x_3140_ = 0;
                v___x_3141_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
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
                    v_reuseFailAlloc_3149_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3149_, 0, v_a_3142_);
                    v___x_3147_ = v_reuseFailAlloc_3149_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3148_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3148_, 0, v___x_3147_);
                return v___x_3148_;
            }
            4 => {
                v___x_3155_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3155_, 0, v_a_3151_);
                v___x_3156_ = l_Std_Http_Server_new(v_config_3133_, v___x_3155_);
                v_a_3157_ = leanh::lean_ctor_get(v___x_3156_, 0);
                leanh::lean_inc(v_a_3157_);
                leanh::lean_dec_ref(v___x_3156_);
                if v_isShared_3154_ == 0 {
                    leanh::lean_ctor_set(v___x_3153_, 0, v_a_3157_);
                    v___x_3159_ = v___x_3153_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3160_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3160_, 0, v_a_3157_);
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
    mut v___f_3162_: *mut leanh::LeanObject,
    mut v_config_3163_: *mut leanh::LeanObject,
    mut v_x_3164_: *mut leanh::LeanObject,
    mut v___y_3165_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3166_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3166_ =
        l_Std_Http_Server_serve___redArg___lam__29(v___f_3162_, v_config_3163_, v_x_3164_);
    return v_res_3166_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__30(
    mut v___f_3167_: *mut leanh::LeanObject,
    mut v_a_3168_: *mut leanh::LeanObject,
    mut v_x_3169_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_val_3172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: u8 = 0;
    let mut v___x_3176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3180_: u8 = 0;
    let mut v___x_3182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3185_: u8 = 0;
    let mut v___x_3187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3188_: u8 = 0;
    let mut v___x_3189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3198_: u8 = 0;
    let mut v_unused_3199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3169_) == 0 {
                    leanh::lean_dec_ref(v___f_3167_);
                    v_a_3177_ = leanh::lean_ctor_get(v_x_3169_, 0);
                    v_isSharedCheck_3185_ = (!leanh::lean_is_exclusive(v_x_3169_)) as u8;
                    if v_isSharedCheck_3185_ == 0 {
                        v___x_3179_ = v_x_3169_;
                        v_isShared_3180_ = v_isSharedCheck_3185_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3177_);
                        leanh::lean_dec(v_x_3169_);
                        v___x_3179_ = leanh::lean_box(0);
                        v_isShared_3180_ = v_isSharedCheck_3185_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_isSharedCheck_3198_ = (!leanh::lean_is_exclusive(v_x_3169_)) as u8;
                    if v_isSharedCheck_3198_ == 0 {
                        v_unused_3199_ = leanh::lean_ctor_get(v_x_3169_, 0);
                        leanh::lean_dec(v_unused_3199_);
                        v___x_3187_ = v_x_3169_;
                        v_isShared_3188_ = v_isSharedCheck_3198_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_dec(v_x_3169_);
                        v___x_3187_ = leanh::lean_box(0);
                        v_isShared_3188_ = v_isSharedCheck_3198_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3173_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3173_, 0, v_val_3172_);
                v___x_3174_ = leanh::lean_unsigned_to_nat(0);
                v___x_3175_ = 0;
                v___x_3176_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
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
                    v_reuseFailAlloc_3184_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3184_, 0, v_a_3177_);
                    v___x_3182_ = v_reuseFailAlloc_3184_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3183_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3183_, 0, v___x_3182_);
                return v___x_3183_;
            }
            4 => {
                v___x_3189_ = lean_uv_tcp_getsockname(v_a_3168_);
                if leanh::lean_obj_tag(v___x_3189_) == 0 {
                    v_a_3190_ = leanh::lean_ctor_get(v___x_3189_, 0);
                    leanh::lean_inc(v_a_3190_);
                    leanh::lean_dec_ref_known(v___x_3189_, 1);
                    if v_isShared_3188_ == 0 {
                        leanh::lean_ctor_set(v___x_3187_, 0, v_a_3190_);
                        v___x_3192_ = v___x_3187_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3193_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3193_, 0, v_a_3190_);
                        v___x_3192_ = v_reuseFailAlloc_3193_;
                        state = 5;
                        continue;
                    }
                } else {
                    v_a_3194_ = leanh::lean_ctor_get(v___x_3189_, 0);
                    leanh::lean_inc(v_a_3194_);
                    leanh::lean_dec_ref_known(v___x_3189_, 1);
                    if v_isShared_3188_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_3187_, 0);
                        leanh::lean_ctor_set(v___x_3187_, 0, v_a_3194_);
                        v___x_3196_ = v___x_3187_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_3197_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3197_, 0, v_a_3194_);
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
    mut v___f_3200_: *mut leanh::LeanObject,
    mut v_a_3201_: *mut leanh::LeanObject,
    mut v_x_3202_: *mut leanh::LeanObject,
    mut v___y_3203_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3204_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3204_ = l_Std_Http_Server_serve___redArg___lam__30(v___f_3200_, v_a_3201_, v_x_3202_);
    leanh::lean_dec(v_a_3201_);
    return v_res_3204_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__31(
    mut v___f_3205_: *mut leanh::LeanObject,
    mut v_a_3206_: *mut leanh::LeanObject,
    mut v_x_3207_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_val_3210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: u8 = 0;
    let mut v___x_3214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3218_: u8 = 0;
    let mut v___x_3220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3223_: u8 = 0;
    let mut v___x_3225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3226_: u8 = 0;
    let mut v___x_3227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3236_: u8 = 0;
    let mut v_unused_3237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3207_) == 0 {
                    leanh::lean_dec_ref(v___f_3205_);
                    v_a_3215_ = leanh::lean_ctor_get(v_x_3207_, 0);
                    v_isSharedCheck_3223_ = (!leanh::lean_is_exclusive(v_x_3207_)) as u8;
                    if v_isSharedCheck_3223_ == 0 {
                        v___x_3217_ = v_x_3207_;
                        v_isShared_3218_ = v_isSharedCheck_3223_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3215_);
                        leanh::lean_dec(v_x_3207_);
                        v___x_3217_ = leanh::lean_box(0);
                        v_isShared_3218_ = v_isSharedCheck_3223_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_isSharedCheck_3236_ = (!leanh::lean_is_exclusive(v_x_3207_)) as u8;
                    if v_isSharedCheck_3236_ == 0 {
                        v_unused_3237_ = leanh::lean_ctor_get(v_x_3207_, 0);
                        leanh::lean_dec(v_unused_3237_);
                        v___x_3225_ = v_x_3207_;
                        v_isShared_3226_ = v_isSharedCheck_3236_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_dec(v_x_3207_);
                        v___x_3225_ = leanh::lean_box(0);
                        v_isShared_3226_ = v_isSharedCheck_3236_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3211_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3211_, 0, v_val_3210_);
                v___x_3212_ = leanh::lean_unsigned_to_nat(0);
                v___x_3213_ = 0;
                v___x_3214_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
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
                    v_reuseFailAlloc_3222_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3222_, 0, v_a_3215_);
                    v___x_3220_ = v_reuseFailAlloc_3222_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3221_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3221_, 0, v___x_3220_);
                return v___x_3221_;
            }
            4 => {
                v___x_3227_ = lean_uv_tcp_nodelay(v_a_3206_);
                if leanh::lean_obj_tag(v___x_3227_) == 0 {
                    v_a_3228_ = leanh::lean_ctor_get(v___x_3227_, 0);
                    leanh::lean_inc(v_a_3228_);
                    leanh::lean_dec_ref_known(v___x_3227_, 1);
                    if v_isShared_3226_ == 0 {
                        leanh::lean_ctor_set(v___x_3225_, 0, v_a_3228_);
                        v___x_3230_ = v___x_3225_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3231_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3231_, 0, v_a_3228_);
                        v___x_3230_ = v_reuseFailAlloc_3231_;
                        state = 5;
                        continue;
                    }
                } else {
                    v_a_3232_ = leanh::lean_ctor_get(v___x_3227_, 0);
                    leanh::lean_inc(v_a_3232_);
                    leanh::lean_dec_ref_known(v___x_3227_, 1);
                    if v_isShared_3226_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_3225_, 0);
                        leanh::lean_ctor_set(v___x_3225_, 0, v_a_3232_);
                        v___x_3234_ = v___x_3225_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_3235_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3235_, 0, v_a_3232_);
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
    mut v___f_3238_: *mut leanh::LeanObject,
    mut v_a_3239_: *mut leanh::LeanObject,
    mut v_x_3240_: *mut leanh::LeanObject,
    mut v___y_3241_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3242_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3242_ = l_Std_Http_Server_serve___redArg___lam__31(v___f_3238_, v_a_3239_, v_x_3240_);
    leanh::lean_dec(v_a_3239_);
    return v_res_3242_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__32(
    mut v___f_3243_: *mut leanh::LeanObject,
    mut v_a_3244_: *mut leanh::LeanObject,
    mut v_backlog_3245_: u32,
    mut v_x_3246_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_val_3249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3252_: u8 = 0;
    let mut v___x_3253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3257_: u8 = 0;
    let mut v___x_3259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3262_: u8 = 0;
    let mut v___x_3264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3265_: u8 = 0;
    let mut v___x_3266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3275_: u8 = 0;
    let mut v_unused_3276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3246_) == 0 {
                    leanh::lean_dec_ref(v___f_3243_);
                    v_a_3254_ = leanh::lean_ctor_get(v_x_3246_, 0);
                    v_isSharedCheck_3262_ = (!leanh::lean_is_exclusive(v_x_3246_)) as u8;
                    if v_isSharedCheck_3262_ == 0 {
                        v___x_3256_ = v_x_3246_;
                        v_isShared_3257_ = v_isSharedCheck_3262_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3254_);
                        leanh::lean_dec(v_x_3246_);
                        v___x_3256_ = leanh::lean_box(0);
                        v_isShared_3257_ = v_isSharedCheck_3262_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_isSharedCheck_3275_ = (!leanh::lean_is_exclusive(v_x_3246_)) as u8;
                    if v_isSharedCheck_3275_ == 0 {
                        v_unused_3276_ = leanh::lean_ctor_get(v_x_3246_, 0);
                        leanh::lean_dec(v_unused_3276_);
                        v___x_3264_ = v_x_3246_;
                        v_isShared_3265_ = v_isSharedCheck_3275_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_dec(v_x_3246_);
                        v___x_3264_ = leanh::lean_box(0);
                        v_isShared_3265_ = v_isSharedCheck_3275_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3250_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3250_, 0, v_val_3249_);
                v___x_3251_ = leanh::lean_unsigned_to_nat(0);
                v___x_3252_ = 0;
                v___x_3253_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
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
                    v_reuseFailAlloc_3261_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3261_, 0, v_a_3254_);
                    v___x_3259_ = v_reuseFailAlloc_3261_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3260_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3260_, 0, v___x_3259_);
                return v___x_3260_;
            }
            4 => {
                v___x_3266_ = lean_uv_tcp_listen(v_a_3244_, v_backlog_3245_);
                if leanh::lean_obj_tag(v___x_3266_) == 0 {
                    v_a_3267_ = leanh::lean_ctor_get(v___x_3266_, 0);
                    leanh::lean_inc(v_a_3267_);
                    leanh::lean_dec_ref_known(v___x_3266_, 1);
                    if v_isShared_3265_ == 0 {
                        leanh::lean_ctor_set(v___x_3264_, 0, v_a_3267_);
                        v___x_3269_ = v___x_3264_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3270_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3270_, 0, v_a_3267_);
                        v___x_3269_ = v_reuseFailAlloc_3270_;
                        state = 5;
                        continue;
                    }
                } else {
                    v_a_3271_ = leanh::lean_ctor_get(v___x_3266_, 0);
                    leanh::lean_inc(v_a_3271_);
                    leanh::lean_dec_ref_known(v___x_3266_, 1);
                    if v_isShared_3265_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_3264_, 0);
                        leanh::lean_ctor_set(v___x_3264_, 0, v_a_3271_);
                        v___x_3273_ = v___x_3264_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_3274_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3274_, 0, v_a_3271_);
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
    mut v___f_3277_: *mut leanh::LeanObject,
    mut v_a_3278_: *mut leanh::LeanObject,
    mut v_backlog_3279_: *mut leanh::LeanObject,
    mut v_x_3280_: *mut leanh::LeanObject,
    mut v___y_3281_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_backlog_boxed_3282_: u32 = 0;
    let mut v_res_3283_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_backlog_boxed_3282_ = leanh::lean_unbox_uint32(v_backlog_3279_);
    leanh::lean_dec(v_backlog_3279_);
    v_res_3283_ = l_Std_Http_Server_serve___redArg___lam__32(
        v___f_3277_,
        v_a_3278_,
        v_backlog_boxed_3282_,
        v_x_3280_,
    );
    leanh::lean_dec(v_a_3278_);
    return v_res_3283_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__33(
    mut v___f_3284_: *mut leanh::LeanObject,
    mut v___x_3285_: *mut leanh::LeanObject,
    mut v___f_3286_: *mut leanh::LeanObject,
    mut v___f_3287_: *mut leanh::LeanObject,
    mut v_inst_3288_: *mut leanh::LeanObject,
    mut v_handler_3289_: *mut leanh::LeanObject,
    mut v_config_3290_: *mut leanh::LeanObject,
    mut v___f_3291_: *mut leanh::LeanObject,
    mut v___f_3292_: *mut leanh::LeanObject,
    mut v___f_3293_: *mut leanh::LeanObject,
    mut v___f_3294_: *mut leanh::LeanObject,
    mut v___f_3295_: *mut leanh::LeanObject,
    mut v___f_3296_: *mut leanh::LeanObject,
    mut v_backlog_3297_: u32,
    mut v_addr_3298_: *mut leanh::LeanObject,
    mut v_x_3299_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_3301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3304_: u8 = 0;
    let mut v___x_3306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3309_: u8 = 0;
    let mut v_a_3310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3313_: u8 = 0;
    let mut v___f_3314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: u8 = 0;
    let mut v___x_3325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3335_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3299_) == 0 {
                    leanh::lean_dec_ref(v___f_3296_);
                    leanh::lean_dec_ref(v___f_3295_);
                    leanh::lean_dec_ref(v___f_3294_);
                    leanh::lean_dec_ref(v___f_3293_);
                    leanh::lean_dec_ref(v___f_3292_);
                    leanh::lean_dec_ref(v___f_3291_);
                    leanh::lean_dec_ref(v_config_3290_);
                    leanh::lean_dec(v_handler_3289_);
                    leanh::lean_dec_ref(v_inst_3288_);
                    leanh::lean_dec_ref(v___f_3287_);
                    leanh::lean_dec_ref(v___f_3286_);
                    leanh::lean_dec_ref(v___x_3285_);
                    leanh::lean_dec_ref(v___f_3284_);
                    v_a_3301_ = leanh::lean_ctor_get(v_x_3299_, 0);
                    v_isSharedCheck_3309_ = (!leanh::lean_is_exclusive(v_x_3299_)) as u8;
                    if v_isSharedCheck_3309_ == 0 {
                        v___x_3303_ = v_x_3299_;
                        v_isShared_3304_ = v_isSharedCheck_3309_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3301_);
                        leanh::lean_dec(v_x_3299_);
                        v___x_3303_ = leanh::lean_box(0);
                        v_isShared_3304_ = v_isSharedCheck_3309_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3310_ = leanh::lean_ctor_get(v_x_3299_, 0);
                    v_isSharedCheck_3335_ = (!leanh::lean_is_exclusive(v_x_3299_)) as u8;
                    if v_isSharedCheck_3335_ == 0 {
                        v___x_3312_ = v_x_3299_;
                        v_isShared_3313_ = v_isSharedCheck_3335_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3310_);
                        leanh::lean_dec(v_x_3299_);
                        v___x_3312_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_3308_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3308_, 0, v_a_3301_);
                    v___x_3306_ = v_reuseFailAlloc_3308_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3307_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3307_, 0, v___x_3306_);
                return v___x_3307_;
            }
            3 => {
                leanh::lean_inc_n(v_a_3310_, 4);
                leanh::lean_inc_ref(v_config_3290_);
                v___f_3314_ = leanh::lean_alloc_closure(
                    l_Std_Http_Server_serve___redArg___lam__28___boxed as *mut core::ffi::c_void,
                    16,
                    14,
                );
                leanh::lean_closure_set(v___f_3314_, 0, v___f_3284_);
                leanh::lean_closure_set(v___f_3314_, 1, v___x_3285_);
                leanh::lean_closure_set(v___f_3314_, 2, v___f_3286_);
                leanh::lean_closure_set(v___f_3314_, 3, v___f_3287_);
                leanh::lean_closure_set(v___f_3314_, 4, v_inst_3288_);
                leanh::lean_closure_set(v___f_3314_, 5, v_handler_3289_);
                leanh::lean_closure_set(v___f_3314_, 6, v_config_3290_);
                leanh::lean_closure_set(v___f_3314_, 7, v___f_3291_);
                leanh::lean_closure_set(v___f_3314_, 8, v_a_3310_);
                leanh::lean_closure_set(v___f_3314_, 9, v___f_3292_);
                leanh::lean_closure_set(v___f_3314_, 10, v___f_3293_);
                leanh::lean_closure_set(v___f_3314_, 11, v___f_3294_);
                leanh::lean_closure_set(v___f_3314_, 12, v___f_3295_);
                leanh::lean_closure_set(v___f_3314_, 13, v___f_3296_);
                v___f_3315_ = leanh::lean_alloc_closure(
                    l_Std_Http_Server_serve___redArg___lam__29___boxed as *mut core::ffi::c_void,
                    4,
                    2,
                );
                leanh::lean_closure_set(v___f_3315_, 0, v___f_3314_);
                leanh::lean_closure_set(v___f_3315_, 1, v_config_3290_);
                v___f_3316_ = leanh::lean_alloc_closure(
                    l_Std_Http_Server_serve___redArg___lam__30___boxed as *mut core::ffi::c_void,
                    4,
                    2,
                );
                leanh::lean_closure_set(v___f_3316_, 0, v___f_3315_);
                leanh::lean_closure_set(v___f_3316_, 1, v_a_3310_);
                v___f_3317_ = leanh::lean_alloc_closure(
                    l_Std_Http_Server_serve___redArg___lam__31___boxed as *mut core::ffi::c_void,
                    4,
                    2,
                );
                leanh::lean_closure_set(v___f_3317_, 0, v___f_3316_);
                leanh::lean_closure_set(v___f_3317_, 1, v_a_3310_);
                v___x_3318_ = leanh::lean_box_uint32(v_backlog_3297_);
                v___f_3319_ = leanh::lean_alloc_closure(
                    l_Std_Http_Server_serve___redArg___lam__32___boxed as *mut core::ffi::c_void,
                    5,
                    3,
                );
                leanh::lean_closure_set(v___f_3319_, 0, v___f_3317_);
                leanh::lean_closure_set(v___f_3319_, 1, v_a_3310_);
                leanh::lean_closure_set(v___f_3319_, 2, v___x_3318_);
                v___x_3326_ = lean_uv_tcp_bind(v_a_3310_, v_addr_3298_);
                leanh::lean_dec(v_a_3310_);
                if leanh::lean_obj_tag(v___x_3326_) == 0 {
                    v_a_3327_ = leanh::lean_ctor_get(v___x_3326_, 0);
                    leanh::lean_inc(v_a_3327_);
                    leanh::lean_dec_ref_known(v___x_3326_, 1);
                    if v_isShared_3313_ == 0 {
                        leanh::lean_ctor_set(v___x_3312_, 0, v_a_3327_);
                        v___x_3329_ = v___x_3312_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3330_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3330_, 0, v_a_3327_);
                        v___x_3329_ = v_reuseFailAlloc_3330_;
                        state = 5;
                        continue;
                    }
                } else {
                    v_a_3331_ = leanh::lean_ctor_get(v___x_3326_, 0);
                    leanh::lean_inc(v_a_3331_);
                    leanh::lean_dec_ref_known(v___x_3326_, 1);
                    if v_isShared_3313_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_3312_, 0);
                        leanh::lean_ctor_set(v___x_3312_, 0, v_a_3331_);
                        v___x_3333_ = v___x_3312_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_3334_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3334_, 0, v_a_3331_);
                        v___x_3333_ = v_reuseFailAlloc_3334_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                v___x_3322_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3322_, 0, v_val_3321_);
                v___x_3323_ = leanh::lean_unsigned_to_nat(0);
                v___x_3324_ = 0;
                v___x_3325_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
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
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3336_: *mut leanh::LeanObject = *_args.add(0);
    let mut v___x_3337_: *mut leanh::LeanObject = *_args.add(1);
    let mut v___f_3338_: *mut leanh::LeanObject = *_args.add(2);
    let mut v___f_3339_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_inst_3340_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_handler_3341_: *mut leanh::LeanObject = *_args.add(5);
    let mut v_config_3342_: *mut leanh::LeanObject = *_args.add(6);
    let mut v___f_3343_: *mut leanh::LeanObject = *_args.add(7);
    let mut v___f_3344_: *mut leanh::LeanObject = *_args.add(8);
    let mut v___f_3345_: *mut leanh::LeanObject = *_args.add(9);
    let mut v___f_3346_: *mut leanh::LeanObject = *_args.add(10);
    let mut v___f_3347_: *mut leanh::LeanObject = *_args.add(11);
    let mut v___f_3348_: *mut leanh::LeanObject = *_args.add(12);
    let mut v_backlog_3349_: *mut leanh::LeanObject = *_args.add(13);
    let mut v_addr_3350_: *mut leanh::LeanObject = *_args.add(14);
    let mut v_x_3351_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_3352_: *mut leanh::LeanObject = *_args.add(16);
    let mut v_backlog_boxed_3353_: u32 = 0;
    let mut v_res_3354_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_backlog_boxed_3353_ = leanh::lean_unbox_uint32(v_backlog_3349_);
    leanh::lean_dec(v_backlog_3349_);
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
    leanh::lean_dec_ref(v_addr_3350_);
    return v_res_3354_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg(
    mut v_inst_3361_: *mut leanh::LeanObject,
    mut v_addr_3362_: *mut leanh::LeanObject,
    mut v_handler_3363_: *mut leanh::LeanObject,
    mut v_config_3364_: *mut leanh::LeanObject,
    mut v_backlog_3365_: u32,
) -> *mut leanh::LeanObject {
    let mut v___f_3367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3383_: u8 = 0;
    let mut v___x_3384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3389_: u8 = 0;
    let mut v___x_3391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3393_: u8 = 0;
    let mut v_a_3394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3397_: u8 = 0;
    let mut v___x_3399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3400_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                v___x_3377_ = leanh::lean_box_uint32(v_backlog_3365_);
                v___f_3378_ = leanh::lean_alloc_closure(
                    l_Std_Http_Server_serve___redArg___lam__33___boxed as *mut core::ffi::c_void,
                    17,
                    15,
                );
                leanh::lean_closure_set(v___f_3378_, 0, v___f_3374_);
                leanh::lean_closure_set(v___f_3378_, 1, v___x_3376_);
                leanh::lean_closure_set(v___f_3378_, 2, v___f_3369_);
                leanh::lean_closure_set(v___f_3378_, 3, v___f_3371_);
                leanh::lean_closure_set(v___f_3378_, 4, v_inst_3361_);
                leanh::lean_closure_set(v___f_3378_, 5, v_handler_3363_);
                leanh::lean_closure_set(v___f_3378_, 6, v_config_3364_);
                leanh::lean_closure_set(v___f_3378_, 7, v___f_3370_);
                leanh::lean_closure_set(v___f_3378_, 8, v___f_3373_);
                leanh::lean_closure_set(v___f_3378_, 9, v___f_3372_);
                leanh::lean_closure_set(v___f_3378_, 10, v___f_3368_);
                leanh::lean_closure_set(v___f_3378_, 11, v___f_3375_);
                leanh::lean_closure_set(v___f_3378_, 12, v___f_3367_);
                leanh::lean_closure_set(v___f_3378_, 13, v___x_3377_);
                leanh::lean_closure_set(v___f_3378_, 14, v_addr_3362_);
                v___x_3385_ = lean_uv_tcp_new();
                if leanh::lean_obj_tag(v___x_3385_) == 0 {
                    v_a_3386_ = leanh::lean_ctor_get(v___x_3385_, 0);
                    v_isSharedCheck_3393_ = (!leanh::lean_is_exclusive(v___x_3385_)) as u8;
                    if v_isSharedCheck_3393_ == 0 {
                        v___x_3388_ = v___x_3385_;
                        v_isShared_3389_ = v_isSharedCheck_3393_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3386_);
                        leanh::lean_dec(v___x_3385_);
                        v___x_3388_ = leanh::lean_box(0);
                        v_isShared_3389_ = v_isSharedCheck_3393_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_3394_ = leanh::lean_ctor_get(v___x_3385_, 0);
                    v_isSharedCheck_3401_ = (!leanh::lean_is_exclusive(v___x_3385_)) as u8;
                    if v_isSharedCheck_3401_ == 0 {
                        v___x_3396_ = v___x_3385_;
                        v_isShared_3397_ = v_isSharedCheck_3401_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3394_);
                        leanh::lean_dec(v___x_3385_);
                        v___x_3396_ = leanh::lean_box(0);
                        v_isShared_3397_ = v_isSharedCheck_3401_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3381_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3381_, 0, v_val_3380_);
                v___x_3382_ = leanh::lean_unsigned_to_nat(0);
                v___x_3383_ = 0;
                v___x_3384_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_3382_,
                    v___x_3383_,
                    v___x_3381_,
                    v___f_3378_,
                );
                return v___x_3384_;
            }
            2 => {
                if v_isShared_3389_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3388_, 1);
                    v___x_3391_ = v___x_3388_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3392_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3392_, 0, v_a_3386_);
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
                    leanh::lean_ctor_set_tag(v___x_3396_, 0);
                    v___x_3399_ = v___x_3396_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3400_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3400_, 0, v_a_3394_);
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
    mut v_inst_3402_: *mut leanh::LeanObject,
    mut v_addr_3403_: *mut leanh::LeanObject,
    mut v_handler_3404_: *mut leanh::LeanObject,
    mut v_config_3405_: *mut leanh::LeanObject,
    mut v_backlog_3406_: *mut leanh::LeanObject,
    mut v_a_3407_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_backlog_boxed_3408_: u32 = 0;
    let mut v_res_3409_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_backlog_boxed_3408_ = leanh::lean_unbox_uint32(v_backlog_3406_);
    leanh::lean_dec(v_backlog_3406_);
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
    mut v_00_u03c3_3410_: *mut leanh::LeanObject,
    mut v_inst_3411_: *mut leanh::LeanObject,
    mut v_addr_3412_: *mut leanh::LeanObject,
    mut v_handler_3413_: *mut leanh::LeanObject,
    mut v_config_3414_: *mut leanh::LeanObject,
    mut v_backlog_3415_: u32,
) -> *mut leanh::LeanObject {
    let mut v___x_3417_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03c3_3418_: *mut leanh::LeanObject,
    mut v_inst_3419_: *mut leanh::LeanObject,
    mut v_addr_3420_: *mut leanh::LeanObject,
    mut v_handler_3421_: *mut leanh::LeanObject,
    mut v_config_3422_: *mut leanh::LeanObject,
    mut v_backlog_3423_: *mut leanh::LeanObject,
    mut v_a_3424_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_backlog_boxed_3425_: u32 = 0;
    let mut v_res_3426_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_backlog_boxed_3425_ = leanh::lean_unbox_uint32(v_backlog_3423_);
    leanh::lean_dec(v_backlog_3423_);
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
pub unsafe fn runtime_initialize_Std_Http_Server(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Async(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Async_TCP(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Sync_CancellationToken(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Sync_Semaphore(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Server_Config(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Server_Handler(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Server_Connection(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Http_Server(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Http_Server(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Async(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Async_TCP(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Sync_CancellationToken(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Sync_Semaphore(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Http_Server_Config(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Http_Server_Handler(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Http_Server_Connection(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Server(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Http_Server(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Http_Server(builtin);
}