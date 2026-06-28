// Lean compiler output
// Module: Std.Http.Server
// Imports: Std.Async Std.Async.TCP Std.Sync.CancellationToken Std.Sync.Semaphore Std.Http.Server.Config Std.Http.Server.Handler Std.Http.Server.Connection
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
use crate::lean_imports_rs::Init::Core::lean_task_map;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq, lean_nat_sub,
};
use crate::lean_imports_rs::Init::System::IO::lean_io_as_task;
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Std::Internal::UV::TCP::{
    lean_uv_tcp_bind, lean_uv_tcp_getpeername, lean_uv_tcp_getsockname, lean_uv_tcp_listen,
    lean_uv_tcp_new, lean_uv_tcp_nodelay,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_box, lean_box_uint32, lean_closure_set, lean_ctor_get,
    lean_ctor_set, lean_ctor_set_tag, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object,
    lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unbox,
    lean_unbox_uint32, lean_unsigned_to_nat,
};
pub static l_Std_Http_Server_waitShutdown___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Http_Server_waitShutdown___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Server_waitShutdown___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Server_waitShutdown___closed__0_value) as *mut LeanObject;
pub static l_Std_Http_Server_waitShutdown___closed__1_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Http_Server_waitShutdown___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_Server_waitShutdown___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Http_Server_waitShutdown___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Server_waitShutdown___closed__1_value) as *mut LeanObject;
pub static l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__0_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__0_value) as *mut LeanObject;
pub static l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__0_value) as *mut LeanObject] };
static mut l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__1_value) as *mut LeanObject;
pub static l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__0_value
) as *mut LeanObject;
pub static l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Std_Async_ContextAsync_instMonadLiftBaseIO___lam__0___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__1_value
) as *mut LeanObject;
pub static l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__2_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_instMonadLiftT___lam__0___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__2_value
) as *mut LeanObject;
pub static l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__3_value: LeanClosureObject<2> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*2) as u16, other: 0, tag: 245 }, m_fun: l_instMonadLiftTOfMonadLift___redArg___lam__0 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 2, m_objs: [core::ptr::addr_of!(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__1_value) as *mut LeanObject] };
static mut l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__3_value
) as *mut LeanObject;
pub static l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__4_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Std_Async_ContextAsync_instMonadFinally___lam__1___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__4_value
) as *mut LeanObject;
pub static l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__5_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__1___boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__5_value
) as *mut LeanObject;
pub static l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__6_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__5___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__6_value
) as *mut LeanObject;
pub static l_Std_Http_Server_serve___redArg___lam__4___closed__0_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Std_Http_Server_serve___redArg___lam__4___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Server_serve___redArg___lam__4___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Http_Server_serve___redArg___lam__4___closed__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_Server_serve___redArg___lam__4___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Http_Server_serve___redArg___lam__4___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Server_serve___redArg___lam__4___closed__1_value)
        as *mut LeanObject;
static mut l_Std_Http_Server_serve___redArg___lam__19___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Server_serve___redArg___lam__19___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Http_Server_serve___redArg___lam__19___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Server_serve___redArg___lam__19___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Http_Server_serve___redArg___lam__19___closed__2_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Http_Extensions_compareName___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Server_serve___redArg___lam__19___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Server_serve___redArg___lam__19___closed__2_value)
        as *mut LeanObject;
pub static l_Std_Http_Server_serve___redArg___lam__28___closed__0_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Http_Server_serve___redArg___lam__10___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Std_Http_Server_serve___redArg___lam__28___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Server_serve___redArg___lam__28___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Http_Server_serve___redArg___lam__28___closed__1_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Http_Server_serve___redArg___lam__6___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Std_Http_Server_serve___redArg___lam__28___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Server_serve___redArg___lam__28___closed__1_value)
        as *mut LeanObject;
pub static l_Std_Http_Server_serve___redArg___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Http_Server_serve___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Server_serve___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Server_serve___redArg___closed__0_value) as *mut LeanObject;
pub static l_Std_Http_Server_serve___redArg___closed__1_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Http_Server_serve___redArg___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Server_serve___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Server_serve___redArg___closed__1_value) as *mut LeanObject;
pub static l_Std_Http_Server_serve___redArg___closed__2_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Http_Server_serve___redArg___lam__3___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Server_serve___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Server_serve___redArg___closed__2_value) as *mut LeanObject;
pub static l_Std_Http_Server_serve___redArg___closed__3_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Http_Server_serve___redArg___lam__4___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Server_serve___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Server_serve___redArg___closed__3_value) as *mut LeanObject;
pub static l_Std_Http_Server_serve___redArg___closed__4_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Http_Server_serve___redArg___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Server_serve___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Server_serve___redArg___closed__4_value) as *mut LeanObject;
pub static l_Std_Http_Server_serve___redArg___closed__5_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Http_Server_serve___redArg___lam__5___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Server_serve___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Server_serve___redArg___closed__5_value) as *mut LeanObject;
pub unsafe fn l_Std_Http_Server_new(
    mut v_config_1714_: *mut LeanObject,
    mut v_localAddr_1715_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_connectionLimit_1721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxConnections_1726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: u8 = 0;
    let mut v___x_1728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1717_ = l_Std_CancellationContext_new();
                v___x_1718_ = lean_unsigned_to_nat(0);
                v___x_1719_ = l_Std_Mutex_new___redArg(v___x_1718_);
                v_maxConnections_1726_ = lean_ctor_get(v_config_1714_, 0);
                v___x_1727_ = lean_nat_dec_eq(v_maxConnections_1726_, v___x_1718_);
                if v___x_1727_ == 0 {
                    lean_inc(v_maxConnections_1726_);
                    v___x_1728_ = l_Std_Semaphore_new(v_maxConnections_1726_);
                    v___x_1729_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1729_, 0, v___x_1728_);
                    v_connectionLimit_1721_ = v___x_1729_;
                    state = 1;
                    continue;
                } else {
                    v___x_1730_ = lean_box(0);
                    v_connectionLimit_1721_ = v___x_1730_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1722_ = lean_box(0);
                v___x_1723_ = l_Std_CloseableChannel_new___redArg(v___x_1722_);
                v___x_1724_ = lean_alloc_ctor(0, 6, (0) as u32);
                lean_ctor_set(v___x_1724_, 0, v___x_1717_);
                lean_ctor_set(v___x_1724_, 1, v___x_1719_);
                lean_ctor_set(v___x_1724_, 2, v_connectionLimit_1721_);
                lean_ctor_set(v___x_1724_, 3, v___x_1723_);
                lean_ctor_set(v___x_1724_, 4, v_config_1714_);
                lean_ctor_set(v___x_1724_, 5, v_localAddr_1715_);
                v___x_1725_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1725_, 0, v___x_1724_);
                return v___x_1725_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Server_new___boxed(
    mut v_config_1731_: *mut LeanObject,
    mut v_localAddr_1732_: *mut LeanObject,
    mut v_a_1733_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1734_: *mut LeanObject = core::ptr::null_mut();
    v_res_1734_ = l_Std_Http_Server_new(v_config_1731_, v_localAddr_1732_);
    return v_res_1734_;
}
pub unsafe fn l_Std_Http_Server_shutdown(mut v_s_1735_: *mut LeanObject) -> *mut LeanObject {
    let mut v_context_1737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut LeanObject = core::ptr::null_mut();
    v_context_1737_ = lean_ctor_get(v_s_1735_, 0);
    lean_inc_ref(v_context_1737_);
    lean_dec_ref(v_s_1735_);
    v___x_1738_ = lean_box(1);
    v___x_1739_ = l_Std_CancellationContext_cancel(v_context_1737_, v___x_1738_);
    v___x_1740_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1740_, 0, v___x_1739_);
    v___x_1741_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1741_, 0, v___x_1740_);
    return v___x_1741_;
}
pub unsafe fn l_Std_Http_Server_shutdown___boxed(
    mut v_s_1742_: *mut LeanObject,
    mut v_a_1743_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1744_: *mut LeanObject = core::ptr::null_mut();
    v_res_1744_ = l_Std_Http_Server_shutdown(v_s_1742_);
    return v_res_1744_;
}
pub unsafe fn l_Std_Http_Server_waitShutdown___lam__0(
    mut v_a_1745_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1746_: *mut LeanObject = core::ptr::null_mut();
    v___x_1746_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1746_, 0, v_a_1745_);
    return v___x_1746_;
}
pub unsafe fn l_Std_Http_Server_waitShutdown___lam__1(
    mut v___f_1747_: *mut LeanObject,
    mut v_x_1748_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1753_: u8 = 0;
    let mut v___x_1755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1758_: u8 = 0;
    let mut v_a_1759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: u8 = 0;
    let mut v___x_1762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1748_) == 0 {
                    lean_dec_ref(v___f_1747_);
                    v_a_1750_ = lean_ctor_get(v_x_1748_, 0);
                    v_isSharedCheck_1758_ = (!lean_is_exclusive(v_x_1748_)) as u8;
                    if v_isSharedCheck_1758_ == 0 {
                        v___x_1752_ = v_x_1748_;
                        v_isShared_1753_ = v_isSharedCheck_1758_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1750_);
                        lean_dec(v_x_1748_);
                        v___x_1752_ = lean_box(0);
                        v_isShared_1753_ = v_isSharedCheck_1758_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1759_ = lean_ctor_get(v_x_1748_, 0);
                    lean_inc(v_a_1759_);
                    lean_dec_ref_known(v_x_1748_, 1);
                    v___x_1760_ = lean_unsigned_to_nat(0);
                    v___x_1761_ = 0;
                    v___x_1762_ = lean_task_map(v___f_1747_, v_a_1759_, v___x_1760_, v___x_1761_);
                    v___x_1763_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1763_, 0, v___x_1762_);
                    return v___x_1763_;
                }
            }
            1 => {
                if v_isShared_1753_ == 0 {
                    v___x_1755_ = v___x_1752_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1757_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1757_, 0, v_a_1750_);
                    v___x_1755_ = v_reuseFailAlloc_1757_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1756_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1756_, 0, v___x_1755_);
                return v___x_1756_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Server_waitShutdown___lam__1___boxed(
    mut v___f_1764_: *mut LeanObject,
    mut v_x_1765_: *mut LeanObject,
    mut v___y_1766_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1767_: *mut LeanObject = core::ptr::null_mut();
    v_res_1767_ = l_Std_Http_Server_waitShutdown___lam__1(v___f_1764_, v_x_1765_);
    return v_res_1767_;
}
pub unsafe fn l_Std_Http_Server_waitShutdown(mut v_s_1771_: *mut LeanObject) -> *mut LeanObject {
    let mut v_shutdownPromise_1773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: u8 = 0;
    let mut v___x_1781_: *mut LeanObject = core::ptr::null_mut();
    v_shutdownPromise_1773_ = lean_ctor_get(v_s_1771_, 3);
    lean_inc_ref(v_shutdownPromise_1773_);
    lean_dec_ref(v_s_1771_);
    v___x_1774_ = lean_box(0);
    v___x_1775_ = l_Std_Channel_recv___redArg(v___x_1774_, v_shutdownPromise_1773_);
    v___f_1776_ = l_Std_Http_Server_waitShutdown___closed__1;
    v___x_1777_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1777_, 0, v___x_1775_);
    v___x_1778_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1778_, 0, v___x_1777_);
    v___x_1779_ = lean_unsigned_to_nat(0);
    v___x_1780_ = 0;
    v___x_1781_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_1779_,
        v___x_1780_,
        v___x_1778_,
        v___f_1776_,
    );
    return v___x_1781_;
}
pub unsafe fn l_Std_Http_Server_waitShutdown___boxed(
    mut v_s_1782_: *mut LeanObject,
    mut v_a_1783_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1784_: *mut LeanObject = core::ptr::null_mut();
    v_res_1784_ = l_Std_Http_Server_waitShutdown(v_s_1782_);
    return v_res_1784_;
}
pub unsafe fn l_Std_Http_Server_waitShutdownSelector(
    mut v_s_1785_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_shutdownPromise_1786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut LeanObject = core::ptr::null_mut();
    v_shutdownPromise_1786_ = lean_ctor_get(v_s_1785_, 3);
    lean_inc_ref(v_shutdownPromise_1786_);
    lean_dec_ref(v_s_1785_);
    v___x_1787_ = lean_box(0);
    v___x_1788_ = l_Std_Channel_recvSelector___redArg(v___x_1787_, v_shutdownPromise_1786_);
    return v___x_1788_;
}
pub unsafe fn l_Std_Http_Server_shutdownAndWait___lam__2(
    mut v_shutdownPromise_1789_: *mut LeanObject,
    mut v___f_1790_: *mut LeanObject,
    mut v_x_1791_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1796_: u8 = 0;
    let mut v___x_1797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: u8 = 0;
    let mut v___x_1804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1806_: u8 = 0;
    let mut v_unused_1807_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1791_) == 0 {
                    lean_dec_ref(v___f_1790_);
                    lean_dec_ref(v_shutdownPromise_1789_);
                    v___x_1793_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1793_, 0, v_x_1791_);
                    return v___x_1793_;
                } else {
                    v_isSharedCheck_1806_ = (!lean_is_exclusive(v_x_1791_)) as u8;
                    if v_isSharedCheck_1806_ == 0 {
                        v_unused_1807_ = lean_ctor_get(v_x_1791_, 0);
                        lean_dec(v_unused_1807_);
                        v___x_1795_ = v_x_1791_;
                        v_isShared_1796_ = v_isSharedCheck_1806_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_x_1791_);
                        v___x_1795_ = lean_box(0);
                        v_isShared_1796_ = v_isSharedCheck_1806_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1797_ = lean_box(0);
                v___x_1798_ = l_Std_Channel_recv___redArg(v___x_1797_, v_shutdownPromise_1789_);
                if v_isShared_1796_ == 0 {
                    lean_ctor_set(v___x_1795_, 0, v___x_1798_);
                    v___x_1800_ = v___x_1795_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1805_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1805_, 0, v___x_1798_);
                    v___x_1800_ = v_reuseFailAlloc_1805_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1801_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1801_, 0, v___x_1800_);
                v___x_1802_ = lean_unsigned_to_nat(0);
                v___x_1803_ = 0;
                v___x_1804_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
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
    mut v_shutdownPromise_1808_: *mut LeanObject,
    mut v___f_1809_: *mut LeanObject,
    mut v_x_1810_: *mut LeanObject,
    mut v___y_1811_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1812_: *mut LeanObject = core::ptr::null_mut();
    v_res_1812_ =
        l_Std_Http_Server_shutdownAndWait___lam__2(v_shutdownPromise_1808_, v___f_1809_, v_x_1810_);
    return v_res_1812_;
}
pub unsafe fn l_Std_Http_Server_shutdownAndWait(mut v_s_1813_: *mut LeanObject) -> *mut LeanObject {
    let mut v_context_1815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_shutdownPromise_1816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: u8 = 0;
    let mut v___x_1825_: *mut LeanObject = core::ptr::null_mut();
    v_context_1815_ = lean_ctor_get(v_s_1813_, 0);
    lean_inc_ref(v_context_1815_);
    v_shutdownPromise_1816_ = lean_ctor_get(v_s_1813_, 3);
    lean_inc_ref(v_shutdownPromise_1816_);
    lean_dec_ref(v_s_1813_);
    v___x_1817_ = lean_box(1);
    v___x_1818_ = l_Std_CancellationContext_cancel(v_context_1815_, v___x_1817_);
    v___f_1819_ = l_Std_Http_Server_waitShutdown___closed__1;
    v___f_1820_ = lean_alloc_closure(
        l_Std_Http_Server_shutdownAndWait___lam__2___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_1820_, 0, v_shutdownPromise_1816_);
    lean_closure_set(v___f_1820_, 1, v___f_1819_);
    v___x_1821_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1821_, 0, v___x_1818_);
    v___x_1822_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1822_, 0, v___x_1821_);
    v___x_1823_ = lean_unsigned_to_nat(0);
    v___x_1824_ = 0;
    v___x_1825_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_1823_,
        v___x_1824_,
        v___x_1822_,
        v___f_1820_,
    );
    return v___x_1825_;
}
pub unsafe fn l_Std_Http_Server_shutdownAndWait___boxed(
    mut v_s_1826_: *mut LeanObject,
    mut v_a_1827_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1828_: *mut LeanObject = core::ptr::null_mut();
    v_res_1828_ = l_Std_Http_Server_shutdownAndWait(v_s_1826_);
    return v_res_1828_;
}
pub unsafe fn l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0(
    mut v___y_1833_: *mut LeanObject,
    mut v___y_1834_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut LeanObject = core::ptr::null_mut();
    v___x_1836_ = lean_st_ref_take(v___y_1833_);
    v___x_1837_ = lean_unsigned_to_nat(1);
    v___x_1838_ = lean_nat_add(v___x_1836_, v___x_1837_);
    lean_dec(v___x_1836_);
    v___x_1839_ = lean_st_ref_set(v___y_1833_, v___x_1838_);
    v___x_1840_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__1;
    return v___x_1840_;
}
pub unsafe fn l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___boxed(
    mut v___y_1841_: *mut LeanObject,
    mut v___y_1842_: *mut LeanObject,
    mut v___y_1843_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1844_: *mut LeanObject = core::ptr::null_mut();
    v_res_1844_ =
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0(
            v___y_1841_,
            v___y_1842_,
        );
    lean_dec_ref(v___y_1842_);
    lean_dec(v___y_1841_);
    return v_res_1844_;
}
pub unsafe fn l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__1(
    mut v___y_1845_: *mut LeanObject,
    mut v___y_1846_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: *mut LeanObject = core::ptr::null_mut();
    v___x_1848_ = lean_st_ref_take(v___y_1845_);
    v___x_1849_ = lean_unsigned_to_nat(1);
    v___x_1850_ = lean_nat_sub(v___x_1848_, v___x_1849_);
    lean_dec(v___x_1848_);
    v___x_1851_ = lean_st_ref_set(v___y_1845_, v___x_1850_);
    v___x_1852_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__1;
    return v___x_1852_;
}
pub unsafe fn l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__1___boxed(
    mut v___y_1853_: *mut LeanObject,
    mut v___y_1854_: *mut LeanObject,
    mut v___y_1855_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1856_: *mut LeanObject = core::ptr::null_mut();
    v_res_1856_ =
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__1(
            v___y_1853_,
            v___y_1854_,
        );
    lean_dec_ref(v___y_1854_);
    lean_dec(v___y_1853_);
    return v_res_1856_;
}
pub unsafe fn l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__2(
    mut v_a_1857_: *mut LeanObject,
    mut v_shutdownPromise_1858_: *mut LeanObject,
    mut v_x_1859_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1866_: u8 = 0;
    let mut v___x_1868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1871_: u8 = 0;
    let mut v_a_1872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: u8 = 0;
    let mut v___x_1875_: u8 = 0;
    let mut v___x_1876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1859_) == 0 {
                    lean_dec_ref(v_shutdownPromise_1858_);
                    v_a_1863_ = lean_ctor_get(v_x_1859_, 0);
                    v_isSharedCheck_1871_ = (!lean_is_exclusive(v_x_1859_)) as u8;
                    if v_isSharedCheck_1871_ == 0 {
                        v___x_1865_ = v_x_1859_;
                        v_isShared_1866_ = v_isSharedCheck_1871_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_1863_);
                        lean_dec(v_x_1859_);
                        v___x_1865_ = lean_box(0);
                        v_isShared_1866_ = v_isSharedCheck_1871_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_1872_ = lean_ctor_get(v_x_1859_, 0);
                    lean_inc(v_a_1872_);
                    lean_dec_ref_known(v_x_1859_, 1);
                    v___x_1873_ = lean_unsigned_to_nat(0);
                    v___x_1874_ = lean_nat_dec_eq(v_a_1857_, v___x_1873_);
                    if v___x_1874_ == 0 {
                        lean_dec(v_a_1872_);
                        lean_dec_ref(v_shutdownPromise_1858_);
                        state = 1;
                        continue;
                    } else {
                        v___x_1875_ = (lean_unbox(v_a_1872_) as u8);
                        lean_dec(v_a_1872_);
                        if v___x_1875_ == 0 {
                            lean_dec_ref(v_shutdownPromise_1858_);
                            state = 1;
                            continue;
                        } else {
                            v___x_1876_ = lean_box(0);
                            v___x_1877_ =
                                l_Std_Channel_send___redArg(v_shutdownPromise_1858_, v___x_1876_);
                            lean_dec_ref(v___x_1877_);
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
                    v_reuseFailAlloc_1870_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1870_, 0, v_a_1863_);
                    v___x_1868_ = v_reuseFailAlloc_1870_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1869_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1869_, 0, v___x_1868_);
                return v___x_1869_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__2___boxed(
    mut v_a_1879_: *mut LeanObject,
    mut v_shutdownPromise_1880_: *mut LeanObject,
    mut v_x_1881_: *mut LeanObject,
    mut v___y_1882_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1883_: *mut LeanObject = core::ptr::null_mut();
    v_res_1883_ =
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__2(
            v_a_1879_,
            v_shutdownPromise_1880_,
            v_x_1881_,
        );
    lean_dec(v_a_1879_);
    return v_res_1883_;
}
pub unsafe fn l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__3(
    mut v_context_1884_: *mut LeanObject,
    mut v_shutdownPromise_1885_: *mut LeanObject,
    mut v_x_1886_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1891_: u8 = 0;
    let mut v___x_1893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1896_: u8 = 0;
    let mut v_a_1897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1900_: u8 = 0;
    let mut v_token_1901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: u8 = 0;
    let mut v___f_1903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: u8 = 0;
    let mut v___x_1910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1912_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1886_) == 0 {
                    lean_dec_ref(v_shutdownPromise_1885_);
                    lean_dec_ref(v_context_1884_);
                    v_a_1888_ = lean_ctor_get(v_x_1886_, 0);
                    v_isSharedCheck_1896_ = (!lean_is_exclusive(v_x_1886_)) as u8;
                    if v_isSharedCheck_1896_ == 0 {
                        v___x_1890_ = v_x_1886_;
                        v_isShared_1891_ = v_isSharedCheck_1896_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1888_);
                        lean_dec(v_x_1886_);
                        v___x_1890_ = lean_box(0);
                        v_isShared_1891_ = v_isSharedCheck_1896_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1897_ = lean_ctor_get(v_x_1886_, 0);
                    v_isSharedCheck_1912_ = (!lean_is_exclusive(v_x_1886_)) as u8;
                    if v_isSharedCheck_1912_ == 0 {
                        v___x_1899_ = v_x_1886_;
                        v_isShared_1900_ = v_isSharedCheck_1912_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1897_);
                        lean_dec(v_x_1886_);
                        v___x_1899_ = lean_box(0);
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
                    v_reuseFailAlloc_1895_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1895_, 0, v_a_1888_);
                    v___x_1893_ = v_reuseFailAlloc_1895_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1894_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1894_, 0, v___x_1893_);
                return v___x_1894_;
            }
            3 => {
                v_token_1901_ = lean_ctor_get(v_context_1884_, 1);
                lean_inc_ref(v_token_1901_);
                lean_dec_ref(v_context_1884_);
                v___x_1902_ = l_Std_CancellationToken_isCancelled(v_token_1901_);
                v___f_1903_ = lean_alloc_closure(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__2___boxed as *mut core::ffi::c_void, 4, 2);
                lean_closure_set(v___f_1903_, 0, v_a_1897_);
                lean_closure_set(v___f_1903_, 1, v_shutdownPromise_1885_);
                v___x_1904_ = lean_box((v___x_1902_) as usize);
                if v_isShared_1900_ == 0 {
                    lean_ctor_set(v___x_1899_, 0, v___x_1904_);
                    v___x_1906_ = v___x_1899_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1911_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1911_, 0, v___x_1904_);
                    v___x_1906_ = v_reuseFailAlloc_1911_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1907_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1907_, 0, v___x_1906_);
                v___x_1908_ = lean_unsigned_to_nat(0);
                v___x_1909_ = 0;
                v___x_1910_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
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
    mut v_context_1913_: *mut LeanObject,
    mut v_shutdownPromise_1914_: *mut LeanObject,
    mut v_x_1915_: *mut LeanObject,
    mut v___y_1916_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1917_: *mut LeanObject = core::ptr::null_mut();
    v_res_1917_ =
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__3(
            v_context_1913_,
            v_shutdownPromise_1914_,
            v_x_1915_,
        );
    return v_res_1917_;
}
pub unsafe fn l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__4(
    mut v___f_1918_: *mut LeanObject,
    mut v_____r_1919_: *mut LeanObject,
    mut v___y_1920_: *mut LeanObject,
    mut v___y_1921_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: u8 = 0;
    let mut v___x_1928_: *mut LeanObject = core::ptr::null_mut();
    v___x_1923_ = lean_st_ref_get(v___y_1920_);
    v___x_1924_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1924_, 0, v___x_1923_);
    v___x_1925_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1925_, 0, v___x_1924_);
    v___x_1926_ = lean_unsigned_to_nat(0);
    v___x_1927_ = 0;
    v___x_1928_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_1926_,
        v___x_1927_,
        v___x_1925_,
        v___f_1918_,
    );
    return v___x_1928_;
}
pub unsafe fn l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__4___boxed(
    mut v___f_1929_: *mut LeanObject,
    mut v_____r_1930_: *mut LeanObject,
    mut v___y_1931_: *mut LeanObject,
    mut v___y_1932_: *mut LeanObject,
    mut v___y_1933_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1934_: *mut LeanObject = core::ptr::null_mut();
    v_res_1934_ =
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__4(
            v___f_1929_,
            v_____r_1930_,
            v___y_1931_,
            v___y_1932_,
        );
    lean_dec_ref(v___y_1932_);
    lean_dec(v___y_1931_);
    return v_res_1934_;
}
pub unsafe fn l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__5(
    mut v_x_1935_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_1936_: *mut LeanObject = core::ptr::null_mut();
    v_fst_1936_ = lean_ctor_get(v_x_1935_, 0);
    lean_inc(v_fst_1936_);
    return v_fst_1936_;
}
pub unsafe fn l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__5___boxed(
    mut v_x_1937_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1938_: *mut LeanObject = core::ptr::null_mut();
    v_res_1938_ =
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__5(
            v_x_1937_,
        );
    lean_dec_ref(v_x_1937_);
    return v_res_1938_;
}
pub unsafe fn l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__6(
    mut v___x_1939_: *mut LeanObject,
    mut v___f_1940_: *mut LeanObject,
    mut v___f_1941_: *mut LeanObject,
    mut v___f_1942_: *mut LeanObject,
    mut v___f_1943_: *mut LeanObject,
    mut v_activeConnections_1944_: *mut LeanObject,
    mut v_____r_1945_: *mut LeanObject,
    mut v___y_1946_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2353__overap_1949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v___x_1939_);
    v___x_1948_ = lean_alloc_closure(
        l_StateRefT_x27_instMonad___aux__13___boxed as *mut core::ffi::c_void,
        9,
        8,
    );
    lean_closure_set(v___x_1948_, 0, lean_box(0));
    lean_closure_set(v___x_1948_, 1, lean_box(0));
    lean_closure_set(v___x_1948_, 2, lean_box(0));
    lean_closure_set(v___x_1948_, 3, v___x_1939_);
    lean_closure_set(v___x_1948_, 4, lean_box(0));
    lean_closure_set(v___x_1948_, 5, lean_box(0));
    lean_closure_set(v___x_1948_, 6, v___f_1940_);
    lean_closure_set(v___x_1948_, 7, v___f_1941_);
    v___x_2353__overap_1949_ = l_Std_Mutex_atomically___redArg(
        v___x_1939_,
        v___f_1942_,
        v___f_1943_,
        v_activeConnections_1944_,
        v___x_1948_,
    );
    lean_inc_ref(v___y_1946_);
    v___x_1950_ = lean_apply_2(v___x_2353__overap_1949_, v___y_1946_, lean_box(0));
    return v___x_1950_;
}
pub unsafe fn l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__6___boxed(
    mut v___x_1951_: *mut LeanObject,
    mut v___f_1952_: *mut LeanObject,
    mut v___f_1953_: *mut LeanObject,
    mut v___f_1954_: *mut LeanObject,
    mut v___f_1955_: *mut LeanObject,
    mut v_activeConnections_1956_: *mut LeanObject,
    mut v_____r_1957_: *mut LeanObject,
    mut v___y_1958_: *mut LeanObject,
    mut v___y_1959_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1960_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v___y_1958_);
    return v_res_1960_;
}
pub unsafe fn l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__7(
    mut v___f_1961_: *mut LeanObject,
    mut v_a_1962_: *mut LeanObject,
    mut v_x_1963_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1963_) == 0 {
        let mut v___x_1965_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v___f_1961_);
        v___x_1965_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_1965_, 0, v_x_1963_);
        return v___x_1965_;
    } else {
        let mut v_a_1966_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1967_: *mut LeanObject = core::ptr::null_mut();
        v_a_1966_ = lean_ctor_get(v_x_1963_, 0);
        lean_inc(v_a_1966_);
        lean_dec_ref_known(v_x_1963_, 1);
        lean_inc_ref(v_a_1962_);
        v___x_1967_ = lean_apply_3(v___f_1961_, v_a_1966_, v_a_1962_, lean_box(0));
        return v___x_1967_;
    }
}
pub unsafe fn l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__7___boxed(
    mut v___f_1968_: *mut LeanObject,
    mut v_a_1969_: *mut LeanObject,
    mut v_x_1970_: *mut LeanObject,
    mut v___y_1971_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1972_: *mut LeanObject = core::ptr::null_mut();
    v_res_1972_ =
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__7(
            v___f_1968_,
            v_a_1969_,
            v_x_1970_,
        );
    lean_dec_ref(v_a_1969_);
    return v_res_1972_;
}
pub unsafe fn l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__8(
    mut v_releaseConnectionPermit_1973_: u8,
    mut v___f_1974_: *mut LeanObject,
    mut v_a_1975_: *mut LeanObject,
    mut v_connectionLimit_1976_: *mut LeanObject,
    mut v___f_1977_: *mut LeanObject,
    mut v_opt_1978_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1985_: u8 = 0;
    let mut v___x_1986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: u8 = 0;
    let mut v___x_1992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1994_: u8 = 0;
    let mut v___x_1995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_releaseConnectionPermit_1973_ == 0 {
                    lean_dec_ref(v___f_1977_);
                    lean_dec(v_connectionLimit_1976_);
                    v___x_1980_ = lean_box(0);
                    lean_inc_ref(v_a_1975_);
                    v___x_1981_ = lean_apply_3(v___f_1974_, v___x_1980_, v_a_1975_, lean_box(0));
                    return v___x_1981_;
                } else {
                    if lean_obj_tag(v_connectionLimit_1976_) == 1 {
                        lean_dec_ref(v___f_1974_);
                        v_val_1982_ = lean_ctor_get(v_connectionLimit_1976_, 0);
                        v_isSharedCheck_1994_ = (!lean_is_exclusive(v_connectionLimit_1976_)) as u8;
                        if v_isSharedCheck_1994_ == 0 {
                            v___x_1984_ = v_connectionLimit_1976_;
                            v_isShared_1985_ = v_isSharedCheck_1994_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_val_1982_);
                            lean_dec(v_connectionLimit_1976_);
                            v___x_1984_ = lean_box(0);
                            v_isShared_1985_ = v_isSharedCheck_1994_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___f_1977_);
                        lean_dec(v_connectionLimit_1976_);
                        v___x_1995_ = lean_box(0);
                        lean_inc_ref(v_a_1975_);
                        v___x_1996_ =
                            lean_apply_3(v___f_1974_, v___x_1995_, v_a_1975_, lean_box(0));
                        return v___x_1996_;
                    }
                }
            }
            1 => {
                v___x_1986_ = l_Std_Semaphore_release(v_val_1982_);
                if v_isShared_1985_ == 0 {
                    lean_ctor_set(v___x_1984_, 0, v___x_1986_);
                    v___x_1988_ = v___x_1984_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1993_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1993_, 0, v___x_1986_);
                    v___x_1988_ = v_reuseFailAlloc_1993_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1989_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1989_, 0, v___x_1988_);
                v___x_1990_ = lean_unsigned_to_nat(0);
                v___x_1991_ = 0;
                v___x_1992_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
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
    mut v_releaseConnectionPermit_1997_: *mut LeanObject,
    mut v___f_1998_: *mut LeanObject,
    mut v_a_1999_: *mut LeanObject,
    mut v_connectionLimit_2000_: *mut LeanObject,
    mut v___f_2001_: *mut LeanObject,
    mut v_opt_2002_: *mut LeanObject,
    mut v___y_2003_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_releaseConnectionPermit_boxed_2004_: u8 = 0;
    let mut v_res_2005_: *mut LeanObject = core::ptr::null_mut();
    v_releaseConnectionPermit_boxed_2004_ = (lean_unbox(v_releaseConnectionPermit_1997_) as u8);
    v_res_2005_ =
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__8(
            v_releaseConnectionPermit_boxed_2004_,
            v___f_1998_,
            v_a_1999_,
            v_connectionLimit_2000_,
            v___f_2001_,
            v_opt_2002_,
        );
    lean_dec(v_opt_2002_);
    lean_dec_ref(v_a_1999_);
    return v_res_2005_;
}
pub unsafe fn l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__9(
    mut v_action_2006_: *mut LeanObject,
    mut v_a_2007_: *mut LeanObject,
    mut v___f_2008_: *mut LeanObject,
    mut v___f_2009_: *mut LeanObject,
    mut v_x_2010_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2015_: u8 = 0;
    let mut v___x_2017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2020_: u8 = 0;
    let mut v___x_2021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: u8 = 0;
    let mut v___x_2024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2032_: u8 = 0;
    let mut v___x_2034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2036_: u8 = 0;
    let mut v_a_2037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2040_: u8 = 0;
    let mut v_fst_2041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2045_: u8 = 0;
    let mut v_a_2046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2049_: u8 = 0;
    let mut v___x_2050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2055_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2010_) == 0 {
                    lean_dec(v___f_2009_);
                    lean_dec_ref(v___f_2008_);
                    lean_dec_ref(v_action_2006_);
                    v_a_2012_ = lean_ctor_get(v_x_2010_, 0);
                    v_isSharedCheck_2020_ = (!lean_is_exclusive(v_x_2010_)) as u8;
                    if v_isSharedCheck_2020_ == 0 {
                        v___x_2014_ = v_x_2010_;
                        v_isShared_2015_ = v_isSharedCheck_2020_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2012_);
                        lean_dec(v_x_2010_);
                        v___x_2014_ = lean_box(0);
                        v_isShared_2015_ = v_isSharedCheck_2020_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v_x_2010_, 1);
                    lean_inc_ref(v_a_2007_);
                    v___x_2021_ = lean_apply_1(v_action_2006_, v_a_2007_);
                    v___x_2022_ = lean_unsigned_to_nat(0);
                    v___x_2023_ = 0;
                    v___x_2024_ = l_Std_Async_EAsync_tryFinally_x27___redArg(
                        v___x_2021_,
                        v___f_2008_,
                        v___x_2022_,
                        v___x_2023_,
                    );
                    if lean_obj_tag(v___x_2024_) == 0 {
                        lean_dec(v___f_2009_);
                        v_a_2028_ = lean_ctor_get(v___x_2024_, 0);
                        lean_inc(v_a_2028_);
                        lean_dec_ref_known(v___x_2024_, 1);
                        if lean_obj_tag(v_a_2028_) == 0 {
                            v_a_2029_ = lean_ctor_get(v_a_2028_, 0);
                            v_isSharedCheck_2036_ = (!lean_is_exclusive(v_a_2028_)) as u8;
                            if v_isSharedCheck_2036_ == 0 {
                                v___x_2031_ = v_a_2028_;
                                v_isShared_2032_ = v_isSharedCheck_2036_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_a_2029_);
                                lean_dec(v_a_2028_);
                                v___x_2031_ = lean_box(0);
                                v_isShared_2032_ = v_isSharedCheck_2036_;
                                state = 4;
                                continue;
                            }
                        } else {
                            v_a_2037_ = lean_ctor_get(v_a_2028_, 0);
                            v_isSharedCheck_2045_ = (!lean_is_exclusive(v_a_2028_)) as u8;
                            if v_isSharedCheck_2045_ == 0 {
                                v___x_2039_ = v_a_2028_;
                                v_isShared_2040_ = v_isSharedCheck_2045_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_a_2037_);
                                lean_dec(v_a_2028_);
                                v___x_2039_ = lean_box(0);
                                v_isShared_2040_ = v_isSharedCheck_2045_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        v_a_2046_ = lean_ctor_get(v___x_2024_, 0);
                        v_isSharedCheck_2055_ = (!lean_is_exclusive(v___x_2024_)) as u8;
                        if v_isSharedCheck_2055_ == 0 {
                            v___x_2048_ = v___x_2024_;
                            v_isShared_2049_ = v_isSharedCheck_2055_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_2046_);
                            lean_dec(v___x_2024_);
                            v___x_2048_ = lean_box(0);
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
                    v_reuseFailAlloc_2019_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2019_, 0, v_a_2012_);
                    v___x_2017_ = v_reuseFailAlloc_2019_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2018_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2018_, 0, v___x_2017_);
                return v___x_2018_;
            }
            3 => {
                v___x_2027_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2027_, 0, v___y_2026_);
                return v___x_2027_;
            }
            4 => {
                if v_isShared_2032_ == 0 {
                    v___x_2034_ = v___x_2031_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2035_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_a_2029_);
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
                v_fst_2041_ = lean_ctor_get(v_a_2037_, 0);
                lean_inc(v_fst_2041_);
                lean_dec(v_a_2037_);
                if v_isShared_2040_ == 0 {
                    lean_ctor_set(v___x_2039_, 0, v_fst_2041_);
                    v___x_2043_ = v___x_2039_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2044_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2044_, 0, v_fst_2041_);
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
                v___x_2050_ = lean_alloc_closure(l_Except_map as *mut core::ffi::c_void, 5, 4);
                lean_closure_set(v___x_2050_, 0, lean_box(0));
                lean_closure_set(v___x_2050_, 1, lean_box(0));
                lean_closure_set(v___x_2050_, 2, lean_box(0));
                lean_closure_set(v___x_2050_, 3, v___f_2009_);
                v___x_2051_ = lean_task_map(v___x_2050_, v_a_2046_, v___x_2022_, v___x_2023_);
                if v_isShared_2049_ == 0 {
                    lean_ctor_set(v___x_2048_, 0, v___x_2051_);
                    v___x_2053_ = v___x_2048_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2054_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2054_, 0, v___x_2051_);
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
    mut v_action_2056_: *mut LeanObject,
    mut v_a_2057_: *mut LeanObject,
    mut v___f_2058_: *mut LeanObject,
    mut v___f_2059_: *mut LeanObject,
    mut v_x_2060_: *mut LeanObject,
    mut v___y_2061_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2062_: *mut LeanObject = core::ptr::null_mut();
    v_res_2062_ =
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__9(
            v_action_2056_,
            v_a_2057_,
            v___f_2058_,
            v___f_2059_,
            v_x_2060_,
        );
    lean_dec_ref(v_a_2057_);
    return v_res_2062_;
}
pub unsafe fn l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg(
    mut v_s_2072_: *mut LeanObject,
    mut v_releaseConnectionPermit_2073_: u8,
    mut v_action_2074_: *mut LeanObject,
    mut v_a_2075_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_context_2078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_activeConnections_2079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_connectionLimit_2080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_shutdownPromise_2081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1520__overap_2085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: u8 = 0;
    let mut v___x_2098_: *mut LeanObject = core::ptr::null_mut();
    v___x_2077_ = l_Std_Async_ContextAsync_instMonad;
    v_context_2078_ = lean_ctor_get(v_s_2072_, 0);
    lean_inc_ref(v_context_2078_);
    v_activeConnections_2079_ = lean_ctor_get(v_s_2072_, 1);
    lean_inc_ref_n(v_activeConnections_2079_, 2);
    v_connectionLimit_2080_ = lean_ctor_get(v_s_2072_, 2);
    lean_inc(v_connectionLimit_2080_);
    v_shutdownPromise_2081_ = lean_ctor_get(v_s_2072_, 3);
    lean_inc_ref(v_shutdownPromise_2081_);
    lean_dec_ref(v_s_2072_);
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
    lean_inc_ref_n(v_a_2075_, 4);
    v___x_2086_ = lean_apply_2(v___x_1520__overap_2085_, v_a_2075_, lean_box(0));
    v___f_2087_ =
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__5;
    v___f_2088_ = lean_alloc_closure(
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__3___boxed
            as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_2088_, 0, v_context_2078_);
    lean_closure_set(v___f_2088_, 1, v_shutdownPromise_2081_);
    v___f_2089_ = lean_alloc_closure(
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__4___boxed
            as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_2089_, 0, v___f_2088_);
    v___f_2090_ =
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__6;
    v___f_2091_ = lean_alloc_closure(
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__6___boxed
            as *mut core::ffi::c_void,
        9,
        6,
    );
    lean_closure_set(v___f_2091_, 0, v___x_2077_);
    lean_closure_set(v___f_2091_, 1, v___f_2087_);
    lean_closure_set(v___f_2091_, 2, v___f_2089_);
    lean_closure_set(v___f_2091_, 3, v___f_2083_);
    lean_closure_set(v___f_2091_, 4, v___f_2084_);
    lean_closure_set(v___f_2091_, 5, v_activeConnections_2079_);
    lean_inc_ref(v___f_2091_);
    v___f_2092_ = lean_alloc_closure(
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__7___boxed
            as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_2092_, 0, v___f_2091_);
    lean_closure_set(v___f_2092_, 1, v_a_2075_);
    v___x_2093_ = lean_box((v_releaseConnectionPermit_2073_) as usize);
    v___f_2094_ = lean_alloc_closure(
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__8___boxed
            as *mut core::ffi::c_void,
        7,
        5,
    );
    lean_closure_set(v___f_2094_, 0, v___x_2093_);
    lean_closure_set(v___f_2094_, 1, v___f_2091_);
    lean_closure_set(v___f_2094_, 2, v_a_2075_);
    lean_closure_set(v___f_2094_, 3, v_connectionLimit_2080_);
    lean_closure_set(v___f_2094_, 4, v___f_2092_);
    v___f_2095_ = lean_alloc_closure(
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__9___boxed
            as *mut core::ffi::c_void,
        6,
        4,
    );
    lean_closure_set(v___f_2095_, 0, v_action_2074_);
    lean_closure_set(v___f_2095_, 1, v_a_2075_);
    lean_closure_set(v___f_2095_, 2, v___f_2094_);
    lean_closure_set(v___f_2095_, 3, v___f_2090_);
    v___x_2096_ = lean_unsigned_to_nat(0);
    v___x_2097_ = 0;
    v___x_2098_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_2096_,
        v___x_2097_,
        v___x_2086_,
        v___f_2095_,
    );
    return v___x_2098_;
}
pub unsafe fn l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___boxed(
    mut v_s_2099_: *mut LeanObject,
    mut v_releaseConnectionPermit_2100_: *mut LeanObject,
    mut v_action_2101_: *mut LeanObject,
    mut v_a_2102_: *mut LeanObject,
    mut v_a_2103_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_releaseConnectionPermit_boxed_2104_: u8 = 0;
    let mut v_res_2105_: *mut LeanObject = core::ptr::null_mut();
    v_releaseConnectionPermit_boxed_2104_ = (lean_unbox(v_releaseConnectionPermit_2100_) as u8);
    v_res_2105_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg(
        v_s_2099_,
        v_releaseConnectionPermit_boxed_2104_,
        v_action_2101_,
        v_a_2102_,
    );
    lean_dec_ref(v_a_2102_);
    return v_res_2105_;
}
pub unsafe fn l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation(
    mut v_00_u03b1_2106_: *mut LeanObject,
    mut v_s_2107_: *mut LeanObject,
    mut v_releaseConnectionPermit_2108_: u8,
    mut v_action_2109_: *mut LeanObject,
    mut v_a_2110_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_context_2113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_activeConnections_2114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_connectionLimit_2115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_shutdownPromise_2116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2130__overap_2120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: u8 = 0;
    let mut v___x_2133_: *mut LeanObject = core::ptr::null_mut();
    v___x_2112_ = l_Std_Async_ContextAsync_instMonad;
    v_context_2113_ = lean_ctor_get(v_s_2107_, 0);
    lean_inc_ref(v_context_2113_);
    v_activeConnections_2114_ = lean_ctor_get(v_s_2107_, 1);
    lean_inc_ref_n(v_activeConnections_2114_, 2);
    v_connectionLimit_2115_ = lean_ctor_get(v_s_2107_, 2);
    lean_inc(v_connectionLimit_2115_);
    v_shutdownPromise_2116_ = lean_ctor_get(v_s_2107_, 3);
    lean_inc_ref(v_shutdownPromise_2116_);
    lean_dec_ref(v_s_2107_);
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
    lean_inc_ref_n(v_a_2110_, 4);
    v___x_2121_ = lean_apply_2(v___x_2130__overap_2120_, v_a_2110_, lean_box(0));
    v___f_2122_ =
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__5;
    v___f_2123_ = lean_alloc_closure(
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__3___boxed
            as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_2123_, 0, v_context_2113_);
    lean_closure_set(v___f_2123_, 1, v_shutdownPromise_2116_);
    v___f_2124_ = lean_alloc_closure(
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__4___boxed
            as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_2124_, 0, v___f_2123_);
    v___f_2125_ =
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__6;
    v___f_2126_ = lean_alloc_closure(
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__6___boxed
            as *mut core::ffi::c_void,
        9,
        6,
    );
    lean_closure_set(v___f_2126_, 0, v___x_2112_);
    lean_closure_set(v___f_2126_, 1, v___f_2122_);
    lean_closure_set(v___f_2126_, 2, v___f_2124_);
    lean_closure_set(v___f_2126_, 3, v___f_2118_);
    lean_closure_set(v___f_2126_, 4, v___f_2119_);
    lean_closure_set(v___f_2126_, 5, v_activeConnections_2114_);
    lean_inc_ref(v___f_2126_);
    v___f_2127_ = lean_alloc_closure(
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__7___boxed
            as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_2127_, 0, v___f_2126_);
    lean_closure_set(v___f_2127_, 1, v_a_2110_);
    v___x_2128_ = lean_box((v_releaseConnectionPermit_2108_) as usize);
    v___f_2129_ = lean_alloc_closure(
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__8___boxed
            as *mut core::ffi::c_void,
        7,
        5,
    );
    lean_closure_set(v___f_2129_, 0, v___x_2128_);
    lean_closure_set(v___f_2129_, 1, v___f_2126_);
    lean_closure_set(v___f_2129_, 2, v_a_2110_);
    lean_closure_set(v___f_2129_, 3, v_connectionLimit_2115_);
    lean_closure_set(v___f_2129_, 4, v___f_2127_);
    v___f_2130_ = lean_alloc_closure(
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__9___boxed
            as *mut core::ffi::c_void,
        6,
        4,
    );
    lean_closure_set(v___f_2130_, 0, v_action_2109_);
    lean_closure_set(v___f_2130_, 1, v_a_2110_);
    lean_closure_set(v___f_2130_, 2, v___f_2129_);
    lean_closure_set(v___f_2130_, 3, v___f_2125_);
    v___x_2131_ = lean_unsigned_to_nat(0);
    v___x_2132_ = 0;
    v___x_2133_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_2131_,
        v___x_2132_,
        v___x_2121_,
        v___f_2130_,
    );
    return v___x_2133_;
}
pub unsafe fn l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___boxed(
    mut v_00_u03b1_2134_: *mut LeanObject,
    mut v_s_2135_: *mut LeanObject,
    mut v_releaseConnectionPermit_2136_: *mut LeanObject,
    mut v_action_2137_: *mut LeanObject,
    mut v_a_2138_: *mut LeanObject,
    mut v_a_2139_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_releaseConnectionPermit_boxed_2140_: u8 = 0;
    let mut v_res_2141_: *mut LeanObject = core::ptr::null_mut();
    v_releaseConnectionPermit_boxed_2140_ = (lean_unbox(v_releaseConnectionPermit_2136_) as u8);
    v_res_2141_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation(
        v_00_u03b1_2134_,
        v_s_2135_,
        v_releaseConnectionPermit_boxed_2140_,
        v_action_2137_,
        v_a_2138_,
    );
    lean_dec_ref(v_a_2138_);
    return v_res_2141_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__0(
    mut v_x_2142_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_2142_) == 0 {
        let mut v___x_2144_: *mut LeanObject = core::ptr::null_mut();
        v___x_2144_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_2144_, 0, v_x_2142_);
        return v___x_2144_;
    } else {
        let mut v___x_2145_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref_known(v_x_2142_, 1);
        v___x_2145_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__1;
        return v___x_2145_;
    }
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__0___boxed(
    mut v_x_2146_: *mut LeanObject,
    mut v___y_2147_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2148_: *mut LeanObject = core::ptr::null_mut();
    v_res_2148_ = l_Std_Http_Server_serve___redArg___lam__0(v_x_2146_);
    return v_res_2148_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__1(
    mut v_x_2149_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2154_: u8 = 0;
    let mut v___x_2156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2159_: u8 = 0;
    let mut v_a_2160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2163_: u8 = 0;
    let mut v_a_2164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2167_: u8 = 0;
    let mut v___x_2169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2175_: u8 = 0;
    let mut v_a_2176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2179_: u8 = 0;
    let mut v___x_2181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2187_: u8 = 0;
    let mut v_isSharedCheck_2188_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2149_) == 0 {
                    v_a_2151_ = lean_ctor_get(v_x_2149_, 0);
                    v_isSharedCheck_2159_ = (!lean_is_exclusive(v_x_2149_)) as u8;
                    if v_isSharedCheck_2159_ == 0 {
                        v___x_2153_ = v_x_2149_;
                        v_isShared_2154_ = v_isSharedCheck_2159_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2151_);
                        lean_dec(v_x_2149_);
                        v___x_2153_ = lean_box(0);
                        v_isShared_2154_ = v_isSharedCheck_2159_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2160_ = lean_ctor_get(v_x_2149_, 0);
                    v_isSharedCheck_2188_ = (!lean_is_exclusive(v_x_2149_)) as u8;
                    if v_isSharedCheck_2188_ == 0 {
                        v___x_2162_ = v_x_2149_;
                        v_isShared_2163_ = v_isSharedCheck_2188_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2160_);
                        lean_dec(v_x_2149_);
                        v___x_2162_ = lean_box(0);
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
                    v_reuseFailAlloc_2158_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2158_, 0, v_a_2151_);
                    v___x_2156_ = v_reuseFailAlloc_2158_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2157_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2157_, 0, v___x_2156_);
                return v___x_2157_;
            }
            3 => {
                if lean_obj_tag(v_a_2160_) == 0 {
                    v_a_2164_ = lean_ctor_get(v_a_2160_, 0);
                    v_isSharedCheck_2175_ = (!lean_is_exclusive(v_a_2160_)) as u8;
                    if v_isSharedCheck_2175_ == 0 {
                        v___x_2166_ = v_a_2160_;
                        v_isShared_2167_ = v_isSharedCheck_2175_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_2164_);
                        lean_dec(v_a_2160_);
                        v___x_2166_ = lean_box(0);
                        v_isShared_2167_ = v_isSharedCheck_2175_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_a_2176_ = lean_ctor_get(v_a_2160_, 0);
                    v_isSharedCheck_2187_ = (!lean_is_exclusive(v_a_2160_)) as u8;
                    if v_isSharedCheck_2187_ == 0 {
                        v___x_2178_ = v_a_2160_;
                        v_isShared_2179_ = v_isSharedCheck_2187_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_2176_);
                        lean_dec(v_a_2160_);
                        v___x_2178_ = lean_box(0);
                        v_isShared_2179_ = v_isSharedCheck_2187_;
                        state = 7;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_2167_ == 0 {
                    lean_ctor_set_tag(v___x_2166_, 1);
                    v___x_2169_ = v___x_2166_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2174_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2174_, 0, v_a_2164_);
                    v___x_2169_ = v_reuseFailAlloc_2174_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_2163_ == 0 {
                    lean_ctor_set(v___x_2162_, 0, v___x_2169_);
                    v___x_2171_ = v___x_2162_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2173_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2173_, 0, v___x_2169_);
                    v___x_2171_ = v_reuseFailAlloc_2173_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_2172_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2172_, 0, v___x_2171_);
                return v___x_2172_;
            }
            7 => {
                if v_isShared_2179_ == 0 {
                    lean_ctor_set_tag(v___x_2178_, 0);
                    v___x_2181_ = v___x_2178_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2186_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2186_, 0, v_a_2176_);
                    v___x_2181_ = v_reuseFailAlloc_2186_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_2163_ == 0 {
                    lean_ctor_set(v___x_2162_, 0, v___x_2181_);
                    v___x_2183_ = v___x_2162_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2185_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2185_, 0, v___x_2181_);
                    v___x_2183_ = v_reuseFailAlloc_2185_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_2184_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2184_, 0, v___x_2183_);
                return v___x_2184_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__1___boxed(
    mut v_x_2189_: *mut LeanObject,
    mut v___y_2190_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2191_: *mut LeanObject = core::ptr::null_mut();
    v_res_2191_ = l_Std_Http_Server_serve___redArg___lam__1(v_x_2189_);
    return v_res_2191_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__3(
    mut v_x_2192_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_2193_: *mut LeanObject = core::ptr::null_mut();
    v_fst_2193_ = lean_ctor_get(v_x_2192_, 0);
    lean_inc(v_fst_2193_);
    return v_fst_2193_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__3___boxed(
    mut v_x_2194_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2195_: *mut LeanObject = core::ptr::null_mut();
    v_res_2195_ = l_Std_Http_Server_serve___redArg___lam__3(v_x_2194_);
    lean_dec_ref(v_x_2194_);
    return v_res_2195_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__4(
    mut v_x_2200_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2202_: *mut LeanObject = core::ptr::null_mut();
    v___x_2202_ = l_Std_Http_Server_serve___redArg___lam__4___closed__1;
    return v___x_2202_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__4___boxed(
    mut v_x_2203_: *mut LeanObject,
    mut v___y_2204_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2205_: *mut LeanObject = core::ptr::null_mut();
    v_res_2205_ = l_Std_Http_Server_serve___redArg___lam__4(v_x_2203_);
    return v_res_2205_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__2(
    mut v_x_2206_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: *mut LeanObject = core::ptr::null_mut();
    v___x_2208_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_2208_, 0, v_x_2206_);
    v___x_2209_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_2209_, 0, v___x_2208_);
    v___x_2210_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2210_, 0, v___x_2209_);
    return v___x_2210_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__2___boxed(
    mut v_x_2211_: *mut LeanObject,
    mut v___y_2212_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2213_: *mut LeanObject = core::ptr::null_mut();
    v_res_2213_ = l_Std_Http_Server_serve___redArg___lam__2(v_x_2211_);
    return v_res_2213_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__5(
    mut v_x_2214_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2219_: u8 = 0;
    let mut v___x_2221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2224_: u8 = 0;
    let mut v_a_2225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2228_: u8 = 0;
    let mut v_token_2229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2235_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2214_) == 0 {
                    v_a_2216_ = lean_ctor_get(v_x_2214_, 0);
                    v_isSharedCheck_2224_ = (!lean_is_exclusive(v_x_2214_)) as u8;
                    if v_isSharedCheck_2224_ == 0 {
                        v___x_2218_ = v_x_2214_;
                        v_isShared_2219_ = v_isSharedCheck_2224_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2216_);
                        lean_dec(v_x_2214_);
                        v___x_2218_ = lean_box(0);
                        v_isShared_2219_ = v_isSharedCheck_2224_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2225_ = lean_ctor_get(v_x_2214_, 0);
                    v_isSharedCheck_2235_ = (!lean_is_exclusive(v_x_2214_)) as u8;
                    if v_isSharedCheck_2235_ == 0 {
                        v___x_2227_ = v_x_2214_;
                        v_isShared_2228_ = v_isSharedCheck_2235_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2225_);
                        lean_dec(v_x_2214_);
                        v___x_2227_ = lean_box(0);
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
                    v_reuseFailAlloc_2223_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2223_, 0, v_a_2216_);
                    v___x_2221_ = v_reuseFailAlloc_2223_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2222_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2222_, 0, v___x_2221_);
                return v___x_2222_;
            }
            3 => {
                v_token_2229_ = lean_ctor_get(v_a_2225_, 1);
                lean_inc_ref(v_token_2229_);
                lean_dec(v_a_2225_);
                v___x_2230_ = l_Std_CancellationToken_selector(v_token_2229_);
                if v_isShared_2228_ == 0 {
                    lean_ctor_set(v___x_2227_, 0, v___x_2230_);
                    v___x_2232_ = v___x_2227_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2234_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2234_, 0, v___x_2230_);
                    v___x_2232_ = v_reuseFailAlloc_2234_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2233_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2233_, 0, v___x_2232_);
                return v___x_2233_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__5___boxed(
    mut v_x_2236_: *mut LeanObject,
    mut v___y_2237_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2238_: *mut LeanObject = core::ptr::null_mut();
    v_res_2238_ = l_Std_Http_Server_serve___redArg___lam__5(v_x_2236_);
    return v_res_2238_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__10(
    mut v___x_2239_: *mut LeanObject,
    mut v_____r_2240_: *mut LeanObject,
    mut v___y_2241_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut LeanObject = core::ptr::null_mut();
    v___x_2243_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2243_, 0, v___x_2239_);
    v___x_2244_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_2244_, 0, v___x_2243_);
    v___x_2245_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2245_, 0, v___x_2244_);
    return v___x_2245_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__10___boxed(
    mut v___x_2246_: *mut LeanObject,
    mut v_____r_2247_: *mut LeanObject,
    mut v___y_2248_: *mut LeanObject,
    mut v___y_2249_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2250_: *mut LeanObject = core::ptr::null_mut();
    v_res_2250_ =
        l_Std_Http_Server_serve___redArg___lam__10(v___x_2246_, v_____r_2247_, v___y_2248_);
    lean_dec_ref(v___y_2248_);
    return v_res_2250_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__6(
    mut v___x_2251_: *mut LeanObject,
    mut v_x_2252_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2257_: u8 = 0;
    let mut v___x_2259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2262_: u8 = 0;
    let mut v___x_2264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2265_: u8 = 0;
    let mut v___x_2266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2271_: u8 = 0;
    let mut v_unused_2272_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2252_) == 0 {
                    v_a_2254_ = lean_ctor_get(v_x_2252_, 0);
                    v_isSharedCheck_2262_ = (!lean_is_exclusive(v_x_2252_)) as u8;
                    if v_isSharedCheck_2262_ == 0 {
                        v___x_2256_ = v_x_2252_;
                        v_isShared_2257_ = v_isSharedCheck_2262_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2254_);
                        lean_dec(v_x_2252_);
                        v___x_2256_ = lean_box(0);
                        v_isShared_2257_ = v_isSharedCheck_2262_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_isSharedCheck_2271_ = (!lean_is_exclusive(v_x_2252_)) as u8;
                    if v_isSharedCheck_2271_ == 0 {
                        v_unused_2272_ = lean_ctor_get(v_x_2252_, 0);
                        lean_dec(v_unused_2272_);
                        v___x_2264_ = v_x_2252_;
                        v_isShared_2265_ = v_isSharedCheck_2271_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v_x_2252_);
                        v___x_2264_ = lean_box(0);
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
                    v_reuseFailAlloc_2261_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2261_, 0, v_a_2254_);
                    v___x_2259_ = v_reuseFailAlloc_2261_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2260_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2260_, 0, v___x_2259_);
                return v___x_2260_;
            }
            3 => {
                v___x_2266_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2266_, 0, v___x_2251_);
                if v_isShared_2265_ == 0 {
                    lean_ctor_set(v___x_2264_, 0, v___x_2266_);
                    v___x_2268_ = v___x_2264_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2270_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2270_, 0, v___x_2266_);
                    v___x_2268_ = v_reuseFailAlloc_2270_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2269_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2269_, 0, v___x_2268_);
                return v___x_2269_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__6___boxed(
    mut v___x_2273_: *mut LeanObject,
    mut v_x_2274_: *mut LeanObject,
    mut v___y_2275_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2276_: *mut LeanObject = core::ptr::null_mut();
    v_res_2276_ = l_Std_Http_Server_serve___redArg___lam__6(v___x_2273_, v_x_2274_);
    return v_res_2276_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__7(
    mut v___f_2277_: *mut LeanObject,
    mut v___y_2278_: *mut LeanObject,
    mut v_x_2279_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2284_: u8 = 0;
    let mut v___x_2286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2289_: u8 = 0;
    let mut v_a_2290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2279_) == 0 {
                    lean_dec_ref(v___f_2277_);
                    v_a_2281_ = lean_ctor_get(v_x_2279_, 0);
                    v_isSharedCheck_2289_ = (!lean_is_exclusive(v_x_2279_)) as u8;
                    if v_isSharedCheck_2289_ == 0 {
                        v___x_2283_ = v_x_2279_;
                        v_isShared_2284_ = v_isSharedCheck_2289_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2281_);
                        lean_dec(v_x_2279_);
                        v___x_2283_ = lean_box(0);
                        v_isShared_2284_ = v_isSharedCheck_2289_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2290_ = lean_ctor_get(v_x_2279_, 0);
                    lean_inc(v_a_2290_);
                    lean_dec_ref_known(v_x_2279_, 1);
                    lean_inc_ref(v___y_2278_);
                    v___x_2291_ = lean_apply_3(v___f_2277_, v_a_2290_, v___y_2278_, lean_box(0));
                    return v___x_2291_;
                }
            }
            1 => {
                if v_isShared_2284_ == 0 {
                    v___x_2286_ = v___x_2283_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2288_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2288_, 0, v_a_2281_);
                    v___x_2286_ = v_reuseFailAlloc_2288_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2287_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2287_, 0, v___x_2286_);
                return v___x_2287_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__7___boxed(
    mut v___f_2292_: *mut LeanObject,
    mut v___y_2293_: *mut LeanObject,
    mut v_x_2294_: *mut LeanObject,
    mut v___y_2295_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2296_: *mut LeanObject = core::ptr::null_mut();
    v_res_2296_ = l_Std_Http_Server_serve___redArg___lam__7(v___f_2292_, v___y_2293_, v_x_2294_);
    lean_dec_ref(v___y_2293_);
    return v_res_2296_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__8(
    mut v_a_2297_: *mut LeanObject,
    mut v_x_2298_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2303_: u8 = 0;
    let mut v___x_2304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2310_: u8 = 0;
    let mut v_unused_2311_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2298_) == 0 {
                    lean_dec_ref(v_a_2297_);
                    v___x_2300_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2300_, 0, v_x_2298_);
                    return v___x_2300_;
                } else {
                    v_isSharedCheck_2310_ = (!lean_is_exclusive(v_x_2298_)) as u8;
                    if v_isSharedCheck_2310_ == 0 {
                        v_unused_2311_ = lean_ctor_get(v_x_2298_, 0);
                        lean_dec(v_unused_2311_);
                        v___x_2302_ = v_x_2298_;
                        v_isShared_2303_ = v_isSharedCheck_2310_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_x_2298_);
                        v___x_2302_ = lean_box(0);
                        v_isShared_2303_ = v_isSharedCheck_2310_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2304_ = lean_box(2);
                v___x_2305_ = l_Std_CancellationContext_cancel(v_a_2297_, v___x_2304_);
                if v_isShared_2303_ == 0 {
                    lean_ctor_set(v___x_2302_, 0, v___x_2305_);
                    v___x_2307_ = v___x_2302_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2309_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2309_, 0, v___x_2305_);
                    v___x_2307_ = v_reuseFailAlloc_2309_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2308_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2308_, 0, v___x_2307_);
                return v___x_2308_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__8___boxed(
    mut v_a_2312_: *mut LeanObject,
    mut v_x_2313_: *mut LeanObject,
    mut v___y_2314_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2315_: *mut LeanObject = core::ptr::null_mut();
    v_res_2315_ = l_Std_Http_Server_serve___redArg___lam__8(v_a_2312_, v_x_2313_);
    return v_res_2315_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__11(
    mut v___f_2316_: *mut LeanObject,
    mut v_a_2317_: *mut LeanObject,
    mut v_x_2318_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_2318_) == 0 {
        let mut v___x_2320_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_a_2317_);
        lean_dec_ref(v___f_2316_);
        v___x_2320_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_2320_, 0, v_x_2318_);
        return v___x_2320_;
    } else {
        let mut v_a_2321_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2322_: *mut LeanObject = core::ptr::null_mut();
        v_a_2321_ = lean_ctor_get(v_x_2318_, 0);
        lean_inc(v_a_2321_);
        lean_dec_ref_known(v_x_2318_, 1);
        v___x_2322_ = lean_apply_3(v___f_2316_, v_a_2321_, v_a_2317_, lean_box(0));
        return v___x_2322_;
    }
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__11___boxed(
    mut v___f_2323_: *mut LeanObject,
    mut v_a_2324_: *mut LeanObject,
    mut v_x_2325_: *mut LeanObject,
    mut v___y_2326_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2327_: *mut LeanObject = core::ptr::null_mut();
    v_res_2327_ = l_Std_Http_Server_serve___redArg___lam__11(v___f_2323_, v_a_2324_, v_x_2325_);
    return v_res_2327_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__9(
    mut v_permitAcquired_2328_: u8,
    mut v___f_2329_: *mut LeanObject,
    mut v___x_2330_: *mut LeanObject,
    mut v_a_2331_: *mut LeanObject,
    mut v_connectionLimit_2332_: *mut LeanObject,
    mut v___x_2333_: *mut LeanObject,
    mut v___x_2334_: u8,
    mut v___f_2335_: *mut LeanObject,
    mut v_opt_2336_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2342_: u8 = 0;
    let mut v___x_2343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2349_: u8 = 0;
    let mut v___x_2350_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_permitAcquired_2328_ == 0 {
                    lean_dec_ref(v___f_2335_);
                    lean_dec(v___x_2333_);
                    lean_dec(v_connectionLimit_2332_);
                    v___x_2338_ = lean_apply_3(v___f_2329_, v___x_2330_, v_a_2331_, lean_box(0));
                    return v___x_2338_;
                } else {
                    if lean_obj_tag(v_connectionLimit_2332_) == 1 {
                        lean_dec_ref(v_a_2331_);
                        lean_dec_ref(v___f_2329_);
                        v_val_2339_ = lean_ctor_get(v_connectionLimit_2332_, 0);
                        v_isSharedCheck_2349_ = (!lean_is_exclusive(v_connectionLimit_2332_)) as u8;
                        if v_isSharedCheck_2349_ == 0 {
                            v___x_2341_ = v_connectionLimit_2332_;
                            v_isShared_2342_ = v_isSharedCheck_2349_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_val_2339_);
                            lean_dec(v_connectionLimit_2332_);
                            v___x_2341_ = lean_box(0);
                            v_isShared_2342_ = v_isSharedCheck_2349_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___f_2335_);
                        lean_dec(v___x_2333_);
                        lean_dec(v_connectionLimit_2332_);
                        v___x_2350_ =
                            lean_apply_3(v___f_2329_, v___x_2330_, v_a_2331_, lean_box(0));
                        return v___x_2350_;
                    }
                }
            }
            1 => {
                v___x_2343_ = l_Std_Semaphore_release(v_val_2339_);
                if v_isShared_2342_ == 0 {
                    lean_ctor_set(v___x_2341_, 0, v___x_2343_);
                    v___x_2345_ = v___x_2341_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2348_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2348_, 0, v___x_2343_);
                    v___x_2345_ = v_reuseFailAlloc_2348_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2346_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2346_, 0, v___x_2345_);
                v___x_2347_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
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
    mut v_permitAcquired_2351_: *mut LeanObject,
    mut v___f_2352_: *mut LeanObject,
    mut v___x_2353_: *mut LeanObject,
    mut v_a_2354_: *mut LeanObject,
    mut v_connectionLimit_2355_: *mut LeanObject,
    mut v___x_2356_: *mut LeanObject,
    mut v___x_2357_: *mut LeanObject,
    mut v___f_2358_: *mut LeanObject,
    mut v_opt_2359_: *mut LeanObject,
    mut v___y_2360_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_permitAcquired_boxed_2361_: u8 = 0;
    let mut v___x_13775__boxed_2362_: u8 = 0;
    let mut v_res_2363_: *mut LeanObject = core::ptr::null_mut();
    v_permitAcquired_boxed_2361_ = (lean_unbox(v_permitAcquired_2351_) as u8);
    v___x_13775__boxed_2362_ = (lean_unbox(v___x_2357_) as u8);
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
    lean_dec(v_opt_2359_);
    return v_res_2363_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__12(
    mut v___x_2364_: *mut LeanObject,
    mut v_inst_2365_: *mut LeanObject,
    mut v_val_2366_: *mut LeanObject,
    mut v_handler_2367_: *mut LeanObject,
    mut v_config_2368_: *mut LeanObject,
    mut v_extensions_2369_: *mut LeanObject,
    mut v_a_2370_: *mut LeanObject,
    mut v___f_2371_: *mut LeanObject,
    mut v___x_2372_: *mut LeanObject,
    mut v___x_2373_: u8,
    mut v___f_2374_: *mut LeanObject,
    mut v_x_2375_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2380_: u8 = 0;
    let mut v___x_2381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2392_: u8 = 0;
    let mut v___x_2394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2396_: u8 = 0;
    let mut v_a_2397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2400_: u8 = 0;
    let mut v_fst_2401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2405_: u8 = 0;
    let mut v_a_2406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2409_: u8 = 0;
    let mut v___x_2410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2415_: u8 = 0;
    let mut v_isSharedCheck_2416_: u8 = 0;
    let mut v_unused_2417_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2375_) == 0 {
                    lean_dec_ref(v___f_2374_);
                    lean_dec(v___x_2372_);
                    lean_dec_ref(v___f_2371_);
                    lean_dec_ref(v_a_2370_);
                    lean_dec(v_extensions_2369_);
                    lean_dec_ref(v_config_2368_);
                    lean_dec(v_handler_2367_);
                    lean_dec(v_val_2366_);
                    lean_dec_ref(v_inst_2365_);
                    lean_dec_ref(v___x_2364_);
                    v___x_2377_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2377_, 0, v_x_2375_);
                    return v___x_2377_;
                } else {
                    v_isSharedCheck_2416_ = (!lean_is_exclusive(v_x_2375_)) as u8;
                    if v_isSharedCheck_2416_ == 0 {
                        v_unused_2417_ = lean_ctor_get(v_x_2375_, 0);
                        lean_dec(v_unused_2417_);
                        v___x_2379_ = v_x_2375_;
                        v_isShared_2380_ = v_isSharedCheck_2416_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_x_2375_);
                        v___x_2379_ = lean_box(0);
                        v_isShared_2380_ = v_isSharedCheck_2416_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2381_ = lean_alloc_closure(
                    l_Std_Http_Server_serveConnection___boxed as *mut core::ffi::c_void,
                    10,
                    9,
                );
                lean_closure_set(v___x_2381_, 0, lean_box(0));
                lean_closure_set(v___x_2381_, 1, lean_box(0));
                lean_closure_set(v___x_2381_, 2, v___x_2364_);
                lean_closure_set(v___x_2381_, 3, v_inst_2365_);
                lean_closure_set(v___x_2381_, 4, v_val_2366_);
                lean_closure_set(v___x_2381_, 5, v_handler_2367_);
                lean_closure_set(v___x_2381_, 6, v_config_2368_);
                lean_closure_set(v___x_2381_, 7, v_extensions_2369_);
                lean_closure_set(v___x_2381_, 8, v_a_2370_);
                lean_inc(v___x_2372_);
                v___x_2382_ = l_Std_Async_EAsync_tryFinally_x27___redArg(
                    v___x_2381_,
                    v___f_2371_,
                    v___x_2372_,
                    v___x_2373_,
                );
                if lean_obj_tag(v___x_2382_) == 0 {
                    lean_dec_ref(v___f_2374_);
                    lean_dec(v___x_2372_);
                    v_a_2388_ = lean_ctor_get(v___x_2382_, 0);
                    lean_inc(v_a_2388_);
                    lean_dec_ref_known(v___x_2382_, 1);
                    if lean_obj_tag(v_a_2388_) == 0 {
                        v_a_2389_ = lean_ctor_get(v_a_2388_, 0);
                        v_isSharedCheck_2396_ = (!lean_is_exclusive(v_a_2388_)) as u8;
                        if v_isSharedCheck_2396_ == 0 {
                            v___x_2391_ = v_a_2388_;
                            v_isShared_2392_ = v_isSharedCheck_2396_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_2389_);
                            lean_dec(v_a_2388_);
                            v___x_2391_ = lean_box(0);
                            v_isShared_2392_ = v_isSharedCheck_2396_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v_a_2397_ = lean_ctor_get(v_a_2388_, 0);
                        v_isSharedCheck_2405_ = (!lean_is_exclusive(v_a_2388_)) as u8;
                        if v_isSharedCheck_2405_ == 0 {
                            v___x_2399_ = v_a_2388_;
                            v_isShared_2400_ = v_isSharedCheck_2405_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_2397_);
                            lean_dec(v_a_2388_);
                            v___x_2399_ = lean_box(0);
                            v_isShared_2400_ = v_isSharedCheck_2405_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_2379_);
                    v_a_2406_ = lean_ctor_get(v___x_2382_, 0);
                    v_isSharedCheck_2415_ = (!lean_is_exclusive(v___x_2382_)) as u8;
                    if v_isSharedCheck_2415_ == 0 {
                        v___x_2408_ = v___x_2382_;
                        v_isShared_2409_ = v_isSharedCheck_2415_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_2406_);
                        lean_dec(v___x_2382_);
                        v___x_2408_ = lean_box(0);
                        v_isShared_2409_ = v_isSharedCheck_2415_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2380_ == 0 {
                    lean_ctor_set_tag(v___x_2379_, 0);
                    lean_ctor_set(v___x_2379_, 0, v___y_2384_);
                    v___x_2386_ = v___x_2379_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2387_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2387_, 0, v___y_2384_);
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
                    v_reuseFailAlloc_2395_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2395_, 0, v_a_2389_);
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
                v_fst_2401_ = lean_ctor_get(v_a_2397_, 0);
                lean_inc(v_fst_2401_);
                lean_dec(v_a_2397_);
                if v_isShared_2400_ == 0 {
                    lean_ctor_set(v___x_2399_, 0, v_fst_2401_);
                    v___x_2403_ = v___x_2399_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2404_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2404_, 0, v_fst_2401_);
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
                v___x_2410_ = lean_alloc_closure(l_Except_map as *mut core::ffi::c_void, 5, 4);
                lean_closure_set(v___x_2410_, 0, lean_box(0));
                lean_closure_set(v___x_2410_, 1, lean_box(0));
                lean_closure_set(v___x_2410_, 2, lean_box(0));
                lean_closure_set(v___x_2410_, 3, v___f_2374_);
                v___x_2411_ = lean_task_map(v___x_2410_, v_a_2406_, v___x_2372_, v___x_2373_);
                if v_isShared_2409_ == 0 {
                    lean_ctor_set(v___x_2408_, 0, v___x_2411_);
                    v___x_2413_ = v___x_2408_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2414_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2414_, 0, v___x_2411_);
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
    mut v___x_2418_: *mut LeanObject,
    mut v_inst_2419_: *mut LeanObject,
    mut v_val_2420_: *mut LeanObject,
    mut v_handler_2421_: *mut LeanObject,
    mut v_config_2422_: *mut LeanObject,
    mut v_extensions_2423_: *mut LeanObject,
    mut v_a_2424_: *mut LeanObject,
    mut v___f_2425_: *mut LeanObject,
    mut v___x_2426_: *mut LeanObject,
    mut v___x_2427_: *mut LeanObject,
    mut v___f_2428_: *mut LeanObject,
    mut v_x_2429_: *mut LeanObject,
    mut v___y_2430_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_13824__boxed_2431_: u8 = 0;
    let mut v_res_2432_: *mut LeanObject = core::ptr::null_mut();
    v___x_13824__boxed_2431_ = (lean_unbox(v___x_2427_) as u8);
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
    mut v___x_2433_: *mut LeanObject,
    mut v_activeConnections_2434_: *mut LeanObject,
    mut v___f_2435_: *mut LeanObject,
    mut v_a_2436_: *mut LeanObject,
    mut v___f_2437_: *mut LeanObject,
    mut v___f_2438_: *mut LeanObject,
    mut v_permitAcquired_2439_: u8,
    mut v___x_2440_: *mut LeanObject,
    mut v_connectionLimit_2441_: *mut LeanObject,
    mut v___x_2442_: *mut LeanObject,
    mut v___x_2443_: u8,
    mut v___x_2444_: *mut LeanObject,
    mut v_inst_2445_: *mut LeanObject,
    mut v_val_2446_: *mut LeanObject,
    mut v_handler_2447_: *mut LeanObject,
    mut v_config_2448_: *mut LeanObject,
    mut v_extensions_2449_: *mut LeanObject,
    mut v___f_2450_: *mut LeanObject,
    mut v___f_2451_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_12955__overap_2455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut LeanObject = core::ptr::null_mut();
    v___f_2453_ =
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__3;
    v___f_2454_ =
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___closed__4;
    lean_inc_ref(v_activeConnections_2434_);
    lean_inc_ref(v___x_2433_);
    v___x_12955__overap_2455_ = l_Std_Mutex_atomically___redArg(
        v___x_2433_,
        v___f_2453_,
        v___f_2454_,
        v_activeConnections_2434_,
        v___f_2435_,
    );
    lean_inc_ref_n(v_a_2436_, 3);
    v___x_2456_ = lean_apply_2(v___x_12955__overap_2455_, v_a_2436_, lean_box(0));
    v___f_2457_ = lean_alloc_closure(
        l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__6___boxed
            as *mut core::ffi::c_void,
        9,
        6,
    );
    lean_closure_set(v___f_2457_, 0, v___x_2433_);
    lean_closure_set(v___f_2457_, 1, v___f_2437_);
    lean_closure_set(v___f_2457_, 2, v___f_2438_);
    lean_closure_set(v___f_2457_, 3, v___f_2453_);
    lean_closure_set(v___f_2457_, 4, v___f_2454_);
    lean_closure_set(v___f_2457_, 5, v_activeConnections_2434_);
    lean_inc_ref(v___f_2457_);
    v___f_2458_ = lean_alloc_closure(
        l_Std_Http_Server_serve___redArg___lam__11___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_2458_, 0, v___f_2457_);
    lean_closure_set(v___f_2458_, 1, v_a_2436_);
    v___x_2459_ = lean_box((v_permitAcquired_2439_) as usize);
    v___x_2460_ = lean_box((v___x_2443_) as usize);
    lean_inc_n(v___x_2442_, 3);
    v___f_2461_ = lean_alloc_closure(
        l_Std_Http_Server_serve___redArg___lam__9___boxed as *mut core::ffi::c_void,
        10,
        8,
    );
    lean_closure_set(v___f_2461_, 0, v___x_2459_);
    lean_closure_set(v___f_2461_, 1, v___f_2457_);
    lean_closure_set(v___f_2461_, 2, v___x_2440_);
    lean_closure_set(v___f_2461_, 3, v_a_2436_);
    lean_closure_set(v___f_2461_, 4, v_connectionLimit_2441_);
    lean_closure_set(v___f_2461_, 5, v___x_2442_);
    lean_closure_set(v___f_2461_, 6, v___x_2460_);
    lean_closure_set(v___f_2461_, 7, v___f_2458_);
    v___x_2462_ = lean_box((v___x_2443_) as usize);
    v___f_2463_ = lean_alloc_closure(
        l_Std_Http_Server_serve___redArg___lam__12___boxed as *mut core::ffi::c_void,
        13,
        11,
    );
    lean_closure_set(v___f_2463_, 0, v___x_2444_);
    lean_closure_set(v___f_2463_, 1, v_inst_2445_);
    lean_closure_set(v___f_2463_, 2, v_val_2446_);
    lean_closure_set(v___f_2463_, 3, v_handler_2447_);
    lean_closure_set(v___f_2463_, 4, v_config_2448_);
    lean_closure_set(v___f_2463_, 5, v_extensions_2449_);
    lean_closure_set(v___f_2463_, 6, v_a_2436_);
    lean_closure_set(v___f_2463_, 7, v___f_2461_);
    lean_closure_set(v___f_2463_, 8, v___x_2442_);
    lean_closure_set(v___f_2463_, 9, v___x_2462_);
    lean_closure_set(v___f_2463_, 10, v___f_2450_);
    v___x_2464_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_2442_,
        v___x_2443_,
        v___x_2456_,
        v___f_2463_,
    );
    v___x_2465_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_2442_,
        v___x_2443_,
        v___x_2464_,
        v___f_2451_,
    );
    return v___x_2465_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__13___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2466_: *mut LeanObject = *_args.add(0);
    let mut v_activeConnections_2467_: *mut LeanObject = *_args.add(1);
    let mut v___f_2468_: *mut LeanObject = *_args.add(2);
    let mut v_a_2469_: *mut LeanObject = *_args.add(3);
    let mut v___f_2470_: *mut LeanObject = *_args.add(4);
    let mut v___f_2471_: *mut LeanObject = *_args.add(5);
    let mut v_permitAcquired_2472_: *mut LeanObject = *_args.add(6);
    let mut v___x_2473_: *mut LeanObject = *_args.add(7);
    let mut v_connectionLimit_2474_: *mut LeanObject = *_args.add(8);
    let mut v___x_2475_: *mut LeanObject = *_args.add(9);
    let mut v___x_2476_: *mut LeanObject = *_args.add(10);
    let mut v___x_2477_: *mut LeanObject = *_args.add(11);
    let mut v_inst_2478_: *mut LeanObject = *_args.add(12);
    let mut v_val_2479_: *mut LeanObject = *_args.add(13);
    let mut v_handler_2480_: *mut LeanObject = *_args.add(14);
    let mut v_config_2481_: *mut LeanObject = *_args.add(15);
    let mut v_extensions_2482_: *mut LeanObject = *_args.add(16);
    let mut v___f_2483_: *mut LeanObject = *_args.add(17);
    let mut v___f_2484_: *mut LeanObject = *_args.add(18);
    let mut v___y_2485_: *mut LeanObject = *_args.add(19);
    let mut v_permitAcquired_boxed_2486_: u8 = 0;
    let mut v___x_13943__boxed_2487_: u8 = 0;
    let mut v_res_2488_: *mut LeanObject = core::ptr::null_mut();
    v_permitAcquired_boxed_2486_ = (lean_unbox(v_permitAcquired_2472_) as u8);
    v___x_13943__boxed_2487_ = (lean_unbox(v___x_2476_) as u8);
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
    mut v___x_2489_: *mut LeanObject,
    mut v_activeConnections_2490_: *mut LeanObject,
    mut v___f_2491_: *mut LeanObject,
    mut v___f_2492_: *mut LeanObject,
    mut v___f_2493_: *mut LeanObject,
    mut v_permitAcquired_2494_: u8,
    mut v___x_2495_: *mut LeanObject,
    mut v_connectionLimit_2496_: *mut LeanObject,
    mut v___x_2497_: *mut LeanObject,
    mut v___x_2498_: u8,
    mut v___x_2499_: *mut LeanObject,
    mut v_inst_2500_: *mut LeanObject,
    mut v_val_2501_: *mut LeanObject,
    mut v_handler_2502_: *mut LeanObject,
    mut v_config_2503_: *mut LeanObject,
    mut v_extensions_2504_: *mut LeanObject,
    mut v___f_2505_: *mut LeanObject,
    mut v_x_2506_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2511_: u8 = 0;
    let mut v___x_2513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2516_: u8 = 0;
    let mut v_a_2517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2520_: u8 = 0;
    let mut v___f_2521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2531_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2506_) == 0 {
                    lean_dec_ref(v___f_2505_);
                    lean_dec(v_extensions_2504_);
                    lean_dec_ref(v_config_2503_);
                    lean_dec(v_handler_2502_);
                    lean_dec(v_val_2501_);
                    lean_dec_ref(v_inst_2500_);
                    lean_dec_ref(v___x_2499_);
                    lean_dec(v___x_2497_);
                    lean_dec(v_connectionLimit_2496_);
                    lean_dec_ref(v___f_2493_);
                    lean_dec_ref(v___f_2492_);
                    lean_dec_ref(v___f_2491_);
                    lean_dec_ref(v_activeConnections_2490_);
                    lean_dec_ref(v___x_2489_);
                    v_a_2508_ = lean_ctor_get(v_x_2506_, 0);
                    v_isSharedCheck_2516_ = (!lean_is_exclusive(v_x_2506_)) as u8;
                    if v_isSharedCheck_2516_ == 0 {
                        v___x_2510_ = v_x_2506_;
                        v_isShared_2511_ = v_isSharedCheck_2516_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2508_);
                        lean_dec(v_x_2506_);
                        v___x_2510_ = lean_box(0);
                        v_isShared_2511_ = v_isSharedCheck_2516_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2517_ = lean_ctor_get(v_x_2506_, 0);
                    v_isSharedCheck_2531_ = (!lean_is_exclusive(v_x_2506_)) as u8;
                    if v_isSharedCheck_2531_ == 0 {
                        v___x_2519_ = v_x_2506_;
                        v_isShared_2520_ = v_isSharedCheck_2531_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2517_);
                        lean_dec(v_x_2506_);
                        v___x_2519_ = lean_box(0);
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
                    v_reuseFailAlloc_2515_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2515_, 0, v_a_2508_);
                    v___x_2513_ = v_reuseFailAlloc_2515_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2514_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2514_, 0, v___x_2513_);
                return v___x_2514_;
            }
            3 => {
                lean_inc(v_a_2517_);
                v___f_2521_ = lean_alloc_closure(
                    l_Std_Http_Server_serve___redArg___lam__8___boxed as *mut core::ffi::c_void,
                    3,
                    1,
                );
                lean_closure_set(v___f_2521_, 0, v_a_2517_);
                v___x_2522_ = lean_box((v_permitAcquired_2494_) as usize);
                v___x_2523_ = lean_box((v___x_2498_) as usize);
                lean_inc(v___x_2497_);
                v___f_2524_ = lean_alloc_closure(
                    l_Std_Http_Server_serve___redArg___lam__13___boxed as *mut core::ffi::c_void,
                    20,
                    19,
                );
                lean_closure_set(v___f_2524_, 0, v___x_2489_);
                lean_closure_set(v___f_2524_, 1, v_activeConnections_2490_);
                lean_closure_set(v___f_2524_, 2, v___f_2491_);
                lean_closure_set(v___f_2524_, 3, v_a_2517_);
                lean_closure_set(v___f_2524_, 4, v___f_2492_);
                lean_closure_set(v___f_2524_, 5, v___f_2493_);
                lean_closure_set(v___f_2524_, 6, v___x_2522_);
                lean_closure_set(v___f_2524_, 7, v___x_2495_);
                lean_closure_set(v___f_2524_, 8, v_connectionLimit_2496_);
                lean_closure_set(v___f_2524_, 9, v___x_2497_);
                lean_closure_set(v___f_2524_, 10, v___x_2523_);
                lean_closure_set(v___f_2524_, 11, v___x_2499_);
                lean_closure_set(v___f_2524_, 12, v_inst_2500_);
                lean_closure_set(v___f_2524_, 13, v_val_2501_);
                lean_closure_set(v___f_2524_, 14, v_handler_2502_);
                lean_closure_set(v___f_2524_, 15, v_config_2503_);
                lean_closure_set(v___f_2524_, 16, v_extensions_2504_);
                lean_closure_set(v___f_2524_, 17, v___f_2505_);
                lean_closure_set(v___f_2524_, 18, v___f_2521_);
                v___x_2525_ = lean_alloc_closure(
                    l_Std_Async_BaseAsync_toRawBaseIO___boxed as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___x_2525_, 0, lean_box(0));
                lean_closure_set(v___x_2525_, 1, v___f_2524_);
                v___x_2526_ = lean_io_as_task(v___x_2525_, v___x_2497_);
                lean_dec_ref(v___x_2526_);
                if v_isShared_2520_ == 0 {
                    lean_ctor_set(v___x_2519_, 0, v___x_2495_);
                    v___x_2528_ = v___x_2519_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2530_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2530_, 0, v___x_2495_);
                    v___x_2528_ = v_reuseFailAlloc_2530_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2529_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2529_, 0, v___x_2528_);
                return v___x_2529_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__14___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2532_: *mut LeanObject = *_args.add(0);
    let mut v_activeConnections_2533_: *mut LeanObject = *_args.add(1);
    let mut v___f_2534_: *mut LeanObject = *_args.add(2);
    let mut v___f_2535_: *mut LeanObject = *_args.add(3);
    let mut v___f_2536_: *mut LeanObject = *_args.add(4);
    let mut v_permitAcquired_2537_: *mut LeanObject = *_args.add(5);
    let mut v___x_2538_: *mut LeanObject = *_args.add(6);
    let mut v_connectionLimit_2539_: *mut LeanObject = *_args.add(7);
    let mut v___x_2540_: *mut LeanObject = *_args.add(8);
    let mut v___x_2541_: *mut LeanObject = *_args.add(9);
    let mut v___x_2542_: *mut LeanObject = *_args.add(10);
    let mut v_inst_2543_: *mut LeanObject = *_args.add(11);
    let mut v_val_2544_: *mut LeanObject = *_args.add(12);
    let mut v_handler_2545_: *mut LeanObject = *_args.add(13);
    let mut v_config_2546_: *mut LeanObject = *_args.add(14);
    let mut v_extensions_2547_: *mut LeanObject = *_args.add(15);
    let mut v___f_2548_: *mut LeanObject = *_args.add(16);
    let mut v_x_2549_: *mut LeanObject = *_args.add(17);
    let mut v___y_2550_: *mut LeanObject = *_args.add(18);
    let mut v_permitAcquired_boxed_2551_: u8 = 0;
    let mut v___x_14010__boxed_2552_: u8 = 0;
    let mut v_res_2553_: *mut LeanObject = core::ptr::null_mut();
    v_permitAcquired_boxed_2551_ = (lean_unbox(v_permitAcquired_2537_) as u8);
    v___x_14010__boxed_2552_ = (lean_unbox(v___x_2541_) as u8);
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
    mut v___x_2554_: *mut LeanObject,
    mut v___x_2555_: u8,
    mut v___f_2556_: *mut LeanObject,
    mut v_x_2557_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2562_: u8 = 0;
    let mut v___x_2564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2567_: u8 = 0;
    let mut v_a_2568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2571_: u8 = 0;
    let mut v___x_2572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2578_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2557_) == 0 {
                    lean_dec_ref(v___f_2556_);
                    lean_dec(v___x_2554_);
                    v_a_2559_ = lean_ctor_get(v_x_2557_, 0);
                    v_isSharedCheck_2567_ = (!lean_is_exclusive(v_x_2557_)) as u8;
                    if v_isSharedCheck_2567_ == 0 {
                        v___x_2561_ = v_x_2557_;
                        v_isShared_2562_ = v_isSharedCheck_2567_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2559_);
                        lean_dec(v_x_2557_);
                        v___x_2561_ = lean_box(0);
                        v_isShared_2562_ = v_isSharedCheck_2567_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2568_ = lean_ctor_get(v_x_2557_, 0);
                    v_isSharedCheck_2578_ = (!lean_is_exclusive(v_x_2557_)) as u8;
                    if v_isSharedCheck_2578_ == 0 {
                        v___x_2570_ = v_x_2557_;
                        v_isShared_2571_ = v_isSharedCheck_2578_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2568_);
                        lean_dec(v_x_2557_);
                        v___x_2570_ = lean_box(0);
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
                    v_reuseFailAlloc_2566_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2566_, 0, v_a_2559_);
                    v___x_2564_ = v_reuseFailAlloc_2566_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2565_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2565_, 0, v___x_2564_);
                return v___x_2565_;
            }
            3 => {
                v___x_2572_ = l_Std_CancellationContext_fork(v_a_2568_);
                if v_isShared_2571_ == 0 {
                    lean_ctor_set(v___x_2570_, 0, v___x_2572_);
                    v___x_2574_ = v___x_2570_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2577_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2577_, 0, v___x_2572_);
                    v___x_2574_ = v_reuseFailAlloc_2577_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2575_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2575_, 0, v___x_2574_);
                v___x_2576_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
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
    mut v___x_2579_: *mut LeanObject,
    mut v___x_2580_: *mut LeanObject,
    mut v___f_2581_: *mut LeanObject,
    mut v_x_2582_: *mut LeanObject,
    mut v___y_2583_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_14092__boxed_2584_: u8 = 0;
    let mut v_res_2585_: *mut LeanObject = core::ptr::null_mut();
    v___x_14092__boxed_2584_ = (lean_unbox(v___x_2580_) as u8);
    v_res_2585_ = l_Std_Http_Server_serve___redArg___lam__15(
        v___x_2579_,
        v___x_14092__boxed_2584_,
        v___f_2581_,
        v_x_2582_,
    );
    return v_res_2585_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__16(
    mut v___x_2586_: *mut LeanObject,
    mut v_activeConnections_2587_: *mut LeanObject,
    mut v___f_2588_: *mut LeanObject,
    mut v___f_2589_: *mut LeanObject,
    mut v___f_2590_: *mut LeanObject,
    mut v_permitAcquired_2591_: u8,
    mut v___x_2592_: *mut LeanObject,
    mut v_connectionLimit_2593_: *mut LeanObject,
    mut v___x_2594_: u8,
    mut v_inst_2595_: *mut LeanObject,
    mut v_val_2596_: *mut LeanObject,
    mut v_handler_2597_: *mut LeanObject,
    mut v_config_2598_: *mut LeanObject,
    mut v___f_2599_: *mut LeanObject,
    mut v___f_2600_: *mut LeanObject,
    mut v_extensions_2601_: *mut LeanObject,
    mut v___y_2602_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut LeanObject = core::ptr::null_mut();
    v___x_2604_ = l_Std_Http_instTransportClient;
    v___x_2605_ = lean_unsigned_to_nat(0);
    v___x_2606_ = lean_box((v_permitAcquired_2591_) as usize);
    v___x_2607_ = lean_box((v___x_2594_) as usize);
    v___f_2608_ = lean_alloc_closure(
        l_Std_Http_Server_serve___redArg___lam__14___boxed as *mut core::ffi::c_void,
        19,
        17,
    );
    lean_closure_set(v___f_2608_, 0, v___x_2586_);
    lean_closure_set(v___f_2608_, 1, v_activeConnections_2587_);
    lean_closure_set(v___f_2608_, 2, v___f_2588_);
    lean_closure_set(v___f_2608_, 3, v___f_2589_);
    lean_closure_set(v___f_2608_, 4, v___f_2590_);
    lean_closure_set(v___f_2608_, 5, v___x_2606_);
    lean_closure_set(v___f_2608_, 6, v___x_2592_);
    lean_closure_set(v___f_2608_, 7, v_connectionLimit_2593_);
    lean_closure_set(v___f_2608_, 8, v___x_2605_);
    lean_closure_set(v___f_2608_, 9, v___x_2607_);
    lean_closure_set(v___f_2608_, 10, v___x_2604_);
    lean_closure_set(v___f_2608_, 11, v_inst_2595_);
    lean_closure_set(v___f_2608_, 12, v_val_2596_);
    lean_closure_set(v___f_2608_, 13, v_handler_2597_);
    lean_closure_set(v___f_2608_, 14, v_config_2598_);
    lean_closure_set(v___f_2608_, 15, v_extensions_2601_);
    lean_closure_set(v___f_2608_, 16, v___f_2599_);
    v___x_2609_ = lean_box((v___x_2594_) as usize);
    v___f_2610_ = lean_alloc_closure(
        l_Std_Http_Server_serve___redArg___lam__15___boxed as *mut core::ffi::c_void,
        5,
        3,
    );
    lean_closure_set(v___f_2610_, 0, v___x_2605_);
    lean_closure_set(v___f_2610_, 1, v___x_2609_);
    lean_closure_set(v___f_2610_, 2, v___f_2608_);
    lean_inc_ref(v___y_2602_);
    v___x_2611_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_2611_, 0, v___y_2602_);
    v___x_2612_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2612_, 0, v___x_2611_);
    v___x_2613_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_2605_,
        v___x_2594_,
        v___x_2612_,
        v___f_2610_,
    );
    v___x_2614_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_2605_,
        v___x_2594_,
        v___x_2613_,
        v___f_2600_,
    );
    return v___x_2614_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__16___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2615_: *mut LeanObject = *_args.add(0);
    let mut v_activeConnections_2616_: *mut LeanObject = *_args.add(1);
    let mut v___f_2617_: *mut LeanObject = *_args.add(2);
    let mut v___f_2618_: *mut LeanObject = *_args.add(3);
    let mut v___f_2619_: *mut LeanObject = *_args.add(4);
    let mut v_permitAcquired_2620_: *mut LeanObject = *_args.add(5);
    let mut v___x_2621_: *mut LeanObject = *_args.add(6);
    let mut v_connectionLimit_2622_: *mut LeanObject = *_args.add(7);
    let mut v___x_2623_: *mut LeanObject = *_args.add(8);
    let mut v_inst_2624_: *mut LeanObject = *_args.add(9);
    let mut v_val_2625_: *mut LeanObject = *_args.add(10);
    let mut v_handler_2626_: *mut LeanObject = *_args.add(11);
    let mut v_config_2627_: *mut LeanObject = *_args.add(12);
    let mut v___f_2628_: *mut LeanObject = *_args.add(13);
    let mut v___f_2629_: *mut LeanObject = *_args.add(14);
    let mut v_extensions_2630_: *mut LeanObject = *_args.add(15);
    let mut v___y_2631_: *mut LeanObject = *_args.add(16);
    let mut v___y_2632_: *mut LeanObject = *_args.add(17);
    let mut v_permitAcquired_boxed_2633_: u8 = 0;
    let mut v___x_14151__boxed_2634_: u8 = 0;
    let mut v_res_2635_: *mut LeanObject = core::ptr::null_mut();
    v_permitAcquired_boxed_2633_ = (lean_unbox(v_permitAcquired_2620_) as u8);
    v___x_14151__boxed_2634_ = (lean_unbox(v___x_2623_) as u8);
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
    lean_dec_ref(v___y_2631_);
    return v_res_2635_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__17(
    mut v___f_2636_: *mut LeanObject,
    mut v___y_2637_: *mut LeanObject,
    mut v_x_2638_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2643_: u8 = 0;
    let mut v___x_2645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2648_: u8 = 0;
    let mut v_a_2649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2650_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2638_) == 0 {
                    lean_dec_ref(v___f_2636_);
                    v_a_2640_ = lean_ctor_get(v_x_2638_, 0);
                    v_isSharedCheck_2648_ = (!lean_is_exclusive(v_x_2638_)) as u8;
                    if v_isSharedCheck_2648_ == 0 {
                        v___x_2642_ = v_x_2638_;
                        v_isShared_2643_ = v_isSharedCheck_2648_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2640_);
                        lean_dec(v_x_2638_);
                        v___x_2642_ = lean_box(0);
                        v_isShared_2643_ = v_isSharedCheck_2648_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2649_ = lean_ctor_get(v_x_2638_, 0);
                    lean_inc(v_a_2649_);
                    lean_dec_ref_known(v_x_2638_, 1);
                    lean_inc_ref(v___y_2637_);
                    v___x_2650_ = lean_apply_3(v___f_2636_, v_a_2649_, v___y_2637_, lean_box(0));
                    return v___x_2650_;
                }
            }
            1 => {
                if v_isShared_2643_ == 0 {
                    v___x_2645_ = v___x_2642_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2647_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2647_, 0, v_a_2640_);
                    v___x_2645_ = v_reuseFailAlloc_2647_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2646_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2646_, 0, v___x_2645_);
                return v___x_2646_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__17___boxed(
    mut v___f_2651_: *mut LeanObject,
    mut v___y_2652_: *mut LeanObject,
    mut v_x_2653_: *mut LeanObject,
    mut v___y_2654_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2655_: *mut LeanObject = core::ptr::null_mut();
    v_res_2655_ = l_Std_Http_Server_serve___redArg___lam__17(v___f_2651_, v___y_2652_, v_x_2653_);
    lean_dec_ref(v___y_2652_);
    return v_res_2655_;
}
pub unsafe fn _init_l_Std_Http_Server_serve___redArg___lam__19___closed__0() -> *mut LeanObject {
    let mut v___x_2656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2657_: *mut LeanObject = core::ptr::null_mut();
    v___x_2656_ = l_Std_Http_Extensions_empty;
    v___x_2657_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_2657_, 0, v___x_2656_);
    return v___x_2657_;
}
pub unsafe fn _init_l_Std_Http_Server_serve___redArg___lam__19___closed__1() -> *mut LeanObject {
    let mut v___x_2658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: *mut LeanObject = core::ptr::null_mut();
    v___x_2658_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Server_serve___redArg___lam__19___closed__0),
        core::ptr::addr_of_mut!(l_Std_Http_Server_serve___redArg___lam__19___closed__0_once),
        _init_l_Std_Http_Server_serve___redArg___lam__19___closed__0,
    );
    v___x_2659_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2659_, 0, v___x_2658_);
    return v___x_2659_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__19(
    mut v___x_2661_: u8,
    mut v___f_2662_: *mut LeanObject,
    mut v___f_2663_: *mut LeanObject,
    mut v_x_2664_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2669_: u8 = 0;
    let mut v___x_2671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2674_: u8 = 0;
    let mut v_a_2675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2682_: u8 = 0;
    let mut v___x_2683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dyn_2685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2695_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2664_) == 0 {
                    lean_dec_ref(v___f_2663_);
                    lean_dec_ref(v___f_2662_);
                    v_a_2666_ = lean_ctor_get(v_x_2664_, 0);
                    v_isSharedCheck_2674_ = (!lean_is_exclusive(v_x_2664_)) as u8;
                    if v_isSharedCheck_2674_ == 0 {
                        v___x_2668_ = v_x_2664_;
                        v_isShared_2669_ = v_isSharedCheck_2674_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2666_);
                        lean_dec(v_x_2664_);
                        v___x_2668_ = lean_box(0);
                        v_isShared_2669_ = v_isSharedCheck_2674_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2675_ = lean_ctor_get(v_x_2664_, 0);
                    lean_inc(v_a_2675_);
                    lean_dec_ref_known(v_x_2664_, 1);
                    if lean_obj_tag(v_a_2675_) == 0 {
                        lean_dec_ref_known(v_a_2675_, 1);
                        lean_dec_ref(v___f_2663_);
                        v___x_2676_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Server_serve___redArg___lam__19___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Server_serve___redArg___lam__19___closed__1_once
                            ),
                            _init_l_Std_Http_Server_serve___redArg___lam__19___closed__1,
                        );
                        v___x_2677_ = lean_unsigned_to_nat(0);
                        v___x_2678_ =
                            l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                                lean_box(0),
                                lean_box(0),
                                v___x_2677_,
                                v___x_2661_,
                                v___x_2676_,
                                v___f_2662_,
                            );
                        return v___x_2678_;
                    } else {
                        lean_dec_ref(v___f_2662_);
                        v_a_2679_ = lean_ctor_get(v_a_2675_, 0);
                        v_isSharedCheck_2695_ = (!lean_is_exclusive(v_a_2675_)) as u8;
                        if v_isSharedCheck_2695_ == 0 {
                            v___x_2681_ = v_a_2675_;
                            v_isShared_2682_ = v_isSharedCheck_2695_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_2679_);
                            lean_dec(v_a_2675_);
                            v___x_2681_ = lean_box(0);
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
                    v_reuseFailAlloc_2673_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2673_, 0, v_a_2666_);
                    v___x_2671_ = v_reuseFailAlloc_2673_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2672_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2672_, 0, v___x_2671_);
                return v___x_2672_;
            }
            3 => {
                v___x_2683_ = l_Std_Http_Extensions_empty;
                v___x_2684_ = l_Std_Http_Server_instImpl_00___x40_Std_Http_Server_Connection_3058719504____hygCtx___hyg_8_;
                v_dyn_2685_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v_dyn_2685_, 0, v___x_2684_);
                lean_ctor_set(v_dyn_2685_, 1, v_a_2679_);
                v___x_2686_ = l_Std_Http_Server_serve___redArg___lam__19___closed__2;
                v___x_2687_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v_dyn_2685_);
                v___x_2688_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(
                    v___x_2686_,
                    v___x_2687_,
                    v_dyn_2685_,
                    v___x_2683_,
                );
                if v_isShared_2682_ == 0 {
                    lean_ctor_set(v___x_2681_, 0, v___x_2688_);
                    v___x_2690_ = v___x_2681_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2694_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2694_, 0, v___x_2688_);
                    v___x_2690_ = v_reuseFailAlloc_2694_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2691_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2691_, 0, v___x_2690_);
                v___x_2692_ = lean_unsigned_to_nat(0);
                v___x_2693_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
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
    mut v___x_2696_: *mut LeanObject,
    mut v___f_2697_: *mut LeanObject,
    mut v___f_2698_: *mut LeanObject,
    mut v_x_2699_: *mut LeanObject,
    mut v___y_2700_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_14248__boxed_2701_: u8 = 0;
    let mut v_res_2702_: *mut LeanObject = core::ptr::null_mut();
    v___x_14248__boxed_2701_ = (lean_unbox(v___x_2696_) as u8);
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
    mut v___f_2704_: *mut LeanObject,
    mut v___x_2705_: *mut LeanObject,
    mut v___y_2706_: *mut LeanObject,
    mut v_connectionLimit_2707_: *mut LeanObject,
    mut v___x_2708_: u8,
    mut v___f_2709_: *mut LeanObject,
    mut v___x_2710_: *mut LeanObject,
    mut v_activeConnections_2711_: *mut LeanObject,
    mut v___f_2712_: *mut LeanObject,
    mut v___f_2713_: *mut LeanObject,
    mut v___f_2714_: *mut LeanObject,
    mut v_inst_2715_: *mut LeanObject,
    mut v_handler_2716_: *mut LeanObject,
    mut v_config_2717_: *mut LeanObject,
    mut v___f_2718_: *mut LeanObject,
    mut v___f_2719_: *mut LeanObject,
    mut v_x_2720_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2725_: u8 = 0;
    let mut v___x_2727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2730_: u8 = 0;
    let mut v_a_2731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2734_: u8 = 0;
    let mut v___x_2735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2739_: u8 = 0;
    let mut v___x_2740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2749_: u8 = 0;
    let mut v___x_2750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2754_: u8 = 0;
    let mut v___x_2755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2775_: u8 = 0;
    let mut v___x_2777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2779_: u8 = 0;
    let mut v_a_2780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2783_: u8 = 0;
    let mut v___x_2785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2787_: u8 = 0;
    let mut v_isSharedCheck_2788_: u8 = 0;
    let mut v_isSharedCheck_2789_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2720_) == 0 {
                    lean_dec_ref(v___f_2719_);
                    lean_dec_ref(v___f_2718_);
                    lean_dec_ref(v_config_2717_);
                    lean_dec(v_handler_2716_);
                    lean_dec_ref(v_inst_2715_);
                    lean_dec_ref(v___f_2714_);
                    lean_dec_ref(v___f_2713_);
                    lean_dec_ref(v___f_2712_);
                    lean_dec_ref(v_activeConnections_2711_);
                    lean_dec_ref(v___x_2710_);
                    lean_dec_ref(v___f_2709_);
                    lean_dec(v_connectionLimit_2707_);
                    lean_dec_ref(v___f_2704_);
                    v_a_2722_ = lean_ctor_get(v_x_2720_, 0);
                    v_isSharedCheck_2730_ = (!lean_is_exclusive(v_x_2720_)) as u8;
                    if v_isSharedCheck_2730_ == 0 {
                        v___x_2724_ = v_x_2720_;
                        v_isShared_2725_ = v_isSharedCheck_2730_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2722_);
                        lean_dec(v_x_2720_);
                        v___x_2724_ = lean_box(0);
                        v_isShared_2725_ = v_isSharedCheck_2730_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2731_ = lean_ctor_get(v_x_2720_, 0);
                    v_isSharedCheck_2789_ = (!lean_is_exclusive(v_x_2720_)) as u8;
                    if v_isSharedCheck_2789_ == 0 {
                        v___x_2733_ = v_x_2720_;
                        v_isShared_2734_ = v_isSharedCheck_2789_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2731_);
                        lean_dec(v_x_2720_);
                        v___x_2733_ = lean_box(0);
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
                    v_reuseFailAlloc_2729_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2729_, 0, v_a_2722_);
                    v___x_2727_ = v_reuseFailAlloc_2729_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2728_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2728_, 0, v___x_2727_);
                return v___x_2728_;
            }
            3 => {
                if lean_obj_tag(v_a_2731_) == 0 {
                    lean_dec_ref(v___f_2719_);
                    lean_dec_ref(v___f_2718_);
                    lean_dec_ref(v_config_2717_);
                    lean_dec(v_handler_2716_);
                    lean_dec_ref(v_inst_2715_);
                    lean_dec_ref(v___f_2714_);
                    lean_dec_ref(v___f_2713_);
                    lean_dec_ref(v___f_2712_);
                    lean_dec_ref(v_activeConnections_2711_);
                    lean_dec_ref(v___x_2710_);
                    if v_permitAcquired_2703_ == 0 {
                        lean_del_object(v___x_2733_);
                        lean_dec_ref(v___f_2709_);
                        lean_dec(v_connectionLimit_2707_);
                        lean_inc_ref(v___y_2706_);
                        v___x_2735_ =
                            lean_apply_3(v___f_2704_, v___x_2705_, v___y_2706_, lean_box(0));
                        return v___x_2735_;
                    } else {
                        if lean_obj_tag(v_connectionLimit_2707_) == 1 {
                            lean_dec_ref(v___f_2704_);
                            v_val_2736_ = lean_ctor_get(v_connectionLimit_2707_, 0);
                            v_isSharedCheck_2749_ =
                                (!lean_is_exclusive(v_connectionLimit_2707_)) as u8;
                            if v_isSharedCheck_2749_ == 0 {
                                v___x_2738_ = v_connectionLimit_2707_;
                                v_isShared_2739_ = v_isSharedCheck_2749_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_val_2736_);
                                lean_dec(v_connectionLimit_2707_);
                                v___x_2738_ = lean_box(0);
                                v_isShared_2739_ = v_isSharedCheck_2749_;
                                state = 4;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_2733_);
                            lean_dec_ref(v___f_2709_);
                            lean_dec(v_connectionLimit_2707_);
                            lean_inc_ref(v___y_2706_);
                            v___x_2750_ =
                                lean_apply_3(v___f_2704_, v___x_2705_, v___y_2706_, lean_box(0));
                            return v___x_2750_;
                        }
                    }
                } else {
                    lean_dec_ref(v___f_2709_);
                    lean_dec_ref(v___f_2704_);
                    v_val_2751_ = lean_ctor_get(v_a_2731_, 0);
                    v_isSharedCheck_2788_ = (!lean_is_exclusive(v_a_2731_)) as u8;
                    if v_isSharedCheck_2788_ == 0 {
                        v___x_2753_ = v_a_2731_;
                        v_isShared_2754_ = v_isSharedCheck_2788_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_val_2751_);
                        lean_dec(v_a_2731_);
                        v___x_2753_ = lean_box(0);
                        v_isShared_2754_ = v_isSharedCheck_2788_;
                        state = 7;
                        continue;
                    }
                }
            }
            4 => {
                v___x_2740_ = l_Std_Semaphore_release(v_val_2736_);
                if v_isShared_2734_ == 0 {
                    lean_ctor_set(v___x_2733_, 0, v___x_2740_);
                    v___x_2742_ = v___x_2733_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2748_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2748_, 0, v___x_2740_);
                    v___x_2742_ = v_reuseFailAlloc_2748_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_2739_ == 0 {
                    lean_ctor_set_tag(v___x_2738_, 0);
                    lean_ctor_set(v___x_2738_, 0, v___x_2742_);
                    v___x_2744_ = v___x_2738_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2747_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2747_, 0, v___x_2742_);
                    v___x_2744_ = v_reuseFailAlloc_2747_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_2745_ = lean_unsigned_to_nat(0);
                v___x_2746_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
                    v___x_2745_,
                    v___x_2708_,
                    v___x_2744_,
                    v___f_2709_,
                );
                return v___x_2746_;
            }
            7 => {
                v___x_2755_ = lean_box((v_permitAcquired_2703_) as usize);
                v___x_2756_ = lean_box((v___x_2708_) as usize);
                lean_inc(v_val_2751_);
                v___f_2757_ = lean_alloc_closure(
                    l_Std_Http_Server_serve___redArg___lam__16___boxed as *mut core::ffi::c_void,
                    18,
                    15,
                );
                lean_closure_set(v___f_2757_, 0, v___x_2710_);
                lean_closure_set(v___f_2757_, 1, v_activeConnections_2711_);
                lean_closure_set(v___f_2757_, 2, v___f_2712_);
                lean_closure_set(v___f_2757_, 3, v___f_2713_);
                lean_closure_set(v___f_2757_, 4, v___f_2714_);
                lean_closure_set(v___f_2757_, 5, v___x_2755_);
                lean_closure_set(v___f_2757_, 6, v___x_2705_);
                lean_closure_set(v___f_2757_, 7, v_connectionLimit_2707_);
                lean_closure_set(v___f_2757_, 8, v___x_2756_);
                lean_closure_set(v___f_2757_, 9, v_inst_2715_);
                lean_closure_set(v___f_2757_, 10, v_val_2751_);
                lean_closure_set(v___f_2757_, 11, v_handler_2716_);
                lean_closure_set(v___f_2757_, 12, v_config_2717_);
                lean_closure_set(v___f_2757_, 13, v___f_2718_);
                lean_closure_set(v___f_2757_, 14, v___f_2719_);
                lean_inc_ref(v___y_2706_);
                v___f_2758_ = lean_alloc_closure(
                    l_Std_Http_Server_serve___redArg___lam__17___boxed as *mut core::ffi::c_void,
                    4,
                    2,
                );
                lean_closure_set(v___f_2758_, 0, v___f_2757_);
                lean_closure_set(v___f_2758_, 1, v___y_2706_);
                v___x_2759_ = lean_box((v___x_2708_) as usize);
                lean_inc_ref(v___f_2758_);
                v___f_2760_ = lean_alloc_closure(
                    l_Std_Http_Server_serve___redArg___lam__19___boxed as *mut core::ffi::c_void,
                    5,
                    3,
                );
                lean_closure_set(v___f_2760_, 0, v___x_2759_);
                lean_closure_set(v___f_2760_, 1, v___f_2758_);
                lean_closure_set(v___f_2760_, 2, v___f_2758_);
                v___x_2771_ = lean_uv_tcp_getpeername(v_val_2751_);
                lean_dec(v_val_2751_);
                if lean_obj_tag(v___x_2771_) == 0 {
                    v_a_2772_ = lean_ctor_get(v___x_2771_, 0);
                    v_isSharedCheck_2779_ = (!lean_is_exclusive(v___x_2771_)) as u8;
                    if v_isSharedCheck_2779_ == 0 {
                        v___x_2774_ = v___x_2771_;
                        v_isShared_2775_ = v_isSharedCheck_2779_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_2772_);
                        lean_dec(v___x_2771_);
                        v___x_2774_ = lean_box(0);
                        v_isShared_2775_ = v_isSharedCheck_2779_;
                        state = 11;
                        continue;
                    }
                } else {
                    v_a_2780_ = lean_ctor_get(v___x_2771_, 0);
                    v_isSharedCheck_2787_ = (!lean_is_exclusive(v___x_2771_)) as u8;
                    if v_isSharedCheck_2787_ == 0 {
                        v___x_2782_ = v___x_2771_;
                        v_isShared_2783_ = v_isSharedCheck_2787_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_a_2780_);
                        lean_dec(v___x_2771_);
                        v___x_2782_ = lean_box(0);
                        v_isShared_2783_ = v_isSharedCheck_2787_;
                        state = 13;
                        continue;
                    }
                }
            }
            8 => {
                if v_isShared_2734_ == 0 {
                    lean_ctor_set(v___x_2733_, 0, v_val_2762_);
                    v___x_2764_ = v___x_2733_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2770_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2770_, 0, v_val_2762_);
                    v___x_2764_ = v_reuseFailAlloc_2770_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_2754_ == 0 {
                    lean_ctor_set_tag(v___x_2753_, 0);
                    lean_ctor_set(v___x_2753_, 0, v___x_2764_);
                    v___x_2766_ = v___x_2753_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2769_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2769_, 0, v___x_2764_);
                    v___x_2766_ = v_reuseFailAlloc_2769_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_2767_ = lean_unsigned_to_nat(0);
                v___x_2768_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
                    v___x_2767_,
                    v___x_2708_,
                    v___x_2766_,
                    v___f_2760_,
                );
                return v___x_2768_;
            }
            11 => {
                if v_isShared_2775_ == 0 {
                    lean_ctor_set_tag(v___x_2774_, 1);
                    v___x_2777_ = v___x_2774_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2778_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2778_, 0, v_a_2772_);
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
                    lean_ctor_set_tag(v___x_2782_, 0);
                    v___x_2785_ = v___x_2782_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2786_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2786_, 0, v_a_2780_);
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
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_permitAcquired_2790_: *mut LeanObject = *_args.add(0);
    let mut v___f_2791_: *mut LeanObject = *_args.add(1);
    let mut v___x_2792_: *mut LeanObject = *_args.add(2);
    let mut v___y_2793_: *mut LeanObject = *_args.add(3);
    let mut v_connectionLimit_2794_: *mut LeanObject = *_args.add(4);
    let mut v___x_2795_: *mut LeanObject = *_args.add(5);
    let mut v___f_2796_: *mut LeanObject = *_args.add(6);
    let mut v___x_2797_: *mut LeanObject = *_args.add(7);
    let mut v_activeConnections_2798_: *mut LeanObject = *_args.add(8);
    let mut v___f_2799_: *mut LeanObject = *_args.add(9);
    let mut v___f_2800_: *mut LeanObject = *_args.add(10);
    let mut v___f_2801_: *mut LeanObject = *_args.add(11);
    let mut v_inst_2802_: *mut LeanObject = *_args.add(12);
    let mut v_handler_2803_: *mut LeanObject = *_args.add(13);
    let mut v_config_2804_: *mut LeanObject = *_args.add(14);
    let mut v___f_2805_: *mut LeanObject = *_args.add(15);
    let mut v___f_2806_: *mut LeanObject = *_args.add(16);
    let mut v_x_2807_: *mut LeanObject = *_args.add(17);
    let mut v___y_2808_: *mut LeanObject = *_args.add(18);
    let mut v_permitAcquired_boxed_2809_: u8 = 0;
    let mut v___x_14330__boxed_2810_: u8 = 0;
    let mut v_res_2811_: *mut LeanObject = core::ptr::null_mut();
    v_permitAcquired_boxed_2809_ = (lean_unbox(v_permitAcquired_2790_) as u8);
    v___x_14330__boxed_2810_ = (lean_unbox(v___x_2795_) as u8);
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
    lean_dec_ref(v___y_2793_);
    return v_res_2811_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__20(
    mut v_a_2812_: *mut LeanObject,
    mut v___f_2813_: *mut LeanObject,
    mut v___f_2814_: *mut LeanObject,
    mut v___x_2815_: u8,
    mut v___f_2816_: *mut LeanObject,
    mut v_x_2817_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2822_: u8 = 0;
    let mut v___x_2824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2827_: u8 = 0;
    let mut v_a_2828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2817_) == 0 {
                    lean_dec_ref(v___f_2816_);
                    lean_dec_ref(v___f_2814_);
                    lean_dec_ref(v___f_2813_);
                    lean_dec(v_a_2812_);
                    v_a_2819_ = lean_ctor_get(v_x_2817_, 0);
                    v_isSharedCheck_2827_ = (!lean_is_exclusive(v_x_2817_)) as u8;
                    if v_isSharedCheck_2827_ == 0 {
                        v___x_2821_ = v_x_2817_;
                        v_isShared_2822_ = v_isSharedCheck_2827_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2819_);
                        lean_dec(v_x_2817_);
                        v___x_2821_ = lean_box(0);
                        v_isShared_2822_ = v_isSharedCheck_2827_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2828_ = lean_ctor_get(v_x_2817_, 0);
                    lean_inc(v_a_2828_);
                    lean_dec_ref_known(v_x_2817_, 1);
                    v___x_2829_ = l_Std_Async_TCP_Socket_Server_acceptSelector(v_a_2812_);
                    v___x_2830_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2830_, 0, v___x_2829_);
                    lean_ctor_set(v___x_2830_, 1, v___f_2813_);
                    v___x_2831_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2831_, 0, v_a_2828_);
                    lean_ctor_set(v___x_2831_, 1, v___f_2814_);
                    v___x_2832_ = lean_unsigned_to_nat(2);
                    v___x_2833_ = lean_mk_empty_array_with_capacity(v___x_2832_);
                    v___x_2834_ = lean_array_push(v___x_2833_, v___x_2830_);
                    v___x_2835_ = lean_array_push(v___x_2834_, v___x_2831_);
                    v___x_2836_ = l_Std_Async_Selectable_one___redArg(v___x_2835_);
                    v___x_2837_ = lean_unsigned_to_nat(0);
                    v___x_2838_ =
                        l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                            lean_box(0),
                            lean_box(0),
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
                    v_reuseFailAlloc_2826_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2826_, 0, v_a_2819_);
                    v___x_2824_ = v_reuseFailAlloc_2826_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2825_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2825_, 0, v___x_2824_);
                return v___x_2825_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__20___boxed(
    mut v_a_2839_: *mut LeanObject,
    mut v___f_2840_: *mut LeanObject,
    mut v___f_2841_: *mut LeanObject,
    mut v___x_2842_: *mut LeanObject,
    mut v___f_2843_: *mut LeanObject,
    mut v_x_2844_: *mut LeanObject,
    mut v___y_2845_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_14508__boxed_2846_: u8 = 0;
    let mut v_res_2847_: *mut LeanObject = core::ptr::null_mut();
    v___x_14508__boxed_2846_ = (lean_unbox(v___x_2842_) as u8);
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
    mut v___f_2849_: *mut LeanObject,
    mut v___f_2850_: *mut LeanObject,
    mut v___x_2851_: *mut LeanObject,
    mut v_connectionLimit_2852_: *mut LeanObject,
    mut v___x_2853_: *mut LeanObject,
    mut v_activeConnections_2854_: *mut LeanObject,
    mut v___f_2855_: *mut LeanObject,
    mut v___f_2856_: *mut LeanObject,
    mut v___f_2857_: *mut LeanObject,
    mut v_inst_2858_: *mut LeanObject,
    mut v_handler_2859_: *mut LeanObject,
    mut v_config_2860_: *mut LeanObject,
    mut v___f_2861_: *mut LeanObject,
    mut v___f_2862_: *mut LeanObject,
    mut v_a_2863_: *mut LeanObject,
    mut v___f_2864_: *mut LeanObject,
    mut v___f_2865_: *mut LeanObject,
    mut v_permitAcquired_2866_: u8,
    mut v___y_2867_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2879_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref_n(v___y_2867_, 3);
    v___x_2869_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_2869_, 0, v___y_2867_);
    v___x_2870_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2870_, 0, v___x_2869_);
    v___x_2871_ = lean_unsigned_to_nat(0);
    v___x_2872_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_2871_,
        v___x_2848_,
        v___x_2870_,
        v___f_2849_,
    );
    lean_inc_ref(v___f_2850_);
    v___f_2873_ = lean_alloc_closure(
        l_Std_Http_Server_serve___redArg___lam__7___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_2873_, 0, v___f_2850_);
    lean_closure_set(v___f_2873_, 1, v___y_2867_);
    v___x_2874_ = lean_box((v_permitAcquired_2866_) as usize);
    v___x_2875_ = lean_box((v___x_2848_) as usize);
    v___f_2876_ = lean_alloc_closure(
        l_Std_Http_Server_serve___redArg___lam__18___boxed as *mut core::ffi::c_void,
        19,
        17,
    );
    lean_closure_set(v___f_2876_, 0, v___x_2874_);
    lean_closure_set(v___f_2876_, 1, v___f_2850_);
    lean_closure_set(v___f_2876_, 2, v___x_2851_);
    lean_closure_set(v___f_2876_, 3, v___y_2867_);
    lean_closure_set(v___f_2876_, 4, v_connectionLimit_2852_);
    lean_closure_set(v___f_2876_, 5, v___x_2875_);
    lean_closure_set(v___f_2876_, 6, v___f_2873_);
    lean_closure_set(v___f_2876_, 7, v___x_2853_);
    lean_closure_set(v___f_2876_, 8, v_activeConnections_2854_);
    lean_closure_set(v___f_2876_, 9, v___f_2855_);
    lean_closure_set(v___f_2876_, 10, v___f_2856_);
    lean_closure_set(v___f_2876_, 11, v___f_2857_);
    lean_closure_set(v___f_2876_, 12, v_inst_2858_);
    lean_closure_set(v___f_2876_, 13, v_handler_2859_);
    lean_closure_set(v___f_2876_, 14, v_config_2860_);
    lean_closure_set(v___f_2876_, 15, v___f_2861_);
    lean_closure_set(v___f_2876_, 16, v___f_2862_);
    v___x_2877_ = lean_box((v___x_2848_) as usize);
    v___f_2878_ = lean_alloc_closure(
        l_Std_Http_Server_serve___redArg___lam__20___boxed as *mut core::ffi::c_void,
        7,
        5,
    );
    lean_closure_set(v___f_2878_, 0, v_a_2863_);
    lean_closure_set(v___f_2878_, 1, v___f_2864_);
    lean_closure_set(v___f_2878_, 2, v___f_2865_);
    lean_closure_set(v___f_2878_, 3, v___x_2877_);
    lean_closure_set(v___f_2878_, 4, v___f_2876_);
    v___x_2879_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_2871_,
        v___x_2848_,
        v___x_2872_,
        v___f_2878_,
    );
    return v___x_2879_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__21___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2880_: *mut LeanObject = *_args.add(0);
    let mut v___f_2881_: *mut LeanObject = *_args.add(1);
    let mut v___f_2882_: *mut LeanObject = *_args.add(2);
    let mut v___x_2883_: *mut LeanObject = *_args.add(3);
    let mut v_connectionLimit_2884_: *mut LeanObject = *_args.add(4);
    let mut v___x_2885_: *mut LeanObject = *_args.add(5);
    let mut v_activeConnections_2886_: *mut LeanObject = *_args.add(6);
    let mut v___f_2887_: *mut LeanObject = *_args.add(7);
    let mut v___f_2888_: *mut LeanObject = *_args.add(8);
    let mut v___f_2889_: *mut LeanObject = *_args.add(9);
    let mut v_inst_2890_: *mut LeanObject = *_args.add(10);
    let mut v_handler_2891_: *mut LeanObject = *_args.add(11);
    let mut v_config_2892_: *mut LeanObject = *_args.add(12);
    let mut v___f_2893_: *mut LeanObject = *_args.add(13);
    let mut v___f_2894_: *mut LeanObject = *_args.add(14);
    let mut v_a_2895_: *mut LeanObject = *_args.add(15);
    let mut v___f_2896_: *mut LeanObject = *_args.add(16);
    let mut v___f_2897_: *mut LeanObject = *_args.add(17);
    let mut v_permitAcquired_2898_: *mut LeanObject = *_args.add(18);
    let mut v___y_2899_: *mut LeanObject = *_args.add(19);
    let mut v___y_2900_: *mut LeanObject = *_args.add(20);
    let mut v___x_14566__boxed_2901_: u8 = 0;
    let mut v_permitAcquired_boxed_2902_: u8 = 0;
    let mut v_res_2903_: *mut LeanObject = core::ptr::null_mut();
    v___x_14566__boxed_2901_ = (lean_unbox(v___x_2880_) as u8);
    v_permitAcquired_boxed_2902_ = (lean_unbox(v_permitAcquired_2898_) as u8);
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
    lean_dec_ref(v___y_2899_);
    return v_res_2903_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__22(
    mut v___f_2904_: *mut LeanObject,
    mut v___y_2905_: *mut LeanObject,
    mut v_x_2906_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2911_: u8 = 0;
    let mut v___x_2913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2916_: u8 = 0;
    let mut v_a_2917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2918_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2906_) == 0 {
                    lean_dec_ref(v___f_2904_);
                    v_a_2908_ = lean_ctor_get(v_x_2906_, 0);
                    v_isSharedCheck_2916_ = (!lean_is_exclusive(v_x_2906_)) as u8;
                    if v_isSharedCheck_2916_ == 0 {
                        v___x_2910_ = v_x_2906_;
                        v_isShared_2911_ = v_isSharedCheck_2916_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2908_);
                        lean_dec(v_x_2906_);
                        v___x_2910_ = lean_box(0);
                        v_isShared_2911_ = v_isSharedCheck_2916_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2917_ = lean_ctor_get(v_x_2906_, 0);
                    lean_inc(v_a_2917_);
                    lean_dec_ref_known(v_x_2906_, 1);
                    lean_inc_ref(v___y_2905_);
                    v___x_2918_ = lean_apply_3(v___f_2904_, v_a_2917_, v___y_2905_, lean_box(0));
                    return v___x_2918_;
                }
            }
            1 => {
                if v_isShared_2911_ == 0 {
                    v___x_2913_ = v___x_2910_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2915_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2915_, 0, v_a_2908_);
                    v___x_2913_ = v_reuseFailAlloc_2915_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2914_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2914_, 0, v___x_2913_);
                return v___x_2914_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__22___boxed(
    mut v___f_2919_: *mut LeanObject,
    mut v___y_2920_: *mut LeanObject,
    mut v_x_2921_: *mut LeanObject,
    mut v___y_2922_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2923_: *mut LeanObject = core::ptr::null_mut();
    v_res_2923_ = l_Std_Http_Server_serve___redArg___lam__22(v___f_2919_, v___y_2920_, v_x_2921_);
    lean_dec_ref(v___y_2920_);
    return v_res_2923_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__23(
    mut v___x_2924_: u8,
    mut v___x_2925_: u8,
    mut v___f_2926_: *mut LeanObject,
    mut v_x_2927_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2932_: u8 = 0;
    let mut v___x_2934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2937_: u8 = 0;
    let mut v___x_2939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2940_: u8 = 0;
    let mut v___x_2941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2948_: u8 = 0;
    let mut v_unused_2949_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2927_) == 0 {
                    lean_dec_ref(v___f_2926_);
                    v_a_2929_ = lean_ctor_get(v_x_2927_, 0);
                    v_isSharedCheck_2937_ = (!lean_is_exclusive(v_x_2927_)) as u8;
                    if v_isSharedCheck_2937_ == 0 {
                        v___x_2931_ = v_x_2927_;
                        v_isShared_2932_ = v_isSharedCheck_2937_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2929_);
                        lean_dec(v_x_2927_);
                        v___x_2931_ = lean_box(0);
                        v_isShared_2932_ = v_isSharedCheck_2937_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_isSharedCheck_2948_ = (!lean_is_exclusive(v_x_2927_)) as u8;
                    if v_isSharedCheck_2948_ == 0 {
                        v_unused_2949_ = lean_ctor_get(v_x_2927_, 0);
                        lean_dec(v_unused_2949_);
                        v___x_2939_ = v_x_2927_;
                        v_isShared_2940_ = v_isSharedCheck_2948_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v_x_2927_);
                        v___x_2939_ = lean_box(0);
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
                    v_reuseFailAlloc_2936_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2936_, 0, v_a_2929_);
                    v___x_2934_ = v_reuseFailAlloc_2936_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2935_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2935_, 0, v___x_2934_);
                return v___x_2935_;
            }
            3 => {
                v___x_2941_ = lean_box((v___x_2924_) as usize);
                if v_isShared_2940_ == 0 {
                    lean_ctor_set(v___x_2939_, 0, v___x_2941_);
                    v___x_2943_ = v___x_2939_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2947_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2947_, 0, v___x_2941_);
                    v___x_2943_ = v_reuseFailAlloc_2947_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2944_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2944_, 0, v___x_2943_);
                v___x_2945_ = lean_unsigned_to_nat(0);
                v___x_2946_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
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
    mut v___x_2950_: *mut LeanObject,
    mut v___x_2951_: *mut LeanObject,
    mut v___f_2952_: *mut LeanObject,
    mut v_x_2953_: *mut LeanObject,
    mut v___y_2954_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_14670__boxed_2955_: u8 = 0;
    let mut v___x_14671__boxed_2956_: u8 = 0;
    let mut v_res_2957_: *mut LeanObject = core::ptr::null_mut();
    v___x_14670__boxed_2955_ = (lean_unbox(v___x_2950_) as u8);
    v___x_14671__boxed_2956_ = (lean_unbox(v___x_2951_) as u8);
    v_res_2957_ = l_Std_Http_Server_serve___redArg___lam__23(
        v___x_14670__boxed_2955_,
        v___x_14671__boxed_2956_,
        v___f_2952_,
        v_x_2953_,
    );
    return v_res_2957_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__24(
    mut v___f_2958_: *mut LeanObject,
    mut v___x_2959_: u8,
    mut v___f_2960_: *mut LeanObject,
    mut v_x_2961_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2966_: u8 = 0;
    let mut v___x_2968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2971_: u8 = 0;
    let mut v_a_2972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2961_) == 0 {
                    lean_dec_ref(v___f_2960_);
                    lean_dec_ref(v___f_2958_);
                    v_a_2963_ = lean_ctor_get(v_x_2961_, 0);
                    v_isSharedCheck_2971_ = (!lean_is_exclusive(v_x_2961_)) as u8;
                    if v_isSharedCheck_2971_ == 0 {
                        v___x_2965_ = v_x_2961_;
                        v_isShared_2966_ = v_isSharedCheck_2971_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2963_);
                        lean_dec(v_x_2961_);
                        v___x_2965_ = lean_box(0);
                        v_isShared_2966_ = v_isSharedCheck_2971_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2972_ = lean_ctor_get(v_x_2961_, 0);
                    lean_inc(v_a_2972_);
                    lean_dec_ref_known(v_x_2961_, 1);
                    v___x_2973_ = l_IO_Promise_result_x21___redArg(v_a_2972_);
                    lean_dec(v_a_2972_);
                    v___x_2974_ = lean_unsigned_to_nat(0);
                    v___x_2975_ = lean_task_map(v___f_2958_, v___x_2973_, v___x_2974_, v___x_2959_);
                    v___x_2976_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2976_, 0, v___x_2975_);
                    v___x_2977_ =
                        l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                            lean_box(0),
                            lean_box(0),
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
                    v_reuseFailAlloc_2970_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2970_, 0, v_a_2963_);
                    v___x_2968_ = v_reuseFailAlloc_2970_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2969_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2969_, 0, v___x_2968_);
                return v___x_2969_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__24___boxed(
    mut v___f_2978_: *mut LeanObject,
    mut v___x_2979_: *mut LeanObject,
    mut v___f_2980_: *mut LeanObject,
    mut v_x_2981_: *mut LeanObject,
    mut v___y_2982_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_14729__boxed_2983_: u8 = 0;
    let mut v_res_2984_: *mut LeanObject = core::ptr::null_mut();
    v___x_14729__boxed_2983_ = (lean_unbox(v___x_2979_) as u8);
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
    mut v___f_2986_: *mut LeanObject,
    mut v_connectionLimit_2987_: *mut LeanObject,
    mut v___f_2988_: *mut LeanObject,
    mut v___f_2989_: *mut LeanObject,
    mut v_b_2990_: *mut LeanObject,
    mut v___y_2991_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3000_: u8 = 0;
    let mut v___x_3001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3003_: u8 = 0;
    let mut v___x_3004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3015_: u8 = 0;
    let mut v___f_3016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3021_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_connectionLimit_2987_) == 1 {
                    v_val_2997_ = lean_ctor_get(v_connectionLimit_2987_, 0);
                    v_isSharedCheck_3015_ = (!lean_is_exclusive(v_connectionLimit_2987_)) as u8;
                    if v_isSharedCheck_3015_ == 0 {
                        v___x_2999_ = v_connectionLimit_2987_;
                        v_isShared_3000_ = v_isSharedCheck_3015_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_2997_);
                        lean_dec(v_connectionLimit_2987_);
                        v___x_2999_ = lean_box(0);
                        v_isShared_3000_ = v_isSharedCheck_3015_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___f_2989_);
                    lean_dec(v_connectionLimit_2987_);
                    lean_inc_ref(v___y_2991_);
                    v___f_3016_ = lean_alloc_closure(
                        l_Std_Http_Server_serve___redArg___lam__22___boxed
                            as *mut core::ffi::c_void,
                        4,
                        2,
                    );
                    lean_closure_set(v___f_3016_, 0, v___f_2988_);
                    lean_closure_set(v___f_3016_, 1, v___y_2991_);
                    v___x_3017_ = lean_box((v___x_2985_) as usize);
                    v___x_3018_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3018_, 0, v___x_3017_);
                    v___x_3019_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3019_, 0, v___x_3018_);
                    v___x_3020_ = lean_unsigned_to_nat(0);
                    v___x_3021_ =
                        l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                            lean_box(0),
                            lean_box(0),
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
                v___x_2995_ = lean_unsigned_to_nat(0);
                v___x_2996_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
                    v___x_2995_,
                    v___x_2985_,
                    v___y_2994_,
                    v___f_2986_,
                );
                return v___x_2996_;
            }
            2 => {
                v___x_3001_ = l_Std_Semaphore_acquire(v_val_2997_);
                lean_inc_ref(v___y_2991_);
                v___f_3002_ = lean_alloc_closure(
                    l_Std_Http_Server_serve___redArg___lam__22___boxed as *mut core::ffi::c_void,
                    4,
                    2,
                );
                lean_closure_set(v___f_3002_, 0, v___f_2988_);
                lean_closure_set(v___f_3002_, 1, v___y_2991_);
                v___x_3003_ = 1;
                v___x_3004_ = lean_box((v___x_3003_) as usize);
                v___x_3005_ = lean_box((v___x_2985_) as usize);
                v___f_3006_ = lean_alloc_closure(
                    l_Std_Http_Server_serve___redArg___lam__23___boxed as *mut core::ffi::c_void,
                    5,
                    3,
                );
                lean_closure_set(v___f_3006_, 0, v___x_3004_);
                lean_closure_set(v___f_3006_, 1, v___x_3005_);
                lean_closure_set(v___f_3006_, 2, v___f_3002_);
                v___x_3007_ = lean_box((v___x_2985_) as usize);
                v___f_3008_ = lean_alloc_closure(
                    l_Std_Http_Server_serve___redArg___lam__24___boxed as *mut core::ffi::c_void,
                    5,
                    3,
                );
                lean_closure_set(v___f_3008_, 0, v___f_2989_);
                lean_closure_set(v___f_3008_, 1, v___x_3007_);
                lean_closure_set(v___f_3008_, 2, v___f_3006_);
                if v_isShared_3000_ == 0 {
                    lean_ctor_set(v___x_2999_, 0, v___x_3001_);
                    v___x_3010_ = v___x_2999_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3014_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3014_, 0, v___x_3001_);
                    v___x_3010_ = v_reuseFailAlloc_3014_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3011_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3011_, 0, v___x_3010_);
                v___x_3012_ = lean_unsigned_to_nat(0);
                v___x_3013_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
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
    mut v___x_3022_: *mut LeanObject,
    mut v___f_3023_: *mut LeanObject,
    mut v_connectionLimit_3024_: *mut LeanObject,
    mut v___f_3025_: *mut LeanObject,
    mut v___f_3026_: *mut LeanObject,
    mut v_b_3027_: *mut LeanObject,
    mut v___y_3028_: *mut LeanObject,
    mut v___y_3029_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_14773__boxed_3030_: u8 = 0;
    let mut v_res_3031_: *mut LeanObject = core::ptr::null_mut();
    v___x_14773__boxed_3030_ = (lean_unbox(v___x_3022_) as u8);
    v_res_3031_ = l_Std_Http_Server_serve___redArg___lam__26(
        v___x_14773__boxed_3030_,
        v___f_3023_,
        v_connectionLimit_3024_,
        v___f_3025_,
        v___f_3026_,
        v_b_3027_,
        v___y_3028_,
    );
    lean_dec_ref(v___y_3028_);
    return v_res_3031_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__25(
    mut v___x_3032_: *mut LeanObject,
    mut v___f_3033_: *mut LeanObject,
    mut v___x_3034_: *mut LeanObject,
    mut v___x_3035_: u8,
    mut v___f_3036_: *mut LeanObject,
    mut v___y_3037_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_13260__overap_3039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3042_: *mut LeanObject = core::ptr::null_mut();
    v___x_13260__overap_3039_ =
        l___private_Init_While_0__whileM_erased___redArg(v___x_3032_, v___f_3033_, v___x_3034_);
    v___x_3040_ = lean_apply_2(v___x_13260__overap_3039_, v___y_3037_, lean_box(0));
    v___x_3041_ = lean_unsigned_to_nat(0);
    v___x_3042_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_3041_,
        v___x_3035_,
        v___x_3040_,
        v___f_3036_,
    );
    return v___x_3042_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__25___boxed(
    mut v___x_3043_: *mut LeanObject,
    mut v___f_3044_: *mut LeanObject,
    mut v___x_3045_: *mut LeanObject,
    mut v___x_3046_: *mut LeanObject,
    mut v___f_3047_: *mut LeanObject,
    mut v___y_3048_: *mut LeanObject,
    mut v___y_3049_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_14852__boxed_3050_: u8 = 0;
    let mut v_res_3051_: *mut LeanObject = core::ptr::null_mut();
    v___x_14852__boxed_3050_ = (lean_unbox(v___x_3046_) as u8);
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
    mut v_x_3052_: *mut LeanObject,
    mut v_x_3053_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3058_: u8 = 0;
    let mut v___x_3060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3063_: u8 = 0;
    let mut v___x_3064_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3053_) == 0 {
                    lean_dec_ref(v_x_3052_);
                    v_a_3055_ = lean_ctor_get(v_x_3053_, 0);
                    v_isSharedCheck_3063_ = (!lean_is_exclusive(v_x_3053_)) as u8;
                    if v_isSharedCheck_3063_ == 0 {
                        v___x_3057_ = v_x_3053_;
                        v_isShared_3058_ = v_isSharedCheck_3063_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3055_);
                        lean_dec(v_x_3053_);
                        v___x_3057_ = lean_box(0);
                        v_isShared_3058_ = v_isSharedCheck_3063_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v_x_3053_, 1);
                    v___x_3064_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3064_, 0, v_x_3052_);
                    return v___x_3064_;
                }
            }
            1 => {
                if v_isShared_3058_ == 0 {
                    v___x_3060_ = v___x_3057_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3062_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3062_, 0, v_a_3055_);
                    v___x_3060_ = v_reuseFailAlloc_3062_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3061_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3061_, 0, v___x_3060_);
                return v___x_3061_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__27___boxed(
    mut v_x_3065_: *mut LeanObject,
    mut v_x_3066_: *mut LeanObject,
    mut v___y_3067_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3068_: *mut LeanObject = core::ptr::null_mut();
    v_res_3068_ = l_Std_Http_Server_serve___redArg___lam__27(v_x_3065_, v_x_3066_);
    return v_res_3068_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__28(
    mut v___f_3073_: *mut LeanObject,
    mut v___x_3074_: *mut LeanObject,
    mut v___f_3075_: *mut LeanObject,
    mut v___f_3076_: *mut LeanObject,
    mut v_inst_3077_: *mut LeanObject,
    mut v_handler_3078_: *mut LeanObject,
    mut v_config_3079_: *mut LeanObject,
    mut v___f_3080_: *mut LeanObject,
    mut v_a_3081_: *mut LeanObject,
    mut v___f_3082_: *mut LeanObject,
    mut v___f_3083_: *mut LeanObject,
    mut v___f_3084_: *mut LeanObject,
    mut v___f_3085_: *mut LeanObject,
    mut v___f_3086_: *mut LeanObject,
    mut v_x_3087_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_3087_) == 0 {
        let mut v___x_3089_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v___f_3086_);
        lean_dec_ref(v___f_3085_);
        lean_dec_ref(v___f_3084_);
        lean_dec_ref(v___f_3083_);
        lean_dec_ref(v___f_3082_);
        lean_dec(v_a_3081_);
        lean_dec_ref(v___f_3080_);
        lean_dec_ref(v_config_3079_);
        lean_dec(v_handler_3078_);
        lean_dec_ref(v_inst_3077_);
        lean_dec_ref(v___f_3076_);
        lean_dec_ref(v___f_3075_);
        lean_dec_ref(v___x_3074_);
        lean_dec_ref(v___f_3073_);
        v___x_3089_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_3089_, 0, v_x_3087_);
        return v___x_3089_;
    } else {
        let mut v_a_3090_: *mut LeanObject = core::ptr::null_mut();
        let mut v_context_3091_: *mut LeanObject = core::ptr::null_mut();
        let mut v_activeConnections_3092_: *mut LeanObject = core::ptr::null_mut();
        let mut v_connectionLimit_3093_: *mut LeanObject = core::ptr::null_mut();
        let mut v_shutdownPromise_3094_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_3095_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_3096_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3097_: u8 = 0;
        let mut v___x_3098_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_3099_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_3100_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3101_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_3102_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3103_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_3104_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3105_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_3106_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3107_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3108_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3109_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3110_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3111_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_3112_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3113_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3114_: *mut LeanObject = core::ptr::null_mut();
        v_a_3090_ = lean_ctor_get(v_x_3087_, 0);
        v_context_3091_ = lean_ctor_get(v_a_3090_, 0);
        v_activeConnections_3092_ = lean_ctor_get(v_a_3090_, 1);
        v_connectionLimit_3093_ = lean_ctor_get(v_a_3090_, 2);
        v_shutdownPromise_3094_ = lean_ctor_get(v_a_3090_, 3);
        lean_inc_ref(v_shutdownPromise_3094_);
        lean_inc_ref_n(v_context_3091_, 2);
        v___f_3095_ = lean_alloc_closure(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__3___boxed as *mut core::ffi::c_void, 4, 2);
        lean_closure_set(v___f_3095_, 0, v_context_3091_);
        lean_closure_set(v___f_3095_, 1, v_shutdownPromise_3094_);
        v___f_3096_ = lean_alloc_closure(l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__4___boxed as *mut core::ffi::c_void, 5, 1);
        lean_closure_set(v___f_3096_, 0, v___f_3095_);
        v___x_3097_ = 0;
        v___x_3098_ = lean_box(0);
        v___f_3099_ = l_Std_Http_Server_serve___redArg___lam__28___closed__0;
        v___f_3100_ = l_Std_Http_Server_serve___redArg___lam__28___closed__1;
        v___x_3101_ = lean_box((v___x_3097_) as usize);
        lean_inc_ref(v_activeConnections_3092_);
        lean_inc_ref(v___x_3074_);
        lean_inc_n(v_connectionLimit_3093_, 2);
        v___f_3102_ = lean_alloc_closure(
            l_Std_Http_Server_serve___redArg___lam__21___boxed as *mut core::ffi::c_void,
            21,
            18,
        );
        lean_closure_set(v___f_3102_, 0, v___x_3101_);
        lean_closure_set(v___f_3102_, 1, v___f_3073_);
        lean_closure_set(v___f_3102_, 2, v___f_3099_);
        lean_closure_set(v___f_3102_, 3, v___x_3098_);
        lean_closure_set(v___f_3102_, 4, v_connectionLimit_3093_);
        lean_closure_set(v___f_3102_, 5, v___x_3074_);
        lean_closure_set(v___f_3102_, 6, v_activeConnections_3092_);
        lean_closure_set(v___f_3102_, 7, v___f_3075_);
        lean_closure_set(v___f_3102_, 8, v___f_3076_);
        lean_closure_set(v___f_3102_, 9, v___f_3096_);
        lean_closure_set(v___f_3102_, 10, v_inst_3077_);
        lean_closure_set(v___f_3102_, 11, v_handler_3078_);
        lean_closure_set(v___f_3102_, 12, v_config_3079_);
        lean_closure_set(v___f_3102_, 13, v___f_3080_);
        lean_closure_set(v___f_3102_, 14, v___f_3100_);
        lean_closure_set(v___f_3102_, 15, v_a_3081_);
        lean_closure_set(v___f_3102_, 16, v___f_3082_);
        lean_closure_set(v___f_3102_, 17, v___f_3083_);
        v___x_3103_ = lean_box((v___x_3097_) as usize);
        v___f_3104_ = lean_alloc_closure(
            l_Std_Http_Server_serve___redArg___lam__26___boxed as *mut core::ffi::c_void,
            8,
            5,
        );
        lean_closure_set(v___f_3104_, 0, v___x_3103_);
        lean_closure_set(v___f_3104_, 1, v___f_3084_);
        lean_closure_set(v___f_3104_, 2, v_connectionLimit_3093_);
        lean_closure_set(v___f_3104_, 3, v___f_3102_);
        lean_closure_set(v___f_3104_, 4, v___f_3085_);
        v___x_3105_ = lean_box((v___x_3097_) as usize);
        v___f_3106_ = lean_alloc_closure(
            l_Std_Http_Server_serve___redArg___lam__25___boxed as *mut core::ffi::c_void,
            7,
            5,
        );
        lean_closure_set(v___f_3106_, 0, v___x_3074_);
        lean_closure_set(v___f_3106_, 1, v___f_3104_);
        lean_closure_set(v___f_3106_, 2, v___x_3098_);
        lean_closure_set(v___f_3106_, 3, v___x_3105_);
        lean_closure_set(v___f_3106_, 4, v___f_3086_);
        v___x_3107_ = lean_box((v___x_3097_) as usize);
        lean_inc(v_a_3090_);
        v___x_3108_ = lean_alloc_closure(
            l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___boxed
                as *mut core::ffi::c_void,
            6,
            5,
        );
        lean_closure_set(v___x_3108_, 0, lean_box(0));
        lean_closure_set(v___x_3108_, 1, v_a_3090_);
        lean_closure_set(v___x_3108_, 2, v___x_3107_);
        lean_closure_set(v___x_3108_, 3, v___f_3106_);
        lean_closure_set(v___x_3108_, 4, v_context_3091_);
        v___x_3109_ = lean_unsigned_to_nat(0);
        v___x_3110_ = lean_alloc_closure(
            l_Std_Async_BaseAsync_toRawBaseIO___boxed as *mut core::ffi::c_void,
            3,
            2,
        );
        lean_closure_set(v___x_3110_, 0, lean_box(0));
        lean_closure_set(v___x_3110_, 1, v___x_3108_);
        v___x_3111_ = lean_io_as_task(v___x_3110_, v___x_3109_);
        lean_dec_ref(v___x_3111_);
        v___f_3112_ = lean_alloc_closure(
            l_Std_Http_Server_serve___redArg___lam__27___boxed as *mut core::ffi::c_void,
            3,
            1,
        );
        lean_closure_set(v___f_3112_, 0, v_x_3087_);
        v___x_3113_ = l___private_Std_Http_Server_0__Std_Http_Server_frameCancellation___redArg___lam__0___closed__1;
        v___x_3114_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
            lean_box(0),
            lean_box(0),
            v___x_3109_,
            v___x_3097_,
            v___x_3113_,
            v___f_3112_,
        );
        return v___x_3114_;
    }
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__28___boxed(
    mut v___f_3115_: *mut LeanObject,
    mut v___x_3116_: *mut LeanObject,
    mut v___f_3117_: *mut LeanObject,
    mut v___f_3118_: *mut LeanObject,
    mut v_inst_3119_: *mut LeanObject,
    mut v_handler_3120_: *mut LeanObject,
    mut v_config_3121_: *mut LeanObject,
    mut v___f_3122_: *mut LeanObject,
    mut v_a_3123_: *mut LeanObject,
    mut v___f_3124_: *mut LeanObject,
    mut v___f_3125_: *mut LeanObject,
    mut v___f_3126_: *mut LeanObject,
    mut v___f_3127_: *mut LeanObject,
    mut v___f_3128_: *mut LeanObject,
    mut v_x_3129_: *mut LeanObject,
    mut v___y_3130_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3131_: *mut LeanObject = core::ptr::null_mut();
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
    mut v___f_3132_: *mut LeanObject,
    mut v_config_3133_: *mut LeanObject,
    mut v_x_3134_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_val_3137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3140_: u8 = 0;
    let mut v___x_3141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3145_: u8 = 0;
    let mut v___x_3147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3150_: u8 = 0;
    let mut v_a_3151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3154_: u8 = 0;
    let mut v___x_3155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3161_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3134_) == 0 {
                    lean_dec_ref(v_config_3133_);
                    lean_dec_ref(v___f_3132_);
                    v_a_3142_ = lean_ctor_get(v_x_3134_, 0);
                    v_isSharedCheck_3150_ = (!lean_is_exclusive(v_x_3134_)) as u8;
                    if v_isSharedCheck_3150_ == 0 {
                        v___x_3144_ = v_x_3134_;
                        v_isShared_3145_ = v_isSharedCheck_3150_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_3142_);
                        lean_dec(v_x_3134_);
                        v___x_3144_ = lean_box(0);
                        v_isShared_3145_ = v_isSharedCheck_3150_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_3151_ = lean_ctor_get(v_x_3134_, 0);
                    v_isSharedCheck_3161_ = (!lean_is_exclusive(v_x_3134_)) as u8;
                    if v_isSharedCheck_3161_ == 0 {
                        v___x_3153_ = v_x_3134_;
                        v_isShared_3154_ = v_isSharedCheck_3161_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_3151_);
                        lean_dec(v_x_3134_);
                        v___x_3153_ = lean_box(0);
                        v_isShared_3154_ = v_isSharedCheck_3161_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3138_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3138_, 0, v_val_3137_);
                v___x_3139_ = lean_unsigned_to_nat(0);
                v___x_3140_ = 0;
                v___x_3141_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
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
                    v_reuseFailAlloc_3149_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3149_, 0, v_a_3142_);
                    v___x_3147_ = v_reuseFailAlloc_3149_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3148_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3148_, 0, v___x_3147_);
                return v___x_3148_;
            }
            4 => {
                v___x_3155_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3155_, 0, v_a_3151_);
                v___x_3156_ = l_Std_Http_Server_new(v_config_3133_, v___x_3155_);
                v_a_3157_ = lean_ctor_get(v___x_3156_, 0);
                lean_inc(v_a_3157_);
                lean_dec_ref(v___x_3156_);
                if v_isShared_3154_ == 0 {
                    lean_ctor_set(v___x_3153_, 0, v_a_3157_);
                    v___x_3159_ = v___x_3153_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3160_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3160_, 0, v_a_3157_);
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
    mut v___f_3162_: *mut LeanObject,
    mut v_config_3163_: *mut LeanObject,
    mut v_x_3164_: *mut LeanObject,
    mut v___y_3165_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3166_: *mut LeanObject = core::ptr::null_mut();
    v_res_3166_ =
        l_Std_Http_Server_serve___redArg___lam__29(v___f_3162_, v_config_3163_, v_x_3164_);
    return v_res_3166_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__30(
    mut v___f_3167_: *mut LeanObject,
    mut v_a_3168_: *mut LeanObject,
    mut v_x_3169_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_val_3172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: u8 = 0;
    let mut v___x_3176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3180_: u8 = 0;
    let mut v___x_3182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3185_: u8 = 0;
    let mut v___x_3187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3188_: u8 = 0;
    let mut v___x_3189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3198_: u8 = 0;
    let mut v_unused_3199_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3169_) == 0 {
                    lean_dec_ref(v___f_3167_);
                    v_a_3177_ = lean_ctor_get(v_x_3169_, 0);
                    v_isSharedCheck_3185_ = (!lean_is_exclusive(v_x_3169_)) as u8;
                    if v_isSharedCheck_3185_ == 0 {
                        v___x_3179_ = v_x_3169_;
                        v_isShared_3180_ = v_isSharedCheck_3185_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_3177_);
                        lean_dec(v_x_3169_);
                        v___x_3179_ = lean_box(0);
                        v_isShared_3180_ = v_isSharedCheck_3185_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_isSharedCheck_3198_ = (!lean_is_exclusive(v_x_3169_)) as u8;
                    if v_isSharedCheck_3198_ == 0 {
                        v_unused_3199_ = lean_ctor_get(v_x_3169_, 0);
                        lean_dec(v_unused_3199_);
                        v___x_3187_ = v_x_3169_;
                        v_isShared_3188_ = v_isSharedCheck_3198_;
                        state = 4;
                        continue;
                    } else {
                        lean_dec(v_x_3169_);
                        v___x_3187_ = lean_box(0);
                        v_isShared_3188_ = v_isSharedCheck_3198_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3173_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3173_, 0, v_val_3172_);
                v___x_3174_ = lean_unsigned_to_nat(0);
                v___x_3175_ = 0;
                v___x_3176_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
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
                    v_reuseFailAlloc_3184_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3184_, 0, v_a_3177_);
                    v___x_3182_ = v_reuseFailAlloc_3184_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3183_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3183_, 0, v___x_3182_);
                return v___x_3183_;
            }
            4 => {
                v___x_3189_ = lean_uv_tcp_getsockname(v_a_3168_);
                if lean_obj_tag(v___x_3189_) == 0 {
                    v_a_3190_ = lean_ctor_get(v___x_3189_, 0);
                    lean_inc(v_a_3190_);
                    lean_dec_ref_known(v___x_3189_, 1);
                    if v_isShared_3188_ == 0 {
                        lean_ctor_set(v___x_3187_, 0, v_a_3190_);
                        v___x_3192_ = v___x_3187_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3193_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3193_, 0, v_a_3190_);
                        v___x_3192_ = v_reuseFailAlloc_3193_;
                        state = 5;
                        continue;
                    }
                } else {
                    v_a_3194_ = lean_ctor_get(v___x_3189_, 0);
                    lean_inc(v_a_3194_);
                    lean_dec_ref_known(v___x_3189_, 1);
                    if v_isShared_3188_ == 0 {
                        lean_ctor_set_tag(v___x_3187_, 0);
                        lean_ctor_set(v___x_3187_, 0, v_a_3194_);
                        v___x_3196_ = v___x_3187_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_3197_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3197_, 0, v_a_3194_);
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
    mut v___f_3200_: *mut LeanObject,
    mut v_a_3201_: *mut LeanObject,
    mut v_x_3202_: *mut LeanObject,
    mut v___y_3203_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3204_: *mut LeanObject = core::ptr::null_mut();
    v_res_3204_ = l_Std_Http_Server_serve___redArg___lam__30(v___f_3200_, v_a_3201_, v_x_3202_);
    lean_dec(v_a_3201_);
    return v_res_3204_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__31(
    mut v___f_3205_: *mut LeanObject,
    mut v_a_3206_: *mut LeanObject,
    mut v_x_3207_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_val_3210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: u8 = 0;
    let mut v___x_3214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3218_: u8 = 0;
    let mut v___x_3220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3223_: u8 = 0;
    let mut v___x_3225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3226_: u8 = 0;
    let mut v___x_3227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3236_: u8 = 0;
    let mut v_unused_3237_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3207_) == 0 {
                    lean_dec_ref(v___f_3205_);
                    v_a_3215_ = lean_ctor_get(v_x_3207_, 0);
                    v_isSharedCheck_3223_ = (!lean_is_exclusive(v_x_3207_)) as u8;
                    if v_isSharedCheck_3223_ == 0 {
                        v___x_3217_ = v_x_3207_;
                        v_isShared_3218_ = v_isSharedCheck_3223_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_3215_);
                        lean_dec(v_x_3207_);
                        v___x_3217_ = lean_box(0);
                        v_isShared_3218_ = v_isSharedCheck_3223_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_isSharedCheck_3236_ = (!lean_is_exclusive(v_x_3207_)) as u8;
                    if v_isSharedCheck_3236_ == 0 {
                        v_unused_3237_ = lean_ctor_get(v_x_3207_, 0);
                        lean_dec(v_unused_3237_);
                        v___x_3225_ = v_x_3207_;
                        v_isShared_3226_ = v_isSharedCheck_3236_;
                        state = 4;
                        continue;
                    } else {
                        lean_dec(v_x_3207_);
                        v___x_3225_ = lean_box(0);
                        v_isShared_3226_ = v_isSharedCheck_3236_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3211_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3211_, 0, v_val_3210_);
                v___x_3212_ = lean_unsigned_to_nat(0);
                v___x_3213_ = 0;
                v___x_3214_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
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
                    v_reuseFailAlloc_3222_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3222_, 0, v_a_3215_);
                    v___x_3220_ = v_reuseFailAlloc_3222_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3221_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3221_, 0, v___x_3220_);
                return v___x_3221_;
            }
            4 => {
                v___x_3227_ = lean_uv_tcp_nodelay(v_a_3206_);
                if lean_obj_tag(v___x_3227_) == 0 {
                    v_a_3228_ = lean_ctor_get(v___x_3227_, 0);
                    lean_inc(v_a_3228_);
                    lean_dec_ref_known(v___x_3227_, 1);
                    if v_isShared_3226_ == 0 {
                        lean_ctor_set(v___x_3225_, 0, v_a_3228_);
                        v___x_3230_ = v___x_3225_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3231_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3231_, 0, v_a_3228_);
                        v___x_3230_ = v_reuseFailAlloc_3231_;
                        state = 5;
                        continue;
                    }
                } else {
                    v_a_3232_ = lean_ctor_get(v___x_3227_, 0);
                    lean_inc(v_a_3232_);
                    lean_dec_ref_known(v___x_3227_, 1);
                    if v_isShared_3226_ == 0 {
                        lean_ctor_set_tag(v___x_3225_, 0);
                        lean_ctor_set(v___x_3225_, 0, v_a_3232_);
                        v___x_3234_ = v___x_3225_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_3235_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3235_, 0, v_a_3232_);
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
    mut v___f_3238_: *mut LeanObject,
    mut v_a_3239_: *mut LeanObject,
    mut v_x_3240_: *mut LeanObject,
    mut v___y_3241_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3242_: *mut LeanObject = core::ptr::null_mut();
    v_res_3242_ = l_Std_Http_Server_serve___redArg___lam__31(v___f_3238_, v_a_3239_, v_x_3240_);
    lean_dec(v_a_3239_);
    return v_res_3242_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__32(
    mut v___f_3243_: *mut LeanObject,
    mut v_a_3244_: *mut LeanObject,
    mut v_backlog_3245_: u32,
    mut v_x_3246_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_val_3249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3252_: u8 = 0;
    let mut v___x_3253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3257_: u8 = 0;
    let mut v___x_3259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3262_: u8 = 0;
    let mut v___x_3264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3265_: u8 = 0;
    let mut v___x_3266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3275_: u8 = 0;
    let mut v_unused_3276_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3246_) == 0 {
                    lean_dec_ref(v___f_3243_);
                    v_a_3254_ = lean_ctor_get(v_x_3246_, 0);
                    v_isSharedCheck_3262_ = (!lean_is_exclusive(v_x_3246_)) as u8;
                    if v_isSharedCheck_3262_ == 0 {
                        v___x_3256_ = v_x_3246_;
                        v_isShared_3257_ = v_isSharedCheck_3262_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_3254_);
                        lean_dec(v_x_3246_);
                        v___x_3256_ = lean_box(0);
                        v_isShared_3257_ = v_isSharedCheck_3262_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_isSharedCheck_3275_ = (!lean_is_exclusive(v_x_3246_)) as u8;
                    if v_isSharedCheck_3275_ == 0 {
                        v_unused_3276_ = lean_ctor_get(v_x_3246_, 0);
                        lean_dec(v_unused_3276_);
                        v___x_3264_ = v_x_3246_;
                        v_isShared_3265_ = v_isSharedCheck_3275_;
                        state = 4;
                        continue;
                    } else {
                        lean_dec(v_x_3246_);
                        v___x_3264_ = lean_box(0);
                        v_isShared_3265_ = v_isSharedCheck_3275_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3250_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3250_, 0, v_val_3249_);
                v___x_3251_ = lean_unsigned_to_nat(0);
                v___x_3252_ = 0;
                v___x_3253_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
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
                    v_reuseFailAlloc_3261_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3261_, 0, v_a_3254_);
                    v___x_3259_ = v_reuseFailAlloc_3261_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3260_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3260_, 0, v___x_3259_);
                return v___x_3260_;
            }
            4 => {
                v___x_3266_ = lean_uv_tcp_listen(v_a_3244_, v_backlog_3245_);
                if lean_obj_tag(v___x_3266_) == 0 {
                    v_a_3267_ = lean_ctor_get(v___x_3266_, 0);
                    lean_inc(v_a_3267_);
                    lean_dec_ref_known(v___x_3266_, 1);
                    if v_isShared_3265_ == 0 {
                        lean_ctor_set(v___x_3264_, 0, v_a_3267_);
                        v___x_3269_ = v___x_3264_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3270_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3270_, 0, v_a_3267_);
                        v___x_3269_ = v_reuseFailAlloc_3270_;
                        state = 5;
                        continue;
                    }
                } else {
                    v_a_3271_ = lean_ctor_get(v___x_3266_, 0);
                    lean_inc(v_a_3271_);
                    lean_dec_ref_known(v___x_3266_, 1);
                    if v_isShared_3265_ == 0 {
                        lean_ctor_set_tag(v___x_3264_, 0);
                        lean_ctor_set(v___x_3264_, 0, v_a_3271_);
                        v___x_3273_ = v___x_3264_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_3274_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3274_, 0, v_a_3271_);
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
    mut v___f_3277_: *mut LeanObject,
    mut v_a_3278_: *mut LeanObject,
    mut v_backlog_3279_: *mut LeanObject,
    mut v_x_3280_: *mut LeanObject,
    mut v___y_3281_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_backlog_boxed_3282_: u32 = 0;
    let mut v_res_3283_: *mut LeanObject = core::ptr::null_mut();
    v_backlog_boxed_3282_ = lean_unbox_uint32(v_backlog_3279_);
    lean_dec(v_backlog_3279_);
    v_res_3283_ = l_Std_Http_Server_serve___redArg___lam__32(
        v___f_3277_,
        v_a_3278_,
        v_backlog_boxed_3282_,
        v_x_3280_,
    );
    lean_dec(v_a_3278_);
    return v_res_3283_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg___lam__33(
    mut v___f_3284_: *mut LeanObject,
    mut v___x_3285_: *mut LeanObject,
    mut v___f_3286_: *mut LeanObject,
    mut v___f_3287_: *mut LeanObject,
    mut v_inst_3288_: *mut LeanObject,
    mut v_handler_3289_: *mut LeanObject,
    mut v_config_3290_: *mut LeanObject,
    mut v___f_3291_: *mut LeanObject,
    mut v___f_3292_: *mut LeanObject,
    mut v___f_3293_: *mut LeanObject,
    mut v___f_3294_: *mut LeanObject,
    mut v___f_3295_: *mut LeanObject,
    mut v___f_3296_: *mut LeanObject,
    mut v_backlog_3297_: u32,
    mut v_addr_3298_: *mut LeanObject,
    mut v_x_3299_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3304_: u8 = 0;
    let mut v___x_3306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3309_: u8 = 0;
    let mut v_a_3310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3313_: u8 = 0;
    let mut v___f_3314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: u8 = 0;
    let mut v___x_3325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3335_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3299_) == 0 {
                    lean_dec_ref(v___f_3296_);
                    lean_dec_ref(v___f_3295_);
                    lean_dec_ref(v___f_3294_);
                    lean_dec_ref(v___f_3293_);
                    lean_dec_ref(v___f_3292_);
                    lean_dec_ref(v___f_3291_);
                    lean_dec_ref(v_config_3290_);
                    lean_dec(v_handler_3289_);
                    lean_dec_ref(v_inst_3288_);
                    lean_dec_ref(v___f_3287_);
                    lean_dec_ref(v___f_3286_);
                    lean_dec_ref(v___x_3285_);
                    lean_dec_ref(v___f_3284_);
                    v_a_3301_ = lean_ctor_get(v_x_3299_, 0);
                    v_isSharedCheck_3309_ = (!lean_is_exclusive(v_x_3299_)) as u8;
                    if v_isSharedCheck_3309_ == 0 {
                        v___x_3303_ = v_x_3299_;
                        v_isShared_3304_ = v_isSharedCheck_3309_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3301_);
                        lean_dec(v_x_3299_);
                        v___x_3303_ = lean_box(0);
                        v_isShared_3304_ = v_isSharedCheck_3309_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3310_ = lean_ctor_get(v_x_3299_, 0);
                    v_isSharedCheck_3335_ = (!lean_is_exclusive(v_x_3299_)) as u8;
                    if v_isSharedCheck_3335_ == 0 {
                        v___x_3312_ = v_x_3299_;
                        v_isShared_3313_ = v_isSharedCheck_3335_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3310_);
                        lean_dec(v_x_3299_);
                        v___x_3312_ = lean_box(0);
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
                    v_reuseFailAlloc_3308_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3308_, 0, v_a_3301_);
                    v___x_3306_ = v_reuseFailAlloc_3308_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3307_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3307_, 0, v___x_3306_);
                return v___x_3307_;
            }
            3 => {
                lean_inc_n(v_a_3310_, 4);
                lean_inc_ref(v_config_3290_);
                v___f_3314_ = lean_alloc_closure(
                    l_Std_Http_Server_serve___redArg___lam__28___boxed as *mut core::ffi::c_void,
                    16,
                    14,
                );
                lean_closure_set(v___f_3314_, 0, v___f_3284_);
                lean_closure_set(v___f_3314_, 1, v___x_3285_);
                lean_closure_set(v___f_3314_, 2, v___f_3286_);
                lean_closure_set(v___f_3314_, 3, v___f_3287_);
                lean_closure_set(v___f_3314_, 4, v_inst_3288_);
                lean_closure_set(v___f_3314_, 5, v_handler_3289_);
                lean_closure_set(v___f_3314_, 6, v_config_3290_);
                lean_closure_set(v___f_3314_, 7, v___f_3291_);
                lean_closure_set(v___f_3314_, 8, v_a_3310_);
                lean_closure_set(v___f_3314_, 9, v___f_3292_);
                lean_closure_set(v___f_3314_, 10, v___f_3293_);
                lean_closure_set(v___f_3314_, 11, v___f_3294_);
                lean_closure_set(v___f_3314_, 12, v___f_3295_);
                lean_closure_set(v___f_3314_, 13, v___f_3296_);
                v___f_3315_ = lean_alloc_closure(
                    l_Std_Http_Server_serve___redArg___lam__29___boxed as *mut core::ffi::c_void,
                    4,
                    2,
                );
                lean_closure_set(v___f_3315_, 0, v___f_3314_);
                lean_closure_set(v___f_3315_, 1, v_config_3290_);
                v___f_3316_ = lean_alloc_closure(
                    l_Std_Http_Server_serve___redArg___lam__30___boxed as *mut core::ffi::c_void,
                    4,
                    2,
                );
                lean_closure_set(v___f_3316_, 0, v___f_3315_);
                lean_closure_set(v___f_3316_, 1, v_a_3310_);
                v___f_3317_ = lean_alloc_closure(
                    l_Std_Http_Server_serve___redArg___lam__31___boxed as *mut core::ffi::c_void,
                    4,
                    2,
                );
                lean_closure_set(v___f_3317_, 0, v___f_3316_);
                lean_closure_set(v___f_3317_, 1, v_a_3310_);
                v___x_3318_ = lean_box_uint32(v_backlog_3297_);
                v___f_3319_ = lean_alloc_closure(
                    l_Std_Http_Server_serve___redArg___lam__32___boxed as *mut core::ffi::c_void,
                    5,
                    3,
                );
                lean_closure_set(v___f_3319_, 0, v___f_3317_);
                lean_closure_set(v___f_3319_, 1, v_a_3310_);
                lean_closure_set(v___f_3319_, 2, v___x_3318_);
                v___x_3326_ = lean_uv_tcp_bind(v_a_3310_, v_addr_3298_);
                lean_dec(v_a_3310_);
                if lean_obj_tag(v___x_3326_) == 0 {
                    v_a_3327_ = lean_ctor_get(v___x_3326_, 0);
                    lean_inc(v_a_3327_);
                    lean_dec_ref_known(v___x_3326_, 1);
                    if v_isShared_3313_ == 0 {
                        lean_ctor_set(v___x_3312_, 0, v_a_3327_);
                        v___x_3329_ = v___x_3312_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3330_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3330_, 0, v_a_3327_);
                        v___x_3329_ = v_reuseFailAlloc_3330_;
                        state = 5;
                        continue;
                    }
                } else {
                    v_a_3331_ = lean_ctor_get(v___x_3326_, 0);
                    lean_inc(v_a_3331_);
                    lean_dec_ref_known(v___x_3326_, 1);
                    if v_isShared_3313_ == 0 {
                        lean_ctor_set_tag(v___x_3312_, 0);
                        lean_ctor_set(v___x_3312_, 0, v_a_3331_);
                        v___x_3333_ = v___x_3312_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_3334_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3334_, 0, v_a_3331_);
                        v___x_3333_ = v_reuseFailAlloc_3334_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                v___x_3322_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3322_, 0, v_val_3321_);
                v___x_3323_ = lean_unsigned_to_nat(0);
                v___x_3324_ = 0;
                v___x_3325_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
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
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3336_: *mut LeanObject = *_args.add(0);
    let mut v___x_3337_: *mut LeanObject = *_args.add(1);
    let mut v___f_3338_: *mut LeanObject = *_args.add(2);
    let mut v___f_3339_: *mut LeanObject = *_args.add(3);
    let mut v_inst_3340_: *mut LeanObject = *_args.add(4);
    let mut v_handler_3341_: *mut LeanObject = *_args.add(5);
    let mut v_config_3342_: *mut LeanObject = *_args.add(6);
    let mut v___f_3343_: *mut LeanObject = *_args.add(7);
    let mut v___f_3344_: *mut LeanObject = *_args.add(8);
    let mut v___f_3345_: *mut LeanObject = *_args.add(9);
    let mut v___f_3346_: *mut LeanObject = *_args.add(10);
    let mut v___f_3347_: *mut LeanObject = *_args.add(11);
    let mut v___f_3348_: *mut LeanObject = *_args.add(12);
    let mut v_backlog_3349_: *mut LeanObject = *_args.add(13);
    let mut v_addr_3350_: *mut LeanObject = *_args.add(14);
    let mut v_x_3351_: *mut LeanObject = *_args.add(15);
    let mut v___y_3352_: *mut LeanObject = *_args.add(16);
    let mut v_backlog_boxed_3353_: u32 = 0;
    let mut v_res_3354_: *mut LeanObject = core::ptr::null_mut();
    v_backlog_boxed_3353_ = lean_unbox_uint32(v_backlog_3349_);
    lean_dec(v_backlog_3349_);
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
    lean_dec_ref(v_addr_3350_);
    return v_res_3354_;
}
pub unsafe fn l_Std_Http_Server_serve___redArg(
    mut v_inst_3361_: *mut LeanObject,
    mut v_addr_3362_: *mut LeanObject,
    mut v_handler_3363_: *mut LeanObject,
    mut v_config_3364_: *mut LeanObject,
    mut v_backlog_3365_: u32,
) -> *mut LeanObject {
    let mut v___f_3367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3383_: u8 = 0;
    let mut v___x_3384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3389_: u8 = 0;
    let mut v___x_3391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3393_: u8 = 0;
    let mut v_a_3394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3397_: u8 = 0;
    let mut v___x_3399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3400_: *mut LeanObject = core::ptr::null_mut();
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
                v___x_3377_ = lean_box_uint32(v_backlog_3365_);
                v___f_3378_ = lean_alloc_closure(
                    l_Std_Http_Server_serve___redArg___lam__33___boxed as *mut core::ffi::c_void,
                    17,
                    15,
                );
                lean_closure_set(v___f_3378_, 0, v___f_3374_);
                lean_closure_set(v___f_3378_, 1, v___x_3376_);
                lean_closure_set(v___f_3378_, 2, v___f_3369_);
                lean_closure_set(v___f_3378_, 3, v___f_3371_);
                lean_closure_set(v___f_3378_, 4, v_inst_3361_);
                lean_closure_set(v___f_3378_, 5, v_handler_3363_);
                lean_closure_set(v___f_3378_, 6, v_config_3364_);
                lean_closure_set(v___f_3378_, 7, v___f_3370_);
                lean_closure_set(v___f_3378_, 8, v___f_3373_);
                lean_closure_set(v___f_3378_, 9, v___f_3372_);
                lean_closure_set(v___f_3378_, 10, v___f_3368_);
                lean_closure_set(v___f_3378_, 11, v___f_3375_);
                lean_closure_set(v___f_3378_, 12, v___f_3367_);
                lean_closure_set(v___f_3378_, 13, v___x_3377_);
                lean_closure_set(v___f_3378_, 14, v_addr_3362_);
                v___x_3385_ = lean_uv_tcp_new();
                if lean_obj_tag(v___x_3385_) == 0 {
                    v_a_3386_ = lean_ctor_get(v___x_3385_, 0);
                    v_isSharedCheck_3393_ = (!lean_is_exclusive(v___x_3385_)) as u8;
                    if v_isSharedCheck_3393_ == 0 {
                        v___x_3388_ = v___x_3385_;
                        v_isShared_3389_ = v_isSharedCheck_3393_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_3386_);
                        lean_dec(v___x_3385_);
                        v___x_3388_ = lean_box(0);
                        v_isShared_3389_ = v_isSharedCheck_3393_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_3394_ = lean_ctor_get(v___x_3385_, 0);
                    v_isSharedCheck_3401_ = (!lean_is_exclusive(v___x_3385_)) as u8;
                    if v_isSharedCheck_3401_ == 0 {
                        v___x_3396_ = v___x_3385_;
                        v_isShared_3397_ = v_isSharedCheck_3401_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_3394_);
                        lean_dec(v___x_3385_);
                        v___x_3396_ = lean_box(0);
                        v_isShared_3397_ = v_isSharedCheck_3401_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3381_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3381_, 0, v_val_3380_);
                v___x_3382_ = lean_unsigned_to_nat(0);
                v___x_3383_ = 0;
                v___x_3384_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
                    v___x_3382_,
                    v___x_3383_,
                    v___x_3381_,
                    v___f_3378_,
                );
                return v___x_3384_;
            }
            2 => {
                if v_isShared_3389_ == 0 {
                    lean_ctor_set_tag(v___x_3388_, 1);
                    v___x_3391_ = v___x_3388_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3392_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3392_, 0, v_a_3386_);
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
                    lean_ctor_set_tag(v___x_3396_, 0);
                    v___x_3399_ = v___x_3396_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3400_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3400_, 0, v_a_3394_);
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
    mut v_inst_3402_: *mut LeanObject,
    mut v_addr_3403_: *mut LeanObject,
    mut v_handler_3404_: *mut LeanObject,
    mut v_config_3405_: *mut LeanObject,
    mut v_backlog_3406_: *mut LeanObject,
    mut v_a_3407_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_backlog_boxed_3408_: u32 = 0;
    let mut v_res_3409_: *mut LeanObject = core::ptr::null_mut();
    v_backlog_boxed_3408_ = lean_unbox_uint32(v_backlog_3406_);
    lean_dec(v_backlog_3406_);
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
    mut v_00_u03c3_3410_: *mut LeanObject,
    mut v_inst_3411_: *mut LeanObject,
    mut v_addr_3412_: *mut LeanObject,
    mut v_handler_3413_: *mut LeanObject,
    mut v_config_3414_: *mut LeanObject,
    mut v_backlog_3415_: u32,
) -> *mut LeanObject {
    let mut v___x_3417_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03c3_3418_: *mut LeanObject,
    mut v_inst_3419_: *mut LeanObject,
    mut v_addr_3420_: *mut LeanObject,
    mut v_handler_3421_: *mut LeanObject,
    mut v_config_3422_: *mut LeanObject,
    mut v_backlog_3423_: *mut LeanObject,
    mut v_a_3424_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_backlog_boxed_3425_: u32 = 0;
    let mut v_res_3426_: *mut LeanObject = core::ptr::null_mut();
    v_backlog_boxed_3425_ = lean_unbox_uint32(v_backlog_3423_);
    lean_dec(v_backlog_3423_);
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
pub unsafe fn runtime_initialize_Std_Http_Server(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Async(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Async_TCP(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Sync_CancellationToken(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Sync_Semaphore(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Server_Config(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Server_Handler(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Server_Connection(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Http_Server(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Http_Server(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Async(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Async_TCP(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Sync_CancellationToken(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Sync_Semaphore(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Http_Server_Config(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Http_Server_Handler(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Http_Server_Connection(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Server(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Http_Server(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Http_Server(builtin);
}
