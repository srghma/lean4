// Lean compiler output
// Module: Std.Async.ContextAsync
// Imports: Std.Internal.UV Std.Async.Timer Std.Sync.CancellationContext
use crate::r#gen::Init::Control::Except::l_Except_map;
use crate::r#gen::Init::Data::Array::Basic::l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map;
use crate::r#gen::Init::Prelude::{
    l_Function_const___boxed, l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4, l_ReaderT_instMonad___redArg,
};
use crate::r#gen::Init::System::IO::l_BaseIO_chainTask___redArg;
use crate::r#gen::Init::System::Promise::l_IO_Promise_result_x21___redArg;
use crate::r#gen::Std::Async::Basic::{
    l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask,
    l_Std_Async_BaseAsync_toRawBaseIO___boxed, l_Std_Async_EAsync_instMonad,
    l_Std_Async_EAsync_tryFinally_x27___redArg,
};
use crate::r#gen::Std::Async::Timer::{
    initialize_Std_Async_Timer, runtime_initialize_Std_Async_Timer,
};
use crate::r#gen::Std::Internal::UV::{
    initialize_Std_Internal_UV, runtime_initialize_Std_Internal_UV,
};
use crate::r#gen::Std::Sync::CancellationContext::{
    initialize_Std_Sync_CancellationContext, l_Std_CancellationContext_cancel,
    l_Std_CancellationContext_fork, l_Std_CancellationContext_new,
    runtime_initialize_Std_Sync_CancellationContext,
};
use crate::r#gen::Std::Sync::CancellationToken::{
    l_Std_CancellationToken_getCancellationReason, l_Std_CancellationToken_isCancelled,
    l_Std_CancellationToken_selector, l_Std_CancellationToken_wait,
};
use crate::ffi::{lean_task_bind, lean_task_map, lean_task_pure};
use crate::ffi::lean_array_size;
use crate::ffi::lean_io_as_task;
use crate::ffi::{lean_io_promise_new, lean_io_promise_resolve};
pub static l_Std_Async_ContextAsync_isCancelled___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Std_Async_ContextAsync_isCancelled___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Async_ContextAsync_isCancelled___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_ContextAsync_isCancelled___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_ContextAsync_getCancellationReason___closed__0_value:
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
    m_fun: l_Std_Async_ContextAsync_getCancellationReason___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Async_ContextAsync_getCancellationReason___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_ContextAsync_getCancellationReason___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_ContextAsync_doneSelector___closed__0_value:
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
    m_fun: l_Std_Async_ContextAsync_doneSelector___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Async_ContextAsync_doneSelector___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_ContextAsync_doneSelector___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_ContextAsync_awaitCancellation___closed__0_value:
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
    m_fun: l_Std_Async_ContextAsync_awaitCancellation___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Async_ContextAsync_awaitCancellation___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_ContextAsync_awaitCancellation___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_ContextAsync_awaitCancellation___closed__1_value:
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
    m_fun: l_Std_Async_ContextAsync_awaitCancellation___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Std_Async_ContextAsync_awaitCancellation___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Async_ContextAsync_awaitCancellation___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_ContextAsync_awaitCancellation___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_ContextAsync_concurrently___redArg___closed__0_value:
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
    m_fun: l_Std_Async_ContextAsync_concurrently___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Async_ContextAsync_concurrently___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_ContextAsync_concurrently___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_ContextAsync_concurrently___redArg___closed__1_value:
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
    m_fun: l_Std_Async_ContextAsync_concurrently___redArg___lam__2___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Async_ContextAsync_concurrently___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_ContextAsync_concurrently___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__0_value:
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
    m_fun: l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Async_ContextAsync_background___redArg___lam__2___closed__0_value:
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
static mut l_Std_Async_ContextAsync_background___redArg___lam__2___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_ContextAsync_background___redArg___lam__2___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_ContextAsync_background___redArg___lam__2___closed__1_value:
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
        l_Std_Async_ContextAsync_background___redArg___lam__2___closed__0_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Async_ContextAsync_background___redArg___lam__2___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_ContextAsync_background___redArg___lam__2___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_ContextAsync_raceAll___redArg___closed__0_value:
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
    m_fun: l_Std_Async_ContextAsync_raceAll___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Async_ContextAsync_raceAll___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_ContextAsync_raceAll___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_ContextAsync_instMonadAsyncAsyncTask___closed__0_value:
    crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Async_ContextAsync_instMonadAsyncAsyncTask___lam__5___boxed
        as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Std_Async_ContextAsync_concurrently___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Async_ContextAsync_concurrently___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Async_ContextAsync_instMonadAsyncAsyncTask___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_ContextAsync_instMonadAsyncAsyncTask___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Async_ContextAsync_instMonadAsyncAsyncTask: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_ContextAsync_instMonadAsyncAsyncTask___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_ContextAsync_instFunctor___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Std_Async_ContextAsync_instFunctor___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Async_ContextAsync_instFunctor___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_ContextAsync_instFunctor___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_ContextAsync_instFunctor___closed__1_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Std_Async_ContextAsync_instFunctor___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Std_Async_ContextAsync_instFunctor___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Async_ContextAsync_instFunctor___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_ContextAsync_instFunctor___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_ContextAsync_instFunctor___closed__2_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_ContextAsync_instFunctor___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Async_ContextAsync_instFunctor___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Async_ContextAsync_instFunctor___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_ContextAsync_instFunctor___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Async_ContextAsync_instFunctor: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_ContextAsync_instFunctor___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_ContextAsync_instMonad___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Std_Async_ContextAsync_instMonad___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Async_ContextAsync_instMonad___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_ContextAsync_instMonad___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_ContextAsync_instMonad___closed__1_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Std_Async_ContextAsync_instMonad___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Async_ContextAsync_instMonad___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_ContextAsync_instMonad___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Async_ContextAsync_instMonad: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Async_ContextAsync_instMonadLiftIO___closed__0_value:
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
    m_fun: l_Std_Async_ContextAsync_instMonadLiftIO___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Async_ContextAsync_instMonadLiftIO___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_ContextAsync_instMonadLiftIO___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_ContextAsync_instMonadLiftIO___closed__1_value:
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
    m_fun: l_Std_Async_ContextAsync_instMonadLiftIO___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Std_Async_ContextAsync_instMonadLiftIO___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Async_ContextAsync_instMonadLiftIO___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_ContextAsync_instMonadLiftIO___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_ContextAsync_instMonadLiftIO___closed__2_value:
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
    m_fun: l_Std_Async_ContextAsync_instMonadLiftIO___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Std_Async_ContextAsync_instMonadLiftIO___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Async_ContextAsync_instMonadLiftIO___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_ContextAsync_instMonadLiftIO___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Async_ContextAsync_instMonadLiftIO: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_ContextAsync_instMonadLiftIO___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_ContextAsync_instMonadLiftBaseIO___closed__0_value:
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
    m_fun: l_Std_Async_ContextAsync_instMonadLiftBaseIO___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Async_ContextAsync_instMonadLiftBaseIO___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_ContextAsync_instMonadLiftBaseIO___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Async_ContextAsync_instMonadLiftBaseIO: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_ContextAsync_instMonadLiftBaseIO___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_ContextAsync_instMonadExceptError___closed__0_value:
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
    m_fun: l_Std_Async_ContextAsync_instMonadExceptError___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Async_ContextAsync_instMonadExceptError___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_ContextAsync_instMonadExceptError___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_ContextAsync_instMonadExceptError___closed__1_value:
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
    m_fun: l_Std_Async_ContextAsync_instMonadExceptError___lam__2___boxed
        as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Async_ContextAsync_instMonadExceptError___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_ContextAsync_instMonadExceptError___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_ContextAsync_instMonadExceptError___closed__2_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Async_ContextAsync_instMonadExceptError___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Async_ContextAsync_instMonadExceptError___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Async_ContextAsync_instMonadExceptError___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_ContextAsync_instMonadExceptError___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Async_ContextAsync_instMonadExceptError: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_ContextAsync_instMonadExceptError___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_ContextAsync_instMonadFinally___closed__0_value:
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
    m_fun: l_Std_Async_ContextAsync_instMonadFinally___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Async_ContextAsync_instMonadFinally___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_ContextAsync_instMonadFinally___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Async_ContextAsync_instMonadFinally: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_ContextAsync_instMonadFinally___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_ContextAsync_instInhabited___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<37> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 37,
    m_capacity: 37,
    m_length: 36,
    m_data: [
        40, 96, 73, 110, 104, 97, 98, 105, 116, 101, 100, 46, 100, 101, 102, 97, 117, 108, 116, 96,
        32, 102, 111, 114, 32, 96, 73, 79, 46, 69, 114, 114, 111, 114, 96, 41, 0,
    ],
};
static mut l_Std_Async_ContextAsync_instInhabited___lam__0___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_ContextAsync_instInhabited___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_ContextAsync_instInhabited___lam__0___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 18,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Async_ContextAsync_instInhabited___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Async_ContextAsync_instInhabited___lam__0___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_ContextAsync_instInhabited___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_ContextAsync_instInhabited___lam__0___closed__2_value:
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
        core::ptr::addr_of!(l_Std_Async_ContextAsync_instInhabited___lam__0___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Async_ContextAsync_instInhabited___lam__0___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_ContextAsync_instInhabited___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_ContextAsync_instInhabited___lam__0___closed__3_value:
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
        core::ptr::addr_of!(l_Std_Async_ContextAsync_instInhabited___lam__0___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Async_ContextAsync_instInhabited___lam__0___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_ContextAsync_instInhabited___lam__0___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_ContextAsync_instInhabited___closed__0_value:
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
    m_fun: l_Std_Async_ContextAsync_instInhabited___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Async_ContextAsync_instInhabited___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_ContextAsync_instInhabited___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_ContextAsync_instMonadAwaitAsyncTask___closed__0_value:
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
    m_fun: l_Std_Async_ContextAsync_instMonadAwaitAsyncTask___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Async_ContextAsync_instMonadAwaitAsyncTask___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_ContextAsync_instMonadAwaitAsyncTask___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Async_ContextAsync_instMonadAwaitAsyncTask: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_ContextAsync_instMonadAwaitAsyncTask___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_ContextAsync_race___redArg___closed__0_value:
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
    m_fun: l_Std_Async_ContextAsync_race___redArg___lam__3___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Async_ContextAsync_race___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_ContextAsync_race___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Std_Async_ContextAsync_runIn___redArg(
    mut v_ctx_2593_: *mut crate::leanh::LeanObject,
    mut v_x_2594_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2596_ = crate::leanh::lean_apply_2(v_x_2594_, v_ctx_2593_, crate::leanh::lean_box(0));
    return v___x_2596_;
}
pub unsafe fn l_Std_Async_ContextAsync_runIn___redArg___boxed(
    mut v_ctx_2597_: *mut crate::leanh::LeanObject,
    mut v_x_2598_: *mut crate::leanh::LeanObject,
    mut v_a_2599_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2600_ = l_Std_Async_ContextAsync_runIn___redArg(v_ctx_2597_, v_x_2598_);
    return v_res_2600_;
}
pub unsafe fn l_Std_Async_ContextAsync_runIn(
    mut v_00_u03b1_2601_: *mut crate::leanh::LeanObject,
    mut v_ctx_2602_: *mut crate::leanh::LeanObject,
    mut v_x_2603_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2605_ = crate::leanh::lean_apply_2(v_x_2603_, v_ctx_2602_, crate::leanh::lean_box(0));
    return v___x_2605_;
}
pub unsafe fn l_Std_Async_ContextAsync_runIn___boxed(
    mut v_00_u03b1_2606_: *mut crate::leanh::LeanObject,
    mut v_ctx_2607_: *mut crate::leanh::LeanObject,
    mut v_x_2608_: *mut crate::leanh::LeanObject,
    mut v_a_2609_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2610_ = l_Std_Async_ContextAsync_runIn(v_00_u03b1_2606_, v_ctx_2607_, v_x_2608_);
    return v_res_2610_;
}
pub unsafe fn l_Std_Async_ContextAsync_run___redArg___lam__0(
    mut v_x_2611_: *mut crate::leanh::LeanObject,
    mut v_x_2612_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2617_: u8 = 0;
    let mut v___x_2619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2622_: u8 = 0;
    let mut v___x_2623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2612_) == 0 {
                    crate::leanh::lean_dec_ref(v_x_2611_);
                    v_a_2614_ = crate::leanh::lean_ctor_get(v_x_2612_, 0);
                    v_isSharedCheck_2622_ = (!crate::leanh::lean_is_exclusive(v_x_2612_)) as u8;
                    if v_isSharedCheck_2622_ == 0 {
                        v___x_2616_ = v_x_2612_;
                        v_isShared_2617_ = v_isSharedCheck_2622_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2614_);
                        crate::leanh::lean_dec(v_x_2612_);
                        v___x_2616_ = crate::leanh::lean_box(0);
                        v_isShared_2617_ = v_isSharedCheck_2622_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v_x_2612_, 1);
                    v___x_2623_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2623_, 0, v_x_2611_);
                    return v___x_2623_;
                }
            }
            1 => {
                if v_isShared_2617_ == 0 {
                    v___x_2619_ = v___x_2616_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2621_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2621_, 0, v_a_2614_);
                    v___x_2619_ = v_reuseFailAlloc_2621_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2620_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2620_, 0, v___x_2619_);
                return v___x_2620_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_run___redArg___lam__0___boxed(
    mut v_x_2624_: *mut crate::leanh::LeanObject,
    mut v_x_2625_: *mut crate::leanh::LeanObject,
    mut v___y_2626_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2627_ = l_Std_Async_ContextAsync_run___redArg___lam__0(v_x_2624_, v_x_2625_);
    return v_res_2627_;
}
pub unsafe fn l_Std_Async_ContextAsync_run___redArg___lam__1(
    mut v_a_2628_: *mut crate::leanh::LeanObject,
    mut v_x_2629_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2629_) == 0 {
        let mut v___x_2631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_a_2628_);
        v___x_2631_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2631_, 0, v_x_2629_);
        return v___x_2631_;
    } else {
        let mut v___x_2632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2638_: u8 = 0;
        let mut v___x_2639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2632_ = crate::leanh::lean_box(2);
        v___x_2633_ = l_Std_CancellationContext_cancel(v_a_2628_, v___x_2632_);
        v___f_2634_ = crate::leanh::lean_alloc_closure(
            l_Std_Async_ContextAsync_run___redArg___lam__0___boxed as *mut core::ffi::c_void,
            3,
            1,
        );
        crate::leanh::lean_closure_set(v___f_2634_, 0, v_x_2629_);
        v___x_2635_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2635_, 0, v___x_2633_);
        v___x_2636_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2636_, 0, v___x_2635_);
        v___x_2637_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_2638_ = 0;
        v___x_2639_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_2637_,
            v___x_2638_,
            v___x_2636_,
            v___f_2634_,
        );
        return v___x_2639_;
    }
}
pub unsafe fn l_Std_Async_ContextAsync_run___redArg___lam__1___boxed(
    mut v_a_2640_: *mut crate::leanh::LeanObject,
    mut v_x_2641_: *mut crate::leanh::LeanObject,
    mut v___y_2642_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2643_ = l_Std_Async_ContextAsync_run___redArg___lam__1(v_a_2640_, v_x_2641_);
    return v_res_2643_;
}
pub unsafe fn l_Std_Async_ContextAsync_run___redArg___lam__2(
    mut v_x_2644_: *mut crate::leanh::LeanObject,
    mut v_x_2645_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2650_: u8 = 0;
    let mut v___x_2652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2655_: u8 = 0;
    let mut v_a_2656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2660_: u8 = 0;
    let mut v___x_2661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2645_) == 0 {
                    crate::leanh::lean_dec_ref(v_x_2644_);
                    v_a_2647_ = crate::leanh::lean_ctor_get(v_x_2645_, 0);
                    v_isSharedCheck_2655_ = (!crate::leanh::lean_is_exclusive(v_x_2645_)) as u8;
                    if v_isSharedCheck_2655_ == 0 {
                        v___x_2649_ = v_x_2645_;
                        v_isShared_2650_ = v_isSharedCheck_2655_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2647_);
                        crate::leanh::lean_dec(v_x_2645_);
                        v___x_2649_ = crate::leanh::lean_box(0);
                        v_isShared_2650_ = v_isSharedCheck_2655_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2656_ = crate::leanh::lean_ctor_get(v_x_2645_, 0);
                    crate::leanh::lean_inc_n(v_a_2656_, 2);
                    crate::leanh::lean_dec_ref_known(v_x_2645_, 1);
                    v___x_2657_ =
                        crate::leanh::lean_apply_2(v_x_2644_, v_a_2656_, crate::leanh::lean_box(0));
                    v___f_2658_ = crate::leanh::lean_alloc_closure(
                        l_Std_Async_ContextAsync_run___redArg___lam__1___boxed
                            as *mut core::ffi::c_void,
                        3,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_2658_, 0, v_a_2656_);
                    v___x_2659_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2660_ = 0;
                    v___x_2661_ =
                        l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v___x_2659_,
                            v___x_2660_,
                            v___x_2657_,
                            v___f_2658_,
                        );
                    return v___x_2661_;
                }
            }
            1 => {
                if v_isShared_2650_ == 0 {
                    v___x_2652_ = v___x_2649_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2654_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2654_, 0, v_a_2647_);
                    v___x_2652_ = v_reuseFailAlloc_2654_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2653_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2653_, 0, v___x_2652_);
                return v___x_2653_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_run___redArg___lam__2___boxed(
    mut v_x_2662_: *mut crate::leanh::LeanObject,
    mut v_x_2663_: *mut crate::leanh::LeanObject,
    mut v___y_2664_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2665_ = l_Std_Async_ContextAsync_run___redArg___lam__2(v_x_2662_, v_x_2663_);
    return v_res_2665_;
}
pub unsafe fn l_Std_Async_ContextAsync_run___redArg(
    mut v_x_2666_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2673_: u8 = 0;
    let mut v___x_2674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2668_ = l_Std_CancellationContext_new();
    v___f_2669_ = crate::leanh::lean_alloc_closure(
        l_Std_Async_ContextAsync_run___redArg___lam__2___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2669_, 0, v_x_2666_);
    v___x_2670_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2670_, 0, v___x_2668_);
    v___x_2671_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2671_, 0, v___x_2670_);
    v___x_2672_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2673_ = 0;
    v___x_2674_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2672_,
        v___x_2673_,
        v___x_2671_,
        v___f_2669_,
    );
    return v___x_2674_;
}
pub unsafe fn l_Std_Async_ContextAsync_run___redArg___boxed(
    mut v_x_2675_: *mut crate::leanh::LeanObject,
    mut v_a_2676_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2677_ = l_Std_Async_ContextAsync_run___redArg(v_x_2675_);
    return v_res_2677_;
}
pub unsafe fn l_Std_Async_ContextAsync_run(
    mut v_00_u03b1_2678_: *mut crate::leanh::LeanObject,
    mut v_x_2679_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2686_: u8 = 0;
    let mut v___x_2687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2681_ = l_Std_CancellationContext_new();
    v___f_2682_ = crate::leanh::lean_alloc_closure(
        l_Std_Async_ContextAsync_run___redArg___lam__2___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2682_, 0, v_x_2679_);
    v___x_2683_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2683_, 0, v___x_2681_);
    v___x_2684_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2684_, 0, v___x_2683_);
    v___x_2685_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2686_ = 0;
    v___x_2687_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2685_,
        v___x_2686_,
        v___x_2684_,
        v___f_2682_,
    );
    return v___x_2687_;
}
pub unsafe fn l_Std_Async_ContextAsync_run___boxed(
    mut v_00_u03b1_2688_: *mut crate::leanh::LeanObject,
    mut v_x_2689_: *mut crate::leanh::LeanObject,
    mut v_a_2690_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2691_ = l_Std_Async_ContextAsync_run(v_00_u03b1_2688_, v_x_2689_);
    return v_res_2691_;
}
pub unsafe fn l_Std_Async_ContextAsync_getContext(
    mut v_ctx_2692_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_ctx_2692_);
    v___x_2694_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2694_, 0, v_ctx_2692_);
    v___x_2695_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2695_, 0, v___x_2694_);
    return v___x_2695_;
}
pub unsafe fn l_Std_Async_ContextAsync_getContext___boxed(
    mut v_ctx_2696_: *mut crate::leanh::LeanObject,
    mut v_a_2697_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2698_ = l_Std_Async_ContextAsync_getContext(v_ctx_2696_);
    crate::leanh::lean_dec_ref(v_ctx_2696_);
    return v_res_2698_;
}
pub unsafe fn l_Std_Async_ContextAsync_isCancelled___lam__0(
    mut v_x_2699_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2704_: u8 = 0;
    let mut v___x_2706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2709_: u8 = 0;
    let mut v_a_2710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2713_: u8 = 0;
    let mut v_token_2714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2715_: u8 = 0;
    let mut v___x_2716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2721_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2699_) == 0 {
                    v_a_2701_ = crate::leanh::lean_ctor_get(v_x_2699_, 0);
                    v_isSharedCheck_2709_ = (!crate::leanh::lean_is_exclusive(v_x_2699_)) as u8;
                    if v_isSharedCheck_2709_ == 0 {
                        v___x_2703_ = v_x_2699_;
                        v_isShared_2704_ = v_isSharedCheck_2709_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2701_);
                        crate::leanh::lean_dec(v_x_2699_);
                        v___x_2703_ = crate::leanh::lean_box(0);
                        v_isShared_2704_ = v_isSharedCheck_2709_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2710_ = crate::leanh::lean_ctor_get(v_x_2699_, 0);
                    v_isSharedCheck_2721_ = (!crate::leanh::lean_is_exclusive(v_x_2699_)) as u8;
                    if v_isSharedCheck_2721_ == 0 {
                        v___x_2712_ = v_x_2699_;
                        v_isShared_2713_ = v_isSharedCheck_2721_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2710_);
                        crate::leanh::lean_dec(v_x_2699_);
                        v___x_2712_ = crate::leanh::lean_box(0);
                        v_isShared_2713_ = v_isSharedCheck_2721_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2704_ == 0 {
                    v___x_2706_ = v___x_2703_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2708_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2708_, 0, v_a_2701_);
                    v___x_2706_ = v_reuseFailAlloc_2708_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2707_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2707_, 0, v___x_2706_);
                return v___x_2707_;
            }
            3 => {
                v_token_2714_ = crate::leanh::lean_ctor_get(v_a_2710_, 1);
                crate::leanh::lean_inc_ref(v_token_2714_);
                crate::leanh::lean_dec(v_a_2710_);
                v___x_2715_ = l_Std_CancellationToken_isCancelled(v_token_2714_);
                v___x_2716_ = crate::leanh::lean_box((v___x_2715_) as usize);
                if v_isShared_2713_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2712_, 0, v___x_2716_);
                    v___x_2718_ = v___x_2712_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2720_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2720_, 0, v___x_2716_);
                    v___x_2718_ = v_reuseFailAlloc_2720_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2719_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2719_, 0, v___x_2718_);
                return v___x_2719_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_isCancelled___lam__0___boxed(
    mut v_x_2722_: *mut crate::leanh::LeanObject,
    mut v___y_2723_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2724_ = l_Std_Async_ContextAsync_isCancelled___lam__0(v_x_2722_);
    return v_res_2724_;
}
pub unsafe fn l_Std_Async_ContextAsync_isCancelled(
    mut v_a_2726_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: u8 = 0;
    let mut v___x_2733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2728_ = l_Std_Async_ContextAsync_isCancelled___closed__0;
    crate::leanh::lean_inc_ref(v_a_2726_);
    v___x_2729_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2729_, 0, v_a_2726_);
    v___x_2730_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2730_, 0, v___x_2729_);
    v___x_2731_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2732_ = 0;
    v___x_2733_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2731_,
        v___x_2732_,
        v___x_2730_,
        v___f_2728_,
    );
    return v___x_2733_;
}
pub unsafe fn l_Std_Async_ContextAsync_isCancelled___boxed(
    mut v_a_2734_: *mut crate::leanh::LeanObject,
    mut v_a_2735_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2736_ = l_Std_Async_ContextAsync_isCancelled(v_a_2734_);
    crate::leanh::lean_dec_ref(v_a_2734_);
    return v_res_2736_;
}
pub unsafe fn l_Std_Async_ContextAsync_getCancellationReason___lam__0(
    mut v_x_2737_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2742_: u8 = 0;
    let mut v___x_2744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2747_: u8 = 0;
    let mut v_a_2748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2751_: u8 = 0;
    let mut v_token_2752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2758_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2737_) == 0 {
                    v_a_2739_ = crate::leanh::lean_ctor_get(v_x_2737_, 0);
                    v_isSharedCheck_2747_ = (!crate::leanh::lean_is_exclusive(v_x_2737_)) as u8;
                    if v_isSharedCheck_2747_ == 0 {
                        v___x_2741_ = v_x_2737_;
                        v_isShared_2742_ = v_isSharedCheck_2747_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2739_);
                        crate::leanh::lean_dec(v_x_2737_);
                        v___x_2741_ = crate::leanh::lean_box(0);
                        v_isShared_2742_ = v_isSharedCheck_2747_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2748_ = crate::leanh::lean_ctor_get(v_x_2737_, 0);
                    v_isSharedCheck_2758_ = (!crate::leanh::lean_is_exclusive(v_x_2737_)) as u8;
                    if v_isSharedCheck_2758_ == 0 {
                        v___x_2750_ = v_x_2737_;
                        v_isShared_2751_ = v_isSharedCheck_2758_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2748_);
                        crate::leanh::lean_dec(v_x_2737_);
                        v___x_2750_ = crate::leanh::lean_box(0);
                        v_isShared_2751_ = v_isSharedCheck_2758_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2742_ == 0 {
                    v___x_2744_ = v___x_2741_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2746_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2746_, 0, v_a_2739_);
                    v___x_2744_ = v_reuseFailAlloc_2746_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2745_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2745_, 0, v___x_2744_);
                return v___x_2745_;
            }
            3 => {
                v_token_2752_ = crate::leanh::lean_ctor_get(v_a_2748_, 1);
                crate::leanh::lean_inc_ref(v_token_2752_);
                crate::leanh::lean_dec(v_a_2748_);
                v___x_2753_ = l_Std_CancellationToken_getCancellationReason(v_token_2752_);
                if v_isShared_2751_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2750_, 0, v___x_2753_);
                    v___x_2755_ = v___x_2750_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2757_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2757_, 0, v___x_2753_);
                    v___x_2755_ = v_reuseFailAlloc_2757_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2756_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2756_, 0, v___x_2755_);
                return v___x_2756_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_getCancellationReason___lam__0___boxed(
    mut v_x_2759_: *mut crate::leanh::LeanObject,
    mut v___y_2760_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2761_ = l_Std_Async_ContextAsync_getCancellationReason___lam__0(v_x_2759_);
    return v_res_2761_;
}
pub unsafe fn l_Std_Async_ContextAsync_getCancellationReason(
    mut v_a_2763_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2769_: u8 = 0;
    let mut v___x_2770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2765_ = l_Std_Async_ContextAsync_getCancellationReason___closed__0;
    crate::leanh::lean_inc_ref(v_a_2763_);
    v___x_2766_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2766_, 0, v_a_2763_);
    v___x_2767_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2767_, 0, v___x_2766_);
    v___x_2768_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2769_ = 0;
    v___x_2770_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2768_,
        v___x_2769_,
        v___x_2767_,
        v___f_2765_,
    );
    return v___x_2770_;
}
pub unsafe fn l_Std_Async_ContextAsync_getCancellationReason___boxed(
    mut v_a_2771_: *mut crate::leanh::LeanObject,
    mut v_a_2772_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2773_ = l_Std_Async_ContextAsync_getCancellationReason(v_a_2771_);
    crate::leanh::lean_dec_ref(v_a_2771_);
    return v_res_2773_;
}
pub unsafe fn l_Std_Async_ContextAsync_cancel___lam__0(
    mut v_reason_2774_: *mut crate::leanh::LeanObject,
    mut v_x_2775_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2780_: u8 = 0;
    let mut v___x_2782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2785_: u8 = 0;
    let mut v_a_2786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2789_: u8 = 0;
    let mut v___x_2790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2795_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2775_) == 0 {
                    crate::leanh::lean_dec(v_reason_2774_);
                    v_a_2777_ = crate::leanh::lean_ctor_get(v_x_2775_, 0);
                    v_isSharedCheck_2785_ = (!crate::leanh::lean_is_exclusive(v_x_2775_)) as u8;
                    if v_isSharedCheck_2785_ == 0 {
                        v___x_2779_ = v_x_2775_;
                        v_isShared_2780_ = v_isSharedCheck_2785_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2777_);
                        crate::leanh::lean_dec(v_x_2775_);
                        v___x_2779_ = crate::leanh::lean_box(0);
                        v_isShared_2780_ = v_isSharedCheck_2785_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2786_ = crate::leanh::lean_ctor_get(v_x_2775_, 0);
                    v_isSharedCheck_2795_ = (!crate::leanh::lean_is_exclusive(v_x_2775_)) as u8;
                    if v_isSharedCheck_2795_ == 0 {
                        v___x_2788_ = v_x_2775_;
                        v_isShared_2789_ = v_isSharedCheck_2795_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2786_);
                        crate::leanh::lean_dec(v_x_2775_);
                        v___x_2788_ = crate::leanh::lean_box(0);
                        v_isShared_2789_ = v_isSharedCheck_2795_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2780_ == 0 {
                    v___x_2782_ = v___x_2779_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2784_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2784_, 0, v_a_2777_);
                    v___x_2782_ = v_reuseFailAlloc_2784_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2783_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2783_, 0, v___x_2782_);
                return v___x_2783_;
            }
            3 => {
                v___x_2790_ = l_Std_CancellationContext_cancel(v_a_2786_, v_reason_2774_);
                if v_isShared_2789_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2788_, 0, v___x_2790_);
                    v___x_2792_ = v___x_2788_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2794_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2794_, 0, v___x_2790_);
                    v___x_2792_ = v_reuseFailAlloc_2794_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2793_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2793_, 0, v___x_2792_);
                return v___x_2793_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_cancel___lam__0___boxed(
    mut v_reason_2796_: *mut crate::leanh::LeanObject,
    mut v_x_2797_: *mut crate::leanh::LeanObject,
    mut v___y_2798_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2799_ = l_Std_Async_ContextAsync_cancel___lam__0(v_reason_2796_, v_x_2797_);
    return v_res_2799_;
}
pub unsafe fn l_Std_Async_ContextAsync_cancel(
    mut v_reason_2800_: *mut crate::leanh::LeanObject,
    mut v_a_2801_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2807_: u8 = 0;
    let mut v___x_2808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2803_ = crate::leanh::lean_alloc_closure(
        l_Std_Async_ContextAsync_cancel___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2803_, 0, v_reason_2800_);
    crate::leanh::lean_inc_ref(v_a_2801_);
    v___x_2804_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2804_, 0, v_a_2801_);
    v___x_2805_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2805_, 0, v___x_2804_);
    v___x_2806_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2807_ = 0;
    v___x_2808_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2806_,
        v___x_2807_,
        v___x_2805_,
        v___f_2803_,
    );
    return v___x_2808_;
}
pub unsafe fn l_Std_Async_ContextAsync_cancel___boxed(
    mut v_reason_2809_: *mut crate::leanh::LeanObject,
    mut v_a_2810_: *mut crate::leanh::LeanObject,
    mut v_a_2811_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2812_ = l_Std_Async_ContextAsync_cancel(v_reason_2809_, v_a_2810_);
    crate::leanh::lean_dec_ref(v_a_2810_);
    return v_res_2812_;
}
pub unsafe fn l_Std_Async_ContextAsync_doneSelector___lam__0(
    mut v_x_2813_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2818_: u8 = 0;
    let mut v___x_2820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2823_: u8 = 0;
    let mut v_a_2824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2827_: u8 = 0;
    let mut v_token_2828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2834_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2813_) == 0 {
                    v_a_2815_ = crate::leanh::lean_ctor_get(v_x_2813_, 0);
                    v_isSharedCheck_2823_ = (!crate::leanh::lean_is_exclusive(v_x_2813_)) as u8;
                    if v_isSharedCheck_2823_ == 0 {
                        v___x_2817_ = v_x_2813_;
                        v_isShared_2818_ = v_isSharedCheck_2823_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2815_);
                        crate::leanh::lean_dec(v_x_2813_);
                        v___x_2817_ = crate::leanh::lean_box(0);
                        v_isShared_2818_ = v_isSharedCheck_2823_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2824_ = crate::leanh::lean_ctor_get(v_x_2813_, 0);
                    v_isSharedCheck_2834_ = (!crate::leanh::lean_is_exclusive(v_x_2813_)) as u8;
                    if v_isSharedCheck_2834_ == 0 {
                        v___x_2826_ = v_x_2813_;
                        v_isShared_2827_ = v_isSharedCheck_2834_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2824_);
                        crate::leanh::lean_dec(v_x_2813_);
                        v___x_2826_ = crate::leanh::lean_box(0);
                        v_isShared_2827_ = v_isSharedCheck_2834_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2818_ == 0 {
                    v___x_2820_ = v___x_2817_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2822_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2822_, 0, v_a_2815_);
                    v___x_2820_ = v_reuseFailAlloc_2822_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2821_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2821_, 0, v___x_2820_);
                return v___x_2821_;
            }
            3 => {
                v_token_2828_ = crate::leanh::lean_ctor_get(v_a_2824_, 1);
                crate::leanh::lean_inc_ref(v_token_2828_);
                crate::leanh::lean_dec(v_a_2824_);
                v___x_2829_ = l_Std_CancellationToken_selector(v_token_2828_);
                if v_isShared_2827_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2826_, 0, v___x_2829_);
                    v___x_2831_ = v___x_2826_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2833_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2833_, 0, v___x_2829_);
                    v___x_2831_ = v_reuseFailAlloc_2833_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2832_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2832_, 0, v___x_2831_);
                return v___x_2832_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_doneSelector___lam__0___boxed(
    mut v_x_2835_: *mut crate::leanh::LeanObject,
    mut v___y_2836_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2837_ = l_Std_Async_ContextAsync_doneSelector___lam__0(v_x_2835_);
    return v_res_2837_;
}
pub unsafe fn l_Std_Async_ContextAsync_doneSelector(
    mut v_a_2839_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: u8 = 0;
    let mut v___x_2846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2841_ = l_Std_Async_ContextAsync_doneSelector___closed__0;
    crate::leanh::lean_inc_ref(v_a_2839_);
    v___x_2842_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2842_, 0, v_a_2839_);
    v___x_2843_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2843_, 0, v___x_2842_);
    v___x_2844_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2845_ = 0;
    v___x_2846_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2844_,
        v___x_2845_,
        v___x_2843_,
        v___f_2841_,
    );
    return v___x_2846_;
}
pub unsafe fn l_Std_Async_ContextAsync_doneSelector___boxed(
    mut v_a_2847_: *mut crate::leanh::LeanObject,
    mut v_a_2848_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2849_ = l_Std_Async_ContextAsync_doneSelector(v_a_2847_);
    crate::leanh::lean_dec_ref(v_a_2847_);
    return v_res_2849_;
}
pub unsafe fn l_Std_Async_ContextAsync_awaitCancellation___lam__0(
    mut v_x_2850_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2855_: u8 = 0;
    let mut v___x_2857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2860_: u8 = 0;
    let mut v_a_2861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2850_) == 0 {
                    v_a_2852_ = crate::leanh::lean_ctor_get(v_x_2850_, 0);
                    v_isSharedCheck_2860_ = (!crate::leanh::lean_is_exclusive(v_x_2850_)) as u8;
                    if v_isSharedCheck_2860_ == 0 {
                        v___x_2854_ = v_x_2850_;
                        v_isShared_2855_ = v_isSharedCheck_2860_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2852_);
                        crate::leanh::lean_dec(v_x_2850_);
                        v___x_2854_ = crate::leanh::lean_box(0);
                        v_isShared_2855_ = v_isSharedCheck_2860_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2861_ = crate::leanh::lean_ctor_get(v_x_2850_, 0);
                    crate::leanh::lean_inc(v_a_2861_);
                    crate::leanh::lean_dec_ref_known(v_x_2850_, 1);
                    v___x_2862_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2862_, 0, v_a_2861_);
                    return v___x_2862_;
                }
            }
            1 => {
                if v_isShared_2855_ == 0 {
                    v___x_2857_ = v___x_2854_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2859_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2859_, 0, v_a_2852_);
                    v___x_2857_ = v_reuseFailAlloc_2859_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2858_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2858_, 0, v___x_2857_);
                return v___x_2858_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_awaitCancellation___lam__0___boxed(
    mut v_x_2863_: *mut crate::leanh::LeanObject,
    mut v___y_2864_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2865_ = l_Std_Async_ContextAsync_awaitCancellation___lam__0(v_x_2863_);
    return v_res_2865_;
}
pub unsafe fn l_Std_Async_ContextAsync_awaitCancellation___lam__1(
    mut v___f_2866_: *mut crate::leanh::LeanObject,
    mut v_x_2867_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_2870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: u8 = 0;
    let mut v___x_2874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2878_: u8 = 0;
    let mut v___x_2880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2883_: u8 = 0;
    let mut v_a_2884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2887_: u8 = 0;
    let mut v_token_2888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2898_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2867_) == 0 {
                    crate::leanh::lean_dec_ref(v___f_2866_);
                    v_a_2875_ = crate::leanh::lean_ctor_get(v_x_2867_, 0);
                    v_isSharedCheck_2883_ = (!crate::leanh::lean_is_exclusive(v_x_2867_)) as u8;
                    if v_isSharedCheck_2883_ == 0 {
                        v___x_2877_ = v_x_2867_;
                        v_isShared_2878_ = v_isSharedCheck_2883_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2875_);
                        crate::leanh::lean_dec(v_x_2867_);
                        v___x_2877_ = crate::leanh::lean_box(0);
                        v_isShared_2878_ = v_isSharedCheck_2883_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_2884_ = crate::leanh::lean_ctor_get(v_x_2867_, 0);
                    v_isSharedCheck_2898_ = (!crate::leanh::lean_is_exclusive(v_x_2867_)) as u8;
                    if v_isSharedCheck_2898_ == 0 {
                        v___x_2886_ = v_x_2867_;
                        v_isShared_2887_ = v_isSharedCheck_2898_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2884_);
                        crate::leanh::lean_dec(v_x_2867_);
                        v___x_2886_ = crate::leanh::lean_box(0);
                        v_isShared_2887_ = v_isSharedCheck_2898_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2871_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2871_, 0, v_val_2870_);
                v___x_2872_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2873_ = 0;
                v___x_2874_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_2872_,
                    v___x_2873_,
                    v___x_2871_,
                    v___f_2866_,
                );
                return v___x_2874_;
            }
            2 => {
                if v_isShared_2878_ == 0 {
                    v___x_2880_ = v___x_2877_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2882_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2882_, 0, v_a_2875_);
                    v___x_2880_ = v_reuseFailAlloc_2882_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2881_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2881_, 0, v___x_2880_);
                return v___x_2881_;
            }
            4 => {
                v_token_2888_ = crate::leanh::lean_ctor_get(v_a_2884_, 1);
                crate::leanh::lean_inc_ref(v_token_2888_);
                crate::leanh::lean_dec(v_a_2884_);
                v___x_2889_ = l_Std_CancellationToken_wait(v_token_2888_);
                if crate::leanh::lean_obj_tag(v___x_2889_) == 0 {
                    v_a_2890_ = crate::leanh::lean_ctor_get(v___x_2889_, 0);
                    crate::leanh::lean_inc(v_a_2890_);
                    crate::leanh::lean_dec_ref_known(v___x_2889_, 1);
                    if v_isShared_2887_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2886_, 0, v_a_2890_);
                        v___x_2892_ = v___x_2886_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2893_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2893_, 0, v_a_2890_);
                        v___x_2892_ = v_reuseFailAlloc_2893_;
                        state = 5;
                        continue;
                    }
                } else {
                    v_a_2894_ = crate::leanh::lean_ctor_get(v___x_2889_, 0);
                    crate::leanh::lean_inc(v_a_2894_);
                    crate::leanh::lean_dec_ref_known(v___x_2889_, 1);
                    if v_isShared_2887_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_2886_, 0);
                        crate::leanh::lean_ctor_set(v___x_2886_, 0, v_a_2894_);
                        v___x_2896_ = v___x_2886_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2897_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2897_, 0, v_a_2894_);
                        v___x_2896_ = v_reuseFailAlloc_2897_;
                        state = 6;
                        continue;
                    }
                }
            }
            5 => {
                v_val_2870_ = v___x_2892_;
                state = 1;
                continue;
            }
            6 => {
                v_val_2870_ = v___x_2896_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_awaitCancellation___lam__1___boxed(
    mut v___f_2899_: *mut crate::leanh::LeanObject,
    mut v_x_2900_: *mut crate::leanh::LeanObject,
    mut v___y_2901_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2902_ = l_Std_Async_ContextAsync_awaitCancellation___lam__1(v___f_2899_, v_x_2900_);
    return v_res_2902_;
}
pub unsafe fn l_Std_Async_ContextAsync_awaitCancellation(
    mut v_a_2906_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2912_: u8 = 0;
    let mut v___x_2913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2908_ = l_Std_Async_ContextAsync_awaitCancellation___closed__1;
    crate::leanh::lean_inc_ref(v_a_2906_);
    v___x_2909_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2909_, 0, v_a_2906_);
    v___x_2910_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2910_, 0, v___x_2909_);
    v___x_2911_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2912_ = 0;
    v___x_2913_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2911_,
        v___x_2912_,
        v___x_2910_,
        v___f_2908_,
    );
    return v___x_2913_;
}
pub unsafe fn l_Std_Async_ContextAsync_awaitCancellation___boxed(
    mut v_a_2914_: *mut crate::leanh::LeanObject,
    mut v_a_2915_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2916_ = l_Std_Async_ContextAsync_awaitCancellation(v_a_2914_);
    crate::leanh::lean_dec_ref(v_a_2914_);
    return v_res_2916_;
}
pub unsafe fn l_Std_Async_ContextAsync_concurrently___redArg___lam__0(
    mut v_x_2917_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2917_) == 0 {
        let mut v_a_2918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_2918_ = crate::leanh::lean_ctor_get(v_x_2917_, 0);
        crate::leanh::lean_inc(v_a_2918_);
        crate::leanh::lean_dec_ref_known(v_x_2917_, 1);
        v___x_2919_ = lean_task_pure(v_a_2918_);
        return v___x_2919_;
    } else {
        let mut v_a_2920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_2920_ = crate::leanh::lean_ctor_get(v_x_2917_, 0);
        crate::leanh::lean_inc_ref(v_a_2920_);
        crate::leanh::lean_dec_ref_known(v_x_2917_, 1);
        return v_a_2920_;
    }
}
pub unsafe fn l_Std_Async_ContextAsync_concurrently___redArg___lam__2(
    mut v_x_2921_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_2922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_2922_ = crate::leanh::lean_ctor_get(v_x_2921_, 0);
    crate::leanh::lean_inc(v_fst_2922_);
    return v_fst_2922_;
}
pub unsafe fn l_Std_Async_ContextAsync_concurrently___redArg___lam__2___boxed(
    mut v_x_2923_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2924_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__2(v_x_2923_);
    crate::leanh::lean_dec_ref(v_x_2923_);
    return v_res_2924_;
}
pub unsafe fn l_Std_Async_ContextAsync_concurrently___redArg___lam__4(
    mut v_a_2925_: *mut crate::leanh::LeanObject,
    mut v_x_2926_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2926_) == 0 {
        let mut v___x_2928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2934_: u8 = 0;
        let mut v___x_2935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2928_ = crate::leanh::lean_box(2);
        v___x_2929_ = l_Std_CancellationContext_cancel(v_a_2925_, v___x_2928_);
        v___f_2930_ = crate::leanh::lean_alloc_closure(
            l_Std_Async_ContextAsync_run___redArg___lam__0___boxed as *mut core::ffi::c_void,
            3,
            1,
        );
        crate::leanh::lean_closure_set(v___f_2930_, 0, v_x_2926_);
        v___x_2931_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2931_, 0, v___x_2929_);
        v___x_2932_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2932_, 0, v___x_2931_);
        v___x_2933_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_2934_ = 0;
        v___x_2935_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_2933_,
            v___x_2934_,
            v___x_2932_,
            v___f_2930_,
        );
        return v___x_2935_;
    } else {
        let mut v___x_2936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_a_2925_);
        v___x_2936_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2936_, 0, v_x_2926_);
        return v___x_2936_;
    }
}
pub unsafe fn l_Std_Async_ContextAsync_concurrently___redArg___lam__4___boxed(
    mut v_a_2937_: *mut crate::leanh::LeanObject,
    mut v_x_2938_: *mut crate::leanh::LeanObject,
    mut v___y_2939_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2940_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__4(v_a_2937_, v_x_2938_);
    return v_res_2940_;
}
pub unsafe fn l_Std_Async_ContextAsync_concurrently___redArg___lam__1(
    mut v_x_2941_: *mut crate::leanh::LeanObject,
    mut v_a_2942_: *mut crate::leanh::LeanObject,
    mut v___f_2943_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2947_: u8 = 0;
    let mut v___x_2948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2945_ = crate::leanh::lean_apply_2(v_x_2941_, v_a_2942_, crate::leanh::lean_box(0));
    v___x_2946_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2947_ = 0;
    v___x_2948_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2946_,
        v___x_2947_,
        v___x_2945_,
        v___f_2943_,
    );
    return v___x_2948_;
}
pub unsafe fn l_Std_Async_ContextAsync_concurrently___redArg___lam__1___boxed(
    mut v_x_2949_: *mut crate::leanh::LeanObject,
    mut v_a_2950_: *mut crate::leanh::LeanObject,
    mut v___f_2951_: *mut crate::leanh::LeanObject,
    mut v___y_2952_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2953_ =
        l_Std_Async_ContextAsync_concurrently___redArg___lam__1(v_x_2949_, v_a_2950_, v___f_2951_);
    return v_res_2953_;
}
pub unsafe fn l_Std_Async_ContextAsync_concurrently___redArg___lam__3(
    mut v_a_2954_: *mut crate::leanh::LeanObject,
    mut v___x_2955_: *mut crate::leanh::LeanObject,
    mut v_x_2956_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2958_ = l_Std_CancellationContext_cancel(v_a_2954_, v___x_2955_);
    v___x_2959_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2959_, 0, v___x_2958_);
    v___x_2960_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2960_, 0, v___x_2959_);
    return v___x_2960_;
}
pub unsafe fn l_Std_Async_ContextAsync_concurrently___redArg___lam__3___boxed(
    mut v_a_2961_: *mut crate::leanh::LeanObject,
    mut v___x_2962_: *mut crate::leanh::LeanObject,
    mut v_x_2963_: *mut crate::leanh::LeanObject,
    mut v___y_2964_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2965_ =
        l_Std_Async_ContextAsync_concurrently___redArg___lam__3(v_a_2961_, v___x_2962_, v_x_2963_);
    crate::leanh::lean_dec(v_x_2963_);
    return v_res_2965_;
}
pub unsafe fn l_Std_Async_ContextAsync_concurrently___redArg___lam__5(
    mut v___f_2966_: *mut crate::leanh::LeanObject,
    mut v___f_2967_: *mut crate::leanh::LeanObject,
    mut v___f_2968_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2971_: u8 = 0;
    let mut v___x_2972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2980_: u8 = 0;
    let mut v___x_2982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2984_: u8 = 0;
    let mut v_a_2985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2988_: u8 = 0;
    let mut v_fst_2989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2993_: u8 = 0;
    let mut v_a_2994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2997_: u8 = 0;
    let mut v___x_2998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3003_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2970_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2971_ = 0;
                v___x_2972_ = l_Std_Async_EAsync_tryFinally_x27___redArg(
                    v___f_2966_,
                    v___f_2967_,
                    v___x_2970_,
                    v___x_2971_,
                );
                if crate::leanh::lean_obj_tag(v___x_2972_) == 0 {
                    crate::leanh::lean_dec(v___f_2968_);
                    v_a_2976_ = crate::leanh::lean_ctor_get(v___x_2972_, 0);
                    crate::leanh::lean_inc(v_a_2976_);
                    crate::leanh::lean_dec_ref_known(v___x_2972_, 1);
                    if crate::leanh::lean_obj_tag(v_a_2976_) == 0 {
                        v_a_2977_ = crate::leanh::lean_ctor_get(v_a_2976_, 0);
                        v_isSharedCheck_2984_ = (!crate::leanh::lean_is_exclusive(v_a_2976_)) as u8;
                        if v_isSharedCheck_2984_ == 0 {
                            v___x_2979_ = v_a_2976_;
                            v_isShared_2980_ = v_isSharedCheck_2984_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2977_);
                            crate::leanh::lean_dec(v_a_2976_);
                            v___x_2979_ = crate::leanh::lean_box(0);
                            v_isShared_2980_ = v_isSharedCheck_2984_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_a_2985_ = crate::leanh::lean_ctor_get(v_a_2976_, 0);
                        v_isSharedCheck_2993_ = (!crate::leanh::lean_is_exclusive(v_a_2976_)) as u8;
                        if v_isSharedCheck_2993_ == 0 {
                            v___x_2987_ = v_a_2976_;
                            v_isShared_2988_ = v_isSharedCheck_2993_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2985_);
                            crate::leanh::lean_dec(v_a_2976_);
                            v___x_2987_ = crate::leanh::lean_box(0);
                            v_isShared_2988_ = v_isSharedCheck_2993_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_a_2994_ = crate::leanh::lean_ctor_get(v___x_2972_, 0);
                    v_isSharedCheck_3003_ = (!crate::leanh::lean_is_exclusive(v___x_2972_)) as u8;
                    if v_isSharedCheck_3003_ == 0 {
                        v___x_2996_ = v___x_2972_;
                        v_isShared_2997_ = v_isSharedCheck_3003_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2994_);
                        crate::leanh::lean_dec(v___x_2972_);
                        v___x_2996_ = crate::leanh::lean_box(0);
                        v_isShared_2997_ = v_isSharedCheck_3003_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2975_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2975_, 0, v___y_2974_);
                return v___x_2975_;
            }
            2 => {
                if v_isShared_2980_ == 0 {
                    v___x_2982_ = v___x_2979_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2983_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2983_, 0, v_a_2977_);
                    v___x_2982_ = v_reuseFailAlloc_2983_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___y_2974_ = v___x_2982_;
                state = 1;
                continue;
            }
            4 => {
                v_fst_2989_ = crate::leanh::lean_ctor_get(v_a_2985_, 0);
                crate::leanh::lean_inc(v_fst_2989_);
                crate::leanh::lean_dec(v_a_2985_);
                if v_isShared_2988_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2987_, 0, v_fst_2989_);
                    v___x_2991_ = v___x_2987_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2992_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2992_, 0, v_fst_2989_);
                    v___x_2991_ = v_reuseFailAlloc_2992_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___y_2974_ = v___x_2991_;
                state = 1;
                continue;
            }
            6 => {
                v___x_2998_ =
                    crate::leanh::lean_alloc_closure(l_Except_map as *mut core::ffi::c_void, 5, 4);
                crate::leanh::lean_closure_set(v___x_2998_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_2998_, 1, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_2998_, 2, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_2998_, 3, v___f_2968_);
                v___x_2999_ = lean_task_map(v___x_2998_, v_a_2994_, v___x_2970_, v___x_2971_);
                if v_isShared_2997_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2996_, 0, v___x_2999_);
                    v___x_3001_ = v___x_2996_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3002_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3002_, 0, v___x_2999_);
                    v___x_3001_ = v_reuseFailAlloc_3002_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3001_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_concurrently___redArg___lam__5___boxed(
    mut v___f_3004_: *mut crate::leanh::LeanObject,
    mut v___f_3005_: *mut crate::leanh::LeanObject,
    mut v___f_3006_: *mut crate::leanh::LeanObject,
    mut v___y_3007_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3008_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__5(
        v___f_3004_,
        v___f_3005_,
        v___f_3006_,
    );
    return v_res_3008_;
}
pub unsafe fn l_Std_Async_ContextAsync_concurrently___redArg___lam__7(
    mut v_a_3009_: *mut crate::leanh::LeanObject,
    mut v___x_3010_: *mut crate::leanh::LeanObject,
    mut v_x_3011_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_3011_) == 0 {
        let mut v___x_3013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3018_: u8 = 0;
        let mut v___x_3019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3013_ = l_Std_CancellationContext_cancel(v_a_3009_, v___x_3010_);
        v___f_3014_ = crate::leanh::lean_alloc_closure(
            l_Std_Async_ContextAsync_run___redArg___lam__0___boxed as *mut core::ffi::c_void,
            3,
            1,
        );
        crate::leanh::lean_closure_set(v___f_3014_, 0, v_x_3011_);
        v___x_3015_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3015_, 0, v___x_3013_);
        v___x_3016_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3016_, 0, v___x_3015_);
        v___x_3017_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_3018_ = 0;
        v___x_3019_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_3017_,
            v___x_3018_,
            v___x_3016_,
            v___f_3014_,
        );
        return v___x_3019_;
    } else {
        let mut v___x_3020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___x_3010_);
        crate::leanh::lean_dec_ref(v_a_3009_);
        v___x_3020_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3020_, 0, v_x_3011_);
        return v___x_3020_;
    }
}
pub unsafe fn l_Std_Async_ContextAsync_concurrently___redArg___lam__7___boxed(
    mut v_a_3021_: *mut crate::leanh::LeanObject,
    mut v___x_3022_: *mut crate::leanh::LeanObject,
    mut v_x_3023_: *mut crate::leanh::LeanObject,
    mut v___y_3024_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3025_ =
        l_Std_Async_ContextAsync_concurrently___redArg___lam__7(v_a_3021_, v___x_3022_, v_x_3023_);
    return v_res_3025_;
}
pub unsafe fn l_Std_Async_ContextAsync_concurrently___redArg___lam__6(
    mut v_y_3026_: *mut crate::leanh::LeanObject,
    mut v_a_3027_: *mut crate::leanh::LeanObject,
    mut v___f_3028_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: u8 = 0;
    let mut v___x_3033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3030_ = crate::leanh::lean_apply_2(v_y_3026_, v_a_3027_, crate::leanh::lean_box(0));
    v___x_3031_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3032_ = 0;
    v___x_3033_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3031_,
        v___x_3032_,
        v___x_3030_,
        v___f_3028_,
    );
    return v___x_3033_;
}
pub unsafe fn l_Std_Async_ContextAsync_concurrently___redArg___lam__6___boxed(
    mut v_y_3034_: *mut crate::leanh::LeanObject,
    mut v_a_3035_: *mut crate::leanh::LeanObject,
    mut v___f_3036_: *mut crate::leanh::LeanObject,
    mut v___y_3037_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3038_ =
        l_Std_Async_ContextAsync_concurrently___redArg___lam__6(v_y_3034_, v_a_3035_, v___f_3036_);
    return v_res_3038_;
}
pub unsafe fn l_Std_Async_ContextAsync_concurrently___redArg___lam__10(
    mut v_a_3039_: *mut crate::leanh::LeanObject,
    mut v_x_3040_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3045_: u8 = 0;
    let mut v___x_3047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3050_: u8 = 0;
    let mut v_a_3051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3054_: u8 = 0;
    let mut v___x_3055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3060_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3040_) == 0 {
                    crate::leanh::lean_dec(v_a_3039_);
                    v_a_3042_ = crate::leanh::lean_ctor_get(v_x_3040_, 0);
                    v_isSharedCheck_3050_ = (!crate::leanh::lean_is_exclusive(v_x_3040_)) as u8;
                    if v_isSharedCheck_3050_ == 0 {
                        v___x_3044_ = v_x_3040_;
                        v_isShared_3045_ = v_isSharedCheck_3050_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3042_);
                        crate::leanh::lean_dec(v_x_3040_);
                        v___x_3044_ = crate::leanh::lean_box(0);
                        v_isShared_3045_ = v_isSharedCheck_3050_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3051_ = crate::leanh::lean_ctor_get(v_x_3040_, 0);
                    v_isSharedCheck_3060_ = (!crate::leanh::lean_is_exclusive(v_x_3040_)) as u8;
                    if v_isSharedCheck_3060_ == 0 {
                        v___x_3053_ = v_x_3040_;
                        v_isShared_3054_ = v_isSharedCheck_3060_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3051_);
                        crate::leanh::lean_dec(v_x_3040_);
                        v___x_3053_ = crate::leanh::lean_box(0);
                        v_isShared_3054_ = v_isSharedCheck_3060_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3045_ == 0 {
                    v___x_3047_ = v___x_3044_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3049_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3049_, 0, v_a_3042_);
                    v___x_3047_ = v_reuseFailAlloc_3049_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3048_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3048_, 0, v___x_3047_);
                return v___x_3048_;
            }
            3 => {
                v___x_3055_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3055_, 0, v_a_3039_);
                crate::leanh::lean_ctor_set(v___x_3055_, 1, v_a_3051_);
                if v_isShared_3054_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3053_, 0, v___x_3055_);
                    v___x_3057_ = v___x_3053_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3059_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3059_, 0, v___x_3055_);
                    v___x_3057_ = v_reuseFailAlloc_3059_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3058_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3058_, 0, v___x_3057_);
                return v___x_3058_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_concurrently___redArg___lam__10___boxed(
    mut v_a_3061_: *mut crate::leanh::LeanObject,
    mut v_x_3062_: *mut crate::leanh::LeanObject,
    mut v___y_3063_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3064_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__10(v_a_3061_, v_x_3062_);
    return v_res_3064_;
}
pub unsafe fn l_Std_Async_ContextAsync_concurrently___redArg___lam__8(
    mut v_a_3065_: *mut crate::leanh::LeanObject,
    mut v_x_3066_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3071_: u8 = 0;
    let mut v___x_3073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3076_: u8 = 0;
    let mut v_a_3077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: u8 = 0;
    let mut v___x_3082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3066_) == 0 {
                    crate::leanh::lean_dec_ref(v_a_3065_);
                    v_a_3068_ = crate::leanh::lean_ctor_get(v_x_3066_, 0);
                    v_isSharedCheck_3076_ = (!crate::leanh::lean_is_exclusive(v_x_3066_)) as u8;
                    if v_isSharedCheck_3076_ == 0 {
                        v___x_3070_ = v_x_3066_;
                        v_isShared_3071_ = v_isSharedCheck_3076_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3068_);
                        crate::leanh::lean_dec(v_x_3066_);
                        v___x_3070_ = crate::leanh::lean_box(0);
                        v_isShared_3071_ = v_isSharedCheck_3076_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3077_ = crate::leanh::lean_ctor_get(v_x_3066_, 0);
                    crate::leanh::lean_inc(v_a_3077_);
                    crate::leanh::lean_dec_ref_known(v_x_3066_, 1);
                    v___f_3078_ = crate::leanh::lean_alloc_closure(
                        l_Std_Async_ContextAsync_concurrently___redArg___lam__10___boxed
                            as *mut core::ffi::c_void,
                        3,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_3078_, 0, v_a_3077_);
                    v___x_3079_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3079_, 0, v_a_3065_);
                    v___x_3080_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3081_ = 0;
                    v___x_3082_ =
                        l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v___x_3080_,
                            v___x_3081_,
                            v___x_3079_,
                            v___f_3078_,
                        );
                    return v___x_3082_;
                }
            }
            1 => {
                if v_isShared_3071_ == 0 {
                    v___x_3073_ = v___x_3070_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3075_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3075_, 0, v_a_3068_);
                    v___x_3073_ = v_reuseFailAlloc_3075_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3074_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3074_, 0, v___x_3073_);
                return v___x_3074_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_concurrently___redArg___lam__8___boxed(
    mut v_a_3083_: *mut crate::leanh::LeanObject,
    mut v_x_3084_: *mut crate::leanh::LeanObject,
    mut v___y_3085_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3086_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__8(v_a_3083_, v_x_3084_);
    return v_res_3086_;
}
pub unsafe fn l_Std_Async_ContextAsync_concurrently___redArg___lam__9(
    mut v_a_3087_: *mut crate::leanh::LeanObject,
    mut v_x_3088_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3093_: u8 = 0;
    let mut v___x_3095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3098_: u8 = 0;
    let mut v_a_3099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3103_: u8 = 0;
    let mut v___x_3104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3088_) == 0 {
                    crate::leanh::lean_dec_ref(v_a_3087_);
                    v_a_3090_ = crate::leanh::lean_ctor_get(v_x_3088_, 0);
                    v_isSharedCheck_3098_ = (!crate::leanh::lean_is_exclusive(v_x_3088_)) as u8;
                    if v_isSharedCheck_3098_ == 0 {
                        v___x_3092_ = v_x_3088_;
                        v_isShared_3093_ = v_isSharedCheck_3098_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3090_);
                        crate::leanh::lean_dec(v_x_3088_);
                        v___x_3092_ = crate::leanh::lean_box(0);
                        v_isShared_3093_ = v_isSharedCheck_3098_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3099_ = crate::leanh::lean_ctor_get(v_x_3088_, 0);
                    crate::leanh::lean_inc(v_a_3099_);
                    crate::leanh::lean_dec_ref_known(v_x_3088_, 1);
                    v___f_3100_ = crate::leanh::lean_alloc_closure(
                        l_Std_Async_ContextAsync_concurrently___redArg___lam__8___boxed
                            as *mut core::ffi::c_void,
                        3,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_3100_, 0, v_a_3099_);
                    v___x_3101_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3101_, 0, v_a_3087_);
                    v___x_3102_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3103_ = 0;
                    v___x_3104_ =
                        l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v___x_3102_,
                            v___x_3103_,
                            v___x_3101_,
                            v___f_3100_,
                        );
                    return v___x_3104_;
                }
            }
            1 => {
                if v_isShared_3093_ == 0 {
                    v___x_3095_ = v___x_3092_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3097_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3097_, 0, v_a_3090_);
                    v___x_3095_ = v_reuseFailAlloc_3097_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3096_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3096_, 0, v___x_3095_);
                return v___x_3096_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_concurrently___redArg___lam__9___boxed(
    mut v_a_3105_: *mut crate::leanh::LeanObject,
    mut v_x_3106_: *mut crate::leanh::LeanObject,
    mut v___y_3107_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3108_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__9(v_a_3105_, v_x_3106_);
    return v_res_3108_;
}
pub unsafe fn l_Std_Async_ContextAsync_concurrently___redArg___lam__11(
    mut v___f_3109_: *mut crate::leanh::LeanObject,
    mut v_prio_3110_: *mut crate::leanh::LeanObject,
    mut v___f_3111_: *mut crate::leanh::LeanObject,
    mut v_x_3112_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3117_: u8 = 0;
    let mut v___x_3119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3122_: u8 = 0;
    let mut v_a_3123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3126_: u8 = 0;
    let mut v___x_3127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3131_: u8 = 0;
    let mut v___x_3132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3136_: u8 = 0;
    let mut v___x_3137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3139_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3112_) == 0 {
                    crate::leanh::lean_dec_ref(v___f_3111_);
                    crate::leanh::lean_dec(v_prio_3110_);
                    crate::leanh::lean_dec_ref(v___f_3109_);
                    v_a_3114_ = crate::leanh::lean_ctor_get(v_x_3112_, 0);
                    v_isSharedCheck_3122_ = (!crate::leanh::lean_is_exclusive(v_x_3112_)) as u8;
                    if v_isSharedCheck_3122_ == 0 {
                        v___x_3116_ = v_x_3112_;
                        v_isShared_3117_ = v_isSharedCheck_3122_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3114_);
                        crate::leanh::lean_dec(v_x_3112_);
                        v___x_3116_ = crate::leanh::lean_box(0);
                        v_isShared_3117_ = v_isSharedCheck_3122_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3123_ = crate::leanh::lean_ctor_get(v_x_3112_, 0);
                    v_isSharedCheck_3139_ = (!crate::leanh::lean_is_exclusive(v_x_3112_)) as u8;
                    if v_isSharedCheck_3139_ == 0 {
                        v___x_3125_ = v_x_3112_;
                        v_isShared_3126_ = v_isSharedCheck_3139_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3123_);
                        crate::leanh::lean_dec(v_x_3112_);
                        v___x_3125_ = crate::leanh::lean_box(0);
                        v_isShared_3126_ = v_isSharedCheck_3139_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3117_ == 0 {
                    v___x_3119_ = v___x_3116_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3121_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3121_, 0, v_a_3114_);
                    v___x_3119_ = v_reuseFailAlloc_3121_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3120_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3120_, 0, v___x_3119_);
                return v___x_3120_;
            }
            3 => {
                v___x_3127_ = crate::leanh::lean_alloc_closure(
                    l_Std_Async_BaseAsync_toRawBaseIO___boxed as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___x_3127_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_3127_, 1, v___f_3109_);
                v___x_3128_ = lean_io_as_task(v___x_3127_, v_prio_3110_);
                v___f_3129_ = crate::leanh::lean_alloc_closure(
                    l_Std_Async_ContextAsync_concurrently___redArg___lam__9___boxed
                        as *mut core::ffi::c_void,
                    3,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3129_, 0, v_a_3123_);
                v___x_3130_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3131_ = 1;
                v___x_3132_ = lean_task_bind(v___x_3128_, v___f_3111_, v___x_3130_, v___x_3131_);
                if v_isShared_3126_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3125_, 0, v___x_3132_);
                    v___x_3134_ = v___x_3125_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3138_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3138_, 0, v___x_3132_);
                    v___x_3134_ = v_reuseFailAlloc_3138_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3135_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3135_, 0, v___x_3134_);
                v___x_3136_ = 0;
                v___x_3137_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_3130_,
                    v___x_3136_,
                    v___x_3135_,
                    v___f_3129_,
                );
                return v___x_3137_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_concurrently___redArg___lam__11___boxed(
    mut v___f_3140_: *mut crate::leanh::LeanObject,
    mut v_prio_3141_: *mut crate::leanh::LeanObject,
    mut v___f_3142_: *mut crate::leanh::LeanObject,
    mut v_x_3143_: *mut crate::leanh::LeanObject,
    mut v___y_3144_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3145_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__11(
        v___f_3140_,
        v_prio_3141_,
        v___f_3142_,
        v_x_3143_,
    );
    return v_res_3145_;
}
pub unsafe fn l_Std_Async_ContextAsync_concurrently___redArg___lam__12(
    mut v_x_3146_: *mut crate::leanh::LeanObject,
    mut v_x_3147_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3152_: u8 = 0;
    let mut v___x_3154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3157_: u8 = 0;
    let mut v___x_3158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3147_) == 0 {
                    crate::leanh::lean_dec_ref(v_x_3146_);
                    v_a_3149_ = crate::leanh::lean_ctor_get(v_x_3147_, 0);
                    v_isSharedCheck_3157_ = (!crate::leanh::lean_is_exclusive(v_x_3147_)) as u8;
                    if v_isSharedCheck_3157_ == 0 {
                        v___x_3151_ = v_x_3147_;
                        v_isShared_3152_ = v_isSharedCheck_3157_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3149_);
                        crate::leanh::lean_dec(v_x_3147_);
                        v___x_3151_ = crate::leanh::lean_box(0);
                        v_isShared_3152_ = v_isSharedCheck_3157_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v_x_3147_, 1);
                    v___x_3158_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3158_, 0, v_x_3146_);
                    return v___x_3158_;
                }
            }
            1 => {
                if v_isShared_3152_ == 0 {
                    v___x_3154_ = v___x_3151_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3156_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3156_, 0, v_a_3149_);
                    v___x_3154_ = v_reuseFailAlloc_3156_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3155_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3155_, 0, v___x_3154_);
                return v___x_3155_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_concurrently___redArg___lam__12___boxed(
    mut v_x_3159_: *mut crate::leanh::LeanObject,
    mut v_x_3160_: *mut crate::leanh::LeanObject,
    mut v___y_3161_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3162_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__12(v_x_3159_, v_x_3160_);
    return v_res_3162_;
}
pub unsafe fn l_Std_Async_ContextAsync_concurrently___redArg___lam__13(
    mut v_a_3163_: *mut crate::leanh::LeanObject,
    mut v___x_3164_: *mut crate::leanh::LeanObject,
    mut v_x_3165_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_3165_) == 0 {
        let mut v___x_3167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___x_3164_);
        crate::leanh::lean_dec_ref(v_a_3163_);
        v___x_3167_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3167_, 0, v_x_3165_);
        return v___x_3167_;
    } else {
        let mut v___x_3168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3173_: u8 = 0;
        let mut v___x_3174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3168_ = l_Std_CancellationContext_cancel(v_a_3163_, v___x_3164_);
        v___f_3169_ = crate::leanh::lean_alloc_closure(
            l_Std_Async_ContextAsync_concurrently___redArg___lam__12___boxed
                as *mut core::ffi::c_void,
            3,
            1,
        );
        crate::leanh::lean_closure_set(v___f_3169_, 0, v_x_3165_);
        v___x_3170_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3170_, 0, v___x_3168_);
        v___x_3171_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3171_, 0, v___x_3170_);
        v___x_3172_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_3173_ = 0;
        v___x_3174_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_3172_,
            v___x_3173_,
            v___x_3171_,
            v___f_3169_,
        );
        return v___x_3174_;
    }
}
pub unsafe fn l_Std_Async_ContextAsync_concurrently___redArg___lam__13___boxed(
    mut v_a_3175_: *mut crate::leanh::LeanObject,
    mut v___x_3176_: *mut crate::leanh::LeanObject,
    mut v_x_3177_: *mut crate::leanh::LeanObject,
    mut v___y_3178_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3179_ =
        l_Std_Async_ContextAsync_concurrently___redArg___lam__13(v_a_3175_, v___x_3176_, v_x_3177_);
    return v_res_3179_;
}
pub unsafe fn l_Std_Async_ContextAsync_concurrently___redArg___lam__14(
    mut v_a_3180_: *mut crate::leanh::LeanObject,
    mut v___f_3181_: *mut crate::leanh::LeanObject,
    mut v___f_3182_: *mut crate::leanh::LeanObject,
    mut v_prio_3183_: *mut crate::leanh::LeanObject,
    mut v_a_3184_: *mut crate::leanh::LeanObject,
    mut v_y_3185_: *mut crate::leanh::LeanObject,
    mut v___f_3186_: *mut crate::leanh::LeanObject,
    mut v___f_3187_: *mut crate::leanh::LeanObject,
    mut v___f_3188_: *mut crate::leanh::LeanObject,
    mut v_x_3189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3194_: u8 = 0;
    let mut v___x_3196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3199_: u8 = 0;
    let mut v_a_3200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3203_: u8 = 0;
    let mut v___x_3204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: u8 = 0;
    let mut v___x_3216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: u8 = 0;
    let mut v___x_3221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3225_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3189_) == 0 {
                    crate::leanh::lean_dec_ref(v___f_3188_);
                    crate::leanh::lean_dec_ref(v___f_3187_);
                    crate::leanh::lean_dec(v___f_3186_);
                    crate::leanh::lean_dec_ref(v_y_3185_);
                    crate::leanh::lean_dec_ref(v_a_3184_);
                    crate::leanh::lean_dec(v_prio_3183_);
                    crate::leanh::lean_dec(v___f_3182_);
                    crate::leanh::lean_dec_ref(v___f_3181_);
                    crate::leanh::lean_dec_ref(v_a_3180_);
                    v_a_3191_ = crate::leanh::lean_ctor_get(v_x_3189_, 0);
                    v_isSharedCheck_3199_ = (!crate::leanh::lean_is_exclusive(v_x_3189_)) as u8;
                    if v_isSharedCheck_3199_ == 0 {
                        v___x_3193_ = v_x_3189_;
                        v_isShared_3194_ = v_isSharedCheck_3199_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3191_);
                        crate::leanh::lean_dec(v_x_3189_);
                        v___x_3193_ = crate::leanh::lean_box(0);
                        v_isShared_3194_ = v_isSharedCheck_3199_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3200_ = crate::leanh::lean_ctor_get(v_x_3189_, 0);
                    v_isSharedCheck_3225_ = (!crate::leanh::lean_is_exclusive(v_x_3189_)) as u8;
                    if v_isSharedCheck_3225_ == 0 {
                        v___x_3202_ = v_x_3189_;
                        v_isShared_3203_ = v_isSharedCheck_3225_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3200_);
                        crate::leanh::lean_dec(v_x_3189_);
                        v___x_3202_ = crate::leanh::lean_box(0);
                        v_isShared_3203_ = v_isSharedCheck_3225_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3194_ == 0 {
                    v___x_3196_ = v___x_3193_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3198_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3198_, 0, v_a_3191_);
                    v___x_3196_ = v_reuseFailAlloc_3198_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3197_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3197_, 0, v___x_3196_);
                return v___x_3197_;
            }
            3 => {
                v___x_3204_ = crate::leanh::lean_box(2);
                v___f_3205_ = crate::leanh::lean_alloc_closure(
                    l_Std_Async_ContextAsync_concurrently___redArg___lam__3___boxed
                        as *mut core::ffi::c_void,
                    4,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_3205_, 0, v_a_3180_);
                crate::leanh::lean_closure_set(v___f_3205_, 1, v___x_3204_);
                v___f_3206_ = crate::leanh::lean_alloc_closure(
                    l_Std_Async_ContextAsync_concurrently___redArg___lam__5___boxed
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_3206_, 0, v___f_3181_);
                crate::leanh::lean_closure_set(v___f_3206_, 1, v___f_3205_);
                crate::leanh::lean_closure_set(v___f_3206_, 2, v___f_3182_);
                v___x_3207_ = crate::leanh::lean_alloc_closure(
                    l_Std_Async_BaseAsync_toRawBaseIO___boxed as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___x_3207_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_3207_, 1, v___f_3206_);
                crate::leanh::lean_inc(v_prio_3183_);
                v___x_3208_ = lean_io_as_task(v___x_3207_, v_prio_3183_);
                crate::leanh::lean_inc_ref(v_a_3184_);
                v___f_3209_ = crate::leanh::lean_alloc_closure(
                    l_Std_Async_ContextAsync_concurrently___redArg___lam__7___boxed
                        as *mut core::ffi::c_void,
                    4,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_3209_, 0, v_a_3184_);
                crate::leanh::lean_closure_set(v___f_3209_, 1, v___x_3204_);
                crate::leanh::lean_inc(v_a_3200_);
                v___f_3210_ = crate::leanh::lean_alloc_closure(
                    l_Std_Async_ContextAsync_concurrently___redArg___lam__6___boxed
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_3210_, 0, v_y_3185_);
                crate::leanh::lean_closure_set(v___f_3210_, 1, v_a_3200_);
                crate::leanh::lean_closure_set(v___f_3210_, 2, v___f_3209_);
                v___f_3211_ = crate::leanh::lean_alloc_closure(
                    l_Std_Async_ContextAsync_concurrently___redArg___lam__3___boxed
                        as *mut core::ffi::c_void,
                    4,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_3211_, 0, v_a_3200_);
                crate::leanh::lean_closure_set(v___f_3211_, 1, v___x_3204_);
                v___f_3212_ = crate::leanh::lean_alloc_closure(
                    l_Std_Async_ContextAsync_concurrently___redArg___lam__5___boxed
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_3212_, 0, v___f_3210_);
                crate::leanh::lean_closure_set(v___f_3212_, 1, v___f_3211_);
                crate::leanh::lean_closure_set(v___f_3212_, 2, v___f_3186_);
                v___f_3213_ = crate::leanh::lean_alloc_closure(
                    l_Std_Async_ContextAsync_concurrently___redArg___lam__11___boxed
                        as *mut core::ffi::c_void,
                    5,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_3213_, 0, v___f_3212_);
                crate::leanh::lean_closure_set(v___f_3213_, 1, v_prio_3183_);
                crate::leanh::lean_closure_set(v___f_3213_, 2, v___f_3187_);
                v___x_3214_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3215_ = 1;
                v___x_3216_ = lean_task_bind(v___x_3208_, v___f_3188_, v___x_3214_, v___x_3215_);
                if v_isShared_3203_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3202_, 0, v___x_3216_);
                    v___x_3218_ = v___x_3202_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3224_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3224_, 0, v___x_3216_);
                    v___x_3218_ = v_reuseFailAlloc_3224_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3219_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3219_, 0, v___x_3218_);
                v___x_3220_ = 0;
                v___x_3221_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_3214_,
                    v___x_3220_,
                    v___x_3219_,
                    v___f_3213_,
                );
                v___f_3222_ = crate::leanh::lean_alloc_closure(
                    l_Std_Async_ContextAsync_concurrently___redArg___lam__13___boxed
                        as *mut core::ffi::c_void,
                    4,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_3222_, 0, v_a_3184_);
                crate::leanh::lean_closure_set(v___f_3222_, 1, v___x_3204_);
                v___x_3223_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_3214_,
                    v___x_3220_,
                    v___x_3221_,
                    v___f_3222_,
                );
                return v___x_3223_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_concurrently___redArg___lam__14___boxed(
    mut v_a_3226_: *mut crate::leanh::LeanObject,
    mut v___f_3227_: *mut crate::leanh::LeanObject,
    mut v___f_3228_: *mut crate::leanh::LeanObject,
    mut v_prio_3229_: *mut crate::leanh::LeanObject,
    mut v_a_3230_: *mut crate::leanh::LeanObject,
    mut v_y_3231_: *mut crate::leanh::LeanObject,
    mut v___f_3232_: *mut crate::leanh::LeanObject,
    mut v___f_3233_: *mut crate::leanh::LeanObject,
    mut v___f_3234_: *mut crate::leanh::LeanObject,
    mut v_x_3235_: *mut crate::leanh::LeanObject,
    mut v___y_3236_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3237_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__14(
        v_a_3226_,
        v___f_3227_,
        v___f_3228_,
        v_prio_3229_,
        v_a_3230_,
        v_y_3231_,
        v___f_3232_,
        v___f_3233_,
        v___f_3234_,
        v_x_3235_,
    );
    return v_res_3237_;
}
pub unsafe fn l_Std_Async_ContextAsync_concurrently___redArg___lam__15(
    mut v_a_3238_: *mut crate::leanh::LeanObject,
    mut v_x_3239_: *mut crate::leanh::LeanObject,
    mut v___f_3240_: *mut crate::leanh::LeanObject,
    mut v___f_3241_: *mut crate::leanh::LeanObject,
    mut v_prio_3242_: *mut crate::leanh::LeanObject,
    mut v_y_3243_: *mut crate::leanh::LeanObject,
    mut v___f_3244_: *mut crate::leanh::LeanObject,
    mut v___f_3245_: *mut crate::leanh::LeanObject,
    mut v___f_3246_: *mut crate::leanh::LeanObject,
    mut v_x_3247_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3252_: u8 = 0;
    let mut v___x_3254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3257_: u8 = 0;
    let mut v_a_3258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3261_: u8 = 0;
    let mut v___x_3262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: u8 = 0;
    let mut v___x_3270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3272_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3247_) == 0 {
                    crate::leanh::lean_dec_ref(v___f_3246_);
                    crate::leanh::lean_dec_ref(v___f_3245_);
                    crate::leanh::lean_dec(v___f_3244_);
                    crate::leanh::lean_dec_ref(v_y_3243_);
                    crate::leanh::lean_dec(v_prio_3242_);
                    crate::leanh::lean_dec(v___f_3241_);
                    crate::leanh::lean_dec_ref(v___f_3240_);
                    crate::leanh::lean_dec_ref(v_x_3239_);
                    crate::leanh::lean_dec_ref(v_a_3238_);
                    v_a_3249_ = crate::leanh::lean_ctor_get(v_x_3247_, 0);
                    v_isSharedCheck_3257_ = (!crate::leanh::lean_is_exclusive(v_x_3247_)) as u8;
                    if v_isSharedCheck_3257_ == 0 {
                        v___x_3251_ = v_x_3247_;
                        v_isShared_3252_ = v_isSharedCheck_3257_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3249_);
                        crate::leanh::lean_dec(v_x_3247_);
                        v___x_3251_ = crate::leanh::lean_box(0);
                        v_isShared_3252_ = v_isSharedCheck_3257_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3258_ = crate::leanh::lean_ctor_get(v_x_3247_, 0);
                    v_isSharedCheck_3272_ = (!crate::leanh::lean_is_exclusive(v_x_3247_)) as u8;
                    if v_isSharedCheck_3272_ == 0 {
                        v___x_3260_ = v_x_3247_;
                        v_isShared_3261_ = v_isSharedCheck_3272_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3258_);
                        crate::leanh::lean_dec(v_x_3247_);
                        v___x_3260_ = crate::leanh::lean_box(0);
                        v_isShared_3261_ = v_isSharedCheck_3272_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3252_ == 0 {
                    v___x_3254_ = v___x_3251_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3256_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3256_, 0, v_a_3249_);
                    v___x_3254_ = v_reuseFailAlloc_3256_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3255_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3255_, 0, v___x_3254_);
                return v___x_3255_;
            }
            3 => {
                crate::leanh::lean_inc_ref(v_a_3238_);
                v___x_3262_ = l_Std_CancellationContext_fork(v_a_3238_);
                crate::leanh::lean_inc(v_a_3258_);
                v___f_3263_ = crate::leanh::lean_alloc_closure(
                    l_Std_Async_ContextAsync_concurrently___redArg___lam__1___boxed
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_3263_, 0, v_x_3239_);
                crate::leanh::lean_closure_set(v___f_3263_, 1, v_a_3258_);
                crate::leanh::lean_closure_set(v___f_3263_, 2, v___f_3240_);
                v___f_3264_ = crate::leanh::lean_alloc_closure(
                    l_Std_Async_ContextAsync_concurrently___redArg___lam__14___boxed
                        as *mut core::ffi::c_void,
                    11,
                    9,
                );
                crate::leanh::lean_closure_set(v___f_3264_, 0, v_a_3258_);
                crate::leanh::lean_closure_set(v___f_3264_, 1, v___f_3263_);
                crate::leanh::lean_closure_set(v___f_3264_, 2, v___f_3241_);
                crate::leanh::lean_closure_set(v___f_3264_, 3, v_prio_3242_);
                crate::leanh::lean_closure_set(v___f_3264_, 4, v_a_3238_);
                crate::leanh::lean_closure_set(v___f_3264_, 5, v_y_3243_);
                crate::leanh::lean_closure_set(v___f_3264_, 6, v___f_3244_);
                crate::leanh::lean_closure_set(v___f_3264_, 7, v___f_3245_);
                crate::leanh::lean_closure_set(v___f_3264_, 8, v___f_3246_);
                if v_isShared_3261_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3260_, 0, v___x_3262_);
                    v___x_3266_ = v___x_3260_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3271_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3271_, 0, v___x_3262_);
                    v___x_3266_ = v_reuseFailAlloc_3271_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3267_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3267_, 0, v___x_3266_);
                v___x_3268_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3269_ = 0;
                v___x_3270_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_3268_,
                    v___x_3269_,
                    v___x_3267_,
                    v___f_3264_,
                );
                return v___x_3270_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_concurrently___redArg___lam__15___boxed(
    mut v_a_3273_: *mut crate::leanh::LeanObject,
    mut v_x_3274_: *mut crate::leanh::LeanObject,
    mut v___f_3275_: *mut crate::leanh::LeanObject,
    mut v___f_3276_: *mut crate::leanh::LeanObject,
    mut v_prio_3277_: *mut crate::leanh::LeanObject,
    mut v_y_3278_: *mut crate::leanh::LeanObject,
    mut v___f_3279_: *mut crate::leanh::LeanObject,
    mut v___f_3280_: *mut crate::leanh::LeanObject,
    mut v___f_3281_: *mut crate::leanh::LeanObject,
    mut v_x_3282_: *mut crate::leanh::LeanObject,
    mut v___y_3283_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3284_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__15(
        v_a_3273_,
        v_x_3274_,
        v___f_3275_,
        v___f_3276_,
        v_prio_3277_,
        v_y_3278_,
        v___f_3279_,
        v___f_3280_,
        v___f_3281_,
        v_x_3282_,
    );
    return v_res_3284_;
}
pub unsafe fn l_Std_Async_ContextAsync_concurrently___redArg___lam__16(
    mut v_x_3285_: *mut crate::leanh::LeanObject,
    mut v___f_3286_: *mut crate::leanh::LeanObject,
    mut v_prio_3287_: *mut crate::leanh::LeanObject,
    mut v_y_3288_: *mut crate::leanh::LeanObject,
    mut v___f_3289_: *mut crate::leanh::LeanObject,
    mut v___f_3290_: *mut crate::leanh::LeanObject,
    mut v___f_3291_: *mut crate::leanh::LeanObject,
    mut v_x_3292_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3297_: u8 = 0;
    let mut v___x_3299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3302_: u8 = 0;
    let mut v_a_3303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3306_: u8 = 0;
    let mut v___x_3307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3314_: u8 = 0;
    let mut v___x_3315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3317_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3292_) == 0 {
                    crate::leanh::lean_dec_ref(v___f_3291_);
                    crate::leanh::lean_dec_ref(v___f_3290_);
                    crate::leanh::lean_dec(v___f_3289_);
                    crate::leanh::lean_dec_ref(v_y_3288_);
                    crate::leanh::lean_dec(v_prio_3287_);
                    crate::leanh::lean_dec(v___f_3286_);
                    crate::leanh::lean_dec_ref(v_x_3285_);
                    v_a_3294_ = crate::leanh::lean_ctor_get(v_x_3292_, 0);
                    v_isSharedCheck_3302_ = (!crate::leanh::lean_is_exclusive(v_x_3292_)) as u8;
                    if v_isSharedCheck_3302_ == 0 {
                        v___x_3296_ = v_x_3292_;
                        v_isShared_3297_ = v_isSharedCheck_3302_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3294_);
                        crate::leanh::lean_dec(v_x_3292_);
                        v___x_3296_ = crate::leanh::lean_box(0);
                        v_isShared_3297_ = v_isSharedCheck_3302_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3303_ = crate::leanh::lean_ctor_get(v_x_3292_, 0);
                    v_isSharedCheck_3317_ = (!crate::leanh::lean_is_exclusive(v_x_3292_)) as u8;
                    if v_isSharedCheck_3317_ == 0 {
                        v___x_3305_ = v_x_3292_;
                        v_isShared_3306_ = v_isSharedCheck_3317_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3303_);
                        crate::leanh::lean_dec(v_x_3292_);
                        v___x_3305_ = crate::leanh::lean_box(0);
                        v_isShared_3306_ = v_isSharedCheck_3317_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3297_ == 0 {
                    v___x_3299_ = v___x_3296_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3301_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3301_, 0, v_a_3294_);
                    v___x_3299_ = v_reuseFailAlloc_3301_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3300_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3300_, 0, v___x_3299_);
                return v___x_3300_;
            }
            3 => {
                crate::leanh::lean_inc_n(v_a_3303_, 2);
                v___x_3307_ = l_Std_CancellationContext_fork(v_a_3303_);
                v___f_3308_ = crate::leanh::lean_alloc_closure(
                    l_Std_Async_ContextAsync_concurrently___redArg___lam__4___boxed
                        as *mut core::ffi::c_void,
                    3,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3308_, 0, v_a_3303_);
                v___f_3309_ = crate::leanh::lean_alloc_closure(
                    l_Std_Async_ContextAsync_concurrently___redArg___lam__15___boxed
                        as *mut core::ffi::c_void,
                    11,
                    9,
                );
                crate::leanh::lean_closure_set(v___f_3309_, 0, v_a_3303_);
                crate::leanh::lean_closure_set(v___f_3309_, 1, v_x_3285_);
                crate::leanh::lean_closure_set(v___f_3309_, 2, v___f_3308_);
                crate::leanh::lean_closure_set(v___f_3309_, 3, v___f_3286_);
                crate::leanh::lean_closure_set(v___f_3309_, 4, v_prio_3287_);
                crate::leanh::lean_closure_set(v___f_3309_, 5, v_y_3288_);
                crate::leanh::lean_closure_set(v___f_3309_, 6, v___f_3289_);
                crate::leanh::lean_closure_set(v___f_3309_, 7, v___f_3290_);
                crate::leanh::lean_closure_set(v___f_3309_, 8, v___f_3291_);
                if v_isShared_3306_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3305_, 0, v___x_3307_);
                    v___x_3311_ = v___x_3305_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3316_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3316_, 0, v___x_3307_);
                    v___x_3311_ = v_reuseFailAlloc_3316_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3312_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3312_, 0, v___x_3311_);
                v___x_3313_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3314_ = 0;
                v___x_3315_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_3313_,
                    v___x_3314_,
                    v___x_3312_,
                    v___f_3309_,
                );
                return v___x_3315_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_concurrently___redArg___lam__16___boxed(
    mut v_x_3318_: *mut crate::leanh::LeanObject,
    mut v___f_3319_: *mut crate::leanh::LeanObject,
    mut v_prio_3320_: *mut crate::leanh::LeanObject,
    mut v_y_3321_: *mut crate::leanh::LeanObject,
    mut v___f_3322_: *mut crate::leanh::LeanObject,
    mut v___f_3323_: *mut crate::leanh::LeanObject,
    mut v___f_3324_: *mut crate::leanh::LeanObject,
    mut v_x_3325_: *mut crate::leanh::LeanObject,
    mut v___y_3326_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3327_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__16(
        v_x_3318_,
        v___f_3319_,
        v_prio_3320_,
        v_y_3321_,
        v___f_3322_,
        v___f_3323_,
        v___f_3324_,
        v_x_3325_,
    );
    return v_res_3327_;
}
pub unsafe fn l_Std_Async_ContextAsync_concurrently___redArg___lam__17(
    mut v___f_3328_: *mut crate::leanh::LeanObject,
    mut v_x_3329_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3334_: u8 = 0;
    let mut v___x_3336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3339_: u8 = 0;
    let mut v_a_3340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3343_: u8 = 0;
    let mut v___x_3344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3349_: u8 = 0;
    let mut v___x_3350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3352_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3329_) == 0 {
                    crate::leanh::lean_dec_ref(v___f_3328_);
                    v_a_3331_ = crate::leanh::lean_ctor_get(v_x_3329_, 0);
                    v_isSharedCheck_3339_ = (!crate::leanh::lean_is_exclusive(v_x_3329_)) as u8;
                    if v_isSharedCheck_3339_ == 0 {
                        v___x_3333_ = v_x_3329_;
                        v_isShared_3334_ = v_isSharedCheck_3339_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3331_);
                        crate::leanh::lean_dec(v_x_3329_);
                        v___x_3333_ = crate::leanh::lean_box(0);
                        v_isShared_3334_ = v_isSharedCheck_3339_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3340_ = crate::leanh::lean_ctor_get(v_x_3329_, 0);
                    v_isSharedCheck_3352_ = (!crate::leanh::lean_is_exclusive(v_x_3329_)) as u8;
                    if v_isSharedCheck_3352_ == 0 {
                        v___x_3342_ = v_x_3329_;
                        v_isShared_3343_ = v_isSharedCheck_3352_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3340_);
                        crate::leanh::lean_dec(v_x_3329_);
                        v___x_3342_ = crate::leanh::lean_box(0);
                        v_isShared_3343_ = v_isSharedCheck_3352_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3334_ == 0 {
                    v___x_3336_ = v___x_3333_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3338_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3338_, 0, v_a_3331_);
                    v___x_3336_ = v_reuseFailAlloc_3338_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3337_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3337_, 0, v___x_3336_);
                return v___x_3337_;
            }
            3 => {
                v___x_3344_ = l_Std_CancellationContext_fork(v_a_3340_);
                if v_isShared_3343_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3342_, 0, v___x_3344_);
                    v___x_3346_ = v___x_3342_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3351_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3351_, 0, v___x_3344_);
                    v___x_3346_ = v_reuseFailAlloc_3351_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3347_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3347_, 0, v___x_3346_);
                v___x_3348_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3349_ = 0;
                v___x_3350_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_3348_,
                    v___x_3349_,
                    v___x_3347_,
                    v___f_3328_,
                );
                return v___x_3350_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_concurrently___redArg___lam__17___boxed(
    mut v___f_3353_: *mut crate::leanh::LeanObject,
    mut v_x_3354_: *mut crate::leanh::LeanObject,
    mut v___y_3355_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3356_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__17(v___f_3353_, v_x_3354_);
    return v_res_3356_;
}
pub unsafe fn l_Std_Async_ContextAsync_concurrently___redArg(
    mut v_x_3359_: *mut crate::leanh::LeanObject,
    mut v_y_3360_: *mut crate::leanh::LeanObject,
    mut v_prio_3361_: *mut crate::leanh::LeanObject,
    mut v_a_3362_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: u8 = 0;
    let mut v___x_3372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3364_ = l_Std_Async_ContextAsync_concurrently___redArg___closed__0;
    v___f_3365_ = l_Std_Async_ContextAsync_concurrently___redArg___closed__1;
    v___f_3366_ = crate::leanh::lean_alloc_closure(
        l_Std_Async_ContextAsync_concurrently___redArg___lam__16___boxed as *mut core::ffi::c_void,
        9,
        7,
    );
    crate::leanh::lean_closure_set(v___f_3366_, 0, v_x_3359_);
    crate::leanh::lean_closure_set(v___f_3366_, 1, v___f_3365_);
    crate::leanh::lean_closure_set(v___f_3366_, 2, v_prio_3361_);
    crate::leanh::lean_closure_set(v___f_3366_, 3, v_y_3360_);
    crate::leanh::lean_closure_set(v___f_3366_, 4, v___f_3365_);
    crate::leanh::lean_closure_set(v___f_3366_, 5, v___f_3364_);
    crate::leanh::lean_closure_set(v___f_3366_, 6, v___f_3364_);
    v___f_3367_ = crate::leanh::lean_alloc_closure(
        l_Std_Async_ContextAsync_concurrently___redArg___lam__17___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3367_, 0, v___f_3366_);
    crate::leanh::lean_inc_ref(v_a_3362_);
    v___x_3368_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3368_, 0, v_a_3362_);
    v___x_3369_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3369_, 0, v___x_3368_);
    v___x_3370_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3371_ = 0;
    v___x_3372_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3370_,
        v___x_3371_,
        v___x_3369_,
        v___f_3367_,
    );
    return v___x_3372_;
}
pub unsafe fn l_Std_Async_ContextAsync_concurrently___redArg___boxed(
    mut v_x_3373_: *mut crate::leanh::LeanObject,
    mut v_y_3374_: *mut crate::leanh::LeanObject,
    mut v_prio_3375_: *mut crate::leanh::LeanObject,
    mut v_a_3376_: *mut crate::leanh::LeanObject,
    mut v_a_3377_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3378_ = l_Std_Async_ContextAsync_concurrently___redArg(
        v_x_3373_,
        v_y_3374_,
        v_prio_3375_,
        v_a_3376_,
    );
    crate::leanh::lean_dec_ref(v_a_3376_);
    return v_res_3378_;
}
pub unsafe fn l_Std_Async_ContextAsync_concurrently(
    mut v_00_u03b1_3379_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3380_: *mut crate::leanh::LeanObject,
    mut v_x_3381_: *mut crate::leanh::LeanObject,
    mut v_y_3382_: *mut crate::leanh::LeanObject,
    mut v_prio_3383_: *mut crate::leanh::LeanObject,
    mut v_a_3384_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3393_: u8 = 0;
    let mut v___x_3394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3386_ = l_Std_Async_ContextAsync_concurrently___redArg___closed__0;
    v___f_3387_ = l_Std_Async_ContextAsync_concurrently___redArg___closed__1;
    v___f_3388_ = crate::leanh::lean_alloc_closure(
        l_Std_Async_ContextAsync_concurrently___redArg___lam__16___boxed as *mut core::ffi::c_void,
        9,
        7,
    );
    crate::leanh::lean_closure_set(v___f_3388_, 0, v_x_3381_);
    crate::leanh::lean_closure_set(v___f_3388_, 1, v___f_3387_);
    crate::leanh::lean_closure_set(v___f_3388_, 2, v_prio_3383_);
    crate::leanh::lean_closure_set(v___f_3388_, 3, v_y_3382_);
    crate::leanh::lean_closure_set(v___f_3388_, 4, v___f_3387_);
    crate::leanh::lean_closure_set(v___f_3388_, 5, v___f_3386_);
    crate::leanh::lean_closure_set(v___f_3388_, 6, v___f_3386_);
    v___f_3389_ = crate::leanh::lean_alloc_closure(
        l_Std_Async_ContextAsync_concurrently___redArg___lam__17___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3389_, 0, v___f_3388_);
    crate::leanh::lean_inc_ref(v_a_3384_);
    v___x_3390_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3390_, 0, v_a_3384_);
    v___x_3391_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3391_, 0, v___x_3390_);
    v___x_3392_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3393_ = 0;
    v___x_3394_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3392_,
        v___x_3393_,
        v___x_3391_,
        v___f_3389_,
    );
    return v___x_3394_;
}
pub unsafe fn l_Std_Async_ContextAsync_concurrently___boxed(
    mut v_00_u03b1_3395_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_3396_: *mut crate::leanh::LeanObject,
    mut v_x_3397_: *mut crate::leanh::LeanObject,
    mut v_y_3398_: *mut crate::leanh::LeanObject,
    mut v_prio_3399_: *mut crate::leanh::LeanObject,
    mut v_a_3400_: *mut crate::leanh::LeanObject,
    mut v_a_3401_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3402_ = l_Std_Async_ContextAsync_concurrently(
        v_00_u03b1_3395_,
        v_00_u03b2_3396_,
        v_x_3397_,
        v_y_3398_,
        v_prio_3399_,
        v_a_3400_,
    );
    crate::leanh::lean_dec_ref(v_a_3400_);
    return v_res_3402_;
}
pub unsafe fn l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__0(
    mut v___y_3403_: *mut crate::leanh::LeanObject,
    mut v___y_3404_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3406_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3406_, 0, v___y_3403_);
    return v___x_3406_;
}
pub unsafe fn l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__0___boxed(
    mut v___y_3407_: *mut crate::leanh::LeanObject,
    mut v___y_3408_: *mut crate::leanh::LeanObject,
    mut v___y_3409_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3410_ =
        l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__0(v___y_3407_, v___y_3408_);
    crate::leanh::lean_dec_ref(v___y_3408_);
    return v_res_3410_;
}
pub unsafe fn l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__3(
    mut v___x_3411_: *mut crate::leanh::LeanObject,
    mut v___f_3412_: *mut crate::leanh::LeanObject,
    mut v_a_3413_: *mut crate::leanh::LeanObject,
    mut v_x_3414_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3419_: u8 = 0;
    let mut v___x_3421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3424_: u8 = 0;
    let mut v_a_3425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3426_: usize = 0;
    let mut v___x_3427_: usize = 0;
    let mut v___x_4336__overap_3428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3414_) == 0 {
                    crate::leanh::lean_dec_ref(v___f_3412_);
                    crate::leanh::lean_dec_ref(v___x_3411_);
                    v_a_3416_ = crate::leanh::lean_ctor_get(v_x_3414_, 0);
                    v_isSharedCheck_3424_ = (!crate::leanh::lean_is_exclusive(v_x_3414_)) as u8;
                    if v_isSharedCheck_3424_ == 0 {
                        v___x_3418_ = v_x_3414_;
                        v_isShared_3419_ = v_isSharedCheck_3424_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3416_);
                        crate::leanh::lean_dec(v_x_3414_);
                        v___x_3418_ = crate::leanh::lean_box(0);
                        v_isShared_3419_ = v_isSharedCheck_3424_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3425_ = crate::leanh::lean_ctor_get(v_x_3414_, 0);
                    crate::leanh::lean_inc(v_a_3425_);
                    crate::leanh::lean_dec_ref_known(v_x_3414_, 1);
                    v_sz_3426_ = lean_array_size(v_a_3425_);
                    v___x_3427_ = 0usize;
                    v___x_4336__overap_3428_ =
                        l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v___x_3411_,
                            v___f_3412_,
                            v_sz_3426_,
                            v___x_3427_,
                            v_a_3425_,
                        );
                    crate::leanh::lean_inc_ref(v_a_3413_);
                    v___x_3429_ = crate::leanh::lean_apply_2(
                        v___x_4336__overap_3428_,
                        v_a_3413_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_3429_;
                }
            }
            1 => {
                if v_isShared_3419_ == 0 {
                    v___x_3421_ = v___x_3418_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3423_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3423_, 0, v_a_3416_);
                    v___x_3421_ = v_reuseFailAlloc_3423_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3422_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3422_, 0, v___x_3421_);
                return v___x_3422_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__3___boxed(
    mut v___x_3430_: *mut crate::leanh::LeanObject,
    mut v___f_3431_: *mut crate::leanh::LeanObject,
    mut v_a_3432_: *mut crate::leanh::LeanObject,
    mut v_x_3433_: *mut crate::leanh::LeanObject,
    mut v___y_3434_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3435_ = l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__3(
        v___x_3430_,
        v___f_3431_,
        v_a_3432_,
        v_x_3433_,
    );
    crate::leanh::lean_dec_ref(v_a_3432_);
    return v_res_3435_;
}
pub unsafe fn l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__4(
    mut v_ctxAsync_3436_: *mut crate::leanh::LeanObject,
    mut v_a_3437_: *mut crate::leanh::LeanObject,
    mut v___f_3438_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: u8 = 0;
    let mut v___x_3443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3440_ =
        crate::leanh::lean_apply_2(v_ctxAsync_3436_, v_a_3437_, crate::leanh::lean_box(0));
    v___x_3441_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3442_ = 0;
    v___x_3443_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3441_,
        v___x_3442_,
        v___x_3440_,
        v___f_3438_,
    );
    return v___x_3443_;
}
pub unsafe fn l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__4___boxed(
    mut v_ctxAsync_3444_: *mut crate::leanh::LeanObject,
    mut v_a_3445_: *mut crate::leanh::LeanObject,
    mut v___f_3446_: *mut crate::leanh::LeanObject,
    mut v___y_3447_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3448_ = l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__4(
        v_ctxAsync_3444_,
        v_a_3445_,
        v___f_3446_,
    );
    return v_res_3448_;
}
pub unsafe fn l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__1(
    mut v_a_3449_: *mut crate::leanh::LeanObject,
    mut v___x_3450_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_3451_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3453_ = l_Std_CancellationContext_cancel(v_a_3449_, v___x_3450_);
    v___x_3454_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3454_, 0, v___x_3453_);
    v___x_3455_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3455_, 0, v___x_3454_);
    return v___x_3455_;
}
pub unsafe fn l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__1___boxed(
    mut v_a_3456_: *mut crate::leanh::LeanObject,
    mut v___x_3457_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_3458_: *mut crate::leanh::LeanObject,
    mut v___y_3459_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3460_ = l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__1(
        v_a_3456_,
        v___x_3457_,
        v_a_x3f_3458_,
    );
    crate::leanh::lean_dec(v_a_x3f_3458_);
    return v_res_3460_;
}
pub unsafe fn l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__5(
    mut v_ctxAsync_3461_: *mut crate::leanh::LeanObject,
    mut v___f_3462_: *mut crate::leanh::LeanObject,
    mut v___f_3463_: *mut crate::leanh::LeanObject,
    mut v_prio_3464_: *mut crate::leanh::LeanObject,
    mut v___f_3465_: *mut crate::leanh::LeanObject,
    mut v_x_3466_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3471_: u8 = 0;
    let mut v___x_3473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3476_: u8 = 0;
    let mut v_a_3477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3480_: u8 = 0;
    let mut v___f_3481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3488_: u8 = 0;
    let mut v___x_3489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3494_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3466_) == 0 {
                    crate::leanh::lean_dec_ref(v___f_3465_);
                    crate::leanh::lean_dec(v_prio_3464_);
                    crate::leanh::lean_dec(v___f_3463_);
                    crate::leanh::lean_dec_ref(v___f_3462_);
                    crate::leanh::lean_dec_ref(v_ctxAsync_3461_);
                    v_a_3468_ = crate::leanh::lean_ctor_get(v_x_3466_, 0);
                    v_isSharedCheck_3476_ = (!crate::leanh::lean_is_exclusive(v_x_3466_)) as u8;
                    if v_isSharedCheck_3476_ == 0 {
                        v___x_3470_ = v_x_3466_;
                        v_isShared_3471_ = v_isSharedCheck_3476_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3468_);
                        crate::leanh::lean_dec(v_x_3466_);
                        v___x_3470_ = crate::leanh::lean_box(0);
                        v_isShared_3471_ = v_isSharedCheck_3476_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3477_ = crate::leanh::lean_ctor_get(v_x_3466_, 0);
                    v_isSharedCheck_3494_ = (!crate::leanh::lean_is_exclusive(v_x_3466_)) as u8;
                    if v_isSharedCheck_3494_ == 0 {
                        v___x_3479_ = v_x_3466_;
                        v_isShared_3480_ = v_isSharedCheck_3494_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3477_);
                        crate::leanh::lean_dec(v_x_3466_);
                        v___x_3479_ = crate::leanh::lean_box(0);
                        v_isShared_3480_ = v_isSharedCheck_3494_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3471_ == 0 {
                    v___x_3473_ = v___x_3470_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3475_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3475_, 0, v_a_3468_);
                    v___x_3473_ = v_reuseFailAlloc_3475_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3474_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3474_, 0, v___x_3473_);
                return v___x_3474_;
            }
            3 => {
                crate::leanh::lean_inc(v_a_3477_);
                v___f_3481_ = crate::leanh::lean_alloc_closure(
                    l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__4___boxed
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_3481_, 0, v_ctxAsync_3461_);
                crate::leanh::lean_closure_set(v___f_3481_, 1, v_a_3477_);
                crate::leanh::lean_closure_set(v___f_3481_, 2, v___f_3462_);
                v___x_3482_ = crate::leanh::lean_box(2);
                v___f_3483_ = crate::leanh::lean_alloc_closure(
                    l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__1___boxed
                        as *mut core::ffi::c_void,
                    4,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_3483_, 0, v_a_3477_);
                crate::leanh::lean_closure_set(v___f_3483_, 1, v___x_3482_);
                v___f_3484_ = crate::leanh::lean_alloc_closure(
                    l_Std_Async_ContextAsync_concurrently___redArg___lam__5___boxed
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_3484_, 0, v___f_3481_);
                crate::leanh::lean_closure_set(v___f_3484_, 1, v___f_3483_);
                crate::leanh::lean_closure_set(v___f_3484_, 2, v___f_3463_);
                v___x_3485_ = crate::leanh::lean_alloc_closure(
                    l_Std_Async_BaseAsync_toRawBaseIO___boxed as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___x_3485_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_3485_, 1, v___f_3484_);
                v___x_3486_ = lean_io_as_task(v___x_3485_, v_prio_3464_);
                v___x_3487_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3488_ = 1;
                v___x_3489_ = lean_task_bind(v___x_3486_, v___f_3465_, v___x_3487_, v___x_3488_);
                if v_isShared_3480_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3479_, 0, v___x_3489_);
                    v___x_3491_ = v___x_3479_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3493_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3493_, 0, v___x_3489_);
                    v___x_3491_ = v_reuseFailAlloc_3493_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3492_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3492_, 0, v___x_3491_);
                return v___x_3492_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__5___boxed(
    mut v_ctxAsync_3495_: *mut crate::leanh::LeanObject,
    mut v___f_3496_: *mut crate::leanh::LeanObject,
    mut v___f_3497_: *mut crate::leanh::LeanObject,
    mut v_prio_3498_: *mut crate::leanh::LeanObject,
    mut v___f_3499_: *mut crate::leanh::LeanObject,
    mut v_x_3500_: *mut crate::leanh::LeanObject,
    mut v___y_3501_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3502_ = l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__5(
        v_ctxAsync_3495_,
        v___f_3496_,
        v___f_3497_,
        v_prio_3498_,
        v___f_3499_,
        v_x_3500_,
    );
    return v_res_3502_;
}
pub unsafe fn l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__2(
    mut v_a_3503_: *mut crate::leanh::LeanObject,
    mut v___f_3504_: *mut crate::leanh::LeanObject,
    mut v___f_3505_: *mut crate::leanh::LeanObject,
    mut v_prio_3506_: *mut crate::leanh::LeanObject,
    mut v___f_3507_: *mut crate::leanh::LeanObject,
    mut v_ctxAsync_3508_: *mut crate::leanh::LeanObject,
    mut v___y_3509_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: u8 = 0;
    let mut v___x_3517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3511_ = l_Std_CancellationContext_fork(v_a_3503_);
    v___f_3512_ = crate::leanh::lean_alloc_closure(
        l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__5___boxed
            as *mut core::ffi::c_void,
        7,
        5,
    );
    crate::leanh::lean_closure_set(v___f_3512_, 0, v_ctxAsync_3508_);
    crate::leanh::lean_closure_set(v___f_3512_, 1, v___f_3504_);
    crate::leanh::lean_closure_set(v___f_3512_, 2, v___f_3505_);
    crate::leanh::lean_closure_set(v___f_3512_, 3, v_prio_3506_);
    crate::leanh::lean_closure_set(v___f_3512_, 4, v___f_3507_);
    v___x_3513_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3513_, 0, v___x_3511_);
    v___x_3514_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3514_, 0, v___x_3513_);
    v___x_3515_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3516_ = 0;
    v___x_3517_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3515_,
        v___x_3516_,
        v___x_3514_,
        v___f_3512_,
    );
    return v___x_3517_;
}
pub unsafe fn l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__2___boxed(
    mut v_a_3518_: *mut crate::leanh::LeanObject,
    mut v___f_3519_: *mut crate::leanh::LeanObject,
    mut v___f_3520_: *mut crate::leanh::LeanObject,
    mut v_prio_3521_: *mut crate::leanh::LeanObject,
    mut v___f_3522_: *mut crate::leanh::LeanObject,
    mut v_ctxAsync_3523_: *mut crate::leanh::LeanObject,
    mut v___y_3524_: *mut crate::leanh::LeanObject,
    mut v___y_3525_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3526_ = l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__2(
        v_a_3518_,
        v___f_3519_,
        v___f_3520_,
        v_prio_3521_,
        v___f_3522_,
        v_ctxAsync_3523_,
        v___y_3524_,
    );
    crate::leanh::lean_dec_ref(v___y_3524_);
    return v_res_3526_;
}
pub unsafe fn l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__6(
    mut v___f_3527_: *mut crate::leanh::LeanObject,
    mut v_prio_3528_: *mut crate::leanh::LeanObject,
    mut v___f_3529_: *mut crate::leanh::LeanObject,
    mut v_xs_3530_: *mut crate::leanh::LeanObject,
    mut v___x_3531_: *mut crate::leanh::LeanObject,
    mut v_a_3532_: *mut crate::leanh::LeanObject,
    mut v___f_3533_: *mut crate::leanh::LeanObject,
    mut v_x_3534_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3539_: u8 = 0;
    let mut v___x_3541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3544_: u8 = 0;
    let mut v_a_3545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3548_: usize = 0;
    let mut v___x_3549_: usize = 0;
    let mut v___x_4458__overap_3550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3553_: u8 = 0;
    let mut v___x_3554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3534_) == 0 {
                    crate::leanh::lean_dec_ref(v___f_3533_);
                    crate::leanh::lean_dec_ref(v___x_3531_);
                    crate::leanh::lean_dec_ref(v_xs_3530_);
                    crate::leanh::lean_dec_ref(v___f_3529_);
                    crate::leanh::lean_dec(v_prio_3528_);
                    crate::leanh::lean_dec(v___f_3527_);
                    v_a_3536_ = crate::leanh::lean_ctor_get(v_x_3534_, 0);
                    v_isSharedCheck_3544_ = (!crate::leanh::lean_is_exclusive(v_x_3534_)) as u8;
                    if v_isSharedCheck_3544_ == 0 {
                        v___x_3538_ = v_x_3534_;
                        v_isShared_3539_ = v_isSharedCheck_3544_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3536_);
                        crate::leanh::lean_dec(v_x_3534_);
                        v___x_3538_ = crate::leanh::lean_box(0);
                        v_isShared_3539_ = v_isSharedCheck_3544_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3545_ = crate::leanh::lean_ctor_get(v_x_3534_, 0);
                    crate::leanh::lean_inc_n(v_a_3545_, 2);
                    crate::leanh::lean_dec_ref_known(v_x_3534_, 1);
                    v___f_3546_ = crate::leanh::lean_alloc_closure(
                        l_Std_Async_ContextAsync_concurrently___redArg___lam__4___boxed
                            as *mut core::ffi::c_void,
                        3,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_3546_, 0, v_a_3545_);
                    v___f_3547_ = crate::leanh::lean_alloc_closure(
                        l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__2___boxed
                            as *mut core::ffi::c_void,
                        8,
                        5,
                    );
                    crate::leanh::lean_closure_set(v___f_3547_, 0, v_a_3545_);
                    crate::leanh::lean_closure_set(v___f_3547_, 1, v___f_3546_);
                    crate::leanh::lean_closure_set(v___f_3547_, 2, v___f_3527_);
                    crate::leanh::lean_closure_set(v___f_3547_, 3, v_prio_3528_);
                    crate::leanh::lean_closure_set(v___f_3547_, 4, v___f_3529_);
                    v_sz_3548_ = lean_array_size(v_xs_3530_);
                    v___x_3549_ = 0usize;
                    v___x_4458__overap_3550_ =
                        l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v___x_3531_,
                            v___f_3547_,
                            v_sz_3548_,
                            v___x_3549_,
                            v_xs_3530_,
                        );
                    crate::leanh::lean_inc_ref(v_a_3532_);
                    v___x_3551_ = crate::leanh::lean_apply_2(
                        v___x_4458__overap_3550_,
                        v_a_3532_,
                        crate::leanh::lean_box(0),
                    );
                    v___x_3552_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3553_ = 0;
                    v___x_3554_ =
                        l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v___x_3552_,
                            v___x_3553_,
                            v___x_3551_,
                            v___f_3533_,
                        );
                    return v___x_3554_;
                }
            }
            1 => {
                if v_isShared_3539_ == 0 {
                    v___x_3541_ = v___x_3538_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3543_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3543_, 0, v_a_3536_);
                    v___x_3541_ = v_reuseFailAlloc_3543_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3542_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3542_, 0, v___x_3541_);
                return v___x_3542_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__6___boxed(
    mut v___f_3555_: *mut crate::leanh::LeanObject,
    mut v_prio_3556_: *mut crate::leanh::LeanObject,
    mut v___f_3557_: *mut crate::leanh::LeanObject,
    mut v_xs_3558_: *mut crate::leanh::LeanObject,
    mut v___x_3559_: *mut crate::leanh::LeanObject,
    mut v_a_3560_: *mut crate::leanh::LeanObject,
    mut v___f_3561_: *mut crate::leanh::LeanObject,
    mut v_x_3562_: *mut crate::leanh::LeanObject,
    mut v___y_3563_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3564_ = l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__6(
        v___f_3555_,
        v_prio_3556_,
        v___f_3557_,
        v_xs_3558_,
        v___x_3559_,
        v_a_3560_,
        v___f_3561_,
        v_x_3562_,
    );
    crate::leanh::lean_dec_ref(v_a_3560_);
    return v_res_3564_;
}
pub unsafe fn l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__7(
    mut v___f_3565_: *mut crate::leanh::LeanObject,
    mut v_x_3566_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3571_: u8 = 0;
    let mut v___x_3573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3576_: u8 = 0;
    let mut v_a_3577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3580_: u8 = 0;
    let mut v___x_3581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3586_: u8 = 0;
    let mut v___x_3587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3589_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3566_) == 0 {
                    crate::leanh::lean_dec_ref(v___f_3565_);
                    v_a_3568_ = crate::leanh::lean_ctor_get(v_x_3566_, 0);
                    v_isSharedCheck_3576_ = (!crate::leanh::lean_is_exclusive(v_x_3566_)) as u8;
                    if v_isSharedCheck_3576_ == 0 {
                        v___x_3570_ = v_x_3566_;
                        v_isShared_3571_ = v_isSharedCheck_3576_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3568_);
                        crate::leanh::lean_dec(v_x_3566_);
                        v___x_3570_ = crate::leanh::lean_box(0);
                        v_isShared_3571_ = v_isSharedCheck_3576_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3577_ = crate::leanh::lean_ctor_get(v_x_3566_, 0);
                    v_isSharedCheck_3589_ = (!crate::leanh::lean_is_exclusive(v_x_3566_)) as u8;
                    if v_isSharedCheck_3589_ == 0 {
                        v___x_3579_ = v_x_3566_;
                        v_isShared_3580_ = v_isSharedCheck_3589_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3577_);
                        crate::leanh::lean_dec(v_x_3566_);
                        v___x_3579_ = crate::leanh::lean_box(0);
                        v_isShared_3580_ = v_isSharedCheck_3589_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3571_ == 0 {
                    v___x_3573_ = v___x_3570_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3575_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3575_, 0, v_a_3568_);
                    v___x_3573_ = v_reuseFailAlloc_3575_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3574_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3574_, 0, v___x_3573_);
                return v___x_3574_;
            }
            3 => {
                v___x_3581_ = l_Std_CancellationContext_fork(v_a_3577_);
                if v_isShared_3580_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3579_, 0, v___x_3581_);
                    v___x_3583_ = v___x_3579_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3588_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3588_, 0, v___x_3581_);
                    v___x_3583_ = v_reuseFailAlloc_3588_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3584_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3584_, 0, v___x_3583_);
                v___x_3585_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3586_ = 0;
                v___x_3587_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_3585_,
                    v___x_3586_,
                    v___x_3584_,
                    v___f_3565_,
                );
                return v___x_3587_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__7___boxed(
    mut v___f_3590_: *mut crate::leanh::LeanObject,
    mut v_x_3591_: *mut crate::leanh::LeanObject,
    mut v___y_3592_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3593_ =
        l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__7(v___f_3590_, v_x_3591_);
    return v_res_3593_;
}
pub unsafe fn _init_l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3595_ = l_Std_Async_EAsync_instMonad(crate::leanh::lean_box(0));
    return v___x_3595_;
}
pub unsafe fn _init_l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3596_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__1_once),
        _init_l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__1,
    );
    v___x_3597_ = l_ReaderT_instMonad___redArg(v___x_3596_);
    return v___x_3597_;
}
pub unsafe fn l_Std_Async_ContextAsync_concurrentlyAll___redArg(
    mut v_xs_3598_: *mut crate::leanh::LeanObject,
    mut v_prio_3599_: *mut crate::leanh::LeanObject,
    mut v_a_3600_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: u8 = 0;
    let mut v___x_3613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3602_ = l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__0;
    v___f_3603_ = l_Std_Async_ContextAsync_concurrently___redArg___closed__0;
    v___f_3604_ = l_Std_Async_ContextAsync_concurrently___redArg___closed__1;
    v___x_3605_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__2),
        core::ptr::addr_of_mut!(l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__2_once),
        _init_l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__2,
    );
    crate::leanh::lean_inc_ref_n(v_a_3600_, 3);
    v___f_3606_ = crate::leanh::lean_alloc_closure(
        l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__3___boxed
            as *mut core::ffi::c_void,
        5,
        3,
    );
    crate::leanh::lean_closure_set(v___f_3606_, 0, v___x_3605_);
    crate::leanh::lean_closure_set(v___f_3606_, 1, v___f_3602_);
    crate::leanh::lean_closure_set(v___f_3606_, 2, v_a_3600_);
    v___f_3607_ = crate::leanh::lean_alloc_closure(
        l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__6___boxed
            as *mut core::ffi::c_void,
        9,
        7,
    );
    crate::leanh::lean_closure_set(v___f_3607_, 0, v___f_3604_);
    crate::leanh::lean_closure_set(v___f_3607_, 1, v_prio_3599_);
    crate::leanh::lean_closure_set(v___f_3607_, 2, v___f_3603_);
    crate::leanh::lean_closure_set(v___f_3607_, 3, v_xs_3598_);
    crate::leanh::lean_closure_set(v___f_3607_, 4, v___x_3605_);
    crate::leanh::lean_closure_set(v___f_3607_, 5, v_a_3600_);
    crate::leanh::lean_closure_set(v___f_3607_, 6, v___f_3606_);
    v___f_3608_ = crate::leanh::lean_alloc_closure(
        l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__7___boxed
            as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3608_, 0, v___f_3607_);
    v___x_3609_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3609_, 0, v_a_3600_);
    v___x_3610_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3610_, 0, v___x_3609_);
    v___x_3611_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3612_ = 0;
    v___x_3613_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3611_,
        v___x_3612_,
        v___x_3610_,
        v___f_3608_,
    );
    return v___x_3613_;
}
pub unsafe fn l_Std_Async_ContextAsync_concurrentlyAll___redArg___boxed(
    mut v_xs_3614_: *mut crate::leanh::LeanObject,
    mut v_prio_3615_: *mut crate::leanh::LeanObject,
    mut v_a_3616_: *mut crate::leanh::LeanObject,
    mut v_a_3617_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3618_ =
        l_Std_Async_ContextAsync_concurrentlyAll___redArg(v_xs_3614_, v_prio_3615_, v_a_3616_);
    crate::leanh::lean_dec_ref(v_a_3616_);
    return v_res_3618_;
}
pub unsafe fn l_Std_Async_ContextAsync_concurrentlyAll(
    mut v_00_u03b1_3619_: *mut crate::leanh::LeanObject,
    mut v_xs_3620_: *mut crate::leanh::LeanObject,
    mut v_prio_3621_: *mut crate::leanh::LeanObject,
    mut v_a_3622_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: u8 = 0;
    let mut v___x_3635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3624_ = l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__0;
    v___f_3625_ = l_Std_Async_ContextAsync_concurrently___redArg___closed__0;
    v___f_3626_ = l_Std_Async_ContextAsync_concurrently___redArg___closed__1;
    v___x_3627_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__2),
        core::ptr::addr_of_mut!(l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__2_once),
        _init_l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__2,
    );
    crate::leanh::lean_inc_ref_n(v_a_3622_, 3);
    v___f_3628_ = crate::leanh::lean_alloc_closure(
        l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__3___boxed
            as *mut core::ffi::c_void,
        5,
        3,
    );
    crate::leanh::lean_closure_set(v___f_3628_, 0, v___x_3627_);
    crate::leanh::lean_closure_set(v___f_3628_, 1, v___f_3624_);
    crate::leanh::lean_closure_set(v___f_3628_, 2, v_a_3622_);
    v___f_3629_ = crate::leanh::lean_alloc_closure(
        l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__6___boxed
            as *mut core::ffi::c_void,
        9,
        7,
    );
    crate::leanh::lean_closure_set(v___f_3629_, 0, v___f_3626_);
    crate::leanh::lean_closure_set(v___f_3629_, 1, v_prio_3621_);
    crate::leanh::lean_closure_set(v___f_3629_, 2, v___f_3625_);
    crate::leanh::lean_closure_set(v___f_3629_, 3, v_xs_3620_);
    crate::leanh::lean_closure_set(v___f_3629_, 4, v___x_3627_);
    crate::leanh::lean_closure_set(v___f_3629_, 5, v_a_3622_);
    crate::leanh::lean_closure_set(v___f_3629_, 6, v___f_3628_);
    v___f_3630_ = crate::leanh::lean_alloc_closure(
        l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__7___boxed
            as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3630_, 0, v___f_3629_);
    v___x_3631_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3631_, 0, v_a_3622_);
    v___x_3632_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3632_, 0, v___x_3631_);
    v___x_3633_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3634_ = 0;
    v___x_3635_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3633_,
        v___x_3634_,
        v___x_3632_,
        v___f_3630_,
    );
    return v___x_3635_;
}
pub unsafe fn l_Std_Async_ContextAsync_concurrentlyAll___boxed(
    mut v_00_u03b1_3636_: *mut crate::leanh::LeanObject,
    mut v_xs_3637_: *mut crate::leanh::LeanObject,
    mut v_prio_3638_: *mut crate::leanh::LeanObject,
    mut v_a_3639_: *mut crate::leanh::LeanObject,
    mut v_a_3640_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3641_ = l_Std_Async_ContextAsync_concurrentlyAll(
        v_00_u03b1_3636_,
        v_xs_3637_,
        v_prio_3638_,
        v_a_3639_,
    );
    crate::leanh::lean_dec_ref(v_a_3639_);
    return v_res_3641_;
}
pub unsafe fn l_Std_Async_ContextAsync_background___redArg___lam__0(
    mut v_a_3642_: *mut crate::leanh::LeanObject,
    mut v_x_3643_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3648_: u8 = 0;
    let mut v___x_3650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3653_: u8 = 0;
    let mut v___x_3655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3656_: u8 = 0;
    let mut v___x_3657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3663_: u8 = 0;
    let mut v_unused_3664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3643_) == 0 {
                    crate::leanh::lean_dec_ref(v_a_3642_);
                    v_a_3645_ = crate::leanh::lean_ctor_get(v_x_3643_, 0);
                    v_isSharedCheck_3653_ = (!crate::leanh::lean_is_exclusive(v_x_3643_)) as u8;
                    if v_isSharedCheck_3653_ == 0 {
                        v___x_3647_ = v_x_3643_;
                        v_isShared_3648_ = v_isSharedCheck_3653_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3645_);
                        crate::leanh::lean_dec(v_x_3643_);
                        v___x_3647_ = crate::leanh::lean_box(0);
                        v_isShared_3648_ = v_isSharedCheck_3653_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_isSharedCheck_3663_ = (!crate::leanh::lean_is_exclusive(v_x_3643_)) as u8;
                    if v_isSharedCheck_3663_ == 0 {
                        v_unused_3664_ = crate::leanh::lean_ctor_get(v_x_3643_, 0);
                        crate::leanh::lean_dec(v_unused_3664_);
                        v___x_3655_ = v_x_3643_;
                        v_isShared_3656_ = v_isSharedCheck_3663_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_x_3643_);
                        v___x_3655_ = crate::leanh::lean_box(0);
                        v_isShared_3656_ = v_isSharedCheck_3663_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3648_ == 0 {
                    v___x_3650_ = v___x_3647_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3652_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3652_, 0, v_a_3645_);
                    v___x_3650_ = v_reuseFailAlloc_3652_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3651_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3651_, 0, v___x_3650_);
                return v___x_3651_;
            }
            3 => {
                v___x_3657_ = crate::leanh::lean_box(2);
                v___x_3658_ = l_Std_CancellationContext_cancel(v_a_3642_, v___x_3657_);
                if v_isShared_3656_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3655_, 0, v___x_3658_);
                    v___x_3660_ = v___x_3655_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3662_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3662_, 0, v___x_3658_);
                    v___x_3660_ = v_reuseFailAlloc_3662_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3661_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3661_, 0, v___x_3660_);
                return v___x_3661_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_background___redArg___lam__0___boxed(
    mut v_a_3665_: *mut crate::leanh::LeanObject,
    mut v_x_3666_: *mut crate::leanh::LeanObject,
    mut v___y_3667_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3668_ = l_Std_Async_ContextAsync_background___redArg___lam__0(v_a_3665_, v_x_3666_);
    return v_res_3668_;
}
pub unsafe fn l_Std_Async_ContextAsync_background___redArg___lam__1(
    mut v_action_3669_: *mut crate::leanh::LeanObject,
    mut v_a_3670_: *mut crate::leanh::LeanObject,
    mut v___f_3671_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3675_: u8 = 0;
    let mut v___x_3676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3673_ = crate::leanh::lean_apply_2(v_action_3669_, v_a_3670_, crate::leanh::lean_box(0));
    v___x_3674_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3675_ = 0;
    v___x_3676_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3674_,
        v___x_3675_,
        v___x_3673_,
        v___f_3671_,
    );
    return v___x_3676_;
}
pub unsafe fn l_Std_Async_ContextAsync_background___redArg___lam__1___boxed(
    mut v_action_3677_: *mut crate::leanh::LeanObject,
    mut v_a_3678_: *mut crate::leanh::LeanObject,
    mut v___f_3679_: *mut crate::leanh::LeanObject,
    mut v___y_3680_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3681_ = l_Std_Async_ContextAsync_background___redArg___lam__1(
        v_action_3677_,
        v_a_3678_,
        v___f_3679_,
    );
    return v_res_3681_;
}
pub unsafe fn l_Std_Async_ContextAsync_background___redArg___lam__2(
    mut v_action_3686_: *mut crate::leanh::LeanObject,
    mut v_prio_3687_: *mut crate::leanh::LeanObject,
    mut v_x_3688_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3693_: u8 = 0;
    let mut v___x_3695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3698_: u8 = 0;
    let mut v_a_3699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3688_) == 0 {
                    crate::leanh::lean_dec(v_prio_3687_);
                    crate::leanh::lean_dec_ref(v_action_3686_);
                    v_a_3690_ = crate::leanh::lean_ctor_get(v_x_3688_, 0);
                    v_isSharedCheck_3698_ = (!crate::leanh::lean_is_exclusive(v_x_3688_)) as u8;
                    if v_isSharedCheck_3698_ == 0 {
                        v___x_3692_ = v_x_3688_;
                        v_isShared_3693_ = v_isSharedCheck_3698_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3690_);
                        crate::leanh::lean_dec(v_x_3688_);
                        v___x_3692_ = crate::leanh::lean_box(0);
                        v_isShared_3693_ = v_isSharedCheck_3698_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3699_ = crate::leanh::lean_ctor_get(v_x_3688_, 0);
                    crate::leanh::lean_inc_n(v_a_3699_, 2);
                    crate::leanh::lean_dec_ref_known(v_x_3688_, 1);
                    v___f_3700_ = crate::leanh::lean_alloc_closure(
                        l_Std_Async_ContextAsync_background___redArg___lam__0___boxed
                            as *mut core::ffi::c_void,
                        3,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_3700_, 0, v_a_3699_);
                    v___f_3701_ = crate::leanh::lean_alloc_closure(
                        l_Std_Async_ContextAsync_background___redArg___lam__1___boxed
                            as *mut core::ffi::c_void,
                        4,
                        3,
                    );
                    crate::leanh::lean_closure_set(v___f_3701_, 0, v_action_3686_);
                    crate::leanh::lean_closure_set(v___f_3701_, 1, v_a_3699_);
                    crate::leanh::lean_closure_set(v___f_3701_, 2, v___f_3700_);
                    v___x_3702_ = crate::leanh::lean_alloc_closure(
                        l_Std_Async_BaseAsync_toRawBaseIO___boxed as *mut core::ffi::c_void,
                        3,
                        2,
                    );
                    crate::leanh::lean_closure_set(v___x_3702_, 0, crate::leanh::lean_box(0));
                    crate::leanh::lean_closure_set(v___x_3702_, 1, v___f_3701_);
                    v___x_3703_ = lean_io_as_task(v___x_3702_, v_prio_3687_);
                    crate::leanh::lean_dec_ref(v___x_3703_);
                    v___x_3704_ = l_Std_Async_ContextAsync_background___redArg___lam__2___closed__1;
                    return v___x_3704_;
                }
            }
            1 => {
                if v_isShared_3693_ == 0 {
                    v___x_3695_ = v___x_3692_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3697_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3697_, 0, v_a_3690_);
                    v___x_3695_ = v_reuseFailAlloc_3697_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3696_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3696_, 0, v___x_3695_);
                return v___x_3696_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_background___redArg___lam__2___boxed(
    mut v_action_3705_: *mut crate::leanh::LeanObject,
    mut v_prio_3706_: *mut crate::leanh::LeanObject,
    mut v_x_3707_: *mut crate::leanh::LeanObject,
    mut v___y_3708_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3709_ = l_Std_Async_ContextAsync_background___redArg___lam__2(
        v_action_3705_,
        v_prio_3706_,
        v_x_3707_,
    );
    return v_res_3709_;
}
pub unsafe fn l_Std_Async_ContextAsync_background___redArg___lam__3(
    mut v___f_3710_: *mut crate::leanh::LeanObject,
    mut v_x_3711_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3716_: u8 = 0;
    let mut v___x_3718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3721_: u8 = 0;
    let mut v_a_3722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3725_: u8 = 0;
    let mut v___x_3726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3731_: u8 = 0;
    let mut v___x_3732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3734_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3711_) == 0 {
                    crate::leanh::lean_dec_ref(v___f_3710_);
                    v_a_3713_ = crate::leanh::lean_ctor_get(v_x_3711_, 0);
                    v_isSharedCheck_3721_ = (!crate::leanh::lean_is_exclusive(v_x_3711_)) as u8;
                    if v_isSharedCheck_3721_ == 0 {
                        v___x_3715_ = v_x_3711_;
                        v_isShared_3716_ = v_isSharedCheck_3721_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3713_);
                        crate::leanh::lean_dec(v_x_3711_);
                        v___x_3715_ = crate::leanh::lean_box(0);
                        v_isShared_3716_ = v_isSharedCheck_3721_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3722_ = crate::leanh::lean_ctor_get(v_x_3711_, 0);
                    v_isSharedCheck_3734_ = (!crate::leanh::lean_is_exclusive(v_x_3711_)) as u8;
                    if v_isSharedCheck_3734_ == 0 {
                        v___x_3724_ = v_x_3711_;
                        v_isShared_3725_ = v_isSharedCheck_3734_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3722_);
                        crate::leanh::lean_dec(v_x_3711_);
                        v___x_3724_ = crate::leanh::lean_box(0);
                        v_isShared_3725_ = v_isSharedCheck_3734_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3716_ == 0 {
                    v___x_3718_ = v___x_3715_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3720_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3720_, 0, v_a_3713_);
                    v___x_3718_ = v_reuseFailAlloc_3720_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3719_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3719_, 0, v___x_3718_);
                return v___x_3719_;
            }
            3 => {
                v___x_3726_ = l_Std_CancellationContext_fork(v_a_3722_);
                if v_isShared_3725_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3724_, 0, v___x_3726_);
                    v___x_3728_ = v___x_3724_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3733_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3733_, 0, v___x_3726_);
                    v___x_3728_ = v_reuseFailAlloc_3733_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3729_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3729_, 0, v___x_3728_);
                v___x_3730_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3731_ = 0;
                v___x_3732_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_3730_,
                    v___x_3731_,
                    v___x_3729_,
                    v___f_3710_,
                );
                return v___x_3732_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_background___redArg___lam__3___boxed(
    mut v___f_3735_: *mut crate::leanh::LeanObject,
    mut v_x_3736_: *mut crate::leanh::LeanObject,
    mut v___y_3737_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3738_ = l_Std_Async_ContextAsync_background___redArg___lam__3(v___f_3735_, v_x_3736_);
    return v_res_3738_;
}
pub unsafe fn l_Std_Async_ContextAsync_background___redArg(
    mut v_action_3739_: *mut crate::leanh::LeanObject,
    mut v_prio_3740_: *mut crate::leanh::LeanObject,
    mut v_a_3741_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3748_: u8 = 0;
    let mut v___x_3749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3743_ = crate::leanh::lean_alloc_closure(
        l_Std_Async_ContextAsync_background___redArg___lam__2___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3743_, 0, v_action_3739_);
    crate::leanh::lean_closure_set(v___f_3743_, 1, v_prio_3740_);
    v___f_3744_ = crate::leanh::lean_alloc_closure(
        l_Std_Async_ContextAsync_background___redArg___lam__3___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3744_, 0, v___f_3743_);
    crate::leanh::lean_inc_ref(v_a_3741_);
    v___x_3745_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3745_, 0, v_a_3741_);
    v___x_3746_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3746_, 0, v___x_3745_);
    v___x_3747_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3748_ = 0;
    v___x_3749_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3747_,
        v___x_3748_,
        v___x_3746_,
        v___f_3744_,
    );
    return v___x_3749_;
}
pub unsafe fn l_Std_Async_ContextAsync_background___redArg___boxed(
    mut v_action_3750_: *mut crate::leanh::LeanObject,
    mut v_prio_3751_: *mut crate::leanh::LeanObject,
    mut v_a_3752_: *mut crate::leanh::LeanObject,
    mut v_a_3753_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3754_ =
        l_Std_Async_ContextAsync_background___redArg(v_action_3750_, v_prio_3751_, v_a_3752_);
    crate::leanh::lean_dec_ref(v_a_3752_);
    return v_res_3754_;
}
pub unsafe fn l_Std_Async_ContextAsync_background(
    mut v_00_u03b1_3755_: *mut crate::leanh::LeanObject,
    mut v_action_3756_: *mut crate::leanh::LeanObject,
    mut v_prio_3757_: *mut crate::leanh::LeanObject,
    mut v_a_3758_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3765_: u8 = 0;
    let mut v___x_3766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3760_ = crate::leanh::lean_alloc_closure(
        l_Std_Async_ContextAsync_background___redArg___lam__2___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3760_, 0, v_action_3756_);
    crate::leanh::lean_closure_set(v___f_3760_, 1, v_prio_3757_);
    v___f_3761_ = crate::leanh::lean_alloc_closure(
        l_Std_Async_ContextAsync_background___redArg___lam__3___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3761_, 0, v___f_3760_);
    crate::leanh::lean_inc_ref(v_a_3758_);
    v___x_3762_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3762_, 0, v_a_3758_);
    v___x_3763_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3763_, 0, v___x_3762_);
    v___x_3764_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3765_ = 0;
    v___x_3766_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3764_,
        v___x_3765_,
        v___x_3763_,
        v___f_3761_,
    );
    return v___x_3766_;
}
pub unsafe fn l_Std_Async_ContextAsync_background___boxed(
    mut v_00_u03b1_3767_: *mut crate::leanh::LeanObject,
    mut v_action_3768_: *mut crate::leanh::LeanObject,
    mut v_prio_3769_: *mut crate::leanh::LeanObject,
    mut v_a_3770_: *mut crate::leanh::LeanObject,
    mut v_a_3771_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3772_ = l_Std_Async_ContextAsync_background(
        v_00_u03b1_3767_,
        v_action_3768_,
        v_prio_3769_,
        v_a_3770_,
    );
    crate::leanh::lean_dec_ref(v_a_3770_);
    return v_res_3772_;
}
pub unsafe fn l_Std_Async_ContextAsync_disown___redArg___lam__0(
    mut v_action_3773_: *mut crate::leanh::LeanObject,
    mut v_a_3774_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3776_ = crate::leanh::lean_apply_2(v_action_3773_, v_a_3774_, crate::leanh::lean_box(0));
    return v___x_3776_;
}
pub unsafe fn l_Std_Async_ContextAsync_disown___redArg___lam__0___boxed(
    mut v_action_3777_: *mut crate::leanh::LeanObject,
    mut v_a_3778_: *mut crate::leanh::LeanObject,
    mut v___y_3779_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3780_ = l_Std_Async_ContextAsync_disown___redArg___lam__0(v_action_3777_, v_a_3778_);
    return v_res_3780_;
}
pub unsafe fn l_Std_Async_ContextAsync_disown___redArg___lam__1(
    mut v_action_3781_: *mut crate::leanh::LeanObject,
    mut v_prio_3782_: *mut crate::leanh::LeanObject,
    mut v_x_3783_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3788_: u8 = 0;
    let mut v___x_3790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3793_: u8 = 0;
    let mut v_a_3794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3783_) == 0 {
                    crate::leanh::lean_dec(v_prio_3782_);
                    crate::leanh::lean_dec_ref(v_action_3781_);
                    v_a_3785_ = crate::leanh::lean_ctor_get(v_x_3783_, 0);
                    v_isSharedCheck_3793_ = (!crate::leanh::lean_is_exclusive(v_x_3783_)) as u8;
                    if v_isSharedCheck_3793_ == 0 {
                        v___x_3787_ = v_x_3783_;
                        v_isShared_3788_ = v_isSharedCheck_3793_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3785_);
                        crate::leanh::lean_dec(v_x_3783_);
                        v___x_3787_ = crate::leanh::lean_box(0);
                        v_isShared_3788_ = v_isSharedCheck_3793_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3794_ = crate::leanh::lean_ctor_get(v_x_3783_, 0);
                    crate::leanh::lean_inc(v_a_3794_);
                    crate::leanh::lean_dec_ref_known(v_x_3783_, 1);
                    v___f_3795_ = crate::leanh::lean_alloc_closure(
                        l_Std_Async_ContextAsync_disown___redArg___lam__0___boxed
                            as *mut core::ffi::c_void,
                        3,
                        2,
                    );
                    crate::leanh::lean_closure_set(v___f_3795_, 0, v_action_3781_);
                    crate::leanh::lean_closure_set(v___f_3795_, 1, v_a_3794_);
                    v___x_3796_ = crate::leanh::lean_alloc_closure(
                        l_Std_Async_BaseAsync_toRawBaseIO___boxed as *mut core::ffi::c_void,
                        3,
                        2,
                    );
                    crate::leanh::lean_closure_set(v___x_3796_, 0, crate::leanh::lean_box(0));
                    crate::leanh::lean_closure_set(v___x_3796_, 1, v___f_3795_);
                    v___x_3797_ = lean_io_as_task(v___x_3796_, v_prio_3782_);
                    crate::leanh::lean_dec_ref(v___x_3797_);
                    v___x_3798_ = l_Std_Async_ContextAsync_background___redArg___lam__2___closed__1;
                    return v___x_3798_;
                }
            }
            1 => {
                if v_isShared_3788_ == 0 {
                    v___x_3790_ = v___x_3787_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3792_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3792_, 0, v_a_3785_);
                    v___x_3790_ = v_reuseFailAlloc_3792_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3791_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3791_, 0, v___x_3790_);
                return v___x_3791_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_disown___redArg___lam__1___boxed(
    mut v_action_3799_: *mut crate::leanh::LeanObject,
    mut v_prio_3800_: *mut crate::leanh::LeanObject,
    mut v_x_3801_: *mut crate::leanh::LeanObject,
    mut v___y_3802_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3803_ =
        l_Std_Async_ContextAsync_disown___redArg___lam__1(v_action_3799_, v_prio_3800_, v_x_3801_);
    return v_res_3803_;
}
pub unsafe fn l_Std_Async_ContextAsync_disown___redArg(
    mut v_action_3804_: *mut crate::leanh::LeanObject,
    mut v_prio_3805_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3812_: u8 = 0;
    let mut v___x_3813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3807_ = l_Std_CancellationContext_new();
    v___f_3808_ = crate::leanh::lean_alloc_closure(
        l_Std_Async_ContextAsync_disown___redArg___lam__1___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3808_, 0, v_action_3804_);
    crate::leanh::lean_closure_set(v___f_3808_, 1, v_prio_3805_);
    v___x_3809_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3809_, 0, v___x_3807_);
    v___x_3810_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3810_, 0, v___x_3809_);
    v___x_3811_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3812_ = 0;
    v___x_3813_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3811_,
        v___x_3812_,
        v___x_3810_,
        v___f_3808_,
    );
    return v___x_3813_;
}
pub unsafe fn l_Std_Async_ContextAsync_disown___redArg___boxed(
    mut v_action_3814_: *mut crate::leanh::LeanObject,
    mut v_prio_3815_: *mut crate::leanh::LeanObject,
    mut v_a_3816_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3817_ = l_Std_Async_ContextAsync_disown___redArg(v_action_3814_, v_prio_3815_);
    return v_res_3817_;
}
pub unsafe fn l_Std_Async_ContextAsync_disown(
    mut v_00_u03b1_3818_: *mut crate::leanh::LeanObject,
    mut v_action_3819_: *mut crate::leanh::LeanObject,
    mut v_prio_3820_: *mut crate::leanh::LeanObject,
    mut v_a_3821_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3828_: u8 = 0;
    let mut v___x_3829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3823_ = l_Std_CancellationContext_new();
    v___f_3824_ = crate::leanh::lean_alloc_closure(
        l_Std_Async_ContextAsync_disown___redArg___lam__1___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3824_, 0, v_action_3819_);
    crate::leanh::lean_closure_set(v___f_3824_, 1, v_prio_3820_);
    v___x_3825_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3825_, 0, v___x_3823_);
    v___x_3826_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3826_, 0, v___x_3825_);
    v___x_3827_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3828_ = 0;
    v___x_3829_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3827_,
        v___x_3828_,
        v___x_3826_,
        v___f_3824_,
    );
    return v___x_3829_;
}
pub unsafe fn l_Std_Async_ContextAsync_disown___boxed(
    mut v_00_u03b1_3830_: *mut crate::leanh::LeanObject,
    mut v_action_3831_: *mut crate::leanh::LeanObject,
    mut v_prio_3832_: *mut crate::leanh::LeanObject,
    mut v_a_3833_: *mut crate::leanh::LeanObject,
    mut v_a_3834_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3835_ =
        l_Std_Async_ContextAsync_disown(v_00_u03b1_3830_, v_action_3831_, v_prio_3832_, v_a_3833_);
    crate::leanh::lean_dec_ref(v_a_3833_);
    return v_res_3835_;
}
pub unsafe fn l_Std_Async_ContextAsync_raceAll___redArg___lam__0(
    mut v_a_3836_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3837_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3837_, 0, v_a_3836_);
    return v___x_3837_;
}
pub unsafe fn l_Std_Async_ContextAsync_raceAll___redArg___lam__2(
    mut v_a_3838_: *mut crate::leanh::LeanObject,
    mut v_x_3839_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3844_: u8 = 0;
    let mut v___x_3846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3849_: u8 = 0;
    let mut v___x_3850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3839_) == 0 {
                    crate::leanh::lean_dec_ref(v_a_3838_);
                    v_a_3841_ = crate::leanh::lean_ctor_get(v_x_3839_, 0);
                    v_isSharedCheck_3849_ = (!crate::leanh::lean_is_exclusive(v_x_3839_)) as u8;
                    if v_isSharedCheck_3849_ == 0 {
                        v___x_3843_ = v_x_3839_;
                        v_isShared_3844_ = v_isSharedCheck_3849_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3841_);
                        crate::leanh::lean_dec(v_x_3839_);
                        v___x_3843_ = crate::leanh::lean_box(0);
                        v_isShared_3844_ = v_isSharedCheck_3849_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v_x_3839_, 1);
                    v___x_3850_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3850_, 0, v_a_3838_);
                    return v___x_3850_;
                }
            }
            1 => {
                if v_isShared_3844_ == 0 {
                    v___x_3846_ = v___x_3843_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3848_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3848_, 0, v_a_3841_);
                    v___x_3846_ = v_reuseFailAlloc_3848_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3847_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3847_, 0, v___x_3846_);
                return v___x_3847_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_raceAll___redArg___lam__2___boxed(
    mut v_a_3851_: *mut crate::leanh::LeanObject,
    mut v_x_3852_: *mut crate::leanh::LeanObject,
    mut v___y_3853_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3854_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__2(v_a_3851_, v_x_3852_);
    return v_res_3854_;
}
pub unsafe fn l_Std_Async_ContextAsync_raceAll___redArg___lam__1(
    mut v_a_3855_: *mut crate::leanh::LeanObject,
    mut v_x_3856_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3861_: u8 = 0;
    let mut v___x_3863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3866_: u8 = 0;
    let mut v_a_3867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3870_: u8 = 0;
    let mut v___x_3871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: u8 = 0;
    let mut v___x_3879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3881_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3856_) == 0 {
                    crate::leanh::lean_dec_ref(v_a_3855_);
                    v_a_3858_ = crate::leanh::lean_ctor_get(v_x_3856_, 0);
                    v_isSharedCheck_3866_ = (!crate::leanh::lean_is_exclusive(v_x_3856_)) as u8;
                    if v_isSharedCheck_3866_ == 0 {
                        v___x_3860_ = v_x_3856_;
                        v_isShared_3861_ = v_isSharedCheck_3866_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3858_);
                        crate::leanh::lean_dec(v_x_3856_);
                        v___x_3860_ = crate::leanh::lean_box(0);
                        v_isShared_3861_ = v_isSharedCheck_3866_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3867_ = crate::leanh::lean_ctor_get(v_x_3856_, 0);
                    v_isSharedCheck_3881_ = (!crate::leanh::lean_is_exclusive(v_x_3856_)) as u8;
                    if v_isSharedCheck_3881_ == 0 {
                        v___x_3869_ = v_x_3856_;
                        v_isShared_3870_ = v_isSharedCheck_3881_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3867_);
                        crate::leanh::lean_dec(v_x_3856_);
                        v___x_3869_ = crate::leanh::lean_box(0);
                        v_isShared_3870_ = v_isSharedCheck_3881_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3861_ == 0 {
                    v___x_3863_ = v___x_3860_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3865_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3865_, 0, v_a_3858_);
                    v___x_3863_ = v_reuseFailAlloc_3865_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3864_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3864_, 0, v___x_3863_);
                return v___x_3864_;
            }
            3 => {
                v___x_3871_ = crate::leanh::lean_box(2);
                v___x_3872_ = l_Std_CancellationContext_cancel(v_a_3855_, v___x_3871_);
                v___f_3873_ = crate::leanh::lean_alloc_closure(
                    l_Std_Async_ContextAsync_raceAll___redArg___lam__2___boxed
                        as *mut core::ffi::c_void,
                    3,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3873_, 0, v_a_3867_);
                if v_isShared_3870_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3869_, 0, v___x_3872_);
                    v___x_3875_ = v___x_3869_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3880_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3880_, 0, v___x_3872_);
                    v___x_3875_ = v_reuseFailAlloc_3880_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3876_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3876_, 0, v___x_3875_);
                v___x_3877_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3878_ = 0;
                v___x_3879_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_3877_,
                    v___x_3878_,
                    v___x_3876_,
                    v___f_3873_,
                );
                return v___x_3879_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_raceAll___redArg___lam__1___boxed(
    mut v_a_3882_: *mut crate::leanh::LeanObject,
    mut v_x_3883_: *mut crate::leanh::LeanObject,
    mut v___y_3884_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3885_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__1(v_a_3882_, v_x_3883_);
    return v_res_3885_;
}
pub unsafe fn l_Std_Async_ContextAsync_raceAll___redArg___lam__3(
    mut v_a_3886_: *mut crate::leanh::LeanObject,
    mut v_x_3887_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3892_: u8 = 0;
    let mut v___x_3894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3898_: u8 = 0;
    let mut v___x_3899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3887_) == 0 {
                    v_a_3889_ = crate::leanh::lean_ctor_get(v_x_3887_, 0);
                    v_isSharedCheck_3898_ = (!crate::leanh::lean_is_exclusive(v_x_3887_)) as u8;
                    if v_isSharedCheck_3898_ == 0 {
                        v___x_3891_ = v_x_3887_;
                        v_isShared_3892_ = v_isSharedCheck_3898_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3889_);
                        crate::leanh::lean_dec(v_x_3887_);
                        v___x_3891_ = crate::leanh::lean_box(0);
                        v_isShared_3892_ = v_isSharedCheck_3898_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_3899_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3899_, 0, v_x_3887_);
                    return v___x_3899_;
                }
            }
            1 => {
                if v_isShared_3892_ == 0 {
                    v___x_3894_ = v___x_3891_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3897_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3897_, 0, v_a_3889_);
                    v___x_3894_ = v_reuseFailAlloc_3897_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3895_ = lean_io_promise_resolve(v___x_3894_, v_a_3886_);
                v___x_3896_ = l_Std_Async_ContextAsync_background___redArg___lam__2___closed__1;
                return v___x_3896_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_raceAll___redArg___lam__3___boxed(
    mut v_a_3900_: *mut crate::leanh::LeanObject,
    mut v_x_3901_: *mut crate::leanh::LeanObject,
    mut v___y_3902_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3903_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__3(v_a_3900_, v_x_3901_);
    crate::leanh::lean_dec(v_a_3900_);
    return v_res_3903_;
}
pub unsafe fn l_Std_Async_ContextAsync_raceAll___redArg___lam__4(
    mut v_a_3904_: *mut crate::leanh::LeanObject,
    mut v_x_3905_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3910_: u8 = 0;
    let mut v___x_3912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3915_: u8 = 0;
    let mut v___x_3916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3905_) == 0 {
                    v_a_3907_ = crate::leanh::lean_ctor_get(v_x_3905_, 0);
                    v_isSharedCheck_3915_ = (!crate::leanh::lean_is_exclusive(v_x_3905_)) as u8;
                    if v_isSharedCheck_3915_ == 0 {
                        v___x_3909_ = v_x_3905_;
                        v_isShared_3910_ = v_isSharedCheck_3915_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3907_);
                        crate::leanh::lean_dec(v_x_3905_);
                        v___x_3909_ = crate::leanh::lean_box(0);
                        v_isShared_3910_ = v_isSharedCheck_3915_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_3916_ = lean_io_promise_resolve(v_x_3905_, v_a_3904_);
                    v___x_3917_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3917_, 0, v___x_3916_);
                    v___x_3918_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3918_, 0, v___x_3917_);
                    return v___x_3918_;
                }
            }
            1 => {
                if v_isShared_3910_ == 0 {
                    v___x_3912_ = v___x_3909_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3914_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3914_, 0, v_a_3907_);
                    v___x_3912_ = v_reuseFailAlloc_3914_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3913_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3913_, 0, v___x_3912_);
                return v___x_3913_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_raceAll___redArg___lam__4___boxed(
    mut v_a_3919_: *mut crate::leanh::LeanObject,
    mut v_x_3920_: *mut crate::leanh::LeanObject,
    mut v___y_3921_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3922_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__4(v_a_3919_, v_x_3920_);
    crate::leanh::lean_dec(v_a_3919_);
    return v_res_3922_;
}
pub unsafe fn l_Std_Async_ContextAsync_raceAll___redArg___lam__5(
    mut v_a_3923_: *mut crate::leanh::LeanObject,
    mut v_x_3924_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3929_: u8 = 0;
    let mut v___x_3930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3936_: u8 = 0;
    let mut v_unused_3937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3924_) == 0 {
                    crate::leanh::lean_dec_ref(v_a_3923_);
                    v___x_3926_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3926_, 0, v_x_3924_);
                    return v___x_3926_;
                } else {
                    v_isSharedCheck_3936_ = (!crate::leanh::lean_is_exclusive(v_x_3924_)) as u8;
                    if v_isSharedCheck_3936_ == 0 {
                        v_unused_3937_ = crate::leanh::lean_ctor_get(v_x_3924_, 0);
                        crate::leanh::lean_dec(v_unused_3937_);
                        v___x_3928_ = v_x_3924_;
                        v_isShared_3929_ = v_isSharedCheck_3936_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_x_3924_);
                        v___x_3928_ = crate::leanh::lean_box(0);
                        v_isShared_3929_ = v_isSharedCheck_3936_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3930_ = crate::leanh::lean_box(2);
                v___x_3931_ = l_Std_CancellationContext_cancel(v_a_3923_, v___x_3930_);
                if v_isShared_3929_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3928_, 0, v___x_3931_);
                    v___x_3933_ = v___x_3928_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3935_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3935_, 0, v___x_3931_);
                    v___x_3933_ = v_reuseFailAlloc_3935_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3934_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3934_, 0, v___x_3933_);
                return v___x_3934_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_raceAll___redArg___lam__5___boxed(
    mut v_a_3938_: *mut crate::leanh::LeanObject,
    mut v_x_3939_: *mut crate::leanh::LeanObject,
    mut v___y_3940_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3941_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__5(v_a_3938_, v_x_3939_);
    return v_res_3941_;
}
pub unsafe fn l_Std_Async_ContextAsync_raceAll___redArg___lam__6(
    mut v_a_3942_: *mut crate::leanh::LeanObject,
    mut v___x_3943_: *mut crate::leanh::LeanObject,
    mut v___f_3944_: *mut crate::leanh::LeanObject,
    mut v___f_3945_: *mut crate::leanh::LeanObject,
    mut v___f_3946_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3949_: u8 = 0;
    let mut v___x_3950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3948_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3948_, 0, v_a_3942_);
    v___x_3949_ = 0;
    crate::leanh::lean_inc_n(v___x_3943_, 2);
    v___x_3950_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3943_,
        v___x_3949_,
        v___x_3948_,
        v___f_3944_,
    );
    v___x_3951_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3943_,
        v___x_3949_,
        v___x_3950_,
        v___f_3945_,
    );
    v___x_3952_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3943_,
        v___x_3949_,
        v___x_3951_,
        v___f_3946_,
    );
    return v___x_3952_;
}
pub unsafe fn l_Std_Async_ContextAsync_raceAll___redArg___lam__6___boxed(
    mut v_a_3953_: *mut crate::leanh::LeanObject,
    mut v___x_3954_: *mut crate::leanh::LeanObject,
    mut v___f_3955_: *mut crate::leanh::LeanObject,
    mut v___f_3956_: *mut crate::leanh::LeanObject,
    mut v___f_3957_: *mut crate::leanh::LeanObject,
    mut v___y_3958_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3959_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__6(
        v_a_3953_,
        v___x_3954_,
        v___f_3955_,
        v___f_3956_,
        v___f_3957_,
    );
    return v_res_3959_;
}
pub unsafe fn l_Std_Async_ContextAsync_raceAll___redArg___lam__7(
    mut v_a_3960_: *mut crate::leanh::LeanObject,
    mut v___x_3961_: *mut crate::leanh::LeanObject,
    mut v___f_3962_: *mut crate::leanh::LeanObject,
    mut v___f_3963_: *mut crate::leanh::LeanObject,
    mut v_x_3964_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3969_: u8 = 0;
    let mut v___x_3971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3974_: u8 = 0;
    let mut v_a_3975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3964_) == 0 {
                    crate::leanh::lean_dec_ref(v___f_3963_);
                    crate::leanh::lean_dec_ref(v___f_3962_);
                    crate::leanh::lean_dec(v___x_3961_);
                    crate::leanh::lean_dec_ref(v_a_3960_);
                    v_a_3966_ = crate::leanh::lean_ctor_get(v_x_3964_, 0);
                    v_isSharedCheck_3974_ = (!crate::leanh::lean_is_exclusive(v_x_3964_)) as u8;
                    if v_isSharedCheck_3974_ == 0 {
                        v___x_3968_ = v_x_3964_;
                        v_isShared_3969_ = v_isSharedCheck_3974_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3966_);
                        crate::leanh::lean_dec(v_x_3964_);
                        v___x_3968_ = crate::leanh::lean_box(0);
                        v_isShared_3969_ = v_isSharedCheck_3974_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3975_ = crate::leanh::lean_ctor_get(v_x_3964_, 0);
                    crate::leanh::lean_inc(v_a_3975_);
                    crate::leanh::lean_dec_ref_known(v_x_3964_, 1);
                    v___f_3976_ = crate::leanh::lean_alloc_closure(
                        l_Std_Async_ContextAsync_raceAll___redArg___lam__5___boxed
                            as *mut core::ffi::c_void,
                        3,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_3976_, 0, v_a_3975_);
                    crate::leanh::lean_inc(v___x_3961_);
                    v___f_3977_ = crate::leanh::lean_alloc_closure(
                        l_Std_Async_ContextAsync_raceAll___redArg___lam__6___boxed
                            as *mut core::ffi::c_void,
                        6,
                        5,
                    );
                    crate::leanh::lean_closure_set(v___f_3977_, 0, v_a_3960_);
                    crate::leanh::lean_closure_set(v___f_3977_, 1, v___x_3961_);
                    crate::leanh::lean_closure_set(v___f_3977_, 2, v___f_3962_);
                    crate::leanh::lean_closure_set(v___f_3977_, 3, v___f_3963_);
                    crate::leanh::lean_closure_set(v___f_3977_, 4, v___f_3976_);
                    v___x_3978_ = crate::leanh::lean_alloc_closure(
                        l_Std_Async_BaseAsync_toRawBaseIO___boxed as *mut core::ffi::c_void,
                        3,
                        2,
                    );
                    crate::leanh::lean_closure_set(v___x_3978_, 0, crate::leanh::lean_box(0));
                    crate::leanh::lean_closure_set(v___x_3978_, 1, v___f_3977_);
                    v___x_3979_ = lean_io_as_task(v___x_3978_, v___x_3961_);
                    crate::leanh::lean_dec_ref(v___x_3979_);
                    v___x_3980_ = l_Std_Async_ContextAsync_background___redArg___lam__2___closed__1;
                    return v___x_3980_;
                }
            }
            1 => {
                if v_isShared_3969_ == 0 {
                    v___x_3971_ = v___x_3968_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3973_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3973_, 0, v_a_3966_);
                    v___x_3971_ = v_reuseFailAlloc_3973_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3972_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3972_, 0, v___x_3971_);
                return v___x_3972_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_raceAll___redArg___lam__7___boxed(
    mut v_a_3981_: *mut crate::leanh::LeanObject,
    mut v___x_3982_: *mut crate::leanh::LeanObject,
    mut v___f_3983_: *mut crate::leanh::LeanObject,
    mut v___f_3984_: *mut crate::leanh::LeanObject,
    mut v_x_3985_: *mut crate::leanh::LeanObject,
    mut v___y_3986_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3987_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__7(
        v_a_3981_,
        v___x_3982_,
        v___f_3983_,
        v___f_3984_,
        v_x_3985_,
    );
    return v_res_3987_;
}
pub unsafe fn l_Std_Async_ContextAsync_raceAll___redArg___lam__8(
    mut v___x_3988_: *mut crate::leanh::LeanObject,
    mut v___f_3989_: *mut crate::leanh::LeanObject,
    mut v_x_3990_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3995_: u8 = 0;
    let mut v___x_3997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4000_: u8 = 0;
    let mut v_a_4001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4004_: u8 = 0;
    let mut v___x_4005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4009_: u8 = 0;
    let mut v___x_4010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4012_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3990_) == 0 {
                    crate::leanh::lean_dec_ref(v___f_3989_);
                    crate::leanh::lean_dec(v___x_3988_);
                    v_a_3992_ = crate::leanh::lean_ctor_get(v_x_3990_, 0);
                    v_isSharedCheck_4000_ = (!crate::leanh::lean_is_exclusive(v_x_3990_)) as u8;
                    if v_isSharedCheck_4000_ == 0 {
                        v___x_3994_ = v_x_3990_;
                        v_isShared_3995_ = v_isSharedCheck_4000_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3992_);
                        crate::leanh::lean_dec(v_x_3990_);
                        v___x_3994_ = crate::leanh::lean_box(0);
                        v_isShared_3995_ = v_isSharedCheck_4000_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4001_ = crate::leanh::lean_ctor_get(v_x_3990_, 0);
                    v_isSharedCheck_4012_ = (!crate::leanh::lean_is_exclusive(v_x_3990_)) as u8;
                    if v_isSharedCheck_4012_ == 0 {
                        v___x_4003_ = v_x_3990_;
                        v_isShared_4004_ = v_isSharedCheck_4012_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4001_);
                        crate::leanh::lean_dec(v_x_3990_);
                        v___x_4003_ = crate::leanh::lean_box(0);
                        v_isShared_4004_ = v_isSharedCheck_4012_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3995_ == 0 {
                    v___x_3997_ = v___x_3994_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3999_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3999_, 0, v_a_3992_);
                    v___x_3997_ = v_reuseFailAlloc_3999_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3998_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3998_, 0, v___x_3997_);
                return v___x_3998_;
            }
            3 => {
                v___x_4005_ = l_Std_CancellationContext_fork(v_a_4001_);
                if v_isShared_4004_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4003_, 0, v___x_4005_);
                    v___x_4007_ = v___x_4003_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4011_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4011_, 0, v___x_4005_);
                    v___x_4007_ = v_reuseFailAlloc_4011_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4008_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4008_, 0, v___x_4007_);
                v___x_4009_ = 0;
                v___x_4010_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_3988_,
                    v___x_4009_,
                    v___x_4008_,
                    v___f_3989_,
                );
                return v___x_4010_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_raceAll___redArg___lam__8___boxed(
    mut v___x_4013_: *mut crate::leanh::LeanObject,
    mut v___f_4014_: *mut crate::leanh::LeanObject,
    mut v_x_4015_: *mut crate::leanh::LeanObject,
    mut v___y_4016_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4017_ =
        l_Std_Async_ContextAsync_raceAll___redArg___lam__8(v___x_4013_, v___f_4014_, v_x_4015_);
    return v_res_4017_;
}
pub unsafe fn l_Std_Async_ContextAsync_raceAll___redArg___lam__9(
    mut v___f_4018_: *mut crate::leanh::LeanObject,
    mut v___f_4019_: *mut crate::leanh::LeanObject,
    mut v___y_4020_: *mut crate::leanh::LeanObject,
    mut v_x_4021_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_4023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4026_: u8 = 0;
    let mut v___x_4028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4031_: u8 = 0;
    let mut v_a_4032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4035_: u8 = 0;
    let mut v___x_4036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4042_: u8 = 0;
    let mut v___x_4043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4045_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4021_) == 0 {
                    crate::leanh::lean_dec_ref(v___f_4019_);
                    crate::leanh::lean_dec_ref(v___f_4018_);
                    v_a_4023_ = crate::leanh::lean_ctor_get(v_x_4021_, 0);
                    v_isSharedCheck_4031_ = (!crate::leanh::lean_is_exclusive(v_x_4021_)) as u8;
                    if v_isSharedCheck_4031_ == 0 {
                        v___x_4025_ = v_x_4021_;
                        v_isShared_4026_ = v_isSharedCheck_4031_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4023_);
                        crate::leanh::lean_dec(v_x_4021_);
                        v___x_4025_ = crate::leanh::lean_box(0);
                        v_isShared_4026_ = v_isSharedCheck_4031_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4032_ = crate::leanh::lean_ctor_get(v_x_4021_, 0);
                    v_isSharedCheck_4045_ = (!crate::leanh::lean_is_exclusive(v_x_4021_)) as u8;
                    if v_isSharedCheck_4045_ == 0 {
                        v___x_4034_ = v_x_4021_;
                        v_isShared_4035_ = v_isSharedCheck_4045_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4032_);
                        crate::leanh::lean_dec(v_x_4021_);
                        v___x_4034_ = crate::leanh::lean_box(0);
                        v_isShared_4035_ = v_isSharedCheck_4045_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4026_ == 0 {
                    v___x_4028_ = v___x_4025_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4030_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4030_, 0, v_a_4023_);
                    v___x_4028_ = v_reuseFailAlloc_4030_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4029_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4029_, 0, v___x_4028_);
                return v___x_4029_;
            }
            3 => {
                v___x_4036_ = crate::leanh::lean_unsigned_to_nat(0);
                v___f_4037_ = crate::leanh::lean_alloc_closure(
                    l_Std_Async_ContextAsync_raceAll___redArg___lam__7___boxed
                        as *mut core::ffi::c_void,
                    6,
                    4,
                );
                crate::leanh::lean_closure_set(v___f_4037_, 0, v_a_4032_);
                crate::leanh::lean_closure_set(v___f_4037_, 1, v___x_4036_);
                crate::leanh::lean_closure_set(v___f_4037_, 2, v___f_4018_);
                crate::leanh::lean_closure_set(v___f_4037_, 3, v___f_4019_);
                v___f_4038_ = crate::leanh::lean_alloc_closure(
                    l_Std_Async_ContextAsync_raceAll___redArg___lam__8___boxed
                        as *mut core::ffi::c_void,
                    4,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_4038_, 0, v___x_4036_);
                crate::leanh::lean_closure_set(v___f_4038_, 1, v___f_4037_);
                crate::leanh::lean_inc_ref(v___y_4020_);
                if v_isShared_4035_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4034_, 0, v___y_4020_);
                    v___x_4040_ = v___x_4034_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4044_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4044_, 0, v___y_4020_);
                    v___x_4040_ = v_reuseFailAlloc_4044_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4041_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4041_, 0, v___x_4040_);
                v___x_4042_ = 0;
                v___x_4043_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_4036_,
                    v___x_4042_,
                    v___x_4041_,
                    v___f_4038_,
                );
                return v___x_4043_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_raceAll___redArg___lam__9___boxed(
    mut v___f_4046_: *mut crate::leanh::LeanObject,
    mut v___f_4047_: *mut crate::leanh::LeanObject,
    mut v___y_4048_: *mut crate::leanh::LeanObject,
    mut v_x_4049_: *mut crate::leanh::LeanObject,
    mut v___y_4050_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4051_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__9(
        v___f_4046_,
        v___f_4047_,
        v___y_4048_,
        v_x_4049_,
    );
    crate::leanh::lean_dec_ref(v___y_4048_);
    return v_res_4051_;
}
pub unsafe fn l_Std_Async_ContextAsync_raceAll___redArg___lam__10(
    mut v_x_4052_: *mut crate::leanh::LeanObject,
    mut v_a_4053_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4055_ = crate::leanh::lean_apply_2(v_x_4052_, v_a_4053_, crate::leanh::lean_box(0));
    return v___x_4055_;
}
pub unsafe fn l_Std_Async_ContextAsync_raceAll___redArg___lam__10___boxed(
    mut v_x_4056_: *mut crate::leanh::LeanObject,
    mut v_a_4057_: *mut crate::leanh::LeanObject,
    mut v___y_4058_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4059_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__10(v_x_4056_, v_a_4057_);
    return v_res_4059_;
}
pub unsafe fn l_Std_Async_ContextAsync_raceAll___redArg___lam__11(
    mut v_x_4060_: *mut crate::leanh::LeanObject,
    mut v_prio_4061_: *mut crate::leanh::LeanObject,
    mut v___f_4062_: *mut crate::leanh::LeanObject,
    mut v___f_4063_: *mut crate::leanh::LeanObject,
    mut v_x_4064_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_4066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4069_: u8 = 0;
    let mut v___x_4071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4074_: u8 = 0;
    let mut v_a_4075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4078_: u8 = 0;
    let mut v___f_4079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4083_: u8 = 0;
    let mut v___x_4084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4088_: u8 = 0;
    let mut v___x_4089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4091_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4064_) == 0 {
                    crate::leanh::lean_dec_ref(v___f_4063_);
                    crate::leanh::lean_dec_ref(v___f_4062_);
                    crate::leanh::lean_dec(v_prio_4061_);
                    crate::leanh::lean_dec_ref(v_x_4060_);
                    v_a_4066_ = crate::leanh::lean_ctor_get(v_x_4064_, 0);
                    v_isSharedCheck_4074_ = (!crate::leanh::lean_is_exclusive(v_x_4064_)) as u8;
                    if v_isSharedCheck_4074_ == 0 {
                        v___x_4068_ = v_x_4064_;
                        v_isShared_4069_ = v_isSharedCheck_4074_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4066_);
                        crate::leanh::lean_dec(v_x_4064_);
                        v___x_4068_ = crate::leanh::lean_box(0);
                        v_isShared_4069_ = v_isSharedCheck_4074_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4075_ = crate::leanh::lean_ctor_get(v_x_4064_, 0);
                    v_isSharedCheck_4091_ = (!crate::leanh::lean_is_exclusive(v_x_4064_)) as u8;
                    if v_isSharedCheck_4091_ == 0 {
                        v___x_4077_ = v_x_4064_;
                        v_isShared_4078_ = v_isSharedCheck_4091_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4075_);
                        crate::leanh::lean_dec(v_x_4064_);
                        v___x_4077_ = crate::leanh::lean_box(0);
                        v_isShared_4078_ = v_isSharedCheck_4091_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4069_ == 0 {
                    v___x_4071_ = v___x_4068_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4073_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4073_, 0, v_a_4066_);
                    v___x_4071_ = v_reuseFailAlloc_4073_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4072_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4072_, 0, v___x_4071_);
                return v___x_4072_;
            }
            3 => {
                v___f_4079_ = crate::leanh::lean_alloc_closure(
                    l_Std_Async_ContextAsync_raceAll___redArg___lam__10___boxed
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_4079_, 0, v_x_4060_);
                crate::leanh::lean_closure_set(v___f_4079_, 1, v_a_4075_);
                v___x_4080_ = crate::leanh::lean_alloc_closure(
                    l_Std_Async_BaseAsync_toRawBaseIO___boxed as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___x_4080_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_4080_, 1, v___f_4079_);
                v___x_4081_ = lean_io_as_task(v___x_4080_, v_prio_4061_);
                v___x_4082_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4083_ = 1;
                v___x_4084_ = lean_task_bind(v___x_4081_, v___f_4062_, v___x_4082_, v___x_4083_);
                if v_isShared_4078_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4077_, 0, v___x_4084_);
                    v___x_4086_ = v___x_4077_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4090_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4090_, 0, v___x_4084_);
                    v___x_4086_ = v_reuseFailAlloc_4090_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4087_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4087_, 0, v___x_4086_);
                v___x_4088_ = 0;
                v___x_4089_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_4082_,
                    v___x_4088_,
                    v___x_4087_,
                    v___f_4063_,
                );
                return v___x_4089_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_raceAll___redArg___lam__11___boxed(
    mut v_x_4092_: *mut crate::leanh::LeanObject,
    mut v_prio_4093_: *mut crate::leanh::LeanObject,
    mut v___f_4094_: *mut crate::leanh::LeanObject,
    mut v___f_4095_: *mut crate::leanh::LeanObject,
    mut v_x_4096_: *mut crate::leanh::LeanObject,
    mut v___y_4097_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4098_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__11(
        v_x_4092_,
        v_prio_4093_,
        v___f_4094_,
        v___f_4095_,
        v_x_4096_,
    );
    return v_res_4098_;
}
pub unsafe fn l_Std_Async_ContextAsync_raceAll___redArg___lam__12(
    mut v_a_4099_: *mut crate::leanh::LeanObject,
    mut v___f_4100_: *mut crate::leanh::LeanObject,
    mut v___f_4101_: *mut crate::leanh::LeanObject,
    mut v_prio_4102_: *mut crate::leanh::LeanObject,
    mut v___f_4103_: *mut crate::leanh::LeanObject,
    mut v_x_4104_: *mut crate::leanh::LeanObject,
    mut v___y_4105_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4113_: u8 = 0;
    let mut v___x_4114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4107_ = l_Std_CancellationContext_fork(v_a_4099_);
    crate::leanh::lean_inc_ref(v___y_4105_);
    v___f_4108_ = crate::leanh::lean_alloc_closure(
        l_Std_Async_ContextAsync_raceAll___redArg___lam__9___boxed as *mut core::ffi::c_void,
        5,
        3,
    );
    crate::leanh::lean_closure_set(v___f_4108_, 0, v___f_4100_);
    crate::leanh::lean_closure_set(v___f_4108_, 1, v___f_4101_);
    crate::leanh::lean_closure_set(v___f_4108_, 2, v___y_4105_);
    v___f_4109_ = crate::leanh::lean_alloc_closure(
        l_Std_Async_ContextAsync_raceAll___redArg___lam__11___boxed as *mut core::ffi::c_void,
        6,
        4,
    );
    crate::leanh::lean_closure_set(v___f_4109_, 0, v_x_4104_);
    crate::leanh::lean_closure_set(v___f_4109_, 1, v_prio_4102_);
    crate::leanh::lean_closure_set(v___f_4109_, 2, v___f_4103_);
    crate::leanh::lean_closure_set(v___f_4109_, 3, v___f_4108_);
    v___x_4110_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4110_, 0, v___x_4107_);
    v___x_4111_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4111_, 0, v___x_4110_);
    v___x_4112_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4113_ = 0;
    v___x_4114_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4112_,
        v___x_4113_,
        v___x_4111_,
        v___f_4109_,
    );
    return v___x_4114_;
}
pub unsafe fn l_Std_Async_ContextAsync_raceAll___redArg___lam__12___boxed(
    mut v_a_4115_: *mut crate::leanh::LeanObject,
    mut v___f_4116_: *mut crate::leanh::LeanObject,
    mut v___f_4117_: *mut crate::leanh::LeanObject,
    mut v_prio_4118_: *mut crate::leanh::LeanObject,
    mut v___f_4119_: *mut crate::leanh::LeanObject,
    mut v_x_4120_: *mut crate::leanh::LeanObject,
    mut v___y_4121_: *mut crate::leanh::LeanObject,
    mut v___y_4122_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4123_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__12(
        v_a_4115_,
        v___f_4116_,
        v___f_4117_,
        v_prio_4118_,
        v___f_4119_,
        v_x_4120_,
        v___y_4121_,
    );
    crate::leanh::lean_dec_ref(v___y_4121_);
    return v_res_4123_;
}
pub unsafe fn l_Std_Async_ContextAsync_raceAll___redArg___lam__13(
    mut v_a_4124_: *mut crate::leanh::LeanObject,
    mut v___f_4125_: *mut crate::leanh::LeanObject,
    mut v___f_4126_: *mut crate::leanh::LeanObject,
    mut v_x_4127_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_4129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4132_: u8 = 0;
    let mut v___x_4134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4137_: u8 = 0;
    let mut v___x_4138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4140_: u8 = 0;
    let mut v___x_4141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4127_) == 0 {
                    crate::leanh::lean_dec_ref(v___f_4126_);
                    crate::leanh::lean_dec_ref(v___f_4125_);
                    v_a_4129_ = crate::leanh::lean_ctor_get(v_x_4127_, 0);
                    v_isSharedCheck_4137_ = (!crate::leanh::lean_is_exclusive(v_x_4127_)) as u8;
                    if v_isSharedCheck_4137_ == 0 {
                        v___x_4131_ = v_x_4127_;
                        v_isShared_4132_ = v_isSharedCheck_4137_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4129_);
                        crate::leanh::lean_dec(v_x_4127_);
                        v___x_4131_ = crate::leanh::lean_box(0);
                        v_isShared_4132_ = v_isSharedCheck_4137_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v_x_4127_, 1);
                    v___x_4138_ = l_IO_Promise_result_x21___redArg(v_a_4124_);
                    v___x_4139_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4140_ = 0;
                    v___x_4141_ = lean_task_map(v___f_4125_, v___x_4138_, v___x_4139_, v___x_4140_);
                    v___x_4142_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4142_, 0, v___x_4141_);
                    v___x_4143_ =
                        l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v___x_4139_,
                            v___x_4140_,
                            v___x_4142_,
                            v___f_4126_,
                        );
                    return v___x_4143_;
                }
            }
            1 => {
                if v_isShared_4132_ == 0 {
                    v___x_4134_ = v___x_4131_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4136_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4136_, 0, v_a_4129_);
                    v___x_4134_ = v_reuseFailAlloc_4136_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4135_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4135_, 0, v___x_4134_);
                return v___x_4135_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_raceAll___redArg___lam__13___boxed(
    mut v_a_4144_: *mut crate::leanh::LeanObject,
    mut v___f_4145_: *mut crate::leanh::LeanObject,
    mut v___f_4146_: *mut crate::leanh::LeanObject,
    mut v_x_4147_: *mut crate::leanh::LeanObject,
    mut v___y_4148_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4149_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__13(
        v_a_4144_,
        v___f_4145_,
        v___f_4146_,
        v_x_4147_,
    );
    crate::leanh::lean_dec(v_a_4144_);
    return v_res_4149_;
}
pub unsafe fn l_Std_Async_ContextAsync_raceAll___redArg___lam__14(
    mut v_a_4150_: *mut crate::leanh::LeanObject,
    mut v_prio_4151_: *mut crate::leanh::LeanObject,
    mut v___f_4152_: *mut crate::leanh::LeanObject,
    mut v_inst_4153_: *mut crate::leanh::LeanObject,
    mut v_xs_4154_: *mut crate::leanh::LeanObject,
    mut v_a_4155_: *mut crate::leanh::LeanObject,
    mut v___f_4156_: *mut crate::leanh::LeanObject,
    mut v___f_4157_: *mut crate::leanh::LeanObject,
    mut v_x_4158_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_4160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4163_: u8 = 0;
    let mut v___x_4165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4168_: u8 = 0;
    let mut v_a_4169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4176_: u8 = 0;
    let mut v___x_4177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4158_) == 0 {
                    crate::leanh::lean_dec_ref(v___f_4157_);
                    crate::leanh::lean_dec_ref(v___f_4156_);
                    crate::leanh::lean_dec(v_xs_4154_);
                    crate::leanh::lean_dec_ref(v_inst_4153_);
                    crate::leanh::lean_dec_ref(v___f_4152_);
                    crate::leanh::lean_dec(v_prio_4151_);
                    crate::leanh::lean_dec_ref(v_a_4150_);
                    v_a_4160_ = crate::leanh::lean_ctor_get(v_x_4158_, 0);
                    v_isSharedCheck_4168_ = (!crate::leanh::lean_is_exclusive(v_x_4158_)) as u8;
                    if v_isSharedCheck_4168_ == 0 {
                        v___x_4162_ = v_x_4158_;
                        v_isShared_4163_ = v_isSharedCheck_4168_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4160_);
                        crate::leanh::lean_dec(v_x_4158_);
                        v___x_4162_ = crate::leanh::lean_box(0);
                        v_isShared_4163_ = v_isSharedCheck_4168_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4169_ = crate::leanh::lean_ctor_get(v_x_4158_, 0);
                    crate::leanh::lean_inc_n(v_a_4169_, 3);
                    crate::leanh::lean_dec_ref_known(v_x_4158_, 1);
                    v___f_4170_ = crate::leanh::lean_alloc_closure(
                        l_Std_Async_ContextAsync_raceAll___redArg___lam__3___boxed
                            as *mut core::ffi::c_void,
                        3,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_4170_, 0, v_a_4169_);
                    v___f_4171_ = crate::leanh::lean_alloc_closure(
                        l_Std_Async_ContextAsync_raceAll___redArg___lam__4___boxed
                            as *mut core::ffi::c_void,
                        3,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_4171_, 0, v_a_4169_);
                    v___f_4172_ = crate::leanh::lean_alloc_closure(
                        l_Std_Async_ContextAsync_raceAll___redArg___lam__12___boxed
                            as *mut core::ffi::c_void,
                        8,
                        5,
                    );
                    crate::leanh::lean_closure_set(v___f_4172_, 0, v_a_4150_);
                    crate::leanh::lean_closure_set(v___f_4172_, 1, v___f_4171_);
                    crate::leanh::lean_closure_set(v___f_4172_, 2, v___f_4170_);
                    crate::leanh::lean_closure_set(v___f_4172_, 3, v_prio_4151_);
                    crate::leanh::lean_closure_set(v___f_4172_, 4, v___f_4152_);
                    crate::leanh::lean_inc_ref(v_a_4155_);
                    v___x_4173_ = crate::leanh::lean_apply_4(
                        v_inst_4153_,
                        v_xs_4154_,
                        v___f_4172_,
                        v_a_4155_,
                        crate::leanh::lean_box(0),
                    );
                    v___f_4174_ = crate::leanh::lean_alloc_closure(
                        l_Std_Async_ContextAsync_raceAll___redArg___lam__13___boxed
                            as *mut core::ffi::c_void,
                        5,
                        3,
                    );
                    crate::leanh::lean_closure_set(v___f_4174_, 0, v_a_4169_);
                    crate::leanh::lean_closure_set(v___f_4174_, 1, v___f_4156_);
                    crate::leanh::lean_closure_set(v___f_4174_, 2, v___f_4157_);
                    v___x_4175_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4176_ = 0;
                    v___x_4177_ =
                        l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v___x_4175_,
                            v___x_4176_,
                            v___x_4173_,
                            v___f_4174_,
                        );
                    return v___x_4177_;
                }
            }
            1 => {
                if v_isShared_4163_ == 0 {
                    v___x_4165_ = v___x_4162_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4167_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4167_, 0, v_a_4160_);
                    v___x_4165_ = v_reuseFailAlloc_4167_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4166_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4166_, 0, v___x_4165_);
                return v___x_4166_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_raceAll___redArg___lam__14___boxed(
    mut v_a_4178_: *mut crate::leanh::LeanObject,
    mut v_prio_4179_: *mut crate::leanh::LeanObject,
    mut v___f_4180_: *mut crate::leanh::LeanObject,
    mut v_inst_4181_: *mut crate::leanh::LeanObject,
    mut v_xs_4182_: *mut crate::leanh::LeanObject,
    mut v_a_4183_: *mut crate::leanh::LeanObject,
    mut v___f_4184_: *mut crate::leanh::LeanObject,
    mut v___f_4185_: *mut crate::leanh::LeanObject,
    mut v_x_4186_: *mut crate::leanh::LeanObject,
    mut v___y_4187_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4188_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__14(
        v_a_4178_,
        v_prio_4179_,
        v___f_4180_,
        v_inst_4181_,
        v_xs_4182_,
        v_a_4183_,
        v___f_4184_,
        v___f_4185_,
        v_x_4186_,
    );
    crate::leanh::lean_dec_ref(v_a_4183_);
    return v_res_4188_;
}
pub unsafe fn l_Std_Async_ContextAsync_raceAll___redArg___lam__15(
    mut v_prio_4189_: *mut crate::leanh::LeanObject,
    mut v___f_4190_: *mut crate::leanh::LeanObject,
    mut v_inst_4191_: *mut crate::leanh::LeanObject,
    mut v_xs_4192_: *mut crate::leanh::LeanObject,
    mut v_a_4193_: *mut crate::leanh::LeanObject,
    mut v___f_4194_: *mut crate::leanh::LeanObject,
    mut v_x_4195_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_4197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4200_: u8 = 0;
    let mut v___x_4202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4205_: u8 = 0;
    let mut v_a_4206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4209_: u8 = 0;
    let mut v___x_4210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4217_: u8 = 0;
    let mut v___x_4218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4220_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4195_) == 0 {
                    crate::leanh::lean_dec_ref(v___f_4194_);
                    crate::leanh::lean_dec(v_xs_4192_);
                    crate::leanh::lean_dec_ref(v_inst_4191_);
                    crate::leanh::lean_dec_ref(v___f_4190_);
                    crate::leanh::lean_dec(v_prio_4189_);
                    v_a_4197_ = crate::leanh::lean_ctor_get(v_x_4195_, 0);
                    v_isSharedCheck_4205_ = (!crate::leanh::lean_is_exclusive(v_x_4195_)) as u8;
                    if v_isSharedCheck_4205_ == 0 {
                        v___x_4199_ = v_x_4195_;
                        v_isShared_4200_ = v_isSharedCheck_4205_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4197_);
                        crate::leanh::lean_dec(v_x_4195_);
                        v___x_4199_ = crate::leanh::lean_box(0);
                        v_isShared_4200_ = v_isSharedCheck_4205_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4206_ = crate::leanh::lean_ctor_get(v_x_4195_, 0);
                    v_isSharedCheck_4220_ = (!crate::leanh::lean_is_exclusive(v_x_4195_)) as u8;
                    if v_isSharedCheck_4220_ == 0 {
                        v___x_4208_ = v_x_4195_;
                        v_isShared_4209_ = v_isSharedCheck_4220_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4206_);
                        crate::leanh::lean_dec(v_x_4195_);
                        v___x_4208_ = crate::leanh::lean_box(0);
                        v_isShared_4209_ = v_isSharedCheck_4220_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4200_ == 0 {
                    v___x_4202_ = v___x_4199_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4204_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4204_, 0, v_a_4197_);
                    v___x_4202_ = v_reuseFailAlloc_4204_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4203_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4203_, 0, v___x_4202_);
                return v___x_4203_;
            }
            3 => {
                v___x_4210_ = lean_io_promise_new();
                crate::leanh::lean_inc(v_a_4206_);
                v___f_4211_ = crate::leanh::lean_alloc_closure(
                    l_Std_Async_ContextAsync_raceAll___redArg___lam__1___boxed
                        as *mut core::ffi::c_void,
                    3,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4211_, 0, v_a_4206_);
                crate::leanh::lean_inc_ref(v_a_4193_);
                v___f_4212_ = crate::leanh::lean_alloc_closure(
                    l_Std_Async_ContextAsync_raceAll___redArg___lam__14___boxed
                        as *mut core::ffi::c_void,
                    10,
                    8,
                );
                crate::leanh::lean_closure_set(v___f_4212_, 0, v_a_4206_);
                crate::leanh::lean_closure_set(v___f_4212_, 1, v_prio_4189_);
                crate::leanh::lean_closure_set(v___f_4212_, 2, v___f_4190_);
                crate::leanh::lean_closure_set(v___f_4212_, 3, v_inst_4191_);
                crate::leanh::lean_closure_set(v___f_4212_, 4, v_xs_4192_);
                crate::leanh::lean_closure_set(v___f_4212_, 5, v_a_4193_);
                crate::leanh::lean_closure_set(v___f_4212_, 6, v___f_4194_);
                crate::leanh::lean_closure_set(v___f_4212_, 7, v___f_4211_);
                if v_isShared_4209_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4208_, 0, v___x_4210_);
                    v___x_4214_ = v___x_4208_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4219_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4219_, 0, v___x_4210_);
                    v___x_4214_ = v_reuseFailAlloc_4219_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4215_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4215_, 0, v___x_4214_);
                v___x_4216_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4217_ = 0;
                v___x_4218_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_4216_,
                    v___x_4217_,
                    v___x_4215_,
                    v___f_4212_,
                );
                return v___x_4218_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_raceAll___redArg___lam__15___boxed(
    mut v_prio_4221_: *mut crate::leanh::LeanObject,
    mut v___f_4222_: *mut crate::leanh::LeanObject,
    mut v_inst_4223_: *mut crate::leanh::LeanObject,
    mut v_xs_4224_: *mut crate::leanh::LeanObject,
    mut v_a_4225_: *mut crate::leanh::LeanObject,
    mut v___f_4226_: *mut crate::leanh::LeanObject,
    mut v_x_4227_: *mut crate::leanh::LeanObject,
    mut v___y_4228_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4229_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__15(
        v_prio_4221_,
        v___f_4222_,
        v_inst_4223_,
        v_xs_4224_,
        v_a_4225_,
        v___f_4226_,
        v_x_4227_,
    );
    crate::leanh::lean_dec_ref(v_a_4225_);
    return v_res_4229_;
}
pub unsafe fn l_Std_Async_ContextAsync_raceAll___redArg(
    mut v_inst_4231_: *mut crate::leanh::LeanObject,
    mut v_xs_4232_: *mut crate::leanh::LeanObject,
    mut v_prio_4233_: *mut crate::leanh::LeanObject,
    mut v_a_4234_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4242_: u8 = 0;
    let mut v___x_4243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4236_ = l_Std_Async_ContextAsync_raceAll___redArg___closed__0;
    v___f_4237_ = l_Std_Async_ContextAsync_concurrently___redArg___closed__0;
    crate::leanh::lean_inc_ref_n(v_a_4234_, 2);
    v___f_4238_ = crate::leanh::lean_alloc_closure(
        l_Std_Async_ContextAsync_raceAll___redArg___lam__15___boxed as *mut core::ffi::c_void,
        8,
        6,
    );
    crate::leanh::lean_closure_set(v___f_4238_, 0, v_prio_4233_);
    crate::leanh::lean_closure_set(v___f_4238_, 1, v___f_4237_);
    crate::leanh::lean_closure_set(v___f_4238_, 2, v_inst_4231_);
    crate::leanh::lean_closure_set(v___f_4238_, 3, v_xs_4232_);
    crate::leanh::lean_closure_set(v___f_4238_, 4, v_a_4234_);
    crate::leanh::lean_closure_set(v___f_4238_, 5, v___f_4236_);
    v___x_4239_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4239_, 0, v_a_4234_);
    v___x_4240_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4240_, 0, v___x_4239_);
    v___x_4241_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4242_ = 0;
    v___x_4243_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4241_,
        v___x_4242_,
        v___x_4240_,
        v___f_4238_,
    );
    return v___x_4243_;
}
pub unsafe fn l_Std_Async_ContextAsync_raceAll___redArg___boxed(
    mut v_inst_4244_: *mut crate::leanh::LeanObject,
    mut v_xs_4245_: *mut crate::leanh::LeanObject,
    mut v_prio_4246_: *mut crate::leanh::LeanObject,
    mut v_a_4247_: *mut crate::leanh::LeanObject,
    mut v_a_4248_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4249_ = l_Std_Async_ContextAsync_raceAll___redArg(
        v_inst_4244_,
        v_xs_4245_,
        v_prio_4246_,
        v_a_4247_,
    );
    crate::leanh::lean_dec_ref(v_a_4247_);
    return v_res_4249_;
}
pub unsafe fn l_Std_Async_ContextAsync_raceAll(
    mut v_c_4250_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_4251_: *mut crate::leanh::LeanObject,
    mut v_inst_4252_: *mut crate::leanh::LeanObject,
    mut v_xs_4253_: *mut crate::leanh::LeanObject,
    mut v_prio_4254_: *mut crate::leanh::LeanObject,
    mut v_a_4255_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4257_ = l_Std_Async_ContextAsync_raceAll___redArg(
        v_inst_4252_,
        v_xs_4253_,
        v_prio_4254_,
        v_a_4255_,
    );
    return v___x_4257_;
}
pub unsafe fn l_Std_Async_ContextAsync_raceAll___boxed(
    mut v_c_4258_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_4259_: *mut crate::leanh::LeanObject,
    mut v_inst_4260_: *mut crate::leanh::LeanObject,
    mut v_xs_4261_: *mut crate::leanh::LeanObject,
    mut v_prio_4262_: *mut crate::leanh::LeanObject,
    mut v_a_4263_: *mut crate::leanh::LeanObject,
    mut v_a_4264_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4265_ = l_Std_Async_ContextAsync_raceAll(
        v_c_4258_,
        v_00_u03b1_4259_,
        v_inst_4260_,
        v_xs_4261_,
        v_prio_4262_,
        v_a_4263_,
    );
    crate::leanh::lean_dec_ref(v_a_4263_);
    return v_res_4265_;
}
pub unsafe fn l_Std_Async_ContextAsync_async___redArg___lam__3(
    mut v___x_4266_: *mut crate::leanh::LeanObject,
    mut v___f_4267_: *mut crate::leanh::LeanObject,
    mut v___f_4268_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4271_: u8 = 0;
    let mut v___x_4272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4280_: u8 = 0;
    let mut v___x_4282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4284_: u8 = 0;
    let mut v_a_4285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4288_: u8 = 0;
    let mut v_fst_4289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4293_: u8 = 0;
    let mut v_a_4294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4297_: u8 = 0;
    let mut v___x_4298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4303_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4270_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4271_ = 0;
                v___x_4272_ = l_Std_Async_EAsync_tryFinally_x27___redArg(
                    v___x_4266_,
                    v___f_4267_,
                    v___x_4270_,
                    v___x_4271_,
                );
                if crate::leanh::lean_obj_tag(v___x_4272_) == 0 {
                    crate::leanh::lean_dec(v___f_4268_);
                    v_a_4276_ = crate::leanh::lean_ctor_get(v___x_4272_, 0);
                    crate::leanh::lean_inc(v_a_4276_);
                    crate::leanh::lean_dec_ref_known(v___x_4272_, 1);
                    if crate::leanh::lean_obj_tag(v_a_4276_) == 0 {
                        v_a_4277_ = crate::leanh::lean_ctor_get(v_a_4276_, 0);
                        v_isSharedCheck_4284_ = (!crate::leanh::lean_is_exclusive(v_a_4276_)) as u8;
                        if v_isSharedCheck_4284_ == 0 {
                            v___x_4279_ = v_a_4276_;
                            v_isShared_4280_ = v_isSharedCheck_4284_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4277_);
                            crate::leanh::lean_dec(v_a_4276_);
                            v___x_4279_ = crate::leanh::lean_box(0);
                            v_isShared_4280_ = v_isSharedCheck_4284_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_a_4285_ = crate::leanh::lean_ctor_get(v_a_4276_, 0);
                        v_isSharedCheck_4293_ = (!crate::leanh::lean_is_exclusive(v_a_4276_)) as u8;
                        if v_isSharedCheck_4293_ == 0 {
                            v___x_4287_ = v_a_4276_;
                            v_isShared_4288_ = v_isSharedCheck_4293_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4285_);
                            crate::leanh::lean_dec(v_a_4276_);
                            v___x_4287_ = crate::leanh::lean_box(0);
                            v_isShared_4288_ = v_isSharedCheck_4293_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_a_4294_ = crate::leanh::lean_ctor_get(v___x_4272_, 0);
                    v_isSharedCheck_4303_ = (!crate::leanh::lean_is_exclusive(v___x_4272_)) as u8;
                    if v_isSharedCheck_4303_ == 0 {
                        v___x_4296_ = v___x_4272_;
                        v_isShared_4297_ = v_isSharedCheck_4303_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4294_);
                        crate::leanh::lean_dec(v___x_4272_);
                        v___x_4296_ = crate::leanh::lean_box(0);
                        v_isShared_4297_ = v_isSharedCheck_4303_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4275_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4275_, 0, v___y_4274_);
                return v___x_4275_;
            }
            2 => {
                if v_isShared_4280_ == 0 {
                    v___x_4282_ = v___x_4279_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4283_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4283_, 0, v_a_4277_);
                    v___x_4282_ = v_reuseFailAlloc_4283_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___y_4274_ = v___x_4282_;
                state = 1;
                continue;
            }
            4 => {
                v_fst_4289_ = crate::leanh::lean_ctor_get(v_a_4285_, 0);
                crate::leanh::lean_inc(v_fst_4289_);
                crate::leanh::lean_dec(v_a_4285_);
                if v_isShared_4288_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4287_, 0, v_fst_4289_);
                    v___x_4291_ = v___x_4287_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4292_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4292_, 0, v_fst_4289_);
                    v___x_4291_ = v_reuseFailAlloc_4292_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___y_4274_ = v___x_4291_;
                state = 1;
                continue;
            }
            6 => {
                v___x_4298_ =
                    crate::leanh::lean_alloc_closure(l_Except_map as *mut core::ffi::c_void, 5, 4);
                crate::leanh::lean_closure_set(v___x_4298_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_4298_, 1, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_4298_, 2, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_4298_, 3, v___f_4268_);
                v___x_4299_ = lean_task_map(v___x_4298_, v_a_4294_, v___x_4270_, v___x_4271_);
                if v_isShared_4297_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4296_, 0, v___x_4299_);
                    v___x_4301_ = v___x_4296_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4302_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4302_, 0, v___x_4299_);
                    v___x_4301_ = v_reuseFailAlloc_4302_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4301_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_async___redArg___lam__3___boxed(
    mut v___x_4304_: *mut crate::leanh::LeanObject,
    mut v___f_4305_: *mut crate::leanh::LeanObject,
    mut v___f_4306_: *mut crate::leanh::LeanObject,
    mut v___y_4307_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4308_ =
        l_Std_Async_ContextAsync_async___redArg___lam__3(v___x_4304_, v___f_4305_, v___f_4306_);
    return v_res_4308_;
}
pub unsafe fn l_Std_Async_ContextAsync_async___redArg___lam__0(
    mut v_x_4309_: *mut crate::leanh::LeanObject,
    mut v___f_4310_: *mut crate::leanh::LeanObject,
    mut v_prio_4311_: *mut crate::leanh::LeanObject,
    mut v___f_4312_: *mut crate::leanh::LeanObject,
    mut v_x_4313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_4315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4318_: u8 = 0;
    let mut v___x_4320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4323_: u8 = 0;
    let mut v_a_4324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4327_: u8 = 0;
    let mut v___x_4328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: u8 = 0;
    let mut v___x_4336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4341_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4313_) == 0 {
                    crate::leanh::lean_dec_ref(v___f_4312_);
                    crate::leanh::lean_dec(v_prio_4311_);
                    crate::leanh::lean_dec(v___f_4310_);
                    crate::leanh::lean_dec_ref(v_x_4309_);
                    v_a_4315_ = crate::leanh::lean_ctor_get(v_x_4313_, 0);
                    v_isSharedCheck_4323_ = (!crate::leanh::lean_is_exclusive(v_x_4313_)) as u8;
                    if v_isSharedCheck_4323_ == 0 {
                        v___x_4317_ = v_x_4313_;
                        v_isShared_4318_ = v_isSharedCheck_4323_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4315_);
                        crate::leanh::lean_dec(v_x_4313_);
                        v___x_4317_ = crate::leanh::lean_box(0);
                        v_isShared_4318_ = v_isSharedCheck_4323_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4324_ = crate::leanh::lean_ctor_get(v_x_4313_, 0);
                    v_isSharedCheck_4341_ = (!crate::leanh::lean_is_exclusive(v_x_4313_)) as u8;
                    if v_isSharedCheck_4341_ == 0 {
                        v___x_4326_ = v_x_4313_;
                        v_isShared_4327_ = v_isSharedCheck_4341_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4324_);
                        crate::leanh::lean_dec(v_x_4313_);
                        v___x_4326_ = crate::leanh::lean_box(0);
                        v_isShared_4327_ = v_isSharedCheck_4341_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4318_ == 0 {
                    v___x_4320_ = v___x_4317_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4322_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4322_, 0, v_a_4315_);
                    v___x_4320_ = v_reuseFailAlloc_4322_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4321_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4321_, 0, v___x_4320_);
                return v___x_4321_;
            }
            3 => {
                crate::leanh::lean_inc(v_a_4324_);
                v___x_4328_ = crate::leanh::lean_apply_1(v_x_4309_, v_a_4324_);
                v___x_4329_ = crate::leanh::lean_box(2);
                v___f_4330_ = crate::leanh::lean_alloc_closure(
                    l_Std_Async_ContextAsync_concurrently___redArg___lam__3___boxed
                        as *mut core::ffi::c_void,
                    4,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_4330_, 0, v_a_4324_);
                crate::leanh::lean_closure_set(v___f_4330_, 1, v___x_4329_);
                v___f_4331_ = crate::leanh::lean_alloc_closure(
                    l_Std_Async_ContextAsync_async___redArg___lam__3___boxed
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_4331_, 0, v___x_4328_);
                crate::leanh::lean_closure_set(v___f_4331_, 1, v___f_4330_);
                crate::leanh::lean_closure_set(v___f_4331_, 2, v___f_4310_);
                v___x_4332_ = crate::leanh::lean_alloc_closure(
                    l_Std_Async_BaseAsync_toRawBaseIO___boxed as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___x_4332_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_4332_, 1, v___f_4331_);
                v___x_4333_ = lean_io_as_task(v___x_4332_, v_prio_4311_);
                v___x_4334_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4335_ = 1;
                v___x_4336_ = lean_task_bind(v___x_4333_, v___f_4312_, v___x_4334_, v___x_4335_);
                if v_isShared_4327_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4326_, 0, v___x_4336_);
                    v___x_4338_ = v___x_4326_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4340_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4340_, 0, v___x_4336_);
                    v___x_4338_ = v_reuseFailAlloc_4340_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4339_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4339_, 0, v___x_4338_);
                return v___x_4339_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_async___redArg___lam__0___boxed(
    mut v_x_4342_: *mut crate::leanh::LeanObject,
    mut v___f_4343_: *mut crate::leanh::LeanObject,
    mut v_prio_4344_: *mut crate::leanh::LeanObject,
    mut v___f_4345_: *mut crate::leanh::LeanObject,
    mut v_x_4346_: *mut crate::leanh::LeanObject,
    mut v___y_4347_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4348_ = l_Std_Async_ContextAsync_async___redArg___lam__0(
        v_x_4342_,
        v___f_4343_,
        v_prio_4344_,
        v___f_4345_,
        v_x_4346_,
    );
    return v_res_4348_;
}
pub unsafe fn l_Std_Async_ContextAsync_async___redArg(
    mut v_x_4349_: *mut crate::leanh::LeanObject,
    mut v_prio_4350_: *mut crate::leanh::LeanObject,
    mut v_ctx_4351_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4360_: u8 = 0;
    let mut v___x_4361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_ctx_4351_);
    v___x_4353_ = l_Std_CancellationContext_fork(v_ctx_4351_);
    v___f_4354_ = l_Std_Async_ContextAsync_concurrently___redArg___closed__1;
    v___f_4355_ = l_Std_Async_ContextAsync_concurrently___redArg___closed__0;
    v___f_4356_ = crate::leanh::lean_alloc_closure(
        l_Std_Async_ContextAsync_async___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        4,
    );
    crate::leanh::lean_closure_set(v___f_4356_, 0, v_x_4349_);
    crate::leanh::lean_closure_set(v___f_4356_, 1, v___f_4354_);
    crate::leanh::lean_closure_set(v___f_4356_, 2, v_prio_4350_);
    crate::leanh::lean_closure_set(v___f_4356_, 3, v___f_4355_);
    v___x_4357_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4357_, 0, v___x_4353_);
    v___x_4358_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4358_, 0, v___x_4357_);
    v___x_4359_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4360_ = 0;
    v___x_4361_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4359_,
        v___x_4360_,
        v___x_4358_,
        v___f_4356_,
    );
    return v___x_4361_;
}
pub unsafe fn l_Std_Async_ContextAsync_async___redArg___boxed(
    mut v_x_4362_: *mut crate::leanh::LeanObject,
    mut v_prio_4363_: *mut crate::leanh::LeanObject,
    mut v_ctx_4364_: *mut crate::leanh::LeanObject,
    mut v_a_4365_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4366_ = l_Std_Async_ContextAsync_async___redArg(v_x_4362_, v_prio_4363_, v_ctx_4364_);
    crate::leanh::lean_dec_ref(v_ctx_4364_);
    return v_res_4366_;
}
pub unsafe fn l_Std_Async_ContextAsync_async(
    mut v_00_u03b1_4367_: *mut crate::leanh::LeanObject,
    mut v_x_4368_: *mut crate::leanh::LeanObject,
    mut v_prio_4369_: *mut crate::leanh::LeanObject,
    mut v_ctx_4370_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4379_: u8 = 0;
    let mut v___x_4380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_ctx_4370_);
    v___x_4372_ = l_Std_CancellationContext_fork(v_ctx_4370_);
    v___f_4373_ = l_Std_Async_ContextAsync_concurrently___redArg___closed__1;
    v___f_4374_ = l_Std_Async_ContextAsync_concurrently___redArg___closed__0;
    v___f_4375_ = crate::leanh::lean_alloc_closure(
        l_Std_Async_ContextAsync_async___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        4,
    );
    crate::leanh::lean_closure_set(v___f_4375_, 0, v_x_4368_);
    crate::leanh::lean_closure_set(v___f_4375_, 1, v___f_4373_);
    crate::leanh::lean_closure_set(v___f_4375_, 2, v_prio_4369_);
    crate::leanh::lean_closure_set(v___f_4375_, 3, v___f_4374_);
    v___x_4376_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4376_, 0, v___x_4372_);
    v___x_4377_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4377_, 0, v___x_4376_);
    v___x_4378_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4379_ = 0;
    v___x_4380_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4378_,
        v___x_4379_,
        v___x_4377_,
        v___f_4375_,
    );
    return v___x_4380_;
}
pub unsafe fn l_Std_Async_ContextAsync_async___boxed(
    mut v_00_u03b1_4381_: *mut crate::leanh::LeanObject,
    mut v_x_4382_: *mut crate::leanh::LeanObject,
    mut v_prio_4383_: *mut crate::leanh::LeanObject,
    mut v_ctx_4384_: *mut crate::leanh::LeanObject,
    mut v_a_4385_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4386_ =
        l_Std_Async_ContextAsync_async(v_00_u03b1_4381_, v_x_4382_, v_prio_4383_, v_ctx_4384_);
    crate::leanh::lean_dec_ref(v_ctx_4384_);
    return v_res_4386_;
}
pub unsafe fn l_Std_Async_ContextAsync_instMonadAsyncAsyncTask___lam__5(
    mut v___f_4387_: *mut crate::leanh::LeanObject,
    mut v___f_4388_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_4389_: *mut crate::leanh::LeanObject,
    mut v_x_4390_: *mut crate::leanh::LeanObject,
    mut v_prio_4391_: *mut crate::leanh::LeanObject,
    mut v___y_4392_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4399_: u8 = 0;
    let mut v___x_4400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v___y_4392_);
    v___x_4394_ = l_Std_CancellationContext_fork(v___y_4392_);
    v___f_4395_ = crate::leanh::lean_alloc_closure(
        l_Std_Async_ContextAsync_async___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        4,
    );
    crate::leanh::lean_closure_set(v___f_4395_, 0, v_x_4390_);
    crate::leanh::lean_closure_set(v___f_4395_, 1, v___f_4387_);
    crate::leanh::lean_closure_set(v___f_4395_, 2, v_prio_4391_);
    crate::leanh::lean_closure_set(v___f_4395_, 3, v___f_4388_);
    v___x_4396_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4396_, 0, v___x_4394_);
    v___x_4397_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4397_, 0, v___x_4396_);
    v___x_4398_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4399_ = 0;
    v___x_4400_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4398_,
        v___x_4399_,
        v___x_4397_,
        v___f_4395_,
    );
    return v___x_4400_;
}
pub unsafe fn l_Std_Async_ContextAsync_instMonadAsyncAsyncTask___lam__5___boxed(
    mut v___f_4401_: *mut crate::leanh::LeanObject,
    mut v___f_4402_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_4403_: *mut crate::leanh::LeanObject,
    mut v_x_4404_: *mut crate::leanh::LeanObject,
    mut v_prio_4405_: *mut crate::leanh::LeanObject,
    mut v___y_4406_: *mut crate::leanh::LeanObject,
    mut v___y_4407_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4408_ = l_Std_Async_ContextAsync_instMonadAsyncAsyncTask___lam__5(
        v___f_4401_,
        v___f_4402_,
        v_00_u03b1_4403_,
        v_x_4404_,
        v_prio_4405_,
        v___y_4406_,
    );
    crate::leanh::lean_dec_ref(v___y_4406_);
    return v_res_4408_;
}
pub unsafe fn l_Std_Async_ContextAsync_instFunctor___lam__0(
    mut v_00_u03b1_4413_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4414_: *mut crate::leanh::LeanObject,
    mut v_f_4415_: *mut crate::leanh::LeanObject,
    mut v_x_4416_: *mut crate::leanh::LeanObject,
    mut v_ctx_4417_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4427_: u8 = 0;
    let mut v___x_4429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4431_: u8 = 0;
    let mut v_a_4432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4435_: u8 = 0;
    let mut v___x_4436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4440_: u8 = 0;
    let mut v_a_4441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4444_: u8 = 0;
    let mut v___x_4445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4447_: u8 = 0;
    let mut v___x_4448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4452_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4419_ =
                    crate::leanh::lean_apply_2(v_x_4416_, v_ctx_4417_, crate::leanh::lean_box(0));
                if crate::leanh::lean_obj_tag(v___x_4419_) == 0 {
                    v_a_4423_ = crate::leanh::lean_ctor_get(v___x_4419_, 0);
                    crate::leanh::lean_inc(v_a_4423_);
                    crate::leanh::lean_dec_ref_known(v___x_4419_, 1);
                    if crate::leanh::lean_obj_tag(v_a_4423_) == 0 {
                        crate::leanh::lean_dec(v_f_4415_);
                        v_a_4424_ = crate::leanh::lean_ctor_get(v_a_4423_, 0);
                        v_isSharedCheck_4431_ = (!crate::leanh::lean_is_exclusive(v_a_4423_)) as u8;
                        if v_isSharedCheck_4431_ == 0 {
                            v___x_4426_ = v_a_4423_;
                            v_isShared_4427_ = v_isSharedCheck_4431_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4424_);
                            crate::leanh::lean_dec(v_a_4423_);
                            v___x_4426_ = crate::leanh::lean_box(0);
                            v_isShared_4427_ = v_isSharedCheck_4431_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_a_4432_ = crate::leanh::lean_ctor_get(v_a_4423_, 0);
                        v_isSharedCheck_4440_ = (!crate::leanh::lean_is_exclusive(v_a_4423_)) as u8;
                        if v_isSharedCheck_4440_ == 0 {
                            v___x_4434_ = v_a_4423_;
                            v_isShared_4435_ = v_isSharedCheck_4440_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4432_);
                            crate::leanh::lean_dec(v_a_4423_);
                            v___x_4434_ = crate::leanh::lean_box(0);
                            v_isShared_4435_ = v_isSharedCheck_4440_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_a_4441_ = crate::leanh::lean_ctor_get(v___x_4419_, 0);
                    v_isSharedCheck_4452_ = (!crate::leanh::lean_is_exclusive(v___x_4419_)) as u8;
                    if v_isSharedCheck_4452_ == 0 {
                        v___x_4443_ = v___x_4419_;
                        v_isShared_4444_ = v_isSharedCheck_4452_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4441_);
                        crate::leanh::lean_dec(v___x_4419_);
                        v___x_4443_ = crate::leanh::lean_box(0);
                        v_isShared_4444_ = v_isSharedCheck_4452_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4422_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4422_, 0, v___y_4421_);
                return v___x_4422_;
            }
            2 => {
                if v_isShared_4427_ == 0 {
                    v___x_4429_ = v___x_4426_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4430_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4430_, 0, v_a_4424_);
                    v___x_4429_ = v_reuseFailAlloc_4430_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___y_4421_ = v___x_4429_;
                state = 1;
                continue;
            }
            4 => {
                v___x_4436_ = crate::leanh::lean_apply_1(v_f_4415_, v_a_4432_);
                if v_isShared_4435_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4434_, 0, v___x_4436_);
                    v___x_4438_ = v___x_4434_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4439_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4439_, 0, v___x_4436_);
                    v___x_4438_ = v_reuseFailAlloc_4439_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___y_4421_ = v___x_4438_;
                state = 1;
                continue;
            }
            6 => {
                v___x_4445_ =
                    crate::leanh::lean_alloc_closure(l_Except_map as *mut core::ffi::c_void, 5, 4);
                crate::leanh::lean_closure_set(v___x_4445_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_4445_, 1, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_4445_, 2, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_4445_, 3, v_f_4415_);
                v___x_4446_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4447_ = 0;
                v___x_4448_ = lean_task_map(v___x_4445_, v_a_4441_, v___x_4446_, v___x_4447_);
                if v_isShared_4444_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4443_, 0, v___x_4448_);
                    v___x_4450_ = v___x_4443_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4451_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4451_, 0, v___x_4448_);
                    v___x_4450_ = v_reuseFailAlloc_4451_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4450_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_instFunctor___lam__0___boxed(
    mut v_00_u03b1_4453_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4454_: *mut crate::leanh::LeanObject,
    mut v_f_4455_: *mut crate::leanh::LeanObject,
    mut v_x_4456_: *mut crate::leanh::LeanObject,
    mut v_ctx_4457_: *mut crate::leanh::LeanObject,
    mut v___y_4458_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4459_ = l_Std_Async_ContextAsync_instFunctor___lam__0(
        v_00_u03b1_4453_,
        v_00_u03b2_4454_,
        v_f_4455_,
        v_x_4456_,
        v_ctx_4457_,
    );
    return v_res_4459_;
}
pub unsafe fn l_Std_Async_ContextAsync_instFunctor___lam__1(
    mut v___f_4460_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_4461_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4462_: *mut crate::leanh::LeanObject,
    mut v___y_4463_: *mut crate::leanh::LeanObject,
    mut v___y_4464_: *mut crate::leanh::LeanObject,
    mut v___y_4465_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4467_ =
        crate::leanh::lean_alloc_closure(l_Function_const___boxed as *mut core::ffi::c_void, 4, 3);
    crate::leanh::lean_closure_set(v___x_4467_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_4467_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_4467_, 2, v___y_4463_);
    crate::leanh::lean_inc_ref(v___y_4465_);
    v___x_4468_ = crate::leanh::lean_apply_6(
        v___f_4460_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4467_,
        v___y_4464_,
        v___y_4465_,
        crate::leanh::lean_box(0),
    );
    return v___x_4468_;
}
pub unsafe fn l_Std_Async_ContextAsync_instFunctor___lam__1___boxed(
    mut v___f_4469_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_4470_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4471_: *mut crate::leanh::LeanObject,
    mut v___y_4472_: *mut crate::leanh::LeanObject,
    mut v___y_4473_: *mut crate::leanh::LeanObject,
    mut v___y_4474_: *mut crate::leanh::LeanObject,
    mut v___y_4475_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4476_ = l_Std_Async_ContextAsync_instFunctor___lam__1(
        v___f_4469_,
        v_00_u03b1_4470_,
        v_00_u03b2_4471_,
        v___y_4472_,
        v___y_4473_,
        v___y_4474_,
    );
    crate::leanh::lean_dec_ref(v___y_4474_);
    return v_res_4476_;
}
pub unsafe fn l_Std_Async_ContextAsync_instMonad___lam__0(
    mut v_00_u03b1_4484_: *mut crate::leanh::LeanObject,
    mut v_a_4485_: *mut crate::leanh::LeanObject,
    mut v_x_4486_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4488_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4488_, 0, v_a_4485_);
    v___x_4489_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4489_, 0, v___x_4488_);
    return v___x_4489_;
}
pub unsafe fn l_Std_Async_ContextAsync_instMonad___lam__0___boxed(
    mut v_00_u03b1_4490_: *mut crate::leanh::LeanObject,
    mut v_a_4491_: *mut crate::leanh::LeanObject,
    mut v_x_4492_: *mut crate::leanh::LeanObject,
    mut v___y_4493_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4494_ =
        l_Std_Async_ContextAsync_instMonad___lam__0(v_00_u03b1_4490_, v_a_4491_, v_x_4492_);
    crate::leanh::lean_dec_ref(v_x_4492_);
    return v_res_4494_;
}
pub unsafe fn l_Std_Async_ContextAsync_instMonad___lam__1(
    mut v_f_4495_: *mut crate::leanh::LeanObject,
    mut v_ctx_4496_: *mut crate::leanh::LeanObject,
    mut v_x_4497_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_4499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4502_: u8 = 0;
    let mut v___x_4504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4507_: u8 = 0;
    let mut v_a_4508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4497_) == 0 {
                    crate::leanh::lean_dec_ref(v_ctx_4496_);
                    crate::leanh::lean_dec_ref(v_f_4495_);
                    v_a_4499_ = crate::leanh::lean_ctor_get(v_x_4497_, 0);
                    v_isSharedCheck_4507_ = (!crate::leanh::lean_is_exclusive(v_x_4497_)) as u8;
                    if v_isSharedCheck_4507_ == 0 {
                        v___x_4501_ = v_x_4497_;
                        v_isShared_4502_ = v_isSharedCheck_4507_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4499_);
                        crate::leanh::lean_dec(v_x_4497_);
                        v___x_4501_ = crate::leanh::lean_box(0);
                        v_isShared_4502_ = v_isSharedCheck_4507_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4508_ = crate::leanh::lean_ctor_get(v_x_4497_, 0);
                    crate::leanh::lean_inc(v_a_4508_);
                    crate::leanh::lean_dec_ref_known(v_x_4497_, 1);
                    v___x_4509_ = crate::leanh::lean_apply_3(
                        v_f_4495_,
                        v_a_4508_,
                        v_ctx_4496_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_4509_;
                }
            }
            1 => {
                if v_isShared_4502_ == 0 {
                    v___x_4504_ = v___x_4501_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4506_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4506_, 0, v_a_4499_);
                    v___x_4504_ = v_reuseFailAlloc_4506_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4505_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4505_, 0, v___x_4504_);
                return v___x_4505_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_instMonad___lam__1___boxed(
    mut v_f_4510_: *mut crate::leanh::LeanObject,
    mut v_ctx_4511_: *mut crate::leanh::LeanObject,
    mut v_x_4512_: *mut crate::leanh::LeanObject,
    mut v___y_4513_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4514_ = l_Std_Async_ContextAsync_instMonad___lam__1(v_f_4510_, v_ctx_4511_, v_x_4512_);
    return v_res_4514_;
}
pub unsafe fn l_Std_Async_ContextAsync_instMonad___lam__2(
    mut v_00_u03b1_4515_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4516_: *mut crate::leanh::LeanObject,
    mut v_x_4517_: *mut crate::leanh::LeanObject,
    mut v_f_4518_: *mut crate::leanh::LeanObject,
    mut v_ctx_4519_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4524_: u8 = 0;
    let mut v___x_4525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_ctx_4519_);
    v___x_4521_ = crate::leanh::lean_apply_2(v_x_4517_, v_ctx_4519_, crate::leanh::lean_box(0));
    v___f_4522_ = crate::leanh::lean_alloc_closure(
        l_Std_Async_ContextAsync_instMonad___lam__1___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_4522_, 0, v_f_4518_);
    crate::leanh::lean_closure_set(v___f_4522_, 1, v_ctx_4519_);
    v___x_4523_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4524_ = 0;
    v___x_4525_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4523_,
        v___x_4524_,
        v___x_4521_,
        v___f_4522_,
    );
    return v___x_4525_;
}
pub unsafe fn l_Std_Async_ContextAsync_instMonad___lam__2___boxed(
    mut v_00_u03b1_4526_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4527_: *mut crate::leanh::LeanObject,
    mut v_x_4528_: *mut crate::leanh::LeanObject,
    mut v_f_4529_: *mut crate::leanh::LeanObject,
    mut v_ctx_4530_: *mut crate::leanh::LeanObject,
    mut v___y_4531_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4532_ = l_Std_Async_ContextAsync_instMonad___lam__2(
        v_00_u03b1_4526_,
        v_00_u03b2_4527_,
        v_x_4528_,
        v_f_4529_,
        v_ctx_4530_,
    );
    return v_res_4532_;
}
pub unsafe fn _init_l_Std_Async_ContextAsync_instMonad() -> *mut crate::leanh::LeanObject {
    let mut v___x_4535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_4537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_4538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_4539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_4540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4535_ = l_Std_Async_ContextAsync_instFunctor;
    v___x_4536_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__1_once),
        _init_l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__1,
    );
    v_toApplicative_4537_ = crate::leanh::lean_ctor_get(v___x_4536_, 0);
    v_toSeq_4538_ = crate::leanh::lean_ctor_get(v_toApplicative_4537_, 2);
    v_toSeqLeft_4539_ = crate::leanh::lean_ctor_get(v_toApplicative_4537_, 3);
    v_toSeqRight_4540_ = crate::leanh::lean_ctor_get(v_toApplicative_4537_, 4);
    v___f_4541_ = l_Std_Async_ContextAsync_instMonad___closed__0;
    v___f_4542_ = l_Std_Async_ContextAsync_instMonad___closed__1;
    crate::leanh::lean_inc(v_toSeqRight_4540_);
    v___f_4543_ = crate::leanh::lean_alloc_closure(
        l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4543_, 0, v_toSeqRight_4540_);
    crate::leanh::lean_inc(v_toSeqLeft_4539_);
    v___f_4544_ = crate::leanh::lean_alloc_closure(
        l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4544_, 0, v_toSeqLeft_4539_);
    crate::leanh::lean_inc(v_toSeq_4538_);
    v___f_4545_ = crate::leanh::lean_alloc_closure(
        l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4545_, 0, v_toSeq_4538_);
    v___x_4546_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4546_, 0, v___x_4535_);
    crate::leanh::lean_ctor_set(v___x_4546_, 1, v___f_4541_);
    crate::leanh::lean_ctor_set(v___x_4546_, 2, v___f_4545_);
    crate::leanh::lean_ctor_set(v___x_4546_, 3, v___f_4544_);
    crate::leanh::lean_ctor_set(v___x_4546_, 4, v___f_4543_);
    v___x_4547_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4547_, 0, v___x_4546_);
    crate::leanh::lean_ctor_set(v___x_4547_, 1, v___f_4542_);
    return v___x_4547_;
}
pub unsafe fn l_Std_Async_ContextAsync_instMonadLiftIO___lam__0(
    mut v_a_4548_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4549_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4549_, 0, v_a_4548_);
    return v___x_4549_;
}
pub unsafe fn l_Std_Async_ContextAsync_instMonadLiftIO___lam__1(
    mut v___f_4550_: *mut crate::leanh::LeanObject,
    mut v_x_4551_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_4553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4556_: u8 = 0;
    let mut v___x_4558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4561_: u8 = 0;
    let mut v_a_4562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4566_: u8 = 0;
    let mut v___x_4568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4571_: u8 = 0;
    let mut v_a_4572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4574_: u8 = 0;
    let mut v___x_4575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4551_) == 0 {
                    crate::leanh::lean_dec_ref(v___f_4550_);
                    v_a_4553_ = crate::leanh::lean_ctor_get(v_x_4551_, 0);
                    v_isSharedCheck_4561_ = (!crate::leanh::lean_is_exclusive(v_x_4551_)) as u8;
                    if v_isSharedCheck_4561_ == 0 {
                        v___x_4555_ = v_x_4551_;
                        v_isShared_4556_ = v_isSharedCheck_4561_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4553_);
                        crate::leanh::lean_dec(v_x_4551_);
                        v___x_4555_ = crate::leanh::lean_box(0);
                        v_isShared_4556_ = v_isSharedCheck_4561_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4562_ = crate::leanh::lean_ctor_get(v_x_4551_, 0);
                    crate::leanh::lean_inc(v_a_4562_);
                    crate::leanh::lean_dec_ref_known(v_x_4551_, 1);
                    if crate::leanh::lean_obj_tag(v_a_4562_) == 0 {
                        crate::leanh::lean_dec_ref(v___f_4550_);
                        v_a_4563_ = crate::leanh::lean_ctor_get(v_a_4562_, 0);
                        v_isSharedCheck_4571_ = (!crate::leanh::lean_is_exclusive(v_a_4562_)) as u8;
                        if v_isSharedCheck_4571_ == 0 {
                            v___x_4565_ = v_a_4562_;
                            v_isShared_4566_ = v_isSharedCheck_4571_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4563_);
                            crate::leanh::lean_dec(v_a_4562_);
                            v___x_4565_ = crate::leanh::lean_box(0);
                            v_isShared_4566_ = v_isSharedCheck_4571_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_4572_ = crate::leanh::lean_ctor_get(v_a_4562_, 0);
                        crate::leanh::lean_inc(v_a_4572_);
                        crate::leanh::lean_dec_ref_known(v_a_4562_, 1);
                        v___x_4573_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_4574_ = 0;
                        v___x_4575_ =
                            lean_task_map(v___f_4550_, v_a_4572_, v___x_4573_, v___x_4574_);
                        v___x_4576_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4576_, 0, v___x_4575_);
                        return v___x_4576_;
                    }
                }
            }
            1 => {
                if v_isShared_4556_ == 0 {
                    v___x_4558_ = v___x_4555_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4560_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4560_, 0, v_a_4553_);
                    v___x_4558_ = v_reuseFailAlloc_4560_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4559_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4559_, 0, v___x_4558_);
                return v___x_4559_;
            }
            3 => {
                if v_isShared_4566_ == 0 {
                    v___x_4568_ = v___x_4565_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4570_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4570_, 0, v_a_4563_);
                    v___x_4568_ = v_reuseFailAlloc_4570_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4569_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4569_, 0, v___x_4568_);
                return v___x_4569_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_instMonadLiftIO___lam__1___boxed(
    mut v___f_4577_: *mut crate::leanh::LeanObject,
    mut v_x_4578_: *mut crate::leanh::LeanObject,
    mut v___y_4579_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4580_ = l_Std_Async_ContextAsync_instMonadLiftIO___lam__1(v___f_4577_, v_x_4578_);
    return v_res_4580_;
}
pub unsafe fn l_Std_Async_ContextAsync_instMonadLiftIO___lam__2(
    mut v___f_4581_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_4582_: *mut crate::leanh::LeanObject,
    mut v_x_4583_: *mut crate::leanh::LeanObject,
    mut v_x_4584_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_4587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4591_: u8 = 0;
    let mut v___x_4592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4597_: u8 = 0;
    let mut v___x_4598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4602_: u8 = 0;
    let mut v_a_4603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4606_: u8 = 0;
    let mut v___x_4608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4610_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4593_ = crate::leanh::lean_apply_1(v_x_4583_, crate::leanh::lean_box(0));
                if crate::leanh::lean_obj_tag(v___x_4593_) == 0 {
                    v_a_4594_ = crate::leanh::lean_ctor_get(v___x_4593_, 0);
                    v_isSharedCheck_4602_ = (!crate::leanh::lean_is_exclusive(v___x_4593_)) as u8;
                    if v_isSharedCheck_4602_ == 0 {
                        v___x_4596_ = v___x_4593_;
                        v_isShared_4597_ = v_isSharedCheck_4602_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4594_);
                        crate::leanh::lean_dec(v___x_4593_);
                        v___x_4596_ = crate::leanh::lean_box(0);
                        v_isShared_4597_ = v_isSharedCheck_4602_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_4603_ = crate::leanh::lean_ctor_get(v___x_4593_, 0);
                    v_isSharedCheck_4610_ = (!crate::leanh::lean_is_exclusive(v___x_4593_)) as u8;
                    if v_isSharedCheck_4610_ == 0 {
                        v___x_4605_ = v___x_4593_;
                        v_isShared_4606_ = v_isSharedCheck_4610_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4603_);
                        crate::leanh::lean_dec(v___x_4593_);
                        v___x_4605_ = crate::leanh::lean_box(0);
                        v_isShared_4606_ = v_isSharedCheck_4610_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4588_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4588_, 0, v_val_4587_);
                v___x_4589_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4589_, 0, v___x_4588_);
                v___x_4590_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4591_ = 0;
                v___x_4592_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_4590_,
                    v___x_4591_,
                    v___x_4589_,
                    v___f_4581_,
                );
                return v___x_4592_;
            }
            2 => {
                v___x_4598_ = lean_task_pure(v_a_4594_);
                if v_isShared_4597_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4596_, 1);
                    crate::leanh::lean_ctor_set(v___x_4596_, 0, v___x_4598_);
                    v___x_4600_ = v___x_4596_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4601_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4601_, 0, v___x_4598_);
                    v___x_4600_ = v_reuseFailAlloc_4601_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_val_4587_ = v___x_4600_;
                state = 1;
                continue;
            }
            4 => {
                if v_isShared_4606_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4605_, 0);
                    v___x_4608_ = v___x_4605_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4609_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4609_, 0, v_a_4603_);
                    v___x_4608_ = v_reuseFailAlloc_4609_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_val_4587_ = v___x_4608_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_instMonadLiftIO___lam__2___boxed(
    mut v___f_4611_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_4612_: *mut crate::leanh::LeanObject,
    mut v_x_4613_: *mut crate::leanh::LeanObject,
    mut v_x_4614_: *mut crate::leanh::LeanObject,
    mut v___y_4615_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4616_ = l_Std_Async_ContextAsync_instMonadLiftIO___lam__2(
        v___f_4611_,
        v_00_u03b1_4612_,
        v_x_4613_,
        v_x_4614_,
    );
    crate::leanh::lean_dec_ref(v_x_4614_);
    return v_res_4616_;
}
pub unsafe fn l_Std_Async_ContextAsync_instMonadLiftBaseIO___lam__0(
    mut v_00_u03b1_4623_: *mut crate::leanh::LeanObject,
    mut v_x_4624_: *mut crate::leanh::LeanObject,
    mut v_x_4625_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4627_ = crate::leanh::lean_apply_1(v_x_4624_, crate::leanh::lean_box(0));
    v___x_4628_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4628_, 0, v___x_4627_);
    v___x_4629_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4629_, 0, v___x_4628_);
    return v___x_4629_;
}
pub unsafe fn l_Std_Async_ContextAsync_instMonadLiftBaseIO___lam__0___boxed(
    mut v_00_u03b1_4630_: *mut crate::leanh::LeanObject,
    mut v_x_4631_: *mut crate::leanh::LeanObject,
    mut v_x_4632_: *mut crate::leanh::LeanObject,
    mut v___y_4633_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4634_ = l_Std_Async_ContextAsync_instMonadLiftBaseIO___lam__0(
        v_00_u03b1_4630_,
        v_x_4631_,
        v_x_4632_,
    );
    crate::leanh::lean_dec_ref(v_x_4632_);
    return v_res_4634_;
}
pub unsafe fn l_Std_Async_ContextAsync_instMonadExceptError___lam__0(
    mut v_00_u03b1_4637_: *mut crate::leanh::LeanObject,
    mut v_e_4638_: *mut crate::leanh::LeanObject,
    mut v_x_4639_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4641_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4641_, 0, v_e_4638_);
    v___x_4642_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4642_, 0, v___x_4641_);
    return v___x_4642_;
}
pub unsafe fn l_Std_Async_ContextAsync_instMonadExceptError___lam__0___boxed(
    mut v_00_u03b1_4643_: *mut crate::leanh::LeanObject,
    mut v_e_4644_: *mut crate::leanh::LeanObject,
    mut v_x_4645_: *mut crate::leanh::LeanObject,
    mut v___y_4646_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4647_ = l_Std_Async_ContextAsync_instMonadExceptError___lam__0(
        v_00_u03b1_4643_,
        v_e_4644_,
        v_x_4645_,
    );
    crate::leanh::lean_dec_ref(v_x_4645_);
    return v_res_4647_;
}
pub unsafe fn l_Std_Async_ContextAsync_instMonadExceptError___lam__1(
    mut v_h_4648_: *mut crate::leanh::LeanObject,
    mut v_ctx_4649_: *mut crate::leanh::LeanObject,
    mut v_x_4650_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4650_) == 0 {
        let mut v_a_4652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_4652_ = crate::leanh::lean_ctor_get(v_x_4650_, 0);
        crate::leanh::lean_inc(v_a_4652_);
        crate::leanh::lean_dec_ref_known(v_x_4650_, 1);
        v___x_4653_ = crate::leanh::lean_apply_3(
            v_h_4648_,
            v_a_4652_,
            v_ctx_4649_,
            crate::leanh::lean_box(0),
        );
        return v___x_4653_;
    } else {
        let mut v___x_4654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_ctx_4649_);
        crate::leanh::lean_dec_ref(v_h_4648_);
        v___x_4654_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4654_, 0, v_x_4650_);
        return v___x_4654_;
    }
}
pub unsafe fn l_Std_Async_ContextAsync_instMonadExceptError___lam__1___boxed(
    mut v_h_4655_: *mut crate::leanh::LeanObject,
    mut v_ctx_4656_: *mut crate::leanh::LeanObject,
    mut v_x_4657_: *mut crate::leanh::LeanObject,
    mut v___y_4658_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4659_ =
        l_Std_Async_ContextAsync_instMonadExceptError___lam__1(v_h_4655_, v_ctx_4656_, v_x_4657_);
    return v_res_4659_;
}
pub unsafe fn l_Std_Async_ContextAsync_instMonadExceptError___lam__2(
    mut v_00_u03b1_4660_: *mut crate::leanh::LeanObject,
    mut v_x_4661_: *mut crate::leanh::LeanObject,
    mut v_h_4662_: *mut crate::leanh::LeanObject,
    mut v_ctx_4663_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4668_: u8 = 0;
    let mut v___x_4669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_ctx_4663_);
    v___x_4665_ = crate::leanh::lean_apply_2(v_x_4661_, v_ctx_4663_, crate::leanh::lean_box(0));
    v___f_4666_ = crate::leanh::lean_alloc_closure(
        l_Std_Async_ContextAsync_instMonadExceptError___lam__1___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_4666_, 0, v_h_4662_);
    crate::leanh::lean_closure_set(v___f_4666_, 1, v_ctx_4663_);
    v___x_4667_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4668_ = 0;
    v___x_4669_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4667_,
        v___x_4668_,
        v___x_4665_,
        v___f_4666_,
    );
    return v___x_4669_;
}
pub unsafe fn l_Std_Async_ContextAsync_instMonadExceptError___lam__2___boxed(
    mut v_00_u03b1_4670_: *mut crate::leanh::LeanObject,
    mut v_x_4671_: *mut crate::leanh::LeanObject,
    mut v_h_4672_: *mut crate::leanh::LeanObject,
    mut v_ctx_4673_: *mut crate::leanh::LeanObject,
    mut v___y_4674_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4675_ = l_Std_Async_ContextAsync_instMonadExceptError___lam__2(
        v_00_u03b1_4670_,
        v_x_4671_,
        v_h_4672_,
        v_ctx_4673_,
    );
    return v_res_4675_;
}
pub unsafe fn l_Std_Async_ContextAsync_instMonadFinally___lam__0(
    mut v_f_4682_: *mut crate::leanh::LeanObject,
    mut v_ctx_4683_: *mut crate::leanh::LeanObject,
    mut v_opt_4684_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4686_ = crate::leanh::lean_apply_3(
        v_f_4682_,
        v_opt_4684_,
        v_ctx_4683_,
        crate::leanh::lean_box(0),
    );
    return v___x_4686_;
}
pub unsafe fn l_Std_Async_ContextAsync_instMonadFinally___lam__0___boxed(
    mut v_f_4687_: *mut crate::leanh::LeanObject,
    mut v_ctx_4688_: *mut crate::leanh::LeanObject,
    mut v_opt_4689_: *mut crate::leanh::LeanObject,
    mut v___y_4690_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4691_ =
        l_Std_Async_ContextAsync_instMonadFinally___lam__0(v_f_4687_, v_ctx_4688_, v_opt_4689_);
    return v_res_4691_;
}
pub unsafe fn l_Std_Async_ContextAsync_instMonadFinally___lam__1(
    mut v_00_u03b1_4692_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4693_: *mut crate::leanh::LeanObject,
    mut v_x_4694_: *mut crate::leanh::LeanObject,
    mut v_f_4695_: *mut crate::leanh::LeanObject,
    mut v_ctx_4696_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4701_: u8 = 0;
    let mut v___x_4702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_ctx_4696_);
    v___f_4698_ = crate::leanh::lean_alloc_closure(
        l_Std_Async_ContextAsync_instMonadFinally___lam__0___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_4698_, 0, v_f_4695_);
    crate::leanh::lean_closure_set(v___f_4698_, 1, v_ctx_4696_);
    v___x_4699_ = crate::leanh::lean_apply_1(v_x_4694_, v_ctx_4696_);
    v___x_4700_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4701_ = 0;
    v___x_4702_ = l_Std_Async_EAsync_tryFinally_x27___redArg(
        v___x_4699_,
        v___f_4698_,
        v___x_4700_,
        v___x_4701_,
    );
    return v___x_4702_;
}
pub unsafe fn l_Std_Async_ContextAsync_instMonadFinally___lam__1___boxed(
    mut v_00_u03b1_4703_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4704_: *mut crate::leanh::LeanObject,
    mut v_x_4705_: *mut crate::leanh::LeanObject,
    mut v_f_4706_: *mut crate::leanh::LeanObject,
    mut v_ctx_4707_: *mut crate::leanh::LeanObject,
    mut v___y_4708_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4709_ = l_Std_Async_ContextAsync_instMonadFinally___lam__1(
        v_00_u03b1_4703_,
        v_00_u03b2_4704_,
        v_x_4705_,
        v_f_4706_,
        v_ctx_4707_,
    );
    return v_res_4709_;
}
pub unsafe fn l_Std_Async_ContextAsync_instInhabited___lam__0(
    mut v_x_4719_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4721_ = l_Std_Async_ContextAsync_instInhabited___lam__0___closed__3;
    return v___x_4721_;
}
pub unsafe fn l_Std_Async_ContextAsync_instInhabited___lam__0___boxed(
    mut v_x_4722_: *mut crate::leanh::LeanObject,
    mut v___y_4723_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4724_ = l_Std_Async_ContextAsync_instInhabited___lam__0(v_x_4722_);
    crate::leanh::lean_dec_ref(v_x_4722_);
    return v_res_4724_;
}
pub unsafe fn l_Std_Async_ContextAsync_instInhabited(
    mut v_00_u03b1_4726_: *mut crate::leanh::LeanObject,
    mut v_inst_4727_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4728_ = l_Std_Async_ContextAsync_instInhabited___closed__0;
    return v___f_4728_;
}
pub unsafe fn l_Std_Async_ContextAsync_instInhabited___boxed(
    mut v_00_u03b1_4729_: *mut crate::leanh::LeanObject,
    mut v_inst_4730_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4731_ = l_Std_Async_ContextAsync_instInhabited(v_00_u03b1_4729_, v_inst_4730_);
    crate::leanh::lean_dec(v_inst_4730_);
    return v_res_4731_;
}
pub unsafe fn l_Std_Async_ContextAsync_instMonadAwaitAsyncTask___lam__0(
    mut v_00_u03b1_4732_: *mut crate::leanh::LeanObject,
    mut v_t_4733_: *mut crate::leanh::LeanObject,
    mut v_x_4734_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4736_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4736_, 0, v_t_4733_);
    return v___x_4736_;
}
pub unsafe fn l_Std_Async_ContextAsync_instMonadAwaitAsyncTask___lam__0___boxed(
    mut v_00_u03b1_4737_: *mut crate::leanh::LeanObject,
    mut v_t_4738_: *mut crate::leanh::LeanObject,
    mut v_x_4739_: *mut crate::leanh::LeanObject,
    mut v___y_4740_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4741_ = l_Std_Async_ContextAsync_instMonadAwaitAsyncTask___lam__0(
        v_00_u03b1_4737_,
        v_t_4738_,
        v_x_4739_,
    );
    crate::leanh::lean_dec_ref(v_x_4739_);
    return v_res_4741_;
}
pub unsafe fn l_Std_Async_ContextAsync_race___redArg___lam__3(
    mut v_x_4744_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_4746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4749_: u8 = 0;
    let mut v___x_4751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4754_: u8 = 0;
    let mut v_a_4755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4744_) == 0 {
                    v_a_4746_ = crate::leanh::lean_ctor_get(v_x_4744_, 0);
                    v_isSharedCheck_4754_ = (!crate::leanh::lean_is_exclusive(v_x_4744_)) as u8;
                    if v_isSharedCheck_4754_ == 0 {
                        v___x_4748_ = v_x_4744_;
                        v_isShared_4749_ = v_isSharedCheck_4754_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4746_);
                        crate::leanh::lean_dec(v_x_4744_);
                        v___x_4748_ = crate::leanh::lean_box(0);
                        v_isShared_4749_ = v_isSharedCheck_4754_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4755_ = crate::leanh::lean_ctor_get(v_x_4744_, 0);
                    crate::leanh::lean_inc(v_a_4755_);
                    crate::leanh::lean_dec_ref_known(v_x_4744_, 1);
                    v___x_4756_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4756_, 0, v_a_4755_);
                    return v___x_4756_;
                }
            }
            1 => {
                if v_isShared_4749_ == 0 {
                    v___x_4751_ = v___x_4748_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4753_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4753_, 0, v_a_4746_);
                    v___x_4751_ = v_reuseFailAlloc_4753_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4752_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4752_, 0, v___x_4751_);
                return v___x_4752_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_race___redArg___lam__3___boxed(
    mut v_x_4757_: *mut crate::leanh::LeanObject,
    mut v___y_4758_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4759_ = l_Std_Async_ContextAsync_race___redArg___lam__3(v_x_4757_);
    return v_res_4759_;
}
pub unsafe fn l_Std_Async_ContextAsync_race___redArg___lam__6(
    mut v___f_4760_: *mut crate::leanh::LeanObject,
    mut v___f_4761_: *mut crate::leanh::LeanObject,
    mut v_prio_4762_: *mut crate::leanh::LeanObject,
    mut v___f_4763_: *mut crate::leanh::LeanObject,
    mut v_x_4764_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_4766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4769_: u8 = 0;
    let mut v___x_4771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4774_: u8 = 0;
    let mut v_a_4775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4778_: u8 = 0;
    let mut v___x_4779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4785_: u8 = 0;
    let mut v___x_4786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4791_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4764_) == 0 {
                    crate::leanh::lean_dec_ref(v___f_4763_);
                    crate::leanh::lean_dec(v_prio_4762_);
                    crate::leanh::lean_dec(v___f_4761_);
                    crate::leanh::lean_dec_ref(v___f_4760_);
                    v_a_4766_ = crate::leanh::lean_ctor_get(v_x_4764_, 0);
                    v_isSharedCheck_4774_ = (!crate::leanh::lean_is_exclusive(v_x_4764_)) as u8;
                    if v_isSharedCheck_4774_ == 0 {
                        v___x_4768_ = v_x_4764_;
                        v_isShared_4769_ = v_isSharedCheck_4774_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4766_);
                        crate::leanh::lean_dec(v_x_4764_);
                        v___x_4768_ = crate::leanh::lean_box(0);
                        v_isShared_4769_ = v_isSharedCheck_4774_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4775_ = crate::leanh::lean_ctor_get(v_x_4764_, 0);
                    v_isSharedCheck_4791_ = (!crate::leanh::lean_is_exclusive(v_x_4764_)) as u8;
                    if v_isSharedCheck_4791_ == 0 {
                        v___x_4777_ = v_x_4764_;
                        v_isShared_4778_ = v_isSharedCheck_4791_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4775_);
                        crate::leanh::lean_dec(v_x_4764_);
                        v___x_4777_ = crate::leanh::lean_box(0);
                        v_isShared_4778_ = v_isSharedCheck_4791_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4769_ == 0 {
                    v___x_4771_ = v___x_4768_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4773_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4773_, 0, v_a_4766_);
                    v___x_4771_ = v_reuseFailAlloc_4773_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4772_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4772_, 0, v___x_4771_);
                return v___x_4772_;
            }
            3 => {
                v___x_4779_ = crate::leanh::lean_box(2);
                v___f_4780_ = crate::leanh::lean_alloc_closure(
                    l_Std_Async_ContextAsync_concurrently___redArg___lam__3___boxed
                        as *mut core::ffi::c_void,
                    4,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_4780_, 0, v_a_4775_);
                crate::leanh::lean_closure_set(v___f_4780_, 1, v___x_4779_);
                v___f_4781_ = crate::leanh::lean_alloc_closure(
                    l_Std_Async_ContextAsync_concurrently___redArg___lam__5___boxed
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_4781_, 0, v___f_4760_);
                crate::leanh::lean_closure_set(v___f_4781_, 1, v___f_4780_);
                crate::leanh::lean_closure_set(v___f_4781_, 2, v___f_4761_);
                v___x_4782_ = crate::leanh::lean_alloc_closure(
                    l_Std_Async_BaseAsync_toRawBaseIO___boxed as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___x_4782_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_4782_, 1, v___f_4781_);
                v___x_4783_ = lean_io_as_task(v___x_4782_, v_prio_4762_);
                v___x_4784_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4785_ = 1;
                v___x_4786_ = lean_task_bind(v___x_4783_, v___f_4763_, v___x_4784_, v___x_4785_);
                if v_isShared_4778_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4777_, 0, v___x_4786_);
                    v___x_4788_ = v___x_4777_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4790_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4790_, 0, v___x_4786_);
                    v___x_4788_ = v_reuseFailAlloc_4790_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4789_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4789_, 0, v___x_4788_);
                return v___x_4789_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_race___redArg___lam__6___boxed(
    mut v___f_4792_: *mut crate::leanh::LeanObject,
    mut v___f_4793_: *mut crate::leanh::LeanObject,
    mut v_prio_4794_: *mut crate::leanh::LeanObject,
    mut v___f_4795_: *mut crate::leanh::LeanObject,
    mut v_x_4796_: *mut crate::leanh::LeanObject,
    mut v___y_4797_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4798_ = l_Std_Async_ContextAsync_race___redArg___lam__6(
        v___f_4792_,
        v___f_4793_,
        v_prio_4794_,
        v___f_4795_,
        v_x_4796_,
    );
    return v_res_4798_;
}
pub unsafe fn l_Std_Async_ContextAsync_race___redArg___lam__0(
    mut v_y_4799_: *mut crate::leanh::LeanObject,
    mut v_a_4800_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4802_ = crate::leanh::lean_apply_2(v_y_4799_, v_a_4800_, crate::leanh::lean_box(0));
    return v___x_4802_;
}
pub unsafe fn l_Std_Async_ContextAsync_race___redArg___lam__0___boxed(
    mut v_y_4803_: *mut crate::leanh::LeanObject,
    mut v_a_4804_: *mut crate::leanh::LeanObject,
    mut v___y_4805_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4806_ = l_Std_Async_ContextAsync_race___redArg___lam__0(v_y_4803_, v_a_4804_);
    return v_res_4806_;
}
pub unsafe fn l_Std_Async_ContextAsync_race___redArg___lam__5(
    mut v_a_4807_: *mut crate::leanh::LeanObject,
    mut v_a_4808_: *mut crate::leanh::LeanObject,
    mut v_result_4809_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4811_ = lean_io_promise_resolve(v_result_4809_, v_a_4807_);
    v___x_4812_ = crate::leanh::lean_box(2);
    v___x_4813_ = l_Std_CancellationContext_cancel(v_a_4808_, v___x_4812_);
    return v___x_4813_;
}
pub unsafe fn l_Std_Async_ContextAsync_race___redArg___lam__5___boxed(
    mut v_a_4814_: *mut crate::leanh::LeanObject,
    mut v_a_4815_: *mut crate::leanh::LeanObject,
    mut v_result_4816_: *mut crate::leanh::LeanObject,
    mut v___y_4817_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4818_ =
        l_Std_Async_ContextAsync_race___redArg___lam__5(v_a_4814_, v_a_4815_, v_result_4816_);
    crate::leanh::lean_dec(v_a_4814_);
    return v_res_4818_;
}
pub unsafe fn l_Std_Async_ContextAsync_race___redArg___lam__4(
    mut v_a_4819_: *mut crate::leanh::LeanObject,
    mut v___f_4820_: *mut crate::leanh::LeanObject,
    mut v___x_4821_: *mut crate::leanh::LeanObject,
    mut v___x_4822_: u8,
    mut v___f_4823_: *mut crate::leanh::LeanObject,
    mut v_x_4824_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_4826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4829_: u8 = 0;
    let mut v___x_4831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4834_: u8 = 0;
    let mut v___x_4836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4837_: u8 = 0;
    let mut v___x_4838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4844_: u8 = 0;
    let mut v_unused_4845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4824_) == 0 {
                    crate::leanh::lean_dec_ref(v___f_4823_);
                    crate::leanh::lean_dec(v___x_4821_);
                    crate::leanh::lean_dec_ref(v___f_4820_);
                    crate::leanh::lean_dec_ref(v_a_4819_);
                    v_a_4826_ = crate::leanh::lean_ctor_get(v_x_4824_, 0);
                    v_isSharedCheck_4834_ = (!crate::leanh::lean_is_exclusive(v_x_4824_)) as u8;
                    if v_isSharedCheck_4834_ == 0 {
                        v___x_4828_ = v_x_4824_;
                        v_isShared_4829_ = v_isSharedCheck_4834_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4826_);
                        crate::leanh::lean_dec(v_x_4824_);
                        v___x_4828_ = crate::leanh::lean_box(0);
                        v_isShared_4829_ = v_isSharedCheck_4834_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_isSharedCheck_4844_ = (!crate::leanh::lean_is_exclusive(v_x_4824_)) as u8;
                    if v_isSharedCheck_4844_ == 0 {
                        v_unused_4845_ = crate::leanh::lean_ctor_get(v_x_4824_, 0);
                        crate::leanh::lean_dec(v_unused_4845_);
                        v___x_4836_ = v_x_4824_;
                        v_isShared_4837_ = v_isSharedCheck_4844_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_x_4824_);
                        v___x_4836_ = crate::leanh::lean_box(0);
                        v_isShared_4837_ = v_isSharedCheck_4844_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4829_ == 0 {
                    v___x_4831_ = v___x_4828_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4833_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4833_, 0, v_a_4826_);
                    v___x_4831_ = v_reuseFailAlloc_4833_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4832_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4832_, 0, v___x_4831_);
                return v___x_4832_;
            }
            3 => {
                crate::leanh::lean_inc(v___x_4821_);
                v___x_4838_ =
                    l_BaseIO_chainTask___redArg(v_a_4819_, v___f_4820_, v___x_4821_, v___x_4822_);
                if v_isShared_4837_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4836_, 0, v___x_4838_);
                    v___x_4840_ = v___x_4836_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4843_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4843_, 0, v___x_4838_);
                    v___x_4840_ = v_reuseFailAlloc_4843_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4841_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4841_, 0, v___x_4840_);
                v___x_4842_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_4821_,
                    v___x_4822_,
                    v___x_4841_,
                    v___f_4823_,
                );
                return v___x_4842_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_race___redArg___lam__4___boxed(
    mut v_a_4846_: *mut crate::leanh::LeanObject,
    mut v___f_4847_: *mut crate::leanh::LeanObject,
    mut v___x_4848_: *mut crate::leanh::LeanObject,
    mut v___x_4849_: *mut crate::leanh::LeanObject,
    mut v___f_4850_: *mut crate::leanh::LeanObject,
    mut v_x_4851_: *mut crate::leanh::LeanObject,
    mut v___y_4852_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4305__boxed_4853_: u8 = 0;
    let mut v_res_4854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4305__boxed_4853_ = (crate::leanh::lean_unbox(v___x_4849_) as u8);
    v_res_4854_ = l_Std_Async_ContextAsync_race___redArg___lam__4(
        v_a_4846_,
        v___f_4847_,
        v___x_4848_,
        v___x_4305__boxed_4853_,
        v___f_4850_,
        v_x_4851_,
    );
    return v_res_4854_;
}
pub unsafe fn l_Std_Async_ContextAsync_race___redArg___lam__1(
    mut v_a_4855_: *mut crate::leanh::LeanObject,
    mut v_a_4856_: *mut crate::leanh::LeanObject,
    mut v_a_4857_: *mut crate::leanh::LeanObject,
    mut v___f_4858_: *mut crate::leanh::LeanObject,
    mut v___f_4859_: *mut crate::leanh::LeanObject,
    mut v_a_4860_: *mut crate::leanh::LeanObject,
    mut v_x_4861_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_4863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4866_: u8 = 0;
    let mut v___x_4868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4871_: u8 = 0;
    let mut v_a_4872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4875_: u8 = 0;
    let mut v___f_4876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4878_: u8 = 0;
    let mut v___x_4879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4889_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4861_) == 0 {
                    crate::leanh::lean_dec_ref(v_a_4860_);
                    crate::leanh::lean_dec_ref(v___f_4859_);
                    crate::leanh::lean_dec_ref(v___f_4858_);
                    crate::leanh::lean_dec_ref(v_a_4857_);
                    crate::leanh::lean_dec_ref(v_a_4856_);
                    crate::leanh::lean_dec_ref(v_a_4855_);
                    v_a_4863_ = crate::leanh::lean_ctor_get(v_x_4861_, 0);
                    v_isSharedCheck_4871_ = (!crate::leanh::lean_is_exclusive(v_x_4861_)) as u8;
                    if v_isSharedCheck_4871_ == 0 {
                        v___x_4865_ = v_x_4861_;
                        v_isShared_4866_ = v_isSharedCheck_4871_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4863_);
                        crate::leanh::lean_dec(v_x_4861_);
                        v___x_4865_ = crate::leanh::lean_box(0);
                        v_isShared_4866_ = v_isSharedCheck_4871_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4872_ = crate::leanh::lean_ctor_get(v_x_4861_, 0);
                    v_isSharedCheck_4889_ = (!crate::leanh::lean_is_exclusive(v_x_4861_)) as u8;
                    if v_isSharedCheck_4889_ == 0 {
                        v___x_4874_ = v_x_4861_;
                        v_isShared_4875_ = v_isSharedCheck_4889_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4872_);
                        crate::leanh::lean_dec(v_x_4861_);
                        v___x_4874_ = crate::leanh::lean_box(0);
                        v_isShared_4875_ = v_isSharedCheck_4889_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4866_ == 0 {
                    v___x_4868_ = v___x_4865_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4870_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4870_, 0, v_a_4863_);
                    v___x_4868_ = v_reuseFailAlloc_4870_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4869_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4869_, 0, v___x_4868_);
                return v___x_4869_;
            }
            3 => {
                crate::leanh::lean_inc_n(v_a_4872_, 2);
                v___f_4876_ = crate::leanh::lean_alloc_closure(
                    l_Std_Async_ContextAsync_race___redArg___lam__5___boxed
                        as *mut core::ffi::c_void,
                    4,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_4876_, 0, v_a_4872_);
                crate::leanh::lean_closure_set(v___f_4876_, 1, v_a_4855_);
                v___x_4877_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4878_ = 0;
                v___x_4879_ =
                    l_BaseIO_chainTask___redArg(v_a_4856_, v___f_4876_, v___x_4877_, v___x_4878_);
                v___f_4880_ = crate::leanh::lean_alloc_closure(
                    l_Std_Async_ContextAsync_race___redArg___lam__5___boxed
                        as *mut core::ffi::c_void,
                    4,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_4880_, 0, v_a_4872_);
                crate::leanh::lean_closure_set(v___f_4880_, 1, v_a_4857_);
                v___f_4881_ = crate::leanh::lean_alloc_closure(
                    l_Std_Async_ContextAsync_raceAll___redArg___lam__13___boxed
                        as *mut core::ffi::c_void,
                    5,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_4881_, 0, v_a_4872_);
                crate::leanh::lean_closure_set(v___f_4881_, 1, v___f_4858_);
                crate::leanh::lean_closure_set(v___f_4881_, 2, v___f_4859_);
                v___x_4882_ = crate::leanh::lean_box((v___x_4878_) as usize);
                v___f_4883_ = crate::leanh::lean_alloc_closure(
                    l_Std_Async_ContextAsync_race___redArg___lam__4___boxed
                        as *mut core::ffi::c_void,
                    7,
                    5,
                );
                crate::leanh::lean_closure_set(v___f_4883_, 0, v_a_4860_);
                crate::leanh::lean_closure_set(v___f_4883_, 1, v___f_4880_);
                crate::leanh::lean_closure_set(v___f_4883_, 2, v___x_4877_);
                crate::leanh::lean_closure_set(v___f_4883_, 3, v___x_4882_);
                crate::leanh::lean_closure_set(v___f_4883_, 4, v___f_4881_);
                if v_isShared_4875_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4874_, 0, v___x_4879_);
                    v___x_4885_ = v___x_4874_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4888_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4888_, 0, v___x_4879_);
                    v___x_4885_ = v_reuseFailAlloc_4888_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4886_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4886_, 0, v___x_4885_);
                v___x_4887_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_4877_,
                    v___x_4878_,
                    v___x_4886_,
                    v___f_4883_,
                );
                return v___x_4887_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_race___redArg___lam__1___boxed(
    mut v_a_4890_: *mut crate::leanh::LeanObject,
    mut v_a_4891_: *mut crate::leanh::LeanObject,
    mut v_a_4892_: *mut crate::leanh::LeanObject,
    mut v___f_4893_: *mut crate::leanh::LeanObject,
    mut v___f_4894_: *mut crate::leanh::LeanObject,
    mut v_a_4895_: *mut crate::leanh::LeanObject,
    mut v_x_4896_: *mut crate::leanh::LeanObject,
    mut v___y_4897_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4898_ = l_Std_Async_ContextAsync_race___redArg___lam__1(
        v_a_4890_,
        v_a_4891_,
        v_a_4892_,
        v___f_4893_,
        v___f_4894_,
        v_a_4895_,
        v_x_4896_,
    );
    return v_res_4898_;
}
pub unsafe fn l_Std_Async_ContextAsync_race___redArg___lam__2(
    mut v_a_4899_: *mut crate::leanh::LeanObject,
    mut v_a_4900_: *mut crate::leanh::LeanObject,
    mut v_a_4901_: *mut crate::leanh::LeanObject,
    mut v___f_4902_: *mut crate::leanh::LeanObject,
    mut v___f_4903_: *mut crate::leanh::LeanObject,
    mut v_x_4904_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_4906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4909_: u8 = 0;
    let mut v___x_4911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4914_: u8 = 0;
    let mut v_a_4915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4918_: u8 = 0;
    let mut v___x_4919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4925_: u8 = 0;
    let mut v___x_4926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4928_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4904_) == 0 {
                    crate::leanh::lean_dec_ref(v___f_4903_);
                    crate::leanh::lean_dec_ref(v___f_4902_);
                    crate::leanh::lean_dec_ref(v_a_4901_);
                    crate::leanh::lean_dec_ref(v_a_4900_);
                    crate::leanh::lean_dec_ref(v_a_4899_);
                    v_a_4906_ = crate::leanh::lean_ctor_get(v_x_4904_, 0);
                    v_isSharedCheck_4914_ = (!crate::leanh::lean_is_exclusive(v_x_4904_)) as u8;
                    if v_isSharedCheck_4914_ == 0 {
                        v___x_4908_ = v_x_4904_;
                        v_isShared_4909_ = v_isSharedCheck_4914_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4906_);
                        crate::leanh::lean_dec(v_x_4904_);
                        v___x_4908_ = crate::leanh::lean_box(0);
                        v_isShared_4909_ = v_isSharedCheck_4914_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4915_ = crate::leanh::lean_ctor_get(v_x_4904_, 0);
                    v_isSharedCheck_4928_ = (!crate::leanh::lean_is_exclusive(v_x_4904_)) as u8;
                    if v_isSharedCheck_4928_ == 0 {
                        v___x_4917_ = v_x_4904_;
                        v_isShared_4918_ = v_isSharedCheck_4928_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4915_);
                        crate::leanh::lean_dec(v_x_4904_);
                        v___x_4917_ = crate::leanh::lean_box(0);
                        v_isShared_4918_ = v_isSharedCheck_4928_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4909_ == 0 {
                    v___x_4911_ = v___x_4908_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4913_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4913_, 0, v_a_4906_);
                    v___x_4911_ = v_reuseFailAlloc_4913_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4912_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4912_, 0, v___x_4911_);
                return v___x_4912_;
            }
            3 => {
                v___x_4919_ = lean_io_promise_new();
                v___f_4920_ = crate::leanh::lean_alloc_closure(
                    l_Std_Async_ContextAsync_race___redArg___lam__1___boxed
                        as *mut core::ffi::c_void,
                    8,
                    6,
                );
                crate::leanh::lean_closure_set(v___f_4920_, 0, v_a_4899_);
                crate::leanh::lean_closure_set(v___f_4920_, 1, v_a_4900_);
                crate::leanh::lean_closure_set(v___f_4920_, 2, v_a_4901_);
                crate::leanh::lean_closure_set(v___f_4920_, 3, v___f_4902_);
                crate::leanh::lean_closure_set(v___f_4920_, 4, v___f_4903_);
                crate::leanh::lean_closure_set(v___f_4920_, 5, v_a_4915_);
                if v_isShared_4918_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4917_, 0, v___x_4919_);
                    v___x_4922_ = v___x_4917_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4927_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4927_, 0, v___x_4919_);
                    v___x_4922_ = v_reuseFailAlloc_4927_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4923_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4923_, 0, v___x_4922_);
                v___x_4924_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4925_ = 0;
                v___x_4926_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_4924_,
                    v___x_4925_,
                    v___x_4923_,
                    v___f_4920_,
                );
                return v___x_4926_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_race___redArg___lam__2___boxed(
    mut v_a_4929_: *mut crate::leanh::LeanObject,
    mut v_a_4930_: *mut crate::leanh::LeanObject,
    mut v_a_4931_: *mut crate::leanh::LeanObject,
    mut v___f_4932_: *mut crate::leanh::LeanObject,
    mut v___f_4933_: *mut crate::leanh::LeanObject,
    mut v_x_4934_: *mut crate::leanh::LeanObject,
    mut v___y_4935_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4936_ = l_Std_Async_ContextAsync_race___redArg___lam__2(
        v_a_4929_,
        v_a_4930_,
        v_a_4931_,
        v___f_4932_,
        v___f_4933_,
        v_x_4934_,
    );
    return v_res_4936_;
}
pub unsafe fn l_Std_Async_ContextAsync_race___redArg___lam__7(
    mut v_a_4937_: *mut crate::leanh::LeanObject,
    mut v___f_4938_: *mut crate::leanh::LeanObject,
    mut v_a_4939_: *mut crate::leanh::LeanObject,
    mut v_a_4940_: *mut crate::leanh::LeanObject,
    mut v___f_4941_: *mut crate::leanh::LeanObject,
    mut v___f_4942_: *mut crate::leanh::LeanObject,
    mut v_x_4943_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_4945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4948_: u8 = 0;
    let mut v___x_4950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4953_: u8 = 0;
    let mut v_a_4954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4957_: u8 = 0;
    let mut v___x_4958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4963_: u8 = 0;
    let mut v___x_4964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4968_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4943_) == 0 {
                    crate::leanh::lean_dec_ref(v___f_4942_);
                    crate::leanh::lean_dec_ref(v___f_4941_);
                    crate::leanh::lean_dec_ref(v_a_4940_);
                    crate::leanh::lean_dec_ref(v_a_4939_);
                    crate::leanh::lean_dec_ref(v___f_4938_);
                    v_a_4945_ = crate::leanh::lean_ctor_get(v_x_4943_, 0);
                    v_isSharedCheck_4953_ = (!crate::leanh::lean_is_exclusive(v_x_4943_)) as u8;
                    if v_isSharedCheck_4953_ == 0 {
                        v___x_4947_ = v_x_4943_;
                        v_isShared_4948_ = v_isSharedCheck_4953_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4945_);
                        crate::leanh::lean_dec(v_x_4943_);
                        v___x_4947_ = crate::leanh::lean_box(0);
                        v_isShared_4948_ = v_isSharedCheck_4953_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4954_ = crate::leanh::lean_ctor_get(v_x_4943_, 0);
                    v_isSharedCheck_4968_ = (!crate::leanh::lean_is_exclusive(v_x_4943_)) as u8;
                    if v_isSharedCheck_4968_ == 0 {
                        v___x_4956_ = v_x_4943_;
                        v_isShared_4957_ = v_isSharedCheck_4968_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4954_);
                        crate::leanh::lean_dec(v_x_4943_);
                        v___x_4956_ = crate::leanh::lean_box(0);
                        v_isShared_4957_ = v_isSharedCheck_4968_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4948_ == 0 {
                    v___x_4950_ = v___x_4947_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4952_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4952_, 0, v_a_4945_);
                    v___x_4950_ = v_reuseFailAlloc_4952_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4951_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4951_, 0, v___x_4950_);
                return v___x_4951_;
            }
            3 => {
                crate::leanh::lean_inc_ref(v_a_4937_);
                v___x_4958_ = l_Std_CancellationContext_fork(v_a_4937_);
                if v_isShared_4957_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4956_, 0, v___x_4958_);
                    v___x_4960_ = v___x_4956_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4967_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4967_, 0, v___x_4958_);
                    v___x_4960_ = v_reuseFailAlloc_4967_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4961_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4961_, 0, v___x_4960_);
                v___x_4962_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4963_ = 0;
                v___x_4964_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_4962_,
                    v___x_4963_,
                    v___x_4961_,
                    v___f_4938_,
                );
                v___f_4965_ = crate::leanh::lean_alloc_closure(
                    l_Std_Async_ContextAsync_race___redArg___lam__2___boxed
                        as *mut core::ffi::c_void,
                    7,
                    5,
                );
                crate::leanh::lean_closure_set(v___f_4965_, 0, v_a_4939_);
                crate::leanh::lean_closure_set(v___f_4965_, 1, v_a_4954_);
                crate::leanh::lean_closure_set(v___f_4965_, 2, v_a_4940_);
                crate::leanh::lean_closure_set(v___f_4965_, 3, v___f_4941_);
                crate::leanh::lean_closure_set(v___f_4965_, 4, v___f_4942_);
                v___x_4966_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_4962_,
                    v___x_4963_,
                    v___x_4964_,
                    v___f_4965_,
                );
                return v___x_4966_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_race___redArg___lam__7___boxed(
    mut v_a_4969_: *mut crate::leanh::LeanObject,
    mut v___f_4970_: *mut crate::leanh::LeanObject,
    mut v_a_4971_: *mut crate::leanh::LeanObject,
    mut v_a_4972_: *mut crate::leanh::LeanObject,
    mut v___f_4973_: *mut crate::leanh::LeanObject,
    mut v___f_4974_: *mut crate::leanh::LeanObject,
    mut v_x_4975_: *mut crate::leanh::LeanObject,
    mut v___y_4976_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4977_ = l_Std_Async_ContextAsync_race___redArg___lam__7(
        v_a_4969_,
        v___f_4970_,
        v_a_4971_,
        v_a_4972_,
        v___f_4973_,
        v___f_4974_,
        v_x_4975_,
    );
    crate::leanh::lean_dec_ref(v_a_4969_);
    return v_res_4977_;
}
pub unsafe fn l_Std_Async_ContextAsync_race___redArg___lam__8(
    mut v_a_4978_: *mut crate::leanh::LeanObject,
    mut v___f_4979_: *mut crate::leanh::LeanObject,
    mut v_y_4980_: *mut crate::leanh::LeanObject,
    mut v___f_4981_: *mut crate::leanh::LeanObject,
    mut v_prio_4982_: *mut crate::leanh::LeanObject,
    mut v___f_4983_: *mut crate::leanh::LeanObject,
    mut v_a_4984_: *mut crate::leanh::LeanObject,
    mut v___f_4985_: *mut crate::leanh::LeanObject,
    mut v___f_4986_: *mut crate::leanh::LeanObject,
    mut v_x_4987_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_4989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4992_: u8 = 0;
    let mut v___x_4994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4997_: u8 = 0;
    let mut v_a_4998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5001_: u8 = 0;
    let mut v___x_5002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5007_: u8 = 0;
    let mut v___x_5008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5014_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4987_) == 0 {
                    crate::leanh::lean_dec_ref(v___f_4986_);
                    crate::leanh::lean_dec_ref(v___f_4985_);
                    crate::leanh::lean_dec_ref(v_a_4984_);
                    crate::leanh::lean_dec_ref(v___f_4983_);
                    crate::leanh::lean_dec(v_prio_4982_);
                    crate::leanh::lean_dec(v___f_4981_);
                    crate::leanh::lean_dec_ref(v_y_4980_);
                    crate::leanh::lean_dec_ref(v___f_4979_);
                    v_a_4989_ = crate::leanh::lean_ctor_get(v_x_4987_, 0);
                    v_isSharedCheck_4997_ = (!crate::leanh::lean_is_exclusive(v_x_4987_)) as u8;
                    if v_isSharedCheck_4997_ == 0 {
                        v___x_4991_ = v_x_4987_;
                        v_isShared_4992_ = v_isSharedCheck_4997_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4989_);
                        crate::leanh::lean_dec(v_x_4987_);
                        v___x_4991_ = crate::leanh::lean_box(0);
                        v_isShared_4992_ = v_isSharedCheck_4997_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4998_ = crate::leanh::lean_ctor_get(v_x_4987_, 0);
                    v_isSharedCheck_5014_ = (!crate::leanh::lean_is_exclusive(v_x_4987_)) as u8;
                    if v_isSharedCheck_5014_ == 0 {
                        v___x_5000_ = v_x_4987_;
                        v_isShared_5001_ = v_isSharedCheck_5014_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4998_);
                        crate::leanh::lean_dec(v_x_4987_);
                        v___x_5000_ = crate::leanh::lean_box(0);
                        v_isShared_5001_ = v_isSharedCheck_5014_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4992_ == 0 {
                    v___x_4994_ = v___x_4991_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4996_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4996_, 0, v_a_4989_);
                    v___x_4994_ = v_reuseFailAlloc_4996_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4995_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4995_, 0, v___x_4994_);
                return v___x_4995_;
            }
            3 => {
                crate::leanh::lean_inc_ref(v_a_4978_);
                v___x_5002_ = l_Std_CancellationContext_fork(v_a_4978_);
                if v_isShared_5001_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5000_, 0, v___x_5002_);
                    v___x_5004_ = v___x_5000_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5013_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5013_, 0, v___x_5002_);
                    v___x_5004_ = v_reuseFailAlloc_5013_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5005_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5005_, 0, v___x_5004_);
                v___x_5006_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5007_ = 0;
                v___x_5008_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_5006_,
                    v___x_5007_,
                    v___x_5005_,
                    v___f_4979_,
                );
                crate::leanh::lean_inc(v_a_4998_);
                v___f_5009_ = crate::leanh::lean_alloc_closure(
                    l_Std_Async_ContextAsync_race___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_5009_, 0, v_y_4980_);
                crate::leanh::lean_closure_set(v___f_5009_, 1, v_a_4998_);
                v___f_5010_ = crate::leanh::lean_alloc_closure(
                    l_Std_Async_ContextAsync_race___redArg___lam__6___boxed
                        as *mut core::ffi::c_void,
                    6,
                    4,
                );
                crate::leanh::lean_closure_set(v___f_5010_, 0, v___f_5009_);
                crate::leanh::lean_closure_set(v___f_5010_, 1, v___f_4981_);
                crate::leanh::lean_closure_set(v___f_5010_, 2, v_prio_4982_);
                crate::leanh::lean_closure_set(v___f_5010_, 3, v___f_4983_);
                crate::leanh::lean_inc_ref(v_a_4978_);
                v___f_5011_ = crate::leanh::lean_alloc_closure(
                    l_Std_Async_ContextAsync_race___redArg___lam__7___boxed
                        as *mut core::ffi::c_void,
                    8,
                    6,
                );
                crate::leanh::lean_closure_set(v___f_5011_, 0, v_a_4978_);
                crate::leanh::lean_closure_set(v___f_5011_, 1, v___f_5010_);
                crate::leanh::lean_closure_set(v___f_5011_, 2, v_a_4998_);
                crate::leanh::lean_closure_set(v___f_5011_, 3, v_a_4984_);
                crate::leanh::lean_closure_set(v___f_5011_, 4, v___f_4985_);
                crate::leanh::lean_closure_set(v___f_5011_, 5, v___f_4986_);
                v___x_5012_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_5006_,
                    v___x_5007_,
                    v___x_5008_,
                    v___f_5011_,
                );
                return v___x_5012_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_race___redArg___lam__8___boxed(
    mut v_a_5015_: *mut crate::leanh::LeanObject,
    mut v___f_5016_: *mut crate::leanh::LeanObject,
    mut v_y_5017_: *mut crate::leanh::LeanObject,
    mut v___f_5018_: *mut crate::leanh::LeanObject,
    mut v_prio_5019_: *mut crate::leanh::LeanObject,
    mut v___f_5020_: *mut crate::leanh::LeanObject,
    mut v_a_5021_: *mut crate::leanh::LeanObject,
    mut v___f_5022_: *mut crate::leanh::LeanObject,
    mut v___f_5023_: *mut crate::leanh::LeanObject,
    mut v_x_5024_: *mut crate::leanh::LeanObject,
    mut v___y_5025_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5026_ = l_Std_Async_ContextAsync_race___redArg___lam__8(
        v_a_5015_,
        v___f_5016_,
        v_y_5017_,
        v___f_5018_,
        v_prio_5019_,
        v___f_5020_,
        v_a_5021_,
        v___f_5022_,
        v___f_5023_,
        v_x_5024_,
    );
    crate::leanh::lean_dec_ref(v_a_5015_);
    return v_res_5026_;
}
pub unsafe fn l_Std_Async_ContextAsync_race___redArg___lam__9(
    mut v_a_5027_: *mut crate::leanh::LeanObject,
    mut v_x_5028_: *mut crate::leanh::LeanObject,
    mut v___f_5029_: *mut crate::leanh::LeanObject,
    mut v_prio_5030_: *mut crate::leanh::LeanObject,
    mut v___f_5031_: *mut crate::leanh::LeanObject,
    mut v_a_5032_: *mut crate::leanh::LeanObject,
    mut v_y_5033_: *mut crate::leanh::LeanObject,
    mut v___f_5034_: *mut crate::leanh::LeanObject,
    mut v___f_5035_: *mut crate::leanh::LeanObject,
    mut v___f_5036_: *mut crate::leanh::LeanObject,
    mut v___f_5037_: *mut crate::leanh::LeanObject,
    mut v_x_5038_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_5040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5043_: u8 = 0;
    let mut v___x_5045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5048_: u8 = 0;
    let mut v_a_5049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5052_: u8 = 0;
    let mut v___x_5053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5061_: u8 = 0;
    let mut v___x_5062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5064_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5038_) == 0 {
                    crate::leanh::lean_dec_ref(v___f_5037_);
                    crate::leanh::lean_dec_ref(v___f_5036_);
                    crate::leanh::lean_dec_ref(v___f_5035_);
                    crate::leanh::lean_dec(v___f_5034_);
                    crate::leanh::lean_dec_ref(v_y_5033_);
                    crate::leanh::lean_dec_ref(v___f_5031_);
                    crate::leanh::lean_dec(v_prio_5030_);
                    crate::leanh::lean_dec(v___f_5029_);
                    crate::leanh::lean_dec_ref(v_x_5028_);
                    crate::leanh::lean_dec_ref(v_a_5027_);
                    v_a_5040_ = crate::leanh::lean_ctor_get(v_x_5038_, 0);
                    v_isSharedCheck_5048_ = (!crate::leanh::lean_is_exclusive(v_x_5038_)) as u8;
                    if v_isSharedCheck_5048_ == 0 {
                        v___x_5042_ = v_x_5038_;
                        v_isShared_5043_ = v_isSharedCheck_5048_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5040_);
                        crate::leanh::lean_dec(v_x_5038_);
                        v___x_5042_ = crate::leanh::lean_box(0);
                        v_isShared_5043_ = v_isSharedCheck_5048_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5049_ = crate::leanh::lean_ctor_get(v_x_5038_, 0);
                    v_isSharedCheck_5064_ = (!crate::leanh::lean_is_exclusive(v_x_5038_)) as u8;
                    if v_isSharedCheck_5064_ == 0 {
                        v___x_5051_ = v_x_5038_;
                        v_isShared_5052_ = v_isSharedCheck_5064_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5049_);
                        crate::leanh::lean_dec(v_x_5038_);
                        v___x_5051_ = crate::leanh::lean_box(0);
                        v_isShared_5052_ = v_isSharedCheck_5064_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5043_ == 0 {
                    v___x_5045_ = v___x_5042_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5047_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5047_, 0, v_a_5040_);
                    v___x_5045_ = v_reuseFailAlloc_5047_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5046_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5046_, 0, v___x_5045_);
                return v___x_5046_;
            }
            3 => {
                v___x_5053_ = l_Std_CancellationContext_fork(v_a_5027_);
                crate::leanh::lean_inc(v_a_5049_);
                v___f_5054_ = crate::leanh::lean_alloc_closure(
                    l_Std_Async_ContextAsync_raceAll___redArg___lam__10___boxed
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_5054_, 0, v_x_5028_);
                crate::leanh::lean_closure_set(v___f_5054_, 1, v_a_5049_);
                crate::leanh::lean_inc(v_prio_5030_);
                v___f_5055_ = crate::leanh::lean_alloc_closure(
                    l_Std_Async_ContextAsync_race___redArg___lam__6___boxed
                        as *mut core::ffi::c_void,
                    6,
                    4,
                );
                crate::leanh::lean_closure_set(v___f_5055_, 0, v___f_5054_);
                crate::leanh::lean_closure_set(v___f_5055_, 1, v___f_5029_);
                crate::leanh::lean_closure_set(v___f_5055_, 2, v_prio_5030_);
                crate::leanh::lean_closure_set(v___f_5055_, 3, v___f_5031_);
                crate::leanh::lean_inc_ref(v_a_5032_);
                v___f_5056_ = crate::leanh::lean_alloc_closure(
                    l_Std_Async_ContextAsync_race___redArg___lam__8___boxed
                        as *mut core::ffi::c_void,
                    11,
                    9,
                );
                crate::leanh::lean_closure_set(v___f_5056_, 0, v_a_5032_);
                crate::leanh::lean_closure_set(v___f_5056_, 1, v___f_5055_);
                crate::leanh::lean_closure_set(v___f_5056_, 2, v_y_5033_);
                crate::leanh::lean_closure_set(v___f_5056_, 3, v___f_5034_);
                crate::leanh::lean_closure_set(v___f_5056_, 4, v_prio_5030_);
                crate::leanh::lean_closure_set(v___f_5056_, 5, v___f_5035_);
                crate::leanh::lean_closure_set(v___f_5056_, 6, v_a_5049_);
                crate::leanh::lean_closure_set(v___f_5056_, 7, v___f_5036_);
                crate::leanh::lean_closure_set(v___f_5056_, 8, v___f_5037_);
                if v_isShared_5052_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5051_, 0, v___x_5053_);
                    v___x_5058_ = v___x_5051_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5063_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5063_, 0, v___x_5053_);
                    v___x_5058_ = v_reuseFailAlloc_5063_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5059_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5059_, 0, v___x_5058_);
                v___x_5060_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5061_ = 0;
                v___x_5062_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_5060_,
                    v___x_5061_,
                    v___x_5059_,
                    v___f_5056_,
                );
                return v___x_5062_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_race___redArg___lam__9___boxed(
    mut v_a_5065_: *mut crate::leanh::LeanObject,
    mut v_x_5066_: *mut crate::leanh::LeanObject,
    mut v___f_5067_: *mut crate::leanh::LeanObject,
    mut v_prio_5068_: *mut crate::leanh::LeanObject,
    mut v___f_5069_: *mut crate::leanh::LeanObject,
    mut v_a_5070_: *mut crate::leanh::LeanObject,
    mut v_y_5071_: *mut crate::leanh::LeanObject,
    mut v___f_5072_: *mut crate::leanh::LeanObject,
    mut v___f_5073_: *mut crate::leanh::LeanObject,
    mut v___f_5074_: *mut crate::leanh::LeanObject,
    mut v___f_5075_: *mut crate::leanh::LeanObject,
    mut v_x_5076_: *mut crate::leanh::LeanObject,
    mut v___y_5077_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5078_ = l_Std_Async_ContextAsync_race___redArg___lam__9(
        v_a_5065_,
        v_x_5066_,
        v___f_5067_,
        v_prio_5068_,
        v___f_5069_,
        v_a_5070_,
        v_y_5071_,
        v___f_5072_,
        v___f_5073_,
        v___f_5074_,
        v___f_5075_,
        v_x_5076_,
    );
    crate::leanh::lean_dec_ref(v_a_5070_);
    return v_res_5078_;
}
pub unsafe fn l_Std_Async_ContextAsync_race___redArg___lam__10(
    mut v_x_5079_: *mut crate::leanh::LeanObject,
    mut v___f_5080_: *mut crate::leanh::LeanObject,
    mut v_prio_5081_: *mut crate::leanh::LeanObject,
    mut v___f_5082_: *mut crate::leanh::LeanObject,
    mut v_a_5083_: *mut crate::leanh::LeanObject,
    mut v_y_5084_: *mut crate::leanh::LeanObject,
    mut v___f_5085_: *mut crate::leanh::LeanObject,
    mut v___f_5086_: *mut crate::leanh::LeanObject,
    mut v___f_5087_: *mut crate::leanh::LeanObject,
    mut v___f_5088_: *mut crate::leanh::LeanObject,
    mut v_x_5089_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_5091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5094_: u8 = 0;
    let mut v___x_5096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5099_: u8 = 0;
    let mut v_a_5100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5103_: u8 = 0;
    let mut v___x_5104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5110_: u8 = 0;
    let mut v___x_5111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5113_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5089_) == 0 {
                    crate::leanh::lean_dec_ref(v___f_5088_);
                    crate::leanh::lean_dec_ref(v___f_5087_);
                    crate::leanh::lean_dec_ref(v___f_5086_);
                    crate::leanh::lean_dec(v___f_5085_);
                    crate::leanh::lean_dec_ref(v_y_5084_);
                    crate::leanh::lean_dec_ref(v___f_5082_);
                    crate::leanh::lean_dec(v_prio_5081_);
                    crate::leanh::lean_dec(v___f_5080_);
                    crate::leanh::lean_dec_ref(v_x_5079_);
                    v_a_5091_ = crate::leanh::lean_ctor_get(v_x_5089_, 0);
                    v_isSharedCheck_5099_ = (!crate::leanh::lean_is_exclusive(v_x_5089_)) as u8;
                    if v_isSharedCheck_5099_ == 0 {
                        v___x_5093_ = v_x_5089_;
                        v_isShared_5094_ = v_isSharedCheck_5099_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5091_);
                        crate::leanh::lean_dec(v_x_5089_);
                        v___x_5093_ = crate::leanh::lean_box(0);
                        v_isShared_5094_ = v_isSharedCheck_5099_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5100_ = crate::leanh::lean_ctor_get(v_x_5089_, 0);
                    v_isSharedCheck_5113_ = (!crate::leanh::lean_is_exclusive(v_x_5089_)) as u8;
                    if v_isSharedCheck_5113_ == 0 {
                        v___x_5102_ = v_x_5089_;
                        v_isShared_5103_ = v_isSharedCheck_5113_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5100_);
                        crate::leanh::lean_dec(v_x_5089_);
                        v___x_5102_ = crate::leanh::lean_box(0);
                        v_isShared_5103_ = v_isSharedCheck_5113_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5094_ == 0 {
                    v___x_5096_ = v___x_5093_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5098_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5098_, 0, v_a_5091_);
                    v___x_5096_ = v_reuseFailAlloc_5098_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5097_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5097_, 0, v___x_5096_);
                return v___x_5097_;
            }
            3 => {
                crate::leanh::lean_inc(v_a_5100_);
                v___x_5104_ = l_Std_CancellationContext_fork(v_a_5100_);
                crate::leanh::lean_inc_ref(v_a_5083_);
                v___f_5105_ = crate::leanh::lean_alloc_closure(
                    l_Std_Async_ContextAsync_race___redArg___lam__9___boxed
                        as *mut core::ffi::c_void,
                    13,
                    11,
                );
                crate::leanh::lean_closure_set(v___f_5105_, 0, v_a_5100_);
                crate::leanh::lean_closure_set(v___f_5105_, 1, v_x_5079_);
                crate::leanh::lean_closure_set(v___f_5105_, 2, v___f_5080_);
                crate::leanh::lean_closure_set(v___f_5105_, 3, v_prio_5081_);
                crate::leanh::lean_closure_set(v___f_5105_, 4, v___f_5082_);
                crate::leanh::lean_closure_set(v___f_5105_, 5, v_a_5083_);
                crate::leanh::lean_closure_set(v___f_5105_, 6, v_y_5084_);
                crate::leanh::lean_closure_set(v___f_5105_, 7, v___f_5085_);
                crate::leanh::lean_closure_set(v___f_5105_, 8, v___f_5086_);
                crate::leanh::lean_closure_set(v___f_5105_, 9, v___f_5087_);
                crate::leanh::lean_closure_set(v___f_5105_, 10, v___f_5088_);
                if v_isShared_5103_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5102_, 0, v___x_5104_);
                    v___x_5107_ = v___x_5102_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5112_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5112_, 0, v___x_5104_);
                    v___x_5107_ = v_reuseFailAlloc_5112_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5108_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5108_, 0, v___x_5107_);
                v___x_5109_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5110_ = 0;
                v___x_5111_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_5109_,
                    v___x_5110_,
                    v___x_5108_,
                    v___f_5105_,
                );
                return v___x_5111_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_race___redArg___lam__10___boxed(
    mut v_x_5114_: *mut crate::leanh::LeanObject,
    mut v___f_5115_: *mut crate::leanh::LeanObject,
    mut v_prio_5116_: *mut crate::leanh::LeanObject,
    mut v___f_5117_: *mut crate::leanh::LeanObject,
    mut v_a_5118_: *mut crate::leanh::LeanObject,
    mut v_y_5119_: *mut crate::leanh::LeanObject,
    mut v___f_5120_: *mut crate::leanh::LeanObject,
    mut v___f_5121_: *mut crate::leanh::LeanObject,
    mut v___f_5122_: *mut crate::leanh::LeanObject,
    mut v___f_5123_: *mut crate::leanh::LeanObject,
    mut v_x_5124_: *mut crate::leanh::LeanObject,
    mut v___y_5125_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5126_ = l_Std_Async_ContextAsync_race___redArg___lam__10(
        v_x_5114_,
        v___f_5115_,
        v_prio_5116_,
        v___f_5117_,
        v_a_5118_,
        v_y_5119_,
        v___f_5120_,
        v___f_5121_,
        v___f_5122_,
        v___f_5123_,
        v_x_5124_,
    );
    crate::leanh::lean_dec_ref(v_a_5118_);
    return v_res_5126_;
}
pub unsafe fn l_Std_Async_ContextAsync_race___redArg(
    mut v_x_5128_: *mut crate::leanh::LeanObject,
    mut v_y_5129_: *mut crate::leanh::LeanObject,
    mut v_prio_5130_: *mut crate::leanh::LeanObject,
    mut v_a_5131_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5141_: u8 = 0;
    let mut v___x_5142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5133_ = l_Std_Async_ContextAsync_concurrently___redArg___closed__1;
    v___f_5134_ = l_Std_Async_ContextAsync_concurrently___redArg___closed__0;
    v___f_5135_ = l_Std_Async_ContextAsync_raceAll___redArg___closed__0;
    v___f_5136_ = l_Std_Async_ContextAsync_race___redArg___closed__0;
    crate::leanh::lean_inc_ref_n(v_a_5131_, 2);
    v___f_5137_ = crate::leanh::lean_alloc_closure(
        l_Std_Async_ContextAsync_race___redArg___lam__10___boxed as *mut core::ffi::c_void,
        12,
        10,
    );
    crate::leanh::lean_closure_set(v___f_5137_, 0, v_x_5128_);
    crate::leanh::lean_closure_set(v___f_5137_, 1, v___f_5133_);
    crate::leanh::lean_closure_set(v___f_5137_, 2, v_prio_5130_);
    crate::leanh::lean_closure_set(v___f_5137_, 3, v___f_5134_);
    crate::leanh::lean_closure_set(v___f_5137_, 4, v_a_5131_);
    crate::leanh::lean_closure_set(v___f_5137_, 5, v_y_5129_);
    crate::leanh::lean_closure_set(v___f_5137_, 6, v___f_5133_);
    crate::leanh::lean_closure_set(v___f_5137_, 7, v___f_5134_);
    crate::leanh::lean_closure_set(v___f_5137_, 8, v___f_5135_);
    crate::leanh::lean_closure_set(v___f_5137_, 9, v___f_5136_);
    v___x_5138_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5138_, 0, v_a_5131_);
    v___x_5139_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5139_, 0, v___x_5138_);
    v___x_5140_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5141_ = 0;
    v___x_5142_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_5140_,
        v___x_5141_,
        v___x_5139_,
        v___f_5137_,
    );
    return v___x_5142_;
}
pub unsafe fn l_Std_Async_ContextAsync_race___redArg___boxed(
    mut v_x_5143_: *mut crate::leanh::LeanObject,
    mut v_y_5144_: *mut crate::leanh::LeanObject,
    mut v_prio_5145_: *mut crate::leanh::LeanObject,
    mut v_a_5146_: *mut crate::leanh::LeanObject,
    mut v_a_5147_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5148_ =
        l_Std_Async_ContextAsync_race___redArg(v_x_5143_, v_y_5144_, v_prio_5145_, v_a_5146_);
    crate::leanh::lean_dec_ref(v_a_5146_);
    return v_res_5148_;
}
pub unsafe fn l_Std_Async_ContextAsync_race(
    mut v_00_u03b1_5149_: *mut crate::leanh::LeanObject,
    mut v_inst_5150_: *mut crate::leanh::LeanObject,
    mut v_x_5151_: *mut crate::leanh::LeanObject,
    mut v_y_5152_: *mut crate::leanh::LeanObject,
    mut v_prio_5153_: *mut crate::leanh::LeanObject,
    mut v_a_5154_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5164_: u8 = 0;
    let mut v___x_5165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5156_ = l_Std_Async_ContextAsync_concurrently___redArg___closed__1;
    v___f_5157_ = l_Std_Async_ContextAsync_concurrently___redArg___closed__0;
    v___f_5158_ = l_Std_Async_ContextAsync_raceAll___redArg___closed__0;
    v___f_5159_ = l_Std_Async_ContextAsync_race___redArg___closed__0;
    crate::leanh::lean_inc_ref_n(v_a_5154_, 2);
    v___f_5160_ = crate::leanh::lean_alloc_closure(
        l_Std_Async_ContextAsync_race___redArg___lam__10___boxed as *mut core::ffi::c_void,
        12,
        10,
    );
    crate::leanh::lean_closure_set(v___f_5160_, 0, v_x_5151_);
    crate::leanh::lean_closure_set(v___f_5160_, 1, v___f_5156_);
    crate::leanh::lean_closure_set(v___f_5160_, 2, v_prio_5153_);
    crate::leanh::lean_closure_set(v___f_5160_, 3, v___f_5157_);
    crate::leanh::lean_closure_set(v___f_5160_, 4, v_a_5154_);
    crate::leanh::lean_closure_set(v___f_5160_, 5, v_y_5152_);
    crate::leanh::lean_closure_set(v___f_5160_, 6, v___f_5156_);
    crate::leanh::lean_closure_set(v___f_5160_, 7, v___f_5157_);
    crate::leanh::lean_closure_set(v___f_5160_, 8, v___f_5158_);
    crate::leanh::lean_closure_set(v___f_5160_, 9, v___f_5159_);
    v___x_5161_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5161_, 0, v_a_5154_);
    v___x_5162_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5162_, 0, v___x_5161_);
    v___x_5163_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5164_ = 0;
    v___x_5165_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_5163_,
        v___x_5164_,
        v___x_5162_,
        v___f_5160_,
    );
    return v___x_5165_;
}
pub unsafe fn l_Std_Async_ContextAsync_race___boxed(
    mut v_00_u03b1_5166_: *mut crate::leanh::LeanObject,
    mut v_inst_5167_: *mut crate::leanh::LeanObject,
    mut v_x_5168_: *mut crate::leanh::LeanObject,
    mut v_y_5169_: *mut crate::leanh::LeanObject,
    mut v_prio_5170_: *mut crate::leanh::LeanObject,
    mut v_a_5171_: *mut crate::leanh::LeanObject,
    mut v_a_5172_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5173_ = l_Std_Async_ContextAsync_race(
        v_00_u03b1_5166_,
        v_inst_5167_,
        v_x_5168_,
        v_y_5169_,
        v_prio_5170_,
        v_a_5171_,
    );
    crate::leanh::lean_dec_ref(v_a_5171_);
    crate::leanh::lean_dec(v_inst_5167_);
    return v_res_5173_;
}
pub unsafe fn l_Std_Async_Selector_cancelled(
    mut v_a_5174_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5180_: u8 = 0;
    let mut v___x_5181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5176_ = l_Std_Async_ContextAsync_doneSelector___closed__0;
    crate::leanh::lean_inc_ref(v_a_5174_);
    v___x_5177_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5177_, 0, v_a_5174_);
    v___x_5178_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5178_, 0, v___x_5177_);
    v___x_5179_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5180_ = 0;
    v___x_5181_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_5179_,
        v___x_5180_,
        v___x_5178_,
        v___f_5176_,
    );
    return v___x_5181_;
}
pub unsafe fn l_Std_Async_Selector_cancelled___boxed(
    mut v_a_5182_: *mut crate::leanh::LeanObject,
    mut v_a_5183_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5184_ = l_Std_Async_Selector_cancelled(v_a_5182_);
    crate::leanh::lean_dec_ref(v_a_5182_);
    return v_res_5184_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Async_ContextAsync(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Internal_UV(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Async_Timer(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Sync_CancellationContext(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Std_Async_ContextAsync_instMonad = _init_l_Std_Async_ContextAsync_instMonad();
    crate::leanh::lean_mark_persistent(l_Std_Async_ContextAsync_instMonad);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Async_ContextAsync(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Async_ContextAsync(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Internal_UV(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Async_Timer(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Sync_CancellationContext(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Async_ContextAsync(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Async_ContextAsync(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Async_ContextAsync(builtin);
}
