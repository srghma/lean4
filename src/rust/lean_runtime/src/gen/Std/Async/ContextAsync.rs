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
use crate::lean_imports_rs::Init::Core::{lean_task_bind, lean_task_map, lean_task_pure};
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_array_size;
use crate::lean_imports_rs::Init::System::IO::lean_io_as_task;
use crate::lean_imports_rs::Init::System::Promise::{lean_io_promise_new, lean_io_promise_resolve};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_apply_4, lean_apply_6, lean_box, lean_closure_set,
    lean_ctor_get, lean_ctor_set, lean_ctor_set_tag, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent, lean_obj_once, lean_obj_tag,
    lean_unbox, lean_unsigned_to_nat,
};
pub static l_Std_Async_ContextAsync_isCancelled___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Async_ContextAsync_isCancelled___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_ContextAsync_isCancelled___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_ContextAsync_isCancelled___closed__0_value) as *mut LeanObject;
pub static l_Std_Async_ContextAsync_getCancellationReason___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Async_ContextAsync_getCancellationReason___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_ContextAsync_getCancellationReason___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_ContextAsync_getCancellationReason___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Async_ContextAsync_doneSelector___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Async_ContextAsync_doneSelector___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_ContextAsync_doneSelector___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_ContextAsync_doneSelector___closed__0_value) as *mut LeanObject;
pub static l_Std_Async_ContextAsync_awaitCancellation___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Async_ContextAsync_awaitCancellation___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_ContextAsync_awaitCancellation___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_ContextAsync_awaitCancellation___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Async_ContextAsync_awaitCancellation___closed__1_value: LeanClosureObject<1> =
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
        m_fun: l_Std_Async_ContextAsync_awaitCancellation___lam__1___boxed
            as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_ContextAsync_awaitCancellation___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Async_ContextAsync_awaitCancellation___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_ContextAsync_awaitCancellation___closed__1_value)
        as *mut LeanObject;
pub static l_Std_Async_ContextAsync_concurrently___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Async_ContextAsync_concurrently___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_ContextAsync_concurrently___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_ContextAsync_concurrently___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Async_ContextAsync_concurrently___redArg___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Async_ContextAsync_concurrently___redArg___lam__2___boxed
            as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_ContextAsync_concurrently___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_ContextAsync_concurrently___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__0_value: LeanClosureObject<
    0,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__0_value)
        as *mut LeanObject;
static mut l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Async_ContextAsync_background___redArg___lam__2___closed__0_value: LeanCtorObject<
    1,
> = LeanCtorObject {
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
static mut l_Std_Async_ContextAsync_background___redArg___lam__2___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_ContextAsync_background___redArg___lam__2___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Async_ContextAsync_background___redArg___lam__2___closed__1_value: LeanCtorObject<
    1,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Async_ContextAsync_background___redArg___lam__2___closed__0_value
    ) as *mut LeanObject],
};
static mut l_Std_Async_ContextAsync_background___redArg___lam__2___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_ContextAsync_background___redArg___lam__2___closed__1_value)
        as *mut LeanObject;
pub static l_Std_Async_ContextAsync_raceAll___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Async_ContextAsync_raceAll___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_ContextAsync_raceAll___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_ContextAsync_raceAll___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Async_ContextAsync_instMonadAsyncAsyncTask___closed__0_value: LeanClosureObject<
    2,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Async_ContextAsync_instMonadAsyncAsyncTask___lam__5___boxed
        as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Std_Async_ContextAsync_concurrently___redArg___closed__1_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Async_ContextAsync_concurrently___redArg___closed__0_value)
            as *mut LeanObject,
    ],
};
static mut l_Std_Async_ContextAsync_instMonadAsyncAsyncTask___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_ContextAsync_instMonadAsyncAsyncTask___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Async_ContextAsync_instMonadAsyncAsyncTask: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_ContextAsync_instMonadAsyncAsyncTask___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Async_ContextAsync_instFunctor___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Async_ContextAsync_instFunctor___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_ContextAsync_instFunctor___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_ContextAsync_instFunctor___closed__0_value) as *mut LeanObject;
pub static l_Std_Async_ContextAsync_instFunctor___closed__1_value: LeanClosureObject<1> =
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
        m_fun: l_Std_Async_ContextAsync_instFunctor___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_ContextAsync_instFunctor___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Async_ContextAsync_instFunctor___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_ContextAsync_instFunctor___closed__1_value) as *mut LeanObject;
pub static l_Std_Async_ContextAsync_instFunctor___closed__2_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_ContextAsync_instFunctor___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Async_ContextAsync_instFunctor___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Async_ContextAsync_instFunctor___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_ContextAsync_instFunctor___closed__2_value) as *mut LeanObject;
pub static mut l_Std_Async_ContextAsync_instFunctor: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_ContextAsync_instFunctor___closed__2_value) as *mut LeanObject;
pub static l_Std_Async_ContextAsync_instMonad___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Async_ContextAsync_instMonad___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_ContextAsync_instMonad___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_ContextAsync_instMonad___closed__0_value) as *mut LeanObject;
pub static l_Std_Async_ContextAsync_instMonad___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Async_ContextAsync_instMonad___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_ContextAsync_instMonad___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_ContextAsync_instMonad___closed__1_value) as *mut LeanObject;
pub static mut l_Std_Async_ContextAsync_instMonad: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Async_ContextAsync_instMonadLiftIO___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Async_ContextAsync_instMonadLiftIO___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_ContextAsync_instMonadLiftIO___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_ContextAsync_instMonadLiftIO___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Async_ContextAsync_instMonadLiftIO___closed__1_value: LeanClosureObject<1> =
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
        m_fun: l_Std_Async_ContextAsync_instMonadLiftIO___lam__1___boxed
            as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_ContextAsync_instMonadLiftIO___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Async_ContextAsync_instMonadLiftIO___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_ContextAsync_instMonadLiftIO___closed__1_value)
        as *mut LeanObject;
pub static l_Std_Async_ContextAsync_instMonadLiftIO___closed__2_value: LeanClosureObject<1> =
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
        m_fun: l_Std_Async_ContextAsync_instMonadLiftIO___lam__2___boxed
            as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_ContextAsync_instMonadLiftIO___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Async_ContextAsync_instMonadLiftIO___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_ContextAsync_instMonadLiftIO___closed__2_value)
        as *mut LeanObject;
pub static mut l_Std_Async_ContextAsync_instMonadLiftIO: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_ContextAsync_instMonadLiftIO___closed__2_value)
        as *mut LeanObject;
pub static l_Std_Async_ContextAsync_instMonadLiftBaseIO___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Async_ContextAsync_instMonadLiftBaseIO___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_ContextAsync_instMonadLiftBaseIO___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_ContextAsync_instMonadLiftBaseIO___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Async_ContextAsync_instMonadLiftBaseIO: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_ContextAsync_instMonadLiftBaseIO___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Async_ContextAsync_instMonadExceptError___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Async_ContextAsync_instMonadExceptError___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_ContextAsync_instMonadExceptError___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_ContextAsync_instMonadExceptError___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Async_ContextAsync_instMonadExceptError___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Async_ContextAsync_instMonadExceptError___lam__2___boxed
            as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_ContextAsync_instMonadExceptError___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_ContextAsync_instMonadExceptError___closed__1_value)
        as *mut LeanObject;
pub static l_Std_Async_ContextAsync_instMonadExceptError___closed__2_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_ContextAsync_instMonadExceptError___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Async_ContextAsync_instMonadExceptError___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Async_ContextAsync_instMonadExceptError___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_ContextAsync_instMonadExceptError___closed__2_value)
        as *mut LeanObject;
pub static mut l_Std_Async_ContextAsync_instMonadExceptError: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_ContextAsync_instMonadExceptError___closed__2_value)
        as *mut LeanObject;
pub static l_Std_Async_ContextAsync_instMonadFinally___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Async_ContextAsync_instMonadFinally___lam__1___boxed
            as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_ContextAsync_instMonadFinally___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_ContextAsync_instMonadFinally___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Async_ContextAsync_instMonadFinally: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_ContextAsync_instMonadFinally___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Async_ContextAsync_instInhabited___lam__0___closed__0_value: LeanStringObject<37> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 37,
        m_capacity: 37,
        m_length: 36,
        m_data: [
            40, 96, 73, 110, 104, 97, 98, 105, 116, 101, 100, 46, 100, 101, 102, 97, 117, 108, 116,
            96, 32, 102, 111, 114, 32, 96, 73, 79, 46, 69, 114, 114, 111, 114, 96, 41, 0,
        ],
    };
static mut l_Std_Async_ContextAsync_instInhabited___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_ContextAsync_instInhabited___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Async_ContextAsync_instInhabited___lam__0___closed__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 18,
        },
        m_objs: [core::ptr::addr_of!(
            l_Std_Async_ContextAsync_instInhabited___lam__0___closed__0_value
        ) as *mut LeanObject],
    };
static mut l_Std_Async_ContextAsync_instInhabited___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_ContextAsync_instInhabited___lam__0___closed__1_value)
        as *mut LeanObject;
pub static l_Std_Async_ContextAsync_instInhabited___lam__0___closed__2_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [core::ptr::addr_of!(
            l_Std_Async_ContextAsync_instInhabited___lam__0___closed__1_value
        ) as *mut LeanObject],
    };
static mut l_Std_Async_ContextAsync_instInhabited___lam__0___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_ContextAsync_instInhabited___lam__0___closed__2_value)
        as *mut LeanObject;
pub static l_Std_Async_ContextAsync_instInhabited___lam__0___closed__3_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [core::ptr::addr_of!(
            l_Std_Async_ContextAsync_instInhabited___lam__0___closed__2_value
        ) as *mut LeanObject],
    };
static mut l_Std_Async_ContextAsync_instInhabited___lam__0___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_ContextAsync_instInhabited___lam__0___closed__3_value)
        as *mut LeanObject;
pub static l_Std_Async_ContextAsync_instInhabited___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Async_ContextAsync_instInhabited___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_ContextAsync_instInhabited___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_ContextAsync_instInhabited___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Async_ContextAsync_instMonadAwaitAsyncTask___closed__0_value: LeanClosureObject<
    0,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Async_ContextAsync_instMonadAwaitAsyncTask___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Async_ContextAsync_instMonadAwaitAsyncTask___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_ContextAsync_instMonadAwaitAsyncTask___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Async_ContextAsync_instMonadAwaitAsyncTask: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_ContextAsync_instMonadAwaitAsyncTask___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Async_ContextAsync_race___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Async_ContextAsync_race___redArg___lam__3___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_ContextAsync_race___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_ContextAsync_race___redArg___closed__0_value)
        as *mut LeanObject;
pub unsafe fn l_Std_Async_ContextAsync_runIn___redArg(
    mut v_ctx_2593_: *mut LeanObject,
    mut v_x_2594_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2596_: *mut LeanObject = core::ptr::null_mut();
    v___x_2596_ = lean_apply_2(v_x_2594_, v_ctx_2593_, lean_box(0));
    return v___x_2596_;
}
pub unsafe fn l_Std_Async_ContextAsync_runIn___redArg___boxed(
    mut v_ctx_2597_: *mut LeanObject,
    mut v_x_2598_: *mut LeanObject,
    mut v_a_2599_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2600_: *mut LeanObject = core::ptr::null_mut();
    v_res_2600_ = l_Std_Async_ContextAsync_runIn___redArg(v_ctx_2597_, v_x_2598_);
    return v_res_2600_;
}
pub unsafe fn l_Std_Async_ContextAsync_runIn(
    mut v_00_u03b1_2601_: *mut LeanObject,
    mut v_ctx_2602_: *mut LeanObject,
    mut v_x_2603_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2605_: *mut LeanObject = core::ptr::null_mut();
    v___x_2605_ = lean_apply_2(v_x_2603_, v_ctx_2602_, lean_box(0));
    return v___x_2605_;
}
pub unsafe fn l_Std_Async_ContextAsync_runIn___boxed(
    mut v_00_u03b1_2606_: *mut LeanObject,
    mut v_ctx_2607_: *mut LeanObject,
    mut v_x_2608_: *mut LeanObject,
    mut v_a_2609_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2610_: *mut LeanObject = core::ptr::null_mut();
    v_res_2610_ = l_Std_Async_ContextAsync_runIn(v_00_u03b1_2606_, v_ctx_2607_, v_x_2608_);
    return v_res_2610_;
}
pub unsafe fn l_Std_Async_ContextAsync_run___redArg___lam__0(
    mut v_x_2611_: *mut LeanObject,
    mut v_x_2612_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2617_: u8 = 0;
    let mut v___x_2619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2622_: u8 = 0;
    let mut v___x_2623_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2612_) == 0 {
                    lean_dec_ref(v_x_2611_);
                    v_a_2614_ = lean_ctor_get(v_x_2612_, 0);
                    v_isSharedCheck_2622_ = (!lean_is_exclusive(v_x_2612_)) as u8;
                    if v_isSharedCheck_2622_ == 0 {
                        v___x_2616_ = v_x_2612_;
                        v_isShared_2617_ = v_isSharedCheck_2622_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2614_);
                        lean_dec(v_x_2612_);
                        v___x_2616_ = lean_box(0);
                        v_isShared_2617_ = v_isSharedCheck_2622_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v_x_2612_, 1);
                    v___x_2623_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2623_, 0, v_x_2611_);
                    return v___x_2623_;
                }
            }
            1 => {
                if v_isShared_2617_ == 0 {
                    v___x_2619_ = v___x_2616_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2621_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2621_, 0, v_a_2614_);
                    v___x_2619_ = v_reuseFailAlloc_2621_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2620_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2620_, 0, v___x_2619_);
                return v___x_2620_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_run___redArg___lam__0___boxed(
    mut v_x_2624_: *mut LeanObject,
    mut v_x_2625_: *mut LeanObject,
    mut v___y_2626_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2627_: *mut LeanObject = core::ptr::null_mut();
    v_res_2627_ = l_Std_Async_ContextAsync_run___redArg___lam__0(v_x_2624_, v_x_2625_);
    return v_res_2627_;
}
pub unsafe fn l_Std_Async_ContextAsync_run___redArg___lam__1(
    mut v_a_2628_: *mut LeanObject,
    mut v_x_2629_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_2629_) == 0 {
        let mut v___x_2631_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_a_2628_);
        v___x_2631_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_2631_, 0, v_x_2629_);
        return v___x_2631_;
    } else {
        let mut v___x_2632_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2633_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_2634_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2635_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2636_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2637_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2638_: u8 = 0;
        let mut v___x_2639_: *mut LeanObject = core::ptr::null_mut();
        v___x_2632_ = lean_box(2);
        v___x_2633_ = l_Std_CancellationContext_cancel(v_a_2628_, v___x_2632_);
        v___f_2634_ = lean_alloc_closure(
            l_Std_Async_ContextAsync_run___redArg___lam__0___boxed as *mut core::ffi::c_void,
            3,
            1,
        );
        lean_closure_set(v___f_2634_, 0, v_x_2629_);
        v___x_2635_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_2635_, 0, v___x_2633_);
        v___x_2636_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_2636_, 0, v___x_2635_);
        v___x_2637_ = lean_unsigned_to_nat(0);
        v___x_2638_ = 0;
        v___x_2639_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
            lean_box(0),
            lean_box(0),
            v___x_2637_,
            v___x_2638_,
            v___x_2636_,
            v___f_2634_,
        );
        return v___x_2639_;
    }
}
pub unsafe fn l_Std_Async_ContextAsync_run___redArg___lam__1___boxed(
    mut v_a_2640_: *mut LeanObject,
    mut v_x_2641_: *mut LeanObject,
    mut v___y_2642_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2643_: *mut LeanObject = core::ptr::null_mut();
    v_res_2643_ = l_Std_Async_ContextAsync_run___redArg___lam__1(v_a_2640_, v_x_2641_);
    return v_res_2643_;
}
pub unsafe fn l_Std_Async_ContextAsync_run___redArg___lam__2(
    mut v_x_2644_: *mut LeanObject,
    mut v_x_2645_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2650_: u8 = 0;
    let mut v___x_2652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2655_: u8 = 0;
    let mut v_a_2656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2660_: u8 = 0;
    let mut v___x_2661_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2645_) == 0 {
                    lean_dec_ref(v_x_2644_);
                    v_a_2647_ = lean_ctor_get(v_x_2645_, 0);
                    v_isSharedCheck_2655_ = (!lean_is_exclusive(v_x_2645_)) as u8;
                    if v_isSharedCheck_2655_ == 0 {
                        v___x_2649_ = v_x_2645_;
                        v_isShared_2650_ = v_isSharedCheck_2655_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2647_);
                        lean_dec(v_x_2645_);
                        v___x_2649_ = lean_box(0);
                        v_isShared_2650_ = v_isSharedCheck_2655_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2656_ = lean_ctor_get(v_x_2645_, 0);
                    lean_inc_n(v_a_2656_, 2);
                    lean_dec_ref_known(v_x_2645_, 1);
                    v___x_2657_ = lean_apply_2(v_x_2644_, v_a_2656_, lean_box(0));
                    v___f_2658_ = lean_alloc_closure(
                        l_Std_Async_ContextAsync_run___redArg___lam__1___boxed
                            as *mut core::ffi::c_void,
                        3,
                        1,
                    );
                    lean_closure_set(v___f_2658_, 0, v_a_2656_);
                    v___x_2659_ = lean_unsigned_to_nat(0);
                    v___x_2660_ = 0;
                    v___x_2661_ =
                        l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                            lean_box(0),
                            lean_box(0),
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
                    v_reuseFailAlloc_2654_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2654_, 0, v_a_2647_);
                    v___x_2652_ = v_reuseFailAlloc_2654_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2653_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2653_, 0, v___x_2652_);
                return v___x_2653_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_run___redArg___lam__2___boxed(
    mut v_x_2662_: *mut LeanObject,
    mut v_x_2663_: *mut LeanObject,
    mut v___y_2664_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2665_: *mut LeanObject = core::ptr::null_mut();
    v_res_2665_ = l_Std_Async_ContextAsync_run___redArg___lam__2(v_x_2662_, v_x_2663_);
    return v_res_2665_;
}
pub unsafe fn l_Std_Async_ContextAsync_run___redArg(
    mut v_x_2666_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2673_: u8 = 0;
    let mut v___x_2674_: *mut LeanObject = core::ptr::null_mut();
    v___x_2668_ = l_Std_CancellationContext_new();
    v___f_2669_ = lean_alloc_closure(
        l_Std_Async_ContextAsync_run___redArg___lam__2___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_2669_, 0, v_x_2666_);
    v___x_2670_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_2670_, 0, v___x_2668_);
    v___x_2671_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2671_, 0, v___x_2670_);
    v___x_2672_ = lean_unsigned_to_nat(0);
    v___x_2673_ = 0;
    v___x_2674_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_2672_,
        v___x_2673_,
        v___x_2671_,
        v___f_2669_,
    );
    return v___x_2674_;
}
pub unsafe fn l_Std_Async_ContextAsync_run___redArg___boxed(
    mut v_x_2675_: *mut LeanObject,
    mut v_a_2676_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2677_: *mut LeanObject = core::ptr::null_mut();
    v_res_2677_ = l_Std_Async_ContextAsync_run___redArg(v_x_2675_);
    return v_res_2677_;
}
pub unsafe fn l_Std_Async_ContextAsync_run(
    mut v_00_u03b1_2678_: *mut LeanObject,
    mut v_x_2679_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2686_: u8 = 0;
    let mut v___x_2687_: *mut LeanObject = core::ptr::null_mut();
    v___x_2681_ = l_Std_CancellationContext_new();
    v___f_2682_ = lean_alloc_closure(
        l_Std_Async_ContextAsync_run___redArg___lam__2___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_2682_, 0, v_x_2679_);
    v___x_2683_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_2683_, 0, v___x_2681_);
    v___x_2684_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2684_, 0, v___x_2683_);
    v___x_2685_ = lean_unsigned_to_nat(0);
    v___x_2686_ = 0;
    v___x_2687_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_2685_,
        v___x_2686_,
        v___x_2684_,
        v___f_2682_,
    );
    return v___x_2687_;
}
pub unsafe fn l_Std_Async_ContextAsync_run___boxed(
    mut v_00_u03b1_2688_: *mut LeanObject,
    mut v_x_2689_: *mut LeanObject,
    mut v_a_2690_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2691_: *mut LeanObject = core::ptr::null_mut();
    v_res_2691_ = l_Std_Async_ContextAsync_run(v_00_u03b1_2688_, v_x_2689_);
    return v_res_2691_;
}
pub unsafe fn l_Std_Async_ContextAsync_getContext(
    mut v_ctx_2692_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2695_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_ctx_2692_);
    v___x_2694_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_2694_, 0, v_ctx_2692_);
    v___x_2695_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2695_, 0, v___x_2694_);
    return v___x_2695_;
}
pub unsafe fn l_Std_Async_ContextAsync_getContext___boxed(
    mut v_ctx_2696_: *mut LeanObject,
    mut v_a_2697_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2698_: *mut LeanObject = core::ptr::null_mut();
    v_res_2698_ = l_Std_Async_ContextAsync_getContext(v_ctx_2696_);
    lean_dec_ref(v_ctx_2696_);
    return v_res_2698_;
}
pub unsafe fn l_Std_Async_ContextAsync_isCancelled___lam__0(
    mut v_x_2699_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2704_: u8 = 0;
    let mut v___x_2706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2709_: u8 = 0;
    let mut v_a_2710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2713_: u8 = 0;
    let mut v_token_2714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2715_: u8 = 0;
    let mut v___x_2716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2721_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2699_) == 0 {
                    v_a_2701_ = lean_ctor_get(v_x_2699_, 0);
                    v_isSharedCheck_2709_ = (!lean_is_exclusive(v_x_2699_)) as u8;
                    if v_isSharedCheck_2709_ == 0 {
                        v___x_2703_ = v_x_2699_;
                        v_isShared_2704_ = v_isSharedCheck_2709_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2701_);
                        lean_dec(v_x_2699_);
                        v___x_2703_ = lean_box(0);
                        v_isShared_2704_ = v_isSharedCheck_2709_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2710_ = lean_ctor_get(v_x_2699_, 0);
                    v_isSharedCheck_2721_ = (!lean_is_exclusive(v_x_2699_)) as u8;
                    if v_isSharedCheck_2721_ == 0 {
                        v___x_2712_ = v_x_2699_;
                        v_isShared_2713_ = v_isSharedCheck_2721_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2710_);
                        lean_dec(v_x_2699_);
                        v___x_2712_ = lean_box(0);
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
                    v_reuseFailAlloc_2708_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2708_, 0, v_a_2701_);
                    v___x_2706_ = v_reuseFailAlloc_2708_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2707_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2707_, 0, v___x_2706_);
                return v___x_2707_;
            }
            3 => {
                v_token_2714_ = lean_ctor_get(v_a_2710_, 1);
                lean_inc_ref(v_token_2714_);
                lean_dec(v_a_2710_);
                v___x_2715_ = l_Std_CancellationToken_isCancelled(v_token_2714_);
                v___x_2716_ = lean_box((v___x_2715_) as usize);
                if v_isShared_2713_ == 0 {
                    lean_ctor_set(v___x_2712_, 0, v___x_2716_);
                    v___x_2718_ = v___x_2712_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2720_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2720_, 0, v___x_2716_);
                    v___x_2718_ = v_reuseFailAlloc_2720_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2719_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2719_, 0, v___x_2718_);
                return v___x_2719_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_isCancelled___lam__0___boxed(
    mut v_x_2722_: *mut LeanObject,
    mut v___y_2723_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2724_: *mut LeanObject = core::ptr::null_mut();
    v_res_2724_ = l_Std_Async_ContextAsync_isCancelled___lam__0(v_x_2722_);
    return v_res_2724_;
}
pub unsafe fn l_Std_Async_ContextAsync_isCancelled(
    mut v_a_2726_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: u8 = 0;
    let mut v___x_2733_: *mut LeanObject = core::ptr::null_mut();
    v___f_2728_ = l_Std_Async_ContextAsync_isCancelled___closed__0;
    lean_inc_ref(v_a_2726_);
    v___x_2729_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_2729_, 0, v_a_2726_);
    v___x_2730_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2730_, 0, v___x_2729_);
    v___x_2731_ = lean_unsigned_to_nat(0);
    v___x_2732_ = 0;
    v___x_2733_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_2731_,
        v___x_2732_,
        v___x_2730_,
        v___f_2728_,
    );
    return v___x_2733_;
}
pub unsafe fn l_Std_Async_ContextAsync_isCancelled___boxed(
    mut v_a_2734_: *mut LeanObject,
    mut v_a_2735_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2736_: *mut LeanObject = core::ptr::null_mut();
    v_res_2736_ = l_Std_Async_ContextAsync_isCancelled(v_a_2734_);
    lean_dec_ref(v_a_2734_);
    return v_res_2736_;
}
pub unsafe fn l_Std_Async_ContextAsync_getCancellationReason___lam__0(
    mut v_x_2737_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2742_: u8 = 0;
    let mut v___x_2744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2747_: u8 = 0;
    let mut v_a_2748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2751_: u8 = 0;
    let mut v_token_2752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2758_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2737_) == 0 {
                    v_a_2739_ = lean_ctor_get(v_x_2737_, 0);
                    v_isSharedCheck_2747_ = (!lean_is_exclusive(v_x_2737_)) as u8;
                    if v_isSharedCheck_2747_ == 0 {
                        v___x_2741_ = v_x_2737_;
                        v_isShared_2742_ = v_isSharedCheck_2747_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2739_);
                        lean_dec(v_x_2737_);
                        v___x_2741_ = lean_box(0);
                        v_isShared_2742_ = v_isSharedCheck_2747_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2748_ = lean_ctor_get(v_x_2737_, 0);
                    v_isSharedCheck_2758_ = (!lean_is_exclusive(v_x_2737_)) as u8;
                    if v_isSharedCheck_2758_ == 0 {
                        v___x_2750_ = v_x_2737_;
                        v_isShared_2751_ = v_isSharedCheck_2758_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2748_);
                        lean_dec(v_x_2737_);
                        v___x_2750_ = lean_box(0);
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
                    v_reuseFailAlloc_2746_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2746_, 0, v_a_2739_);
                    v___x_2744_ = v_reuseFailAlloc_2746_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2745_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2745_, 0, v___x_2744_);
                return v___x_2745_;
            }
            3 => {
                v_token_2752_ = lean_ctor_get(v_a_2748_, 1);
                lean_inc_ref(v_token_2752_);
                lean_dec(v_a_2748_);
                v___x_2753_ = l_Std_CancellationToken_getCancellationReason(v_token_2752_);
                if v_isShared_2751_ == 0 {
                    lean_ctor_set(v___x_2750_, 0, v___x_2753_);
                    v___x_2755_ = v___x_2750_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2757_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2757_, 0, v___x_2753_);
                    v___x_2755_ = v_reuseFailAlloc_2757_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2756_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2756_, 0, v___x_2755_);
                return v___x_2756_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_getCancellationReason___lam__0___boxed(
    mut v_x_2759_: *mut LeanObject,
    mut v___y_2760_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2761_: *mut LeanObject = core::ptr::null_mut();
    v_res_2761_ = l_Std_Async_ContextAsync_getCancellationReason___lam__0(v_x_2759_);
    return v_res_2761_;
}
pub unsafe fn l_Std_Async_ContextAsync_getCancellationReason(
    mut v_a_2763_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2769_: u8 = 0;
    let mut v___x_2770_: *mut LeanObject = core::ptr::null_mut();
    v___f_2765_ = l_Std_Async_ContextAsync_getCancellationReason___closed__0;
    lean_inc_ref(v_a_2763_);
    v___x_2766_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_2766_, 0, v_a_2763_);
    v___x_2767_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2767_, 0, v___x_2766_);
    v___x_2768_ = lean_unsigned_to_nat(0);
    v___x_2769_ = 0;
    v___x_2770_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_2768_,
        v___x_2769_,
        v___x_2767_,
        v___f_2765_,
    );
    return v___x_2770_;
}
pub unsafe fn l_Std_Async_ContextAsync_getCancellationReason___boxed(
    mut v_a_2771_: *mut LeanObject,
    mut v_a_2772_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2773_: *mut LeanObject = core::ptr::null_mut();
    v_res_2773_ = l_Std_Async_ContextAsync_getCancellationReason(v_a_2771_);
    lean_dec_ref(v_a_2771_);
    return v_res_2773_;
}
pub unsafe fn l_Std_Async_ContextAsync_cancel___lam__0(
    mut v_reason_2774_: *mut LeanObject,
    mut v_x_2775_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2780_: u8 = 0;
    let mut v___x_2782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2785_: u8 = 0;
    let mut v_a_2786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2789_: u8 = 0;
    let mut v___x_2790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2795_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2775_) == 0 {
                    lean_dec(v_reason_2774_);
                    v_a_2777_ = lean_ctor_get(v_x_2775_, 0);
                    v_isSharedCheck_2785_ = (!lean_is_exclusive(v_x_2775_)) as u8;
                    if v_isSharedCheck_2785_ == 0 {
                        v___x_2779_ = v_x_2775_;
                        v_isShared_2780_ = v_isSharedCheck_2785_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2777_);
                        lean_dec(v_x_2775_);
                        v___x_2779_ = lean_box(0);
                        v_isShared_2780_ = v_isSharedCheck_2785_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2786_ = lean_ctor_get(v_x_2775_, 0);
                    v_isSharedCheck_2795_ = (!lean_is_exclusive(v_x_2775_)) as u8;
                    if v_isSharedCheck_2795_ == 0 {
                        v___x_2788_ = v_x_2775_;
                        v_isShared_2789_ = v_isSharedCheck_2795_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2786_);
                        lean_dec(v_x_2775_);
                        v___x_2788_ = lean_box(0);
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
                    v_reuseFailAlloc_2784_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2784_, 0, v_a_2777_);
                    v___x_2782_ = v_reuseFailAlloc_2784_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2783_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2783_, 0, v___x_2782_);
                return v___x_2783_;
            }
            3 => {
                v___x_2790_ = l_Std_CancellationContext_cancel(v_a_2786_, v_reason_2774_);
                if v_isShared_2789_ == 0 {
                    lean_ctor_set(v___x_2788_, 0, v___x_2790_);
                    v___x_2792_ = v___x_2788_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2794_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2794_, 0, v___x_2790_);
                    v___x_2792_ = v_reuseFailAlloc_2794_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2793_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2793_, 0, v___x_2792_);
                return v___x_2793_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_cancel___lam__0___boxed(
    mut v_reason_2796_: *mut LeanObject,
    mut v_x_2797_: *mut LeanObject,
    mut v___y_2798_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2799_: *mut LeanObject = core::ptr::null_mut();
    v_res_2799_ = l_Std_Async_ContextAsync_cancel___lam__0(v_reason_2796_, v_x_2797_);
    return v_res_2799_;
}
pub unsafe fn l_Std_Async_ContextAsync_cancel(
    mut v_reason_2800_: *mut LeanObject,
    mut v_a_2801_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2807_: u8 = 0;
    let mut v___x_2808_: *mut LeanObject = core::ptr::null_mut();
    v___f_2803_ = lean_alloc_closure(
        l_Std_Async_ContextAsync_cancel___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_2803_, 0, v_reason_2800_);
    lean_inc_ref(v_a_2801_);
    v___x_2804_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_2804_, 0, v_a_2801_);
    v___x_2805_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2805_, 0, v___x_2804_);
    v___x_2806_ = lean_unsigned_to_nat(0);
    v___x_2807_ = 0;
    v___x_2808_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_2806_,
        v___x_2807_,
        v___x_2805_,
        v___f_2803_,
    );
    return v___x_2808_;
}
pub unsafe fn l_Std_Async_ContextAsync_cancel___boxed(
    mut v_reason_2809_: *mut LeanObject,
    mut v_a_2810_: *mut LeanObject,
    mut v_a_2811_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2812_: *mut LeanObject = core::ptr::null_mut();
    v_res_2812_ = l_Std_Async_ContextAsync_cancel(v_reason_2809_, v_a_2810_);
    lean_dec_ref(v_a_2810_);
    return v_res_2812_;
}
pub unsafe fn l_Std_Async_ContextAsync_doneSelector___lam__0(
    mut v_x_2813_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2818_: u8 = 0;
    let mut v___x_2820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2823_: u8 = 0;
    let mut v_a_2824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2827_: u8 = 0;
    let mut v_token_2828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2834_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2813_) == 0 {
                    v_a_2815_ = lean_ctor_get(v_x_2813_, 0);
                    v_isSharedCheck_2823_ = (!lean_is_exclusive(v_x_2813_)) as u8;
                    if v_isSharedCheck_2823_ == 0 {
                        v___x_2817_ = v_x_2813_;
                        v_isShared_2818_ = v_isSharedCheck_2823_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2815_);
                        lean_dec(v_x_2813_);
                        v___x_2817_ = lean_box(0);
                        v_isShared_2818_ = v_isSharedCheck_2823_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2824_ = lean_ctor_get(v_x_2813_, 0);
                    v_isSharedCheck_2834_ = (!lean_is_exclusive(v_x_2813_)) as u8;
                    if v_isSharedCheck_2834_ == 0 {
                        v___x_2826_ = v_x_2813_;
                        v_isShared_2827_ = v_isSharedCheck_2834_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2824_);
                        lean_dec(v_x_2813_);
                        v___x_2826_ = lean_box(0);
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
                    v_reuseFailAlloc_2822_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2822_, 0, v_a_2815_);
                    v___x_2820_ = v_reuseFailAlloc_2822_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2821_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2821_, 0, v___x_2820_);
                return v___x_2821_;
            }
            3 => {
                v_token_2828_ = lean_ctor_get(v_a_2824_, 1);
                lean_inc_ref(v_token_2828_);
                lean_dec(v_a_2824_);
                v___x_2829_ = l_Std_CancellationToken_selector(v_token_2828_);
                if v_isShared_2827_ == 0 {
                    lean_ctor_set(v___x_2826_, 0, v___x_2829_);
                    v___x_2831_ = v___x_2826_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2833_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2833_, 0, v___x_2829_);
                    v___x_2831_ = v_reuseFailAlloc_2833_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2832_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2832_, 0, v___x_2831_);
                return v___x_2832_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_doneSelector___lam__0___boxed(
    mut v_x_2835_: *mut LeanObject,
    mut v___y_2836_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2837_: *mut LeanObject = core::ptr::null_mut();
    v_res_2837_ = l_Std_Async_ContextAsync_doneSelector___lam__0(v_x_2835_);
    return v_res_2837_;
}
pub unsafe fn l_Std_Async_ContextAsync_doneSelector(
    mut v_a_2839_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: u8 = 0;
    let mut v___x_2846_: *mut LeanObject = core::ptr::null_mut();
    v___f_2841_ = l_Std_Async_ContextAsync_doneSelector___closed__0;
    lean_inc_ref(v_a_2839_);
    v___x_2842_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_2842_, 0, v_a_2839_);
    v___x_2843_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2843_, 0, v___x_2842_);
    v___x_2844_ = lean_unsigned_to_nat(0);
    v___x_2845_ = 0;
    v___x_2846_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_2844_,
        v___x_2845_,
        v___x_2843_,
        v___f_2841_,
    );
    return v___x_2846_;
}
pub unsafe fn l_Std_Async_ContextAsync_doneSelector___boxed(
    mut v_a_2847_: *mut LeanObject,
    mut v_a_2848_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2849_: *mut LeanObject = core::ptr::null_mut();
    v_res_2849_ = l_Std_Async_ContextAsync_doneSelector(v_a_2847_);
    lean_dec_ref(v_a_2847_);
    return v_res_2849_;
}
pub unsafe fn l_Std_Async_ContextAsync_awaitCancellation___lam__0(
    mut v_x_2850_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2855_: u8 = 0;
    let mut v___x_2857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2860_: u8 = 0;
    let mut v_a_2861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2850_) == 0 {
                    v_a_2852_ = lean_ctor_get(v_x_2850_, 0);
                    v_isSharedCheck_2860_ = (!lean_is_exclusive(v_x_2850_)) as u8;
                    if v_isSharedCheck_2860_ == 0 {
                        v___x_2854_ = v_x_2850_;
                        v_isShared_2855_ = v_isSharedCheck_2860_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2852_);
                        lean_dec(v_x_2850_);
                        v___x_2854_ = lean_box(0);
                        v_isShared_2855_ = v_isSharedCheck_2860_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2861_ = lean_ctor_get(v_x_2850_, 0);
                    lean_inc(v_a_2861_);
                    lean_dec_ref_known(v_x_2850_, 1);
                    v___x_2862_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2862_, 0, v_a_2861_);
                    return v___x_2862_;
                }
            }
            1 => {
                if v_isShared_2855_ == 0 {
                    v___x_2857_ = v___x_2854_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2859_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2859_, 0, v_a_2852_);
                    v___x_2857_ = v_reuseFailAlloc_2859_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2858_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2858_, 0, v___x_2857_);
                return v___x_2858_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_awaitCancellation___lam__0___boxed(
    mut v_x_2863_: *mut LeanObject,
    mut v___y_2864_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2865_: *mut LeanObject = core::ptr::null_mut();
    v_res_2865_ = l_Std_Async_ContextAsync_awaitCancellation___lam__0(v_x_2863_);
    return v_res_2865_;
}
pub unsafe fn l_Std_Async_ContextAsync_awaitCancellation___lam__1(
    mut v___f_2866_: *mut LeanObject,
    mut v_x_2867_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_val_2870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: u8 = 0;
    let mut v___x_2874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2878_: u8 = 0;
    let mut v___x_2880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2883_: u8 = 0;
    let mut v_a_2884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2887_: u8 = 0;
    let mut v_token_2888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2898_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2867_) == 0 {
                    lean_dec_ref(v___f_2866_);
                    v_a_2875_ = lean_ctor_get(v_x_2867_, 0);
                    v_isSharedCheck_2883_ = (!lean_is_exclusive(v_x_2867_)) as u8;
                    if v_isSharedCheck_2883_ == 0 {
                        v___x_2877_ = v_x_2867_;
                        v_isShared_2878_ = v_isSharedCheck_2883_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_2875_);
                        lean_dec(v_x_2867_);
                        v___x_2877_ = lean_box(0);
                        v_isShared_2878_ = v_isSharedCheck_2883_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_2884_ = lean_ctor_get(v_x_2867_, 0);
                    v_isSharedCheck_2898_ = (!lean_is_exclusive(v_x_2867_)) as u8;
                    if v_isSharedCheck_2898_ == 0 {
                        v___x_2886_ = v_x_2867_;
                        v_isShared_2887_ = v_isSharedCheck_2898_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_2884_);
                        lean_dec(v_x_2867_);
                        v___x_2886_ = lean_box(0);
                        v_isShared_2887_ = v_isSharedCheck_2898_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2871_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2871_, 0, v_val_2870_);
                v___x_2872_ = lean_unsigned_to_nat(0);
                v___x_2873_ = 0;
                v___x_2874_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
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
                    v_reuseFailAlloc_2882_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2882_, 0, v_a_2875_);
                    v___x_2880_ = v_reuseFailAlloc_2882_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2881_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2881_, 0, v___x_2880_);
                return v___x_2881_;
            }
            4 => {
                v_token_2888_ = lean_ctor_get(v_a_2884_, 1);
                lean_inc_ref(v_token_2888_);
                lean_dec(v_a_2884_);
                v___x_2889_ = l_Std_CancellationToken_wait(v_token_2888_);
                if lean_obj_tag(v___x_2889_) == 0 {
                    v_a_2890_ = lean_ctor_get(v___x_2889_, 0);
                    lean_inc(v_a_2890_);
                    lean_dec_ref_known(v___x_2889_, 1);
                    if v_isShared_2887_ == 0 {
                        lean_ctor_set(v___x_2886_, 0, v_a_2890_);
                        v___x_2892_ = v___x_2886_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2893_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2893_, 0, v_a_2890_);
                        v___x_2892_ = v_reuseFailAlloc_2893_;
                        state = 5;
                        continue;
                    }
                } else {
                    v_a_2894_ = lean_ctor_get(v___x_2889_, 0);
                    lean_inc(v_a_2894_);
                    lean_dec_ref_known(v___x_2889_, 1);
                    if v_isShared_2887_ == 0 {
                        lean_ctor_set_tag(v___x_2886_, 0);
                        lean_ctor_set(v___x_2886_, 0, v_a_2894_);
                        v___x_2896_ = v___x_2886_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2897_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2897_, 0, v_a_2894_);
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
    mut v___f_2899_: *mut LeanObject,
    mut v_x_2900_: *mut LeanObject,
    mut v___y_2901_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2902_: *mut LeanObject = core::ptr::null_mut();
    v_res_2902_ = l_Std_Async_ContextAsync_awaitCancellation___lam__1(v___f_2899_, v_x_2900_);
    return v_res_2902_;
}
pub unsafe fn l_Std_Async_ContextAsync_awaitCancellation(
    mut v_a_2906_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2912_: u8 = 0;
    let mut v___x_2913_: *mut LeanObject = core::ptr::null_mut();
    v___f_2908_ = l_Std_Async_ContextAsync_awaitCancellation___closed__1;
    lean_inc_ref(v_a_2906_);
    v___x_2909_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_2909_, 0, v_a_2906_);
    v___x_2910_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2910_, 0, v___x_2909_);
    v___x_2911_ = lean_unsigned_to_nat(0);
    v___x_2912_ = 0;
    v___x_2913_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_2911_,
        v___x_2912_,
        v___x_2910_,
        v___f_2908_,
    );
    return v___x_2913_;
}
pub unsafe fn l_Std_Async_ContextAsync_awaitCancellation___boxed(
    mut v_a_2914_: *mut LeanObject,
    mut v_a_2915_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2916_: *mut LeanObject = core::ptr::null_mut();
    v_res_2916_ = l_Std_Async_ContextAsync_awaitCancellation(v_a_2914_);
    lean_dec_ref(v_a_2914_);
    return v_res_2916_;
}
pub unsafe fn l_Std_Async_ContextAsync_concurrently___redArg___lam__0(
    mut v_x_2917_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_2917_) == 0 {
        let mut v_a_2918_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2919_: *mut LeanObject = core::ptr::null_mut();
        v_a_2918_ = lean_ctor_get(v_x_2917_, 0);
        lean_inc(v_a_2918_);
        lean_dec_ref_known(v_x_2917_, 1);
        v___x_2919_ = lean_task_pure(v_a_2918_);
        return v___x_2919_;
    } else {
        let mut v_a_2920_: *mut LeanObject = core::ptr::null_mut();
        v_a_2920_ = lean_ctor_get(v_x_2917_, 0);
        lean_inc_ref(v_a_2920_);
        lean_dec_ref_known(v_x_2917_, 1);
        return v_a_2920_;
    }
}
pub unsafe fn l_Std_Async_ContextAsync_concurrently___redArg___lam__2(
    mut v_x_2921_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_2922_: *mut LeanObject = core::ptr::null_mut();
    v_fst_2922_ = lean_ctor_get(v_x_2921_, 0);
    lean_inc(v_fst_2922_);
    return v_fst_2922_;
}
pub unsafe fn l_Std_Async_ContextAsync_concurrently___redArg___lam__2___boxed(
    mut v_x_2923_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2924_: *mut LeanObject = core::ptr::null_mut();
    v_res_2924_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__2(v_x_2923_);
    lean_dec_ref(v_x_2923_);
    return v_res_2924_;
}
pub unsafe fn l_Std_Async_ContextAsync_concurrently___redArg___lam__4(
    mut v_a_2925_: *mut LeanObject,
    mut v_x_2926_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_2926_) == 0 {
        let mut v___x_2928_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2929_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_2930_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2931_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2932_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2933_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2934_: u8 = 0;
        let mut v___x_2935_: *mut LeanObject = core::ptr::null_mut();
        v___x_2928_ = lean_box(2);
        v___x_2929_ = l_Std_CancellationContext_cancel(v_a_2925_, v___x_2928_);
        v___f_2930_ = lean_alloc_closure(
            l_Std_Async_ContextAsync_run___redArg___lam__0___boxed as *mut core::ffi::c_void,
            3,
            1,
        );
        lean_closure_set(v___f_2930_, 0, v_x_2926_);
        v___x_2931_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_2931_, 0, v___x_2929_);
        v___x_2932_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_2932_, 0, v___x_2931_);
        v___x_2933_ = lean_unsigned_to_nat(0);
        v___x_2934_ = 0;
        v___x_2935_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
            lean_box(0),
            lean_box(0),
            v___x_2933_,
            v___x_2934_,
            v___x_2932_,
            v___f_2930_,
        );
        return v___x_2935_;
    } else {
        let mut v___x_2936_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_a_2925_);
        v___x_2936_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_2936_, 0, v_x_2926_);
        return v___x_2936_;
    }
}
pub unsafe fn l_Std_Async_ContextAsync_concurrently___redArg___lam__4___boxed(
    mut v_a_2937_: *mut LeanObject,
    mut v_x_2938_: *mut LeanObject,
    mut v___y_2939_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2940_: *mut LeanObject = core::ptr::null_mut();
    v_res_2940_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__4(v_a_2937_, v_x_2938_);
    return v_res_2940_;
}
pub unsafe fn l_Std_Async_ContextAsync_concurrently___redArg___lam__1(
    mut v_x_2941_: *mut LeanObject,
    mut v_a_2942_: *mut LeanObject,
    mut v___f_2943_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2947_: u8 = 0;
    let mut v___x_2948_: *mut LeanObject = core::ptr::null_mut();
    v___x_2945_ = lean_apply_2(v_x_2941_, v_a_2942_, lean_box(0));
    v___x_2946_ = lean_unsigned_to_nat(0);
    v___x_2947_ = 0;
    v___x_2948_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_2946_,
        v___x_2947_,
        v___x_2945_,
        v___f_2943_,
    );
    return v___x_2948_;
}
pub unsafe fn l_Std_Async_ContextAsync_concurrently___redArg___lam__1___boxed(
    mut v_x_2949_: *mut LeanObject,
    mut v_a_2950_: *mut LeanObject,
    mut v___f_2951_: *mut LeanObject,
    mut v___y_2952_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2953_: *mut LeanObject = core::ptr::null_mut();
    v_res_2953_ =
        l_Std_Async_ContextAsync_concurrently___redArg___lam__1(v_x_2949_, v_a_2950_, v___f_2951_);
    return v_res_2953_;
}
pub unsafe fn l_Std_Async_ContextAsync_concurrently___redArg___lam__3(
    mut v_a_2954_: *mut LeanObject,
    mut v___x_2955_: *mut LeanObject,
    mut v_x_2956_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2960_: *mut LeanObject = core::ptr::null_mut();
    v___x_2958_ = l_Std_CancellationContext_cancel(v_a_2954_, v___x_2955_);
    v___x_2959_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_2959_, 0, v___x_2958_);
    v___x_2960_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2960_, 0, v___x_2959_);
    return v___x_2960_;
}
pub unsafe fn l_Std_Async_ContextAsync_concurrently___redArg___lam__3___boxed(
    mut v_a_2961_: *mut LeanObject,
    mut v___x_2962_: *mut LeanObject,
    mut v_x_2963_: *mut LeanObject,
    mut v___y_2964_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2965_: *mut LeanObject = core::ptr::null_mut();
    v_res_2965_ =
        l_Std_Async_ContextAsync_concurrently___redArg___lam__3(v_a_2961_, v___x_2962_, v_x_2963_);
    lean_dec(v_x_2963_);
    return v_res_2965_;
}
pub unsafe fn l_Std_Async_ContextAsync_concurrently___redArg___lam__5(
    mut v___f_2966_: *mut LeanObject,
    mut v___f_2967_: *mut LeanObject,
    mut v___f_2968_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2971_: u8 = 0;
    let mut v___x_2972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2980_: u8 = 0;
    let mut v___x_2982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2984_: u8 = 0;
    let mut v_a_2985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2988_: u8 = 0;
    let mut v_fst_2989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2993_: u8 = 0;
    let mut v_a_2994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2997_: u8 = 0;
    let mut v___x_2998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3003_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2970_ = lean_unsigned_to_nat(0);
                v___x_2971_ = 0;
                v___x_2972_ = l_Std_Async_EAsync_tryFinally_x27___redArg(
                    v___f_2966_,
                    v___f_2967_,
                    v___x_2970_,
                    v___x_2971_,
                );
                if lean_obj_tag(v___x_2972_) == 0 {
                    lean_dec(v___f_2968_);
                    v_a_2976_ = lean_ctor_get(v___x_2972_, 0);
                    lean_inc(v_a_2976_);
                    lean_dec_ref_known(v___x_2972_, 1);
                    if lean_obj_tag(v_a_2976_) == 0 {
                        v_a_2977_ = lean_ctor_get(v_a_2976_, 0);
                        v_isSharedCheck_2984_ = (!lean_is_exclusive(v_a_2976_)) as u8;
                        if v_isSharedCheck_2984_ == 0 {
                            v___x_2979_ = v_a_2976_;
                            v_isShared_2980_ = v_isSharedCheck_2984_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_2977_);
                            lean_dec(v_a_2976_);
                            v___x_2979_ = lean_box(0);
                            v_isShared_2980_ = v_isSharedCheck_2984_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_a_2985_ = lean_ctor_get(v_a_2976_, 0);
                        v_isSharedCheck_2993_ = (!lean_is_exclusive(v_a_2976_)) as u8;
                        if v_isSharedCheck_2993_ == 0 {
                            v___x_2987_ = v_a_2976_;
                            v_isShared_2988_ = v_isSharedCheck_2993_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_2985_);
                            lean_dec(v_a_2976_);
                            v___x_2987_ = lean_box(0);
                            v_isShared_2988_ = v_isSharedCheck_2993_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_a_2994_ = lean_ctor_get(v___x_2972_, 0);
                    v_isSharedCheck_3003_ = (!lean_is_exclusive(v___x_2972_)) as u8;
                    if v_isSharedCheck_3003_ == 0 {
                        v___x_2996_ = v___x_2972_;
                        v_isShared_2997_ = v_isSharedCheck_3003_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_2994_);
                        lean_dec(v___x_2972_);
                        v___x_2996_ = lean_box(0);
                        v_isShared_2997_ = v_isSharedCheck_3003_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2975_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2975_, 0, v___y_2974_);
                return v___x_2975_;
            }
            2 => {
                if v_isShared_2980_ == 0 {
                    v___x_2982_ = v___x_2979_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2983_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2983_, 0, v_a_2977_);
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
                v_fst_2989_ = lean_ctor_get(v_a_2985_, 0);
                lean_inc(v_fst_2989_);
                lean_dec(v_a_2985_);
                if v_isShared_2988_ == 0 {
                    lean_ctor_set(v___x_2987_, 0, v_fst_2989_);
                    v___x_2991_ = v___x_2987_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2992_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2992_, 0, v_fst_2989_);
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
                v___x_2998_ = lean_alloc_closure(l_Except_map as *mut core::ffi::c_void, 5, 4);
                lean_closure_set(v___x_2998_, 0, lean_box(0));
                lean_closure_set(v___x_2998_, 1, lean_box(0));
                lean_closure_set(v___x_2998_, 2, lean_box(0));
                lean_closure_set(v___x_2998_, 3, v___f_2968_);
                v___x_2999_ = lean_task_map(v___x_2998_, v_a_2994_, v___x_2970_, v___x_2971_);
                if v_isShared_2997_ == 0 {
                    lean_ctor_set(v___x_2996_, 0, v___x_2999_);
                    v___x_3001_ = v___x_2996_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3002_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3002_, 0, v___x_2999_);
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
    mut v___f_3004_: *mut LeanObject,
    mut v___f_3005_: *mut LeanObject,
    mut v___f_3006_: *mut LeanObject,
    mut v___y_3007_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3008_: *mut LeanObject = core::ptr::null_mut();
    v_res_3008_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__5(
        v___f_3004_,
        v___f_3005_,
        v___f_3006_,
    );
    return v_res_3008_;
}
pub unsafe fn l_Std_Async_ContextAsync_concurrently___redArg___lam__7(
    mut v_a_3009_: *mut LeanObject,
    mut v___x_3010_: *mut LeanObject,
    mut v_x_3011_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_3011_) == 0 {
        let mut v___x_3013_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_3014_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3015_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3016_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3017_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3018_: u8 = 0;
        let mut v___x_3019_: *mut LeanObject = core::ptr::null_mut();
        v___x_3013_ = l_Std_CancellationContext_cancel(v_a_3009_, v___x_3010_);
        v___f_3014_ = lean_alloc_closure(
            l_Std_Async_ContextAsync_run___redArg___lam__0___boxed as *mut core::ffi::c_void,
            3,
            1,
        );
        lean_closure_set(v___f_3014_, 0, v_x_3011_);
        v___x_3015_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_3015_, 0, v___x_3013_);
        v___x_3016_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_3016_, 0, v___x_3015_);
        v___x_3017_ = lean_unsigned_to_nat(0);
        v___x_3018_ = 0;
        v___x_3019_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
            lean_box(0),
            lean_box(0),
            v___x_3017_,
            v___x_3018_,
            v___x_3016_,
            v___f_3014_,
        );
        return v___x_3019_;
    } else {
        let mut v___x_3020_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___x_3010_);
        lean_dec_ref(v_a_3009_);
        v___x_3020_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_3020_, 0, v_x_3011_);
        return v___x_3020_;
    }
}
pub unsafe fn l_Std_Async_ContextAsync_concurrently___redArg___lam__7___boxed(
    mut v_a_3021_: *mut LeanObject,
    mut v___x_3022_: *mut LeanObject,
    mut v_x_3023_: *mut LeanObject,
    mut v___y_3024_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3025_: *mut LeanObject = core::ptr::null_mut();
    v_res_3025_ =
        l_Std_Async_ContextAsync_concurrently___redArg___lam__7(v_a_3021_, v___x_3022_, v_x_3023_);
    return v_res_3025_;
}
pub unsafe fn l_Std_Async_ContextAsync_concurrently___redArg___lam__6(
    mut v_y_3026_: *mut LeanObject,
    mut v_a_3027_: *mut LeanObject,
    mut v___f_3028_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: u8 = 0;
    let mut v___x_3033_: *mut LeanObject = core::ptr::null_mut();
    v___x_3030_ = lean_apply_2(v_y_3026_, v_a_3027_, lean_box(0));
    v___x_3031_ = lean_unsigned_to_nat(0);
    v___x_3032_ = 0;
    v___x_3033_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_3031_,
        v___x_3032_,
        v___x_3030_,
        v___f_3028_,
    );
    return v___x_3033_;
}
pub unsafe fn l_Std_Async_ContextAsync_concurrently___redArg___lam__6___boxed(
    mut v_y_3034_: *mut LeanObject,
    mut v_a_3035_: *mut LeanObject,
    mut v___f_3036_: *mut LeanObject,
    mut v___y_3037_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3038_: *mut LeanObject = core::ptr::null_mut();
    v_res_3038_ =
        l_Std_Async_ContextAsync_concurrently___redArg___lam__6(v_y_3034_, v_a_3035_, v___f_3036_);
    return v_res_3038_;
}
pub unsafe fn l_Std_Async_ContextAsync_concurrently___redArg___lam__10(
    mut v_a_3039_: *mut LeanObject,
    mut v_x_3040_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3045_: u8 = 0;
    let mut v___x_3047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3050_: u8 = 0;
    let mut v_a_3051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3054_: u8 = 0;
    let mut v___x_3055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3060_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3040_) == 0 {
                    lean_dec(v_a_3039_);
                    v_a_3042_ = lean_ctor_get(v_x_3040_, 0);
                    v_isSharedCheck_3050_ = (!lean_is_exclusive(v_x_3040_)) as u8;
                    if v_isSharedCheck_3050_ == 0 {
                        v___x_3044_ = v_x_3040_;
                        v_isShared_3045_ = v_isSharedCheck_3050_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3042_);
                        lean_dec(v_x_3040_);
                        v___x_3044_ = lean_box(0);
                        v_isShared_3045_ = v_isSharedCheck_3050_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3051_ = lean_ctor_get(v_x_3040_, 0);
                    v_isSharedCheck_3060_ = (!lean_is_exclusive(v_x_3040_)) as u8;
                    if v_isSharedCheck_3060_ == 0 {
                        v___x_3053_ = v_x_3040_;
                        v_isShared_3054_ = v_isSharedCheck_3060_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3051_);
                        lean_dec(v_x_3040_);
                        v___x_3053_ = lean_box(0);
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
                    v_reuseFailAlloc_3049_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3049_, 0, v_a_3042_);
                    v___x_3047_ = v_reuseFailAlloc_3049_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3048_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3048_, 0, v___x_3047_);
                return v___x_3048_;
            }
            3 => {
                v___x_3055_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3055_, 0, v_a_3039_);
                lean_ctor_set(v___x_3055_, 1, v_a_3051_);
                if v_isShared_3054_ == 0 {
                    lean_ctor_set(v___x_3053_, 0, v___x_3055_);
                    v___x_3057_ = v___x_3053_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3059_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3059_, 0, v___x_3055_);
                    v___x_3057_ = v_reuseFailAlloc_3059_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3058_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3058_, 0, v___x_3057_);
                return v___x_3058_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_concurrently___redArg___lam__10___boxed(
    mut v_a_3061_: *mut LeanObject,
    mut v_x_3062_: *mut LeanObject,
    mut v___y_3063_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3064_: *mut LeanObject = core::ptr::null_mut();
    v_res_3064_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__10(v_a_3061_, v_x_3062_);
    return v_res_3064_;
}
pub unsafe fn l_Std_Async_ContextAsync_concurrently___redArg___lam__8(
    mut v_a_3065_: *mut LeanObject,
    mut v_x_3066_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3071_: u8 = 0;
    let mut v___x_3073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3076_: u8 = 0;
    let mut v_a_3077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: u8 = 0;
    let mut v___x_3082_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3066_) == 0 {
                    lean_dec_ref(v_a_3065_);
                    v_a_3068_ = lean_ctor_get(v_x_3066_, 0);
                    v_isSharedCheck_3076_ = (!lean_is_exclusive(v_x_3066_)) as u8;
                    if v_isSharedCheck_3076_ == 0 {
                        v___x_3070_ = v_x_3066_;
                        v_isShared_3071_ = v_isSharedCheck_3076_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3068_);
                        lean_dec(v_x_3066_);
                        v___x_3070_ = lean_box(0);
                        v_isShared_3071_ = v_isSharedCheck_3076_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3077_ = lean_ctor_get(v_x_3066_, 0);
                    lean_inc(v_a_3077_);
                    lean_dec_ref_known(v_x_3066_, 1);
                    v___f_3078_ = lean_alloc_closure(
                        l_Std_Async_ContextAsync_concurrently___redArg___lam__10___boxed
                            as *mut core::ffi::c_void,
                        3,
                        1,
                    );
                    lean_closure_set(v___f_3078_, 0, v_a_3077_);
                    v___x_3079_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3079_, 0, v_a_3065_);
                    v___x_3080_ = lean_unsigned_to_nat(0);
                    v___x_3081_ = 0;
                    v___x_3082_ =
                        l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                            lean_box(0),
                            lean_box(0),
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
                    v_reuseFailAlloc_3075_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3075_, 0, v_a_3068_);
                    v___x_3073_ = v_reuseFailAlloc_3075_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3074_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3074_, 0, v___x_3073_);
                return v___x_3074_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_concurrently___redArg___lam__8___boxed(
    mut v_a_3083_: *mut LeanObject,
    mut v_x_3084_: *mut LeanObject,
    mut v___y_3085_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3086_: *mut LeanObject = core::ptr::null_mut();
    v_res_3086_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__8(v_a_3083_, v_x_3084_);
    return v_res_3086_;
}
pub unsafe fn l_Std_Async_ContextAsync_concurrently___redArg___lam__9(
    mut v_a_3087_: *mut LeanObject,
    mut v_x_3088_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3093_: u8 = 0;
    let mut v___x_3095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3098_: u8 = 0;
    let mut v_a_3099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3103_: u8 = 0;
    let mut v___x_3104_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3088_) == 0 {
                    lean_dec_ref(v_a_3087_);
                    v_a_3090_ = lean_ctor_get(v_x_3088_, 0);
                    v_isSharedCheck_3098_ = (!lean_is_exclusive(v_x_3088_)) as u8;
                    if v_isSharedCheck_3098_ == 0 {
                        v___x_3092_ = v_x_3088_;
                        v_isShared_3093_ = v_isSharedCheck_3098_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3090_);
                        lean_dec(v_x_3088_);
                        v___x_3092_ = lean_box(0);
                        v_isShared_3093_ = v_isSharedCheck_3098_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3099_ = lean_ctor_get(v_x_3088_, 0);
                    lean_inc(v_a_3099_);
                    lean_dec_ref_known(v_x_3088_, 1);
                    v___f_3100_ = lean_alloc_closure(
                        l_Std_Async_ContextAsync_concurrently___redArg___lam__8___boxed
                            as *mut core::ffi::c_void,
                        3,
                        1,
                    );
                    lean_closure_set(v___f_3100_, 0, v_a_3099_);
                    v___x_3101_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3101_, 0, v_a_3087_);
                    v___x_3102_ = lean_unsigned_to_nat(0);
                    v___x_3103_ = 0;
                    v___x_3104_ =
                        l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                            lean_box(0),
                            lean_box(0),
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
                    v_reuseFailAlloc_3097_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3097_, 0, v_a_3090_);
                    v___x_3095_ = v_reuseFailAlloc_3097_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3096_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3096_, 0, v___x_3095_);
                return v___x_3096_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_concurrently___redArg___lam__9___boxed(
    mut v_a_3105_: *mut LeanObject,
    mut v_x_3106_: *mut LeanObject,
    mut v___y_3107_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3108_: *mut LeanObject = core::ptr::null_mut();
    v_res_3108_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__9(v_a_3105_, v_x_3106_);
    return v_res_3108_;
}
pub unsafe fn l_Std_Async_ContextAsync_concurrently___redArg___lam__11(
    mut v___f_3109_: *mut LeanObject,
    mut v_prio_3110_: *mut LeanObject,
    mut v___f_3111_: *mut LeanObject,
    mut v_x_3112_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3117_: u8 = 0;
    let mut v___x_3119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3122_: u8 = 0;
    let mut v_a_3123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3126_: u8 = 0;
    let mut v___x_3127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3131_: u8 = 0;
    let mut v___x_3132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3136_: u8 = 0;
    let mut v___x_3137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3139_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3112_) == 0 {
                    lean_dec_ref(v___f_3111_);
                    lean_dec(v_prio_3110_);
                    lean_dec_ref(v___f_3109_);
                    v_a_3114_ = lean_ctor_get(v_x_3112_, 0);
                    v_isSharedCheck_3122_ = (!lean_is_exclusive(v_x_3112_)) as u8;
                    if v_isSharedCheck_3122_ == 0 {
                        v___x_3116_ = v_x_3112_;
                        v_isShared_3117_ = v_isSharedCheck_3122_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3114_);
                        lean_dec(v_x_3112_);
                        v___x_3116_ = lean_box(0);
                        v_isShared_3117_ = v_isSharedCheck_3122_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3123_ = lean_ctor_get(v_x_3112_, 0);
                    v_isSharedCheck_3139_ = (!lean_is_exclusive(v_x_3112_)) as u8;
                    if v_isSharedCheck_3139_ == 0 {
                        v___x_3125_ = v_x_3112_;
                        v_isShared_3126_ = v_isSharedCheck_3139_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3123_);
                        lean_dec(v_x_3112_);
                        v___x_3125_ = lean_box(0);
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
                    v_reuseFailAlloc_3121_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3121_, 0, v_a_3114_);
                    v___x_3119_ = v_reuseFailAlloc_3121_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3120_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3120_, 0, v___x_3119_);
                return v___x_3120_;
            }
            3 => {
                v___x_3127_ = lean_alloc_closure(
                    l_Std_Async_BaseAsync_toRawBaseIO___boxed as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___x_3127_, 0, lean_box(0));
                lean_closure_set(v___x_3127_, 1, v___f_3109_);
                v___x_3128_ = lean_io_as_task(v___x_3127_, v_prio_3110_);
                v___f_3129_ = lean_alloc_closure(
                    l_Std_Async_ContextAsync_concurrently___redArg___lam__9___boxed
                        as *mut core::ffi::c_void,
                    3,
                    1,
                );
                lean_closure_set(v___f_3129_, 0, v_a_3123_);
                v___x_3130_ = lean_unsigned_to_nat(0);
                v___x_3131_ = 1;
                v___x_3132_ = lean_task_bind(v___x_3128_, v___f_3111_, v___x_3130_, v___x_3131_);
                if v_isShared_3126_ == 0 {
                    lean_ctor_set(v___x_3125_, 0, v___x_3132_);
                    v___x_3134_ = v___x_3125_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3138_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3138_, 0, v___x_3132_);
                    v___x_3134_ = v_reuseFailAlloc_3138_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3135_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3135_, 0, v___x_3134_);
                v___x_3136_ = 0;
                v___x_3137_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
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
    mut v___f_3140_: *mut LeanObject,
    mut v_prio_3141_: *mut LeanObject,
    mut v___f_3142_: *mut LeanObject,
    mut v_x_3143_: *mut LeanObject,
    mut v___y_3144_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3145_: *mut LeanObject = core::ptr::null_mut();
    v_res_3145_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__11(
        v___f_3140_,
        v_prio_3141_,
        v___f_3142_,
        v_x_3143_,
    );
    return v_res_3145_;
}
pub unsafe fn l_Std_Async_ContextAsync_concurrently___redArg___lam__12(
    mut v_x_3146_: *mut LeanObject,
    mut v_x_3147_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3152_: u8 = 0;
    let mut v___x_3154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3157_: u8 = 0;
    let mut v___x_3158_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3147_) == 0 {
                    lean_dec_ref(v_x_3146_);
                    v_a_3149_ = lean_ctor_get(v_x_3147_, 0);
                    v_isSharedCheck_3157_ = (!lean_is_exclusive(v_x_3147_)) as u8;
                    if v_isSharedCheck_3157_ == 0 {
                        v___x_3151_ = v_x_3147_;
                        v_isShared_3152_ = v_isSharedCheck_3157_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3149_);
                        lean_dec(v_x_3147_);
                        v___x_3151_ = lean_box(0);
                        v_isShared_3152_ = v_isSharedCheck_3157_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v_x_3147_, 1);
                    v___x_3158_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3158_, 0, v_x_3146_);
                    return v___x_3158_;
                }
            }
            1 => {
                if v_isShared_3152_ == 0 {
                    v___x_3154_ = v___x_3151_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3156_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3156_, 0, v_a_3149_);
                    v___x_3154_ = v_reuseFailAlloc_3156_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3155_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3155_, 0, v___x_3154_);
                return v___x_3155_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_concurrently___redArg___lam__12___boxed(
    mut v_x_3159_: *mut LeanObject,
    mut v_x_3160_: *mut LeanObject,
    mut v___y_3161_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3162_: *mut LeanObject = core::ptr::null_mut();
    v_res_3162_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__12(v_x_3159_, v_x_3160_);
    return v_res_3162_;
}
pub unsafe fn l_Std_Async_ContextAsync_concurrently___redArg___lam__13(
    mut v_a_3163_: *mut LeanObject,
    mut v___x_3164_: *mut LeanObject,
    mut v_x_3165_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_3165_) == 0 {
        let mut v___x_3167_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___x_3164_);
        lean_dec_ref(v_a_3163_);
        v___x_3167_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_3167_, 0, v_x_3165_);
        return v___x_3167_;
    } else {
        let mut v___x_3168_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_3169_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3170_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3171_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3172_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3173_: u8 = 0;
        let mut v___x_3174_: *mut LeanObject = core::ptr::null_mut();
        v___x_3168_ = l_Std_CancellationContext_cancel(v_a_3163_, v___x_3164_);
        v___f_3169_ = lean_alloc_closure(
            l_Std_Async_ContextAsync_concurrently___redArg___lam__12___boxed
                as *mut core::ffi::c_void,
            3,
            1,
        );
        lean_closure_set(v___f_3169_, 0, v_x_3165_);
        v___x_3170_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_3170_, 0, v___x_3168_);
        v___x_3171_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_3171_, 0, v___x_3170_);
        v___x_3172_ = lean_unsigned_to_nat(0);
        v___x_3173_ = 0;
        v___x_3174_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
            lean_box(0),
            lean_box(0),
            v___x_3172_,
            v___x_3173_,
            v___x_3171_,
            v___f_3169_,
        );
        return v___x_3174_;
    }
}
pub unsafe fn l_Std_Async_ContextAsync_concurrently___redArg___lam__13___boxed(
    mut v_a_3175_: *mut LeanObject,
    mut v___x_3176_: *mut LeanObject,
    mut v_x_3177_: *mut LeanObject,
    mut v___y_3178_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3179_: *mut LeanObject = core::ptr::null_mut();
    v_res_3179_ =
        l_Std_Async_ContextAsync_concurrently___redArg___lam__13(v_a_3175_, v___x_3176_, v_x_3177_);
    return v_res_3179_;
}
pub unsafe fn l_Std_Async_ContextAsync_concurrently___redArg___lam__14(
    mut v_a_3180_: *mut LeanObject,
    mut v___f_3181_: *mut LeanObject,
    mut v___f_3182_: *mut LeanObject,
    mut v_prio_3183_: *mut LeanObject,
    mut v_a_3184_: *mut LeanObject,
    mut v_y_3185_: *mut LeanObject,
    mut v___f_3186_: *mut LeanObject,
    mut v___f_3187_: *mut LeanObject,
    mut v___f_3188_: *mut LeanObject,
    mut v_x_3189_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3194_: u8 = 0;
    let mut v___x_3196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3199_: u8 = 0;
    let mut v_a_3200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3203_: u8 = 0;
    let mut v___x_3204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: u8 = 0;
    let mut v___x_3216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: u8 = 0;
    let mut v___x_3221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3225_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3189_) == 0 {
                    lean_dec_ref(v___f_3188_);
                    lean_dec_ref(v___f_3187_);
                    lean_dec(v___f_3186_);
                    lean_dec_ref(v_y_3185_);
                    lean_dec_ref(v_a_3184_);
                    lean_dec(v_prio_3183_);
                    lean_dec(v___f_3182_);
                    lean_dec_ref(v___f_3181_);
                    lean_dec_ref(v_a_3180_);
                    v_a_3191_ = lean_ctor_get(v_x_3189_, 0);
                    v_isSharedCheck_3199_ = (!lean_is_exclusive(v_x_3189_)) as u8;
                    if v_isSharedCheck_3199_ == 0 {
                        v___x_3193_ = v_x_3189_;
                        v_isShared_3194_ = v_isSharedCheck_3199_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3191_);
                        lean_dec(v_x_3189_);
                        v___x_3193_ = lean_box(0);
                        v_isShared_3194_ = v_isSharedCheck_3199_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3200_ = lean_ctor_get(v_x_3189_, 0);
                    v_isSharedCheck_3225_ = (!lean_is_exclusive(v_x_3189_)) as u8;
                    if v_isSharedCheck_3225_ == 0 {
                        v___x_3202_ = v_x_3189_;
                        v_isShared_3203_ = v_isSharedCheck_3225_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3200_);
                        lean_dec(v_x_3189_);
                        v___x_3202_ = lean_box(0);
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
                    v_reuseFailAlloc_3198_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3198_, 0, v_a_3191_);
                    v___x_3196_ = v_reuseFailAlloc_3198_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3197_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3197_, 0, v___x_3196_);
                return v___x_3197_;
            }
            3 => {
                v___x_3204_ = lean_box(2);
                v___f_3205_ = lean_alloc_closure(
                    l_Std_Async_ContextAsync_concurrently___redArg___lam__3___boxed
                        as *mut core::ffi::c_void,
                    4,
                    2,
                );
                lean_closure_set(v___f_3205_, 0, v_a_3180_);
                lean_closure_set(v___f_3205_, 1, v___x_3204_);
                v___f_3206_ = lean_alloc_closure(
                    l_Std_Async_ContextAsync_concurrently___redArg___lam__5___boxed
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                lean_closure_set(v___f_3206_, 0, v___f_3181_);
                lean_closure_set(v___f_3206_, 1, v___f_3205_);
                lean_closure_set(v___f_3206_, 2, v___f_3182_);
                v___x_3207_ = lean_alloc_closure(
                    l_Std_Async_BaseAsync_toRawBaseIO___boxed as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___x_3207_, 0, lean_box(0));
                lean_closure_set(v___x_3207_, 1, v___f_3206_);
                lean_inc(v_prio_3183_);
                v___x_3208_ = lean_io_as_task(v___x_3207_, v_prio_3183_);
                lean_inc_ref(v_a_3184_);
                v___f_3209_ = lean_alloc_closure(
                    l_Std_Async_ContextAsync_concurrently___redArg___lam__7___boxed
                        as *mut core::ffi::c_void,
                    4,
                    2,
                );
                lean_closure_set(v___f_3209_, 0, v_a_3184_);
                lean_closure_set(v___f_3209_, 1, v___x_3204_);
                lean_inc(v_a_3200_);
                v___f_3210_ = lean_alloc_closure(
                    l_Std_Async_ContextAsync_concurrently___redArg___lam__6___boxed
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                lean_closure_set(v___f_3210_, 0, v_y_3185_);
                lean_closure_set(v___f_3210_, 1, v_a_3200_);
                lean_closure_set(v___f_3210_, 2, v___f_3209_);
                v___f_3211_ = lean_alloc_closure(
                    l_Std_Async_ContextAsync_concurrently___redArg___lam__3___boxed
                        as *mut core::ffi::c_void,
                    4,
                    2,
                );
                lean_closure_set(v___f_3211_, 0, v_a_3200_);
                lean_closure_set(v___f_3211_, 1, v___x_3204_);
                v___f_3212_ = lean_alloc_closure(
                    l_Std_Async_ContextAsync_concurrently___redArg___lam__5___boxed
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                lean_closure_set(v___f_3212_, 0, v___f_3210_);
                lean_closure_set(v___f_3212_, 1, v___f_3211_);
                lean_closure_set(v___f_3212_, 2, v___f_3186_);
                v___f_3213_ = lean_alloc_closure(
                    l_Std_Async_ContextAsync_concurrently___redArg___lam__11___boxed
                        as *mut core::ffi::c_void,
                    5,
                    3,
                );
                lean_closure_set(v___f_3213_, 0, v___f_3212_);
                lean_closure_set(v___f_3213_, 1, v_prio_3183_);
                lean_closure_set(v___f_3213_, 2, v___f_3187_);
                v___x_3214_ = lean_unsigned_to_nat(0);
                v___x_3215_ = 1;
                v___x_3216_ = lean_task_bind(v___x_3208_, v___f_3188_, v___x_3214_, v___x_3215_);
                if v_isShared_3203_ == 0 {
                    lean_ctor_set(v___x_3202_, 0, v___x_3216_);
                    v___x_3218_ = v___x_3202_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3224_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3224_, 0, v___x_3216_);
                    v___x_3218_ = v_reuseFailAlloc_3224_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3219_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3219_, 0, v___x_3218_);
                v___x_3220_ = 0;
                v___x_3221_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
                    v___x_3214_,
                    v___x_3220_,
                    v___x_3219_,
                    v___f_3213_,
                );
                v___f_3222_ = lean_alloc_closure(
                    l_Std_Async_ContextAsync_concurrently___redArg___lam__13___boxed
                        as *mut core::ffi::c_void,
                    4,
                    2,
                );
                lean_closure_set(v___f_3222_, 0, v_a_3184_);
                lean_closure_set(v___f_3222_, 1, v___x_3204_);
                v___x_3223_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
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
    mut v_a_3226_: *mut LeanObject,
    mut v___f_3227_: *mut LeanObject,
    mut v___f_3228_: *mut LeanObject,
    mut v_prio_3229_: *mut LeanObject,
    mut v_a_3230_: *mut LeanObject,
    mut v_y_3231_: *mut LeanObject,
    mut v___f_3232_: *mut LeanObject,
    mut v___f_3233_: *mut LeanObject,
    mut v___f_3234_: *mut LeanObject,
    mut v_x_3235_: *mut LeanObject,
    mut v___y_3236_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3237_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_a_3238_: *mut LeanObject,
    mut v_x_3239_: *mut LeanObject,
    mut v___f_3240_: *mut LeanObject,
    mut v___f_3241_: *mut LeanObject,
    mut v_prio_3242_: *mut LeanObject,
    mut v_y_3243_: *mut LeanObject,
    mut v___f_3244_: *mut LeanObject,
    mut v___f_3245_: *mut LeanObject,
    mut v___f_3246_: *mut LeanObject,
    mut v_x_3247_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3252_: u8 = 0;
    let mut v___x_3254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3257_: u8 = 0;
    let mut v_a_3258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3261_: u8 = 0;
    let mut v___x_3262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: u8 = 0;
    let mut v___x_3270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3272_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3247_) == 0 {
                    lean_dec_ref(v___f_3246_);
                    lean_dec_ref(v___f_3245_);
                    lean_dec(v___f_3244_);
                    lean_dec_ref(v_y_3243_);
                    lean_dec(v_prio_3242_);
                    lean_dec(v___f_3241_);
                    lean_dec_ref(v___f_3240_);
                    lean_dec_ref(v_x_3239_);
                    lean_dec_ref(v_a_3238_);
                    v_a_3249_ = lean_ctor_get(v_x_3247_, 0);
                    v_isSharedCheck_3257_ = (!lean_is_exclusive(v_x_3247_)) as u8;
                    if v_isSharedCheck_3257_ == 0 {
                        v___x_3251_ = v_x_3247_;
                        v_isShared_3252_ = v_isSharedCheck_3257_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3249_);
                        lean_dec(v_x_3247_);
                        v___x_3251_ = lean_box(0);
                        v_isShared_3252_ = v_isSharedCheck_3257_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3258_ = lean_ctor_get(v_x_3247_, 0);
                    v_isSharedCheck_3272_ = (!lean_is_exclusive(v_x_3247_)) as u8;
                    if v_isSharedCheck_3272_ == 0 {
                        v___x_3260_ = v_x_3247_;
                        v_isShared_3261_ = v_isSharedCheck_3272_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3258_);
                        lean_dec(v_x_3247_);
                        v___x_3260_ = lean_box(0);
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
                    v_reuseFailAlloc_3256_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3256_, 0, v_a_3249_);
                    v___x_3254_ = v_reuseFailAlloc_3256_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3255_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3255_, 0, v___x_3254_);
                return v___x_3255_;
            }
            3 => {
                lean_inc_ref(v_a_3238_);
                v___x_3262_ = l_Std_CancellationContext_fork(v_a_3238_);
                lean_inc(v_a_3258_);
                v___f_3263_ = lean_alloc_closure(
                    l_Std_Async_ContextAsync_concurrently___redArg___lam__1___boxed
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                lean_closure_set(v___f_3263_, 0, v_x_3239_);
                lean_closure_set(v___f_3263_, 1, v_a_3258_);
                lean_closure_set(v___f_3263_, 2, v___f_3240_);
                v___f_3264_ = lean_alloc_closure(
                    l_Std_Async_ContextAsync_concurrently___redArg___lam__14___boxed
                        as *mut core::ffi::c_void,
                    11,
                    9,
                );
                lean_closure_set(v___f_3264_, 0, v_a_3258_);
                lean_closure_set(v___f_3264_, 1, v___f_3263_);
                lean_closure_set(v___f_3264_, 2, v___f_3241_);
                lean_closure_set(v___f_3264_, 3, v_prio_3242_);
                lean_closure_set(v___f_3264_, 4, v_a_3238_);
                lean_closure_set(v___f_3264_, 5, v_y_3243_);
                lean_closure_set(v___f_3264_, 6, v___f_3244_);
                lean_closure_set(v___f_3264_, 7, v___f_3245_);
                lean_closure_set(v___f_3264_, 8, v___f_3246_);
                if v_isShared_3261_ == 0 {
                    lean_ctor_set(v___x_3260_, 0, v___x_3262_);
                    v___x_3266_ = v___x_3260_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3271_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3271_, 0, v___x_3262_);
                    v___x_3266_ = v_reuseFailAlloc_3271_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3267_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3267_, 0, v___x_3266_);
                v___x_3268_ = lean_unsigned_to_nat(0);
                v___x_3269_ = 0;
                v___x_3270_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
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
    mut v_a_3273_: *mut LeanObject,
    mut v_x_3274_: *mut LeanObject,
    mut v___f_3275_: *mut LeanObject,
    mut v___f_3276_: *mut LeanObject,
    mut v_prio_3277_: *mut LeanObject,
    mut v_y_3278_: *mut LeanObject,
    mut v___f_3279_: *mut LeanObject,
    mut v___f_3280_: *mut LeanObject,
    mut v___f_3281_: *mut LeanObject,
    mut v_x_3282_: *mut LeanObject,
    mut v___y_3283_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3284_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_x_3285_: *mut LeanObject,
    mut v___f_3286_: *mut LeanObject,
    mut v_prio_3287_: *mut LeanObject,
    mut v_y_3288_: *mut LeanObject,
    mut v___f_3289_: *mut LeanObject,
    mut v___f_3290_: *mut LeanObject,
    mut v___f_3291_: *mut LeanObject,
    mut v_x_3292_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3297_: u8 = 0;
    let mut v___x_3299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3302_: u8 = 0;
    let mut v_a_3303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3306_: u8 = 0;
    let mut v___x_3307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3314_: u8 = 0;
    let mut v___x_3315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3317_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3292_) == 0 {
                    lean_dec_ref(v___f_3291_);
                    lean_dec_ref(v___f_3290_);
                    lean_dec(v___f_3289_);
                    lean_dec_ref(v_y_3288_);
                    lean_dec(v_prio_3287_);
                    lean_dec(v___f_3286_);
                    lean_dec_ref(v_x_3285_);
                    v_a_3294_ = lean_ctor_get(v_x_3292_, 0);
                    v_isSharedCheck_3302_ = (!lean_is_exclusive(v_x_3292_)) as u8;
                    if v_isSharedCheck_3302_ == 0 {
                        v___x_3296_ = v_x_3292_;
                        v_isShared_3297_ = v_isSharedCheck_3302_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3294_);
                        lean_dec(v_x_3292_);
                        v___x_3296_ = lean_box(0);
                        v_isShared_3297_ = v_isSharedCheck_3302_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3303_ = lean_ctor_get(v_x_3292_, 0);
                    v_isSharedCheck_3317_ = (!lean_is_exclusive(v_x_3292_)) as u8;
                    if v_isSharedCheck_3317_ == 0 {
                        v___x_3305_ = v_x_3292_;
                        v_isShared_3306_ = v_isSharedCheck_3317_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3303_);
                        lean_dec(v_x_3292_);
                        v___x_3305_ = lean_box(0);
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
                    v_reuseFailAlloc_3301_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3301_, 0, v_a_3294_);
                    v___x_3299_ = v_reuseFailAlloc_3301_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3300_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3300_, 0, v___x_3299_);
                return v___x_3300_;
            }
            3 => {
                lean_inc_n(v_a_3303_, 2);
                v___x_3307_ = l_Std_CancellationContext_fork(v_a_3303_);
                v___f_3308_ = lean_alloc_closure(
                    l_Std_Async_ContextAsync_concurrently___redArg___lam__4___boxed
                        as *mut core::ffi::c_void,
                    3,
                    1,
                );
                lean_closure_set(v___f_3308_, 0, v_a_3303_);
                v___f_3309_ = lean_alloc_closure(
                    l_Std_Async_ContextAsync_concurrently___redArg___lam__15___boxed
                        as *mut core::ffi::c_void,
                    11,
                    9,
                );
                lean_closure_set(v___f_3309_, 0, v_a_3303_);
                lean_closure_set(v___f_3309_, 1, v_x_3285_);
                lean_closure_set(v___f_3309_, 2, v___f_3308_);
                lean_closure_set(v___f_3309_, 3, v___f_3286_);
                lean_closure_set(v___f_3309_, 4, v_prio_3287_);
                lean_closure_set(v___f_3309_, 5, v_y_3288_);
                lean_closure_set(v___f_3309_, 6, v___f_3289_);
                lean_closure_set(v___f_3309_, 7, v___f_3290_);
                lean_closure_set(v___f_3309_, 8, v___f_3291_);
                if v_isShared_3306_ == 0 {
                    lean_ctor_set(v___x_3305_, 0, v___x_3307_);
                    v___x_3311_ = v___x_3305_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3316_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3316_, 0, v___x_3307_);
                    v___x_3311_ = v_reuseFailAlloc_3316_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3312_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3312_, 0, v___x_3311_);
                v___x_3313_ = lean_unsigned_to_nat(0);
                v___x_3314_ = 0;
                v___x_3315_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
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
    mut v_x_3318_: *mut LeanObject,
    mut v___f_3319_: *mut LeanObject,
    mut v_prio_3320_: *mut LeanObject,
    mut v_y_3321_: *mut LeanObject,
    mut v___f_3322_: *mut LeanObject,
    mut v___f_3323_: *mut LeanObject,
    mut v___f_3324_: *mut LeanObject,
    mut v_x_3325_: *mut LeanObject,
    mut v___y_3326_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3327_: *mut LeanObject = core::ptr::null_mut();
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
    mut v___f_3328_: *mut LeanObject,
    mut v_x_3329_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3334_: u8 = 0;
    let mut v___x_3336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3339_: u8 = 0;
    let mut v_a_3340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3343_: u8 = 0;
    let mut v___x_3344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3349_: u8 = 0;
    let mut v___x_3350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3352_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3329_) == 0 {
                    lean_dec_ref(v___f_3328_);
                    v_a_3331_ = lean_ctor_get(v_x_3329_, 0);
                    v_isSharedCheck_3339_ = (!lean_is_exclusive(v_x_3329_)) as u8;
                    if v_isSharedCheck_3339_ == 0 {
                        v___x_3333_ = v_x_3329_;
                        v_isShared_3334_ = v_isSharedCheck_3339_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3331_);
                        lean_dec(v_x_3329_);
                        v___x_3333_ = lean_box(0);
                        v_isShared_3334_ = v_isSharedCheck_3339_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3340_ = lean_ctor_get(v_x_3329_, 0);
                    v_isSharedCheck_3352_ = (!lean_is_exclusive(v_x_3329_)) as u8;
                    if v_isSharedCheck_3352_ == 0 {
                        v___x_3342_ = v_x_3329_;
                        v_isShared_3343_ = v_isSharedCheck_3352_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3340_);
                        lean_dec(v_x_3329_);
                        v___x_3342_ = lean_box(0);
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
                    v_reuseFailAlloc_3338_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3338_, 0, v_a_3331_);
                    v___x_3336_ = v_reuseFailAlloc_3338_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3337_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3337_, 0, v___x_3336_);
                return v___x_3337_;
            }
            3 => {
                v___x_3344_ = l_Std_CancellationContext_fork(v_a_3340_);
                if v_isShared_3343_ == 0 {
                    lean_ctor_set(v___x_3342_, 0, v___x_3344_);
                    v___x_3346_ = v___x_3342_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3351_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3351_, 0, v___x_3344_);
                    v___x_3346_ = v_reuseFailAlloc_3351_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3347_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3347_, 0, v___x_3346_);
                v___x_3348_ = lean_unsigned_to_nat(0);
                v___x_3349_ = 0;
                v___x_3350_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
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
    mut v___f_3353_: *mut LeanObject,
    mut v_x_3354_: *mut LeanObject,
    mut v___y_3355_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3356_: *mut LeanObject = core::ptr::null_mut();
    v_res_3356_ = l_Std_Async_ContextAsync_concurrently___redArg___lam__17(v___f_3353_, v_x_3354_);
    return v_res_3356_;
}
pub unsafe fn l_Std_Async_ContextAsync_concurrently___redArg(
    mut v_x_3359_: *mut LeanObject,
    mut v_y_3360_: *mut LeanObject,
    mut v_prio_3361_: *mut LeanObject,
    mut v_a_3362_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: u8 = 0;
    let mut v___x_3372_: *mut LeanObject = core::ptr::null_mut();
    v___f_3364_ = l_Std_Async_ContextAsync_concurrently___redArg___closed__0;
    v___f_3365_ = l_Std_Async_ContextAsync_concurrently___redArg___closed__1;
    v___f_3366_ = lean_alloc_closure(
        l_Std_Async_ContextAsync_concurrently___redArg___lam__16___boxed as *mut core::ffi::c_void,
        9,
        7,
    );
    lean_closure_set(v___f_3366_, 0, v_x_3359_);
    lean_closure_set(v___f_3366_, 1, v___f_3365_);
    lean_closure_set(v___f_3366_, 2, v_prio_3361_);
    lean_closure_set(v___f_3366_, 3, v_y_3360_);
    lean_closure_set(v___f_3366_, 4, v___f_3365_);
    lean_closure_set(v___f_3366_, 5, v___f_3364_);
    lean_closure_set(v___f_3366_, 6, v___f_3364_);
    v___f_3367_ = lean_alloc_closure(
        l_Std_Async_ContextAsync_concurrently___redArg___lam__17___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_3367_, 0, v___f_3366_);
    lean_inc_ref(v_a_3362_);
    v___x_3368_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_3368_, 0, v_a_3362_);
    v___x_3369_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3369_, 0, v___x_3368_);
    v___x_3370_ = lean_unsigned_to_nat(0);
    v___x_3371_ = 0;
    v___x_3372_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_3370_,
        v___x_3371_,
        v___x_3369_,
        v___f_3367_,
    );
    return v___x_3372_;
}
pub unsafe fn l_Std_Async_ContextAsync_concurrently___redArg___boxed(
    mut v_x_3373_: *mut LeanObject,
    mut v_y_3374_: *mut LeanObject,
    mut v_prio_3375_: *mut LeanObject,
    mut v_a_3376_: *mut LeanObject,
    mut v_a_3377_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3378_: *mut LeanObject = core::ptr::null_mut();
    v_res_3378_ = l_Std_Async_ContextAsync_concurrently___redArg(
        v_x_3373_,
        v_y_3374_,
        v_prio_3375_,
        v_a_3376_,
    );
    lean_dec_ref(v_a_3376_);
    return v_res_3378_;
}
pub unsafe fn l_Std_Async_ContextAsync_concurrently(
    mut v_00_u03b1_3379_: *mut LeanObject,
    mut v_00_u03b2_3380_: *mut LeanObject,
    mut v_x_3381_: *mut LeanObject,
    mut v_y_3382_: *mut LeanObject,
    mut v_prio_3383_: *mut LeanObject,
    mut v_a_3384_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3393_: u8 = 0;
    let mut v___x_3394_: *mut LeanObject = core::ptr::null_mut();
    v___f_3386_ = l_Std_Async_ContextAsync_concurrently___redArg___closed__0;
    v___f_3387_ = l_Std_Async_ContextAsync_concurrently___redArg___closed__1;
    v___f_3388_ = lean_alloc_closure(
        l_Std_Async_ContextAsync_concurrently___redArg___lam__16___boxed as *mut core::ffi::c_void,
        9,
        7,
    );
    lean_closure_set(v___f_3388_, 0, v_x_3381_);
    lean_closure_set(v___f_3388_, 1, v___f_3387_);
    lean_closure_set(v___f_3388_, 2, v_prio_3383_);
    lean_closure_set(v___f_3388_, 3, v_y_3382_);
    lean_closure_set(v___f_3388_, 4, v___f_3387_);
    lean_closure_set(v___f_3388_, 5, v___f_3386_);
    lean_closure_set(v___f_3388_, 6, v___f_3386_);
    v___f_3389_ = lean_alloc_closure(
        l_Std_Async_ContextAsync_concurrently___redArg___lam__17___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_3389_, 0, v___f_3388_);
    lean_inc_ref(v_a_3384_);
    v___x_3390_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_3390_, 0, v_a_3384_);
    v___x_3391_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3391_, 0, v___x_3390_);
    v___x_3392_ = lean_unsigned_to_nat(0);
    v___x_3393_ = 0;
    v___x_3394_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_3392_,
        v___x_3393_,
        v___x_3391_,
        v___f_3389_,
    );
    return v___x_3394_;
}
pub unsafe fn l_Std_Async_ContextAsync_concurrently___boxed(
    mut v_00_u03b1_3395_: *mut LeanObject,
    mut v_00_u03b2_3396_: *mut LeanObject,
    mut v_x_3397_: *mut LeanObject,
    mut v_y_3398_: *mut LeanObject,
    mut v_prio_3399_: *mut LeanObject,
    mut v_a_3400_: *mut LeanObject,
    mut v_a_3401_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3402_: *mut LeanObject = core::ptr::null_mut();
    v_res_3402_ = l_Std_Async_ContextAsync_concurrently(
        v_00_u03b1_3395_,
        v_00_u03b2_3396_,
        v_x_3397_,
        v_y_3398_,
        v_prio_3399_,
        v_a_3400_,
    );
    lean_dec_ref(v_a_3400_);
    return v_res_3402_;
}
pub unsafe fn l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__0(
    mut v___y_3403_: *mut LeanObject,
    mut v___y_3404_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3406_: *mut LeanObject = core::ptr::null_mut();
    v___x_3406_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_3406_, 0, v___y_3403_);
    return v___x_3406_;
}
pub unsafe fn l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__0___boxed(
    mut v___y_3407_: *mut LeanObject,
    mut v___y_3408_: *mut LeanObject,
    mut v___y_3409_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3410_: *mut LeanObject = core::ptr::null_mut();
    v_res_3410_ =
        l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__0(v___y_3407_, v___y_3408_);
    lean_dec_ref(v___y_3408_);
    return v_res_3410_;
}
pub unsafe fn l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__3(
    mut v___x_3411_: *mut LeanObject,
    mut v___f_3412_: *mut LeanObject,
    mut v_a_3413_: *mut LeanObject,
    mut v_x_3414_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3419_: u8 = 0;
    let mut v___x_3421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3424_: u8 = 0;
    let mut v_a_3425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3426_: usize = 0;
    let mut v___x_3427_: usize = 0;
    let mut v___x_4336__overap_3428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3429_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3414_) == 0 {
                    lean_dec_ref(v___f_3412_);
                    lean_dec_ref(v___x_3411_);
                    v_a_3416_ = lean_ctor_get(v_x_3414_, 0);
                    v_isSharedCheck_3424_ = (!lean_is_exclusive(v_x_3414_)) as u8;
                    if v_isSharedCheck_3424_ == 0 {
                        v___x_3418_ = v_x_3414_;
                        v_isShared_3419_ = v_isSharedCheck_3424_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3416_);
                        lean_dec(v_x_3414_);
                        v___x_3418_ = lean_box(0);
                        v_isShared_3419_ = v_isSharedCheck_3424_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3425_ = lean_ctor_get(v_x_3414_, 0);
                    lean_inc(v_a_3425_);
                    lean_dec_ref_known(v_x_3414_, 1);
                    v_sz_3426_ = lean_array_size(v_a_3425_);
                    v___x_3427_ = 0usize;
                    v___x_4336__overap_3428_ =
                        l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                            lean_box(0),
                            lean_box(0),
                            lean_box(0),
                            v___x_3411_,
                            v___f_3412_,
                            v_sz_3426_,
                            v___x_3427_,
                            v_a_3425_,
                        );
                    lean_inc_ref(v_a_3413_);
                    v___x_3429_ = lean_apply_2(v___x_4336__overap_3428_, v_a_3413_, lean_box(0));
                    return v___x_3429_;
                }
            }
            1 => {
                if v_isShared_3419_ == 0 {
                    v___x_3421_ = v___x_3418_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3423_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3423_, 0, v_a_3416_);
                    v___x_3421_ = v_reuseFailAlloc_3423_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3422_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3422_, 0, v___x_3421_);
                return v___x_3422_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__3___boxed(
    mut v___x_3430_: *mut LeanObject,
    mut v___f_3431_: *mut LeanObject,
    mut v_a_3432_: *mut LeanObject,
    mut v_x_3433_: *mut LeanObject,
    mut v___y_3434_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3435_: *mut LeanObject = core::ptr::null_mut();
    v_res_3435_ = l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__3(
        v___x_3430_,
        v___f_3431_,
        v_a_3432_,
        v_x_3433_,
    );
    lean_dec_ref(v_a_3432_);
    return v_res_3435_;
}
pub unsafe fn l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__4(
    mut v_ctxAsync_3436_: *mut LeanObject,
    mut v_a_3437_: *mut LeanObject,
    mut v___f_3438_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: u8 = 0;
    let mut v___x_3443_: *mut LeanObject = core::ptr::null_mut();
    v___x_3440_ = lean_apply_2(v_ctxAsync_3436_, v_a_3437_, lean_box(0));
    v___x_3441_ = lean_unsigned_to_nat(0);
    v___x_3442_ = 0;
    v___x_3443_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_3441_,
        v___x_3442_,
        v___x_3440_,
        v___f_3438_,
    );
    return v___x_3443_;
}
pub unsafe fn l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__4___boxed(
    mut v_ctxAsync_3444_: *mut LeanObject,
    mut v_a_3445_: *mut LeanObject,
    mut v___f_3446_: *mut LeanObject,
    mut v___y_3447_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3448_: *mut LeanObject = core::ptr::null_mut();
    v_res_3448_ = l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__4(
        v_ctxAsync_3444_,
        v_a_3445_,
        v___f_3446_,
    );
    return v_res_3448_;
}
pub unsafe fn l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__1(
    mut v_a_3449_: *mut LeanObject,
    mut v___x_3450_: *mut LeanObject,
    mut v_a_x3f_3451_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3455_: *mut LeanObject = core::ptr::null_mut();
    v___x_3453_ = l_Std_CancellationContext_cancel(v_a_3449_, v___x_3450_);
    v___x_3454_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_3454_, 0, v___x_3453_);
    v___x_3455_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3455_, 0, v___x_3454_);
    return v___x_3455_;
}
pub unsafe fn l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__1___boxed(
    mut v_a_3456_: *mut LeanObject,
    mut v___x_3457_: *mut LeanObject,
    mut v_a_x3f_3458_: *mut LeanObject,
    mut v___y_3459_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3460_: *mut LeanObject = core::ptr::null_mut();
    v_res_3460_ = l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__1(
        v_a_3456_,
        v___x_3457_,
        v_a_x3f_3458_,
    );
    lean_dec(v_a_x3f_3458_);
    return v_res_3460_;
}
pub unsafe fn l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__5(
    mut v_ctxAsync_3461_: *mut LeanObject,
    mut v___f_3462_: *mut LeanObject,
    mut v___f_3463_: *mut LeanObject,
    mut v_prio_3464_: *mut LeanObject,
    mut v___f_3465_: *mut LeanObject,
    mut v_x_3466_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3471_: u8 = 0;
    let mut v___x_3473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3476_: u8 = 0;
    let mut v_a_3477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3480_: u8 = 0;
    let mut v___f_3481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3488_: u8 = 0;
    let mut v___x_3489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3494_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3466_) == 0 {
                    lean_dec_ref(v___f_3465_);
                    lean_dec(v_prio_3464_);
                    lean_dec(v___f_3463_);
                    lean_dec_ref(v___f_3462_);
                    lean_dec_ref(v_ctxAsync_3461_);
                    v_a_3468_ = lean_ctor_get(v_x_3466_, 0);
                    v_isSharedCheck_3476_ = (!lean_is_exclusive(v_x_3466_)) as u8;
                    if v_isSharedCheck_3476_ == 0 {
                        v___x_3470_ = v_x_3466_;
                        v_isShared_3471_ = v_isSharedCheck_3476_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3468_);
                        lean_dec(v_x_3466_);
                        v___x_3470_ = lean_box(0);
                        v_isShared_3471_ = v_isSharedCheck_3476_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3477_ = lean_ctor_get(v_x_3466_, 0);
                    v_isSharedCheck_3494_ = (!lean_is_exclusive(v_x_3466_)) as u8;
                    if v_isSharedCheck_3494_ == 0 {
                        v___x_3479_ = v_x_3466_;
                        v_isShared_3480_ = v_isSharedCheck_3494_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3477_);
                        lean_dec(v_x_3466_);
                        v___x_3479_ = lean_box(0);
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
                    v_reuseFailAlloc_3475_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3475_, 0, v_a_3468_);
                    v___x_3473_ = v_reuseFailAlloc_3475_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3474_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3474_, 0, v___x_3473_);
                return v___x_3474_;
            }
            3 => {
                lean_inc(v_a_3477_);
                v___f_3481_ = lean_alloc_closure(
                    l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__4___boxed
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                lean_closure_set(v___f_3481_, 0, v_ctxAsync_3461_);
                lean_closure_set(v___f_3481_, 1, v_a_3477_);
                lean_closure_set(v___f_3481_, 2, v___f_3462_);
                v___x_3482_ = lean_box(2);
                v___f_3483_ = lean_alloc_closure(
                    l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__1___boxed
                        as *mut core::ffi::c_void,
                    4,
                    2,
                );
                lean_closure_set(v___f_3483_, 0, v_a_3477_);
                lean_closure_set(v___f_3483_, 1, v___x_3482_);
                v___f_3484_ = lean_alloc_closure(
                    l_Std_Async_ContextAsync_concurrently___redArg___lam__5___boxed
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                lean_closure_set(v___f_3484_, 0, v___f_3481_);
                lean_closure_set(v___f_3484_, 1, v___f_3483_);
                lean_closure_set(v___f_3484_, 2, v___f_3463_);
                v___x_3485_ = lean_alloc_closure(
                    l_Std_Async_BaseAsync_toRawBaseIO___boxed as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___x_3485_, 0, lean_box(0));
                lean_closure_set(v___x_3485_, 1, v___f_3484_);
                v___x_3486_ = lean_io_as_task(v___x_3485_, v_prio_3464_);
                v___x_3487_ = lean_unsigned_to_nat(0);
                v___x_3488_ = 1;
                v___x_3489_ = lean_task_bind(v___x_3486_, v___f_3465_, v___x_3487_, v___x_3488_);
                if v_isShared_3480_ == 0 {
                    lean_ctor_set(v___x_3479_, 0, v___x_3489_);
                    v___x_3491_ = v___x_3479_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3493_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3493_, 0, v___x_3489_);
                    v___x_3491_ = v_reuseFailAlloc_3493_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3492_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3492_, 0, v___x_3491_);
                return v___x_3492_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__5___boxed(
    mut v_ctxAsync_3495_: *mut LeanObject,
    mut v___f_3496_: *mut LeanObject,
    mut v___f_3497_: *mut LeanObject,
    mut v_prio_3498_: *mut LeanObject,
    mut v___f_3499_: *mut LeanObject,
    mut v_x_3500_: *mut LeanObject,
    mut v___y_3501_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3502_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_a_3503_: *mut LeanObject,
    mut v___f_3504_: *mut LeanObject,
    mut v___f_3505_: *mut LeanObject,
    mut v_prio_3506_: *mut LeanObject,
    mut v___f_3507_: *mut LeanObject,
    mut v_ctxAsync_3508_: *mut LeanObject,
    mut v___y_3509_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: u8 = 0;
    let mut v___x_3517_: *mut LeanObject = core::ptr::null_mut();
    v___x_3511_ = l_Std_CancellationContext_fork(v_a_3503_);
    v___f_3512_ = lean_alloc_closure(
        l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__5___boxed
            as *mut core::ffi::c_void,
        7,
        5,
    );
    lean_closure_set(v___f_3512_, 0, v_ctxAsync_3508_);
    lean_closure_set(v___f_3512_, 1, v___f_3504_);
    lean_closure_set(v___f_3512_, 2, v___f_3505_);
    lean_closure_set(v___f_3512_, 3, v_prio_3506_);
    lean_closure_set(v___f_3512_, 4, v___f_3507_);
    v___x_3513_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_3513_, 0, v___x_3511_);
    v___x_3514_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3514_, 0, v___x_3513_);
    v___x_3515_ = lean_unsigned_to_nat(0);
    v___x_3516_ = 0;
    v___x_3517_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_3515_,
        v___x_3516_,
        v___x_3514_,
        v___f_3512_,
    );
    return v___x_3517_;
}
pub unsafe fn l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__2___boxed(
    mut v_a_3518_: *mut LeanObject,
    mut v___f_3519_: *mut LeanObject,
    mut v___f_3520_: *mut LeanObject,
    mut v_prio_3521_: *mut LeanObject,
    mut v___f_3522_: *mut LeanObject,
    mut v_ctxAsync_3523_: *mut LeanObject,
    mut v___y_3524_: *mut LeanObject,
    mut v___y_3525_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3526_: *mut LeanObject = core::ptr::null_mut();
    v_res_3526_ = l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__2(
        v_a_3518_,
        v___f_3519_,
        v___f_3520_,
        v_prio_3521_,
        v___f_3522_,
        v_ctxAsync_3523_,
        v___y_3524_,
    );
    lean_dec_ref(v___y_3524_);
    return v_res_3526_;
}
pub unsafe fn l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__6(
    mut v___f_3527_: *mut LeanObject,
    mut v_prio_3528_: *mut LeanObject,
    mut v___f_3529_: *mut LeanObject,
    mut v_xs_3530_: *mut LeanObject,
    mut v___x_3531_: *mut LeanObject,
    mut v_a_3532_: *mut LeanObject,
    mut v___f_3533_: *mut LeanObject,
    mut v_x_3534_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3539_: u8 = 0;
    let mut v___x_3541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3544_: u8 = 0;
    let mut v_a_3545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3548_: usize = 0;
    let mut v___x_3549_: usize = 0;
    let mut v___x_4458__overap_3550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3553_: u8 = 0;
    let mut v___x_3554_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3534_) == 0 {
                    lean_dec_ref(v___f_3533_);
                    lean_dec_ref(v___x_3531_);
                    lean_dec_ref(v_xs_3530_);
                    lean_dec_ref(v___f_3529_);
                    lean_dec(v_prio_3528_);
                    lean_dec(v___f_3527_);
                    v_a_3536_ = lean_ctor_get(v_x_3534_, 0);
                    v_isSharedCheck_3544_ = (!lean_is_exclusive(v_x_3534_)) as u8;
                    if v_isSharedCheck_3544_ == 0 {
                        v___x_3538_ = v_x_3534_;
                        v_isShared_3539_ = v_isSharedCheck_3544_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3536_);
                        lean_dec(v_x_3534_);
                        v___x_3538_ = lean_box(0);
                        v_isShared_3539_ = v_isSharedCheck_3544_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3545_ = lean_ctor_get(v_x_3534_, 0);
                    lean_inc_n(v_a_3545_, 2);
                    lean_dec_ref_known(v_x_3534_, 1);
                    v___f_3546_ = lean_alloc_closure(
                        l_Std_Async_ContextAsync_concurrently___redArg___lam__4___boxed
                            as *mut core::ffi::c_void,
                        3,
                        1,
                    );
                    lean_closure_set(v___f_3546_, 0, v_a_3545_);
                    v___f_3547_ = lean_alloc_closure(
                        l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__2___boxed
                            as *mut core::ffi::c_void,
                        8,
                        5,
                    );
                    lean_closure_set(v___f_3547_, 0, v_a_3545_);
                    lean_closure_set(v___f_3547_, 1, v___f_3546_);
                    lean_closure_set(v___f_3547_, 2, v___f_3527_);
                    lean_closure_set(v___f_3547_, 3, v_prio_3528_);
                    lean_closure_set(v___f_3547_, 4, v___f_3529_);
                    v_sz_3548_ = lean_array_size(v_xs_3530_);
                    v___x_3549_ = 0usize;
                    v___x_4458__overap_3550_ =
                        l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                            lean_box(0),
                            lean_box(0),
                            lean_box(0),
                            v___x_3531_,
                            v___f_3547_,
                            v_sz_3548_,
                            v___x_3549_,
                            v_xs_3530_,
                        );
                    lean_inc_ref(v_a_3532_);
                    v___x_3551_ = lean_apply_2(v___x_4458__overap_3550_, v_a_3532_, lean_box(0));
                    v___x_3552_ = lean_unsigned_to_nat(0);
                    v___x_3553_ = 0;
                    v___x_3554_ =
                        l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                            lean_box(0),
                            lean_box(0),
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
                    v_reuseFailAlloc_3543_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3543_, 0, v_a_3536_);
                    v___x_3541_ = v_reuseFailAlloc_3543_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3542_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3542_, 0, v___x_3541_);
                return v___x_3542_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__6___boxed(
    mut v___f_3555_: *mut LeanObject,
    mut v_prio_3556_: *mut LeanObject,
    mut v___f_3557_: *mut LeanObject,
    mut v_xs_3558_: *mut LeanObject,
    mut v___x_3559_: *mut LeanObject,
    mut v_a_3560_: *mut LeanObject,
    mut v___f_3561_: *mut LeanObject,
    mut v_x_3562_: *mut LeanObject,
    mut v___y_3563_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3564_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_a_3560_);
    return v_res_3564_;
}
pub unsafe fn l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__7(
    mut v___f_3565_: *mut LeanObject,
    mut v_x_3566_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3571_: u8 = 0;
    let mut v___x_3573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3576_: u8 = 0;
    let mut v_a_3577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3580_: u8 = 0;
    let mut v___x_3581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3586_: u8 = 0;
    let mut v___x_3587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3589_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3566_) == 0 {
                    lean_dec_ref(v___f_3565_);
                    v_a_3568_ = lean_ctor_get(v_x_3566_, 0);
                    v_isSharedCheck_3576_ = (!lean_is_exclusive(v_x_3566_)) as u8;
                    if v_isSharedCheck_3576_ == 0 {
                        v___x_3570_ = v_x_3566_;
                        v_isShared_3571_ = v_isSharedCheck_3576_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3568_);
                        lean_dec(v_x_3566_);
                        v___x_3570_ = lean_box(0);
                        v_isShared_3571_ = v_isSharedCheck_3576_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3577_ = lean_ctor_get(v_x_3566_, 0);
                    v_isSharedCheck_3589_ = (!lean_is_exclusive(v_x_3566_)) as u8;
                    if v_isSharedCheck_3589_ == 0 {
                        v___x_3579_ = v_x_3566_;
                        v_isShared_3580_ = v_isSharedCheck_3589_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3577_);
                        lean_dec(v_x_3566_);
                        v___x_3579_ = lean_box(0);
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
                    v_reuseFailAlloc_3575_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3575_, 0, v_a_3568_);
                    v___x_3573_ = v_reuseFailAlloc_3575_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3574_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3574_, 0, v___x_3573_);
                return v___x_3574_;
            }
            3 => {
                v___x_3581_ = l_Std_CancellationContext_fork(v_a_3577_);
                if v_isShared_3580_ == 0 {
                    lean_ctor_set(v___x_3579_, 0, v___x_3581_);
                    v___x_3583_ = v___x_3579_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3588_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3588_, 0, v___x_3581_);
                    v___x_3583_ = v_reuseFailAlloc_3588_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3584_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3584_, 0, v___x_3583_);
                v___x_3585_ = lean_unsigned_to_nat(0);
                v___x_3586_ = 0;
                v___x_3587_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
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
    mut v___f_3590_: *mut LeanObject,
    mut v_x_3591_: *mut LeanObject,
    mut v___y_3592_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3593_: *mut LeanObject = core::ptr::null_mut();
    v_res_3593_ =
        l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__7(v___f_3590_, v_x_3591_);
    return v_res_3593_;
}
pub unsafe fn _init_l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_3595_: *mut LeanObject = core::ptr::null_mut();
    v___x_3595_ = l_Std_Async_EAsync_instMonad(lean_box(0));
    return v___x_3595_;
}
pub unsafe fn _init_l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_3596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: *mut LeanObject = core::ptr::null_mut();
    v___x_3596_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__1_once),
        _init_l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__1,
    );
    v___x_3597_ = l_ReaderT_instMonad___redArg(v___x_3596_);
    return v___x_3597_;
}
pub unsafe fn l_Std_Async_ContextAsync_concurrentlyAll___redArg(
    mut v_xs_3598_: *mut LeanObject,
    mut v_prio_3599_: *mut LeanObject,
    mut v_a_3600_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: u8 = 0;
    let mut v___x_3613_: *mut LeanObject = core::ptr::null_mut();
    v___f_3602_ = l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__0;
    v___f_3603_ = l_Std_Async_ContextAsync_concurrently___redArg___closed__0;
    v___f_3604_ = l_Std_Async_ContextAsync_concurrently___redArg___closed__1;
    v___x_3605_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__2),
        core::ptr::addr_of_mut!(l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__2_once),
        _init_l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__2,
    );
    lean_inc_ref_n(v_a_3600_, 3);
    v___f_3606_ = lean_alloc_closure(
        l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__3___boxed
            as *mut core::ffi::c_void,
        5,
        3,
    );
    lean_closure_set(v___f_3606_, 0, v___x_3605_);
    lean_closure_set(v___f_3606_, 1, v___f_3602_);
    lean_closure_set(v___f_3606_, 2, v_a_3600_);
    v___f_3607_ = lean_alloc_closure(
        l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__6___boxed
            as *mut core::ffi::c_void,
        9,
        7,
    );
    lean_closure_set(v___f_3607_, 0, v___f_3604_);
    lean_closure_set(v___f_3607_, 1, v_prio_3599_);
    lean_closure_set(v___f_3607_, 2, v___f_3603_);
    lean_closure_set(v___f_3607_, 3, v_xs_3598_);
    lean_closure_set(v___f_3607_, 4, v___x_3605_);
    lean_closure_set(v___f_3607_, 5, v_a_3600_);
    lean_closure_set(v___f_3607_, 6, v___f_3606_);
    v___f_3608_ = lean_alloc_closure(
        l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__7___boxed
            as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_3608_, 0, v___f_3607_);
    v___x_3609_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_3609_, 0, v_a_3600_);
    v___x_3610_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3610_, 0, v___x_3609_);
    v___x_3611_ = lean_unsigned_to_nat(0);
    v___x_3612_ = 0;
    v___x_3613_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_3611_,
        v___x_3612_,
        v___x_3610_,
        v___f_3608_,
    );
    return v___x_3613_;
}
pub unsafe fn l_Std_Async_ContextAsync_concurrentlyAll___redArg___boxed(
    mut v_xs_3614_: *mut LeanObject,
    mut v_prio_3615_: *mut LeanObject,
    mut v_a_3616_: *mut LeanObject,
    mut v_a_3617_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3618_: *mut LeanObject = core::ptr::null_mut();
    v_res_3618_ =
        l_Std_Async_ContextAsync_concurrentlyAll___redArg(v_xs_3614_, v_prio_3615_, v_a_3616_);
    lean_dec_ref(v_a_3616_);
    return v_res_3618_;
}
pub unsafe fn l_Std_Async_ContextAsync_concurrentlyAll(
    mut v_00_u03b1_3619_: *mut LeanObject,
    mut v_xs_3620_: *mut LeanObject,
    mut v_prio_3621_: *mut LeanObject,
    mut v_a_3622_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: u8 = 0;
    let mut v___x_3635_: *mut LeanObject = core::ptr::null_mut();
    v___f_3624_ = l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__0;
    v___f_3625_ = l_Std_Async_ContextAsync_concurrently___redArg___closed__0;
    v___f_3626_ = l_Std_Async_ContextAsync_concurrently___redArg___closed__1;
    v___x_3627_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__2),
        core::ptr::addr_of_mut!(l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__2_once),
        _init_l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__2,
    );
    lean_inc_ref_n(v_a_3622_, 3);
    v___f_3628_ = lean_alloc_closure(
        l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__3___boxed
            as *mut core::ffi::c_void,
        5,
        3,
    );
    lean_closure_set(v___f_3628_, 0, v___x_3627_);
    lean_closure_set(v___f_3628_, 1, v___f_3624_);
    lean_closure_set(v___f_3628_, 2, v_a_3622_);
    v___f_3629_ = lean_alloc_closure(
        l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__6___boxed
            as *mut core::ffi::c_void,
        9,
        7,
    );
    lean_closure_set(v___f_3629_, 0, v___f_3626_);
    lean_closure_set(v___f_3629_, 1, v_prio_3621_);
    lean_closure_set(v___f_3629_, 2, v___f_3625_);
    lean_closure_set(v___f_3629_, 3, v_xs_3620_);
    lean_closure_set(v___f_3629_, 4, v___x_3627_);
    lean_closure_set(v___f_3629_, 5, v_a_3622_);
    lean_closure_set(v___f_3629_, 6, v___f_3628_);
    v___f_3630_ = lean_alloc_closure(
        l_Std_Async_ContextAsync_concurrentlyAll___redArg___lam__7___boxed
            as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_3630_, 0, v___f_3629_);
    v___x_3631_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_3631_, 0, v_a_3622_);
    v___x_3632_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3632_, 0, v___x_3631_);
    v___x_3633_ = lean_unsigned_to_nat(0);
    v___x_3634_ = 0;
    v___x_3635_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_3633_,
        v___x_3634_,
        v___x_3632_,
        v___f_3630_,
    );
    return v___x_3635_;
}
pub unsafe fn l_Std_Async_ContextAsync_concurrentlyAll___boxed(
    mut v_00_u03b1_3636_: *mut LeanObject,
    mut v_xs_3637_: *mut LeanObject,
    mut v_prio_3638_: *mut LeanObject,
    mut v_a_3639_: *mut LeanObject,
    mut v_a_3640_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3641_: *mut LeanObject = core::ptr::null_mut();
    v_res_3641_ = l_Std_Async_ContextAsync_concurrentlyAll(
        v_00_u03b1_3636_,
        v_xs_3637_,
        v_prio_3638_,
        v_a_3639_,
    );
    lean_dec_ref(v_a_3639_);
    return v_res_3641_;
}
pub unsafe fn l_Std_Async_ContextAsync_background___redArg___lam__0(
    mut v_a_3642_: *mut LeanObject,
    mut v_x_3643_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3648_: u8 = 0;
    let mut v___x_3650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3653_: u8 = 0;
    let mut v___x_3655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3656_: u8 = 0;
    let mut v___x_3657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3663_: u8 = 0;
    let mut v_unused_3664_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3643_) == 0 {
                    lean_dec_ref(v_a_3642_);
                    v_a_3645_ = lean_ctor_get(v_x_3643_, 0);
                    v_isSharedCheck_3653_ = (!lean_is_exclusive(v_x_3643_)) as u8;
                    if v_isSharedCheck_3653_ == 0 {
                        v___x_3647_ = v_x_3643_;
                        v_isShared_3648_ = v_isSharedCheck_3653_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3645_);
                        lean_dec(v_x_3643_);
                        v___x_3647_ = lean_box(0);
                        v_isShared_3648_ = v_isSharedCheck_3653_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_isSharedCheck_3663_ = (!lean_is_exclusive(v_x_3643_)) as u8;
                    if v_isSharedCheck_3663_ == 0 {
                        v_unused_3664_ = lean_ctor_get(v_x_3643_, 0);
                        lean_dec(v_unused_3664_);
                        v___x_3655_ = v_x_3643_;
                        v_isShared_3656_ = v_isSharedCheck_3663_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v_x_3643_);
                        v___x_3655_ = lean_box(0);
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
                    v_reuseFailAlloc_3652_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3652_, 0, v_a_3645_);
                    v___x_3650_ = v_reuseFailAlloc_3652_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3651_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3651_, 0, v___x_3650_);
                return v___x_3651_;
            }
            3 => {
                v___x_3657_ = lean_box(2);
                v___x_3658_ = l_Std_CancellationContext_cancel(v_a_3642_, v___x_3657_);
                if v_isShared_3656_ == 0 {
                    lean_ctor_set(v___x_3655_, 0, v___x_3658_);
                    v___x_3660_ = v___x_3655_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3662_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3662_, 0, v___x_3658_);
                    v___x_3660_ = v_reuseFailAlloc_3662_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3661_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3661_, 0, v___x_3660_);
                return v___x_3661_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_background___redArg___lam__0___boxed(
    mut v_a_3665_: *mut LeanObject,
    mut v_x_3666_: *mut LeanObject,
    mut v___y_3667_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3668_: *mut LeanObject = core::ptr::null_mut();
    v_res_3668_ = l_Std_Async_ContextAsync_background___redArg___lam__0(v_a_3665_, v_x_3666_);
    return v_res_3668_;
}
pub unsafe fn l_Std_Async_ContextAsync_background___redArg___lam__1(
    mut v_action_3669_: *mut LeanObject,
    mut v_a_3670_: *mut LeanObject,
    mut v___f_3671_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3675_: u8 = 0;
    let mut v___x_3676_: *mut LeanObject = core::ptr::null_mut();
    v___x_3673_ = lean_apply_2(v_action_3669_, v_a_3670_, lean_box(0));
    v___x_3674_ = lean_unsigned_to_nat(0);
    v___x_3675_ = 0;
    v___x_3676_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_3674_,
        v___x_3675_,
        v___x_3673_,
        v___f_3671_,
    );
    return v___x_3676_;
}
pub unsafe fn l_Std_Async_ContextAsync_background___redArg___lam__1___boxed(
    mut v_action_3677_: *mut LeanObject,
    mut v_a_3678_: *mut LeanObject,
    mut v___f_3679_: *mut LeanObject,
    mut v___y_3680_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3681_: *mut LeanObject = core::ptr::null_mut();
    v_res_3681_ = l_Std_Async_ContextAsync_background___redArg___lam__1(
        v_action_3677_,
        v_a_3678_,
        v___f_3679_,
    );
    return v_res_3681_;
}
pub unsafe fn l_Std_Async_ContextAsync_background___redArg___lam__2(
    mut v_action_3686_: *mut LeanObject,
    mut v_prio_3687_: *mut LeanObject,
    mut v_x_3688_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3693_: u8 = 0;
    let mut v___x_3695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3698_: u8 = 0;
    let mut v_a_3699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3704_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3688_) == 0 {
                    lean_dec(v_prio_3687_);
                    lean_dec_ref(v_action_3686_);
                    v_a_3690_ = lean_ctor_get(v_x_3688_, 0);
                    v_isSharedCheck_3698_ = (!lean_is_exclusive(v_x_3688_)) as u8;
                    if v_isSharedCheck_3698_ == 0 {
                        v___x_3692_ = v_x_3688_;
                        v_isShared_3693_ = v_isSharedCheck_3698_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3690_);
                        lean_dec(v_x_3688_);
                        v___x_3692_ = lean_box(0);
                        v_isShared_3693_ = v_isSharedCheck_3698_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3699_ = lean_ctor_get(v_x_3688_, 0);
                    lean_inc_n(v_a_3699_, 2);
                    lean_dec_ref_known(v_x_3688_, 1);
                    v___f_3700_ = lean_alloc_closure(
                        l_Std_Async_ContextAsync_background___redArg___lam__0___boxed
                            as *mut core::ffi::c_void,
                        3,
                        1,
                    );
                    lean_closure_set(v___f_3700_, 0, v_a_3699_);
                    v___f_3701_ = lean_alloc_closure(
                        l_Std_Async_ContextAsync_background___redArg___lam__1___boxed
                            as *mut core::ffi::c_void,
                        4,
                        3,
                    );
                    lean_closure_set(v___f_3701_, 0, v_action_3686_);
                    lean_closure_set(v___f_3701_, 1, v_a_3699_);
                    lean_closure_set(v___f_3701_, 2, v___f_3700_);
                    v___x_3702_ = lean_alloc_closure(
                        l_Std_Async_BaseAsync_toRawBaseIO___boxed as *mut core::ffi::c_void,
                        3,
                        2,
                    );
                    lean_closure_set(v___x_3702_, 0, lean_box(0));
                    lean_closure_set(v___x_3702_, 1, v___f_3701_);
                    v___x_3703_ = lean_io_as_task(v___x_3702_, v_prio_3687_);
                    lean_dec_ref(v___x_3703_);
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
                    v_reuseFailAlloc_3697_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3697_, 0, v_a_3690_);
                    v___x_3695_ = v_reuseFailAlloc_3697_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3696_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3696_, 0, v___x_3695_);
                return v___x_3696_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_background___redArg___lam__2___boxed(
    mut v_action_3705_: *mut LeanObject,
    mut v_prio_3706_: *mut LeanObject,
    mut v_x_3707_: *mut LeanObject,
    mut v___y_3708_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3709_: *mut LeanObject = core::ptr::null_mut();
    v_res_3709_ = l_Std_Async_ContextAsync_background___redArg___lam__2(
        v_action_3705_,
        v_prio_3706_,
        v_x_3707_,
    );
    return v_res_3709_;
}
pub unsafe fn l_Std_Async_ContextAsync_background___redArg___lam__3(
    mut v___f_3710_: *mut LeanObject,
    mut v_x_3711_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3716_: u8 = 0;
    let mut v___x_3718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3721_: u8 = 0;
    let mut v_a_3722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3725_: u8 = 0;
    let mut v___x_3726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3731_: u8 = 0;
    let mut v___x_3732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3734_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3711_) == 0 {
                    lean_dec_ref(v___f_3710_);
                    v_a_3713_ = lean_ctor_get(v_x_3711_, 0);
                    v_isSharedCheck_3721_ = (!lean_is_exclusive(v_x_3711_)) as u8;
                    if v_isSharedCheck_3721_ == 0 {
                        v___x_3715_ = v_x_3711_;
                        v_isShared_3716_ = v_isSharedCheck_3721_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3713_);
                        lean_dec(v_x_3711_);
                        v___x_3715_ = lean_box(0);
                        v_isShared_3716_ = v_isSharedCheck_3721_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3722_ = lean_ctor_get(v_x_3711_, 0);
                    v_isSharedCheck_3734_ = (!lean_is_exclusive(v_x_3711_)) as u8;
                    if v_isSharedCheck_3734_ == 0 {
                        v___x_3724_ = v_x_3711_;
                        v_isShared_3725_ = v_isSharedCheck_3734_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3722_);
                        lean_dec(v_x_3711_);
                        v___x_3724_ = lean_box(0);
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
                    v_reuseFailAlloc_3720_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3720_, 0, v_a_3713_);
                    v___x_3718_ = v_reuseFailAlloc_3720_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3719_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3719_, 0, v___x_3718_);
                return v___x_3719_;
            }
            3 => {
                v___x_3726_ = l_Std_CancellationContext_fork(v_a_3722_);
                if v_isShared_3725_ == 0 {
                    lean_ctor_set(v___x_3724_, 0, v___x_3726_);
                    v___x_3728_ = v___x_3724_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3733_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3733_, 0, v___x_3726_);
                    v___x_3728_ = v_reuseFailAlloc_3733_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3729_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3729_, 0, v___x_3728_);
                v___x_3730_ = lean_unsigned_to_nat(0);
                v___x_3731_ = 0;
                v___x_3732_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
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
    mut v___f_3735_: *mut LeanObject,
    mut v_x_3736_: *mut LeanObject,
    mut v___y_3737_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3738_: *mut LeanObject = core::ptr::null_mut();
    v_res_3738_ = l_Std_Async_ContextAsync_background___redArg___lam__3(v___f_3735_, v_x_3736_);
    return v_res_3738_;
}
pub unsafe fn l_Std_Async_ContextAsync_background___redArg(
    mut v_action_3739_: *mut LeanObject,
    mut v_prio_3740_: *mut LeanObject,
    mut v_a_3741_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3748_: u8 = 0;
    let mut v___x_3749_: *mut LeanObject = core::ptr::null_mut();
    v___f_3743_ = lean_alloc_closure(
        l_Std_Async_ContextAsync_background___redArg___lam__2___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_3743_, 0, v_action_3739_);
    lean_closure_set(v___f_3743_, 1, v_prio_3740_);
    v___f_3744_ = lean_alloc_closure(
        l_Std_Async_ContextAsync_background___redArg___lam__3___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_3744_, 0, v___f_3743_);
    lean_inc_ref(v_a_3741_);
    v___x_3745_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_3745_, 0, v_a_3741_);
    v___x_3746_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3746_, 0, v___x_3745_);
    v___x_3747_ = lean_unsigned_to_nat(0);
    v___x_3748_ = 0;
    v___x_3749_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_3747_,
        v___x_3748_,
        v___x_3746_,
        v___f_3744_,
    );
    return v___x_3749_;
}
pub unsafe fn l_Std_Async_ContextAsync_background___redArg___boxed(
    mut v_action_3750_: *mut LeanObject,
    mut v_prio_3751_: *mut LeanObject,
    mut v_a_3752_: *mut LeanObject,
    mut v_a_3753_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3754_: *mut LeanObject = core::ptr::null_mut();
    v_res_3754_ =
        l_Std_Async_ContextAsync_background___redArg(v_action_3750_, v_prio_3751_, v_a_3752_);
    lean_dec_ref(v_a_3752_);
    return v_res_3754_;
}
pub unsafe fn l_Std_Async_ContextAsync_background(
    mut v_00_u03b1_3755_: *mut LeanObject,
    mut v_action_3756_: *mut LeanObject,
    mut v_prio_3757_: *mut LeanObject,
    mut v_a_3758_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3765_: u8 = 0;
    let mut v___x_3766_: *mut LeanObject = core::ptr::null_mut();
    v___f_3760_ = lean_alloc_closure(
        l_Std_Async_ContextAsync_background___redArg___lam__2___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_3760_, 0, v_action_3756_);
    lean_closure_set(v___f_3760_, 1, v_prio_3757_);
    v___f_3761_ = lean_alloc_closure(
        l_Std_Async_ContextAsync_background___redArg___lam__3___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_3761_, 0, v___f_3760_);
    lean_inc_ref(v_a_3758_);
    v___x_3762_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_3762_, 0, v_a_3758_);
    v___x_3763_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3763_, 0, v___x_3762_);
    v___x_3764_ = lean_unsigned_to_nat(0);
    v___x_3765_ = 0;
    v___x_3766_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_3764_,
        v___x_3765_,
        v___x_3763_,
        v___f_3761_,
    );
    return v___x_3766_;
}
pub unsafe fn l_Std_Async_ContextAsync_background___boxed(
    mut v_00_u03b1_3767_: *mut LeanObject,
    mut v_action_3768_: *mut LeanObject,
    mut v_prio_3769_: *mut LeanObject,
    mut v_a_3770_: *mut LeanObject,
    mut v_a_3771_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3772_: *mut LeanObject = core::ptr::null_mut();
    v_res_3772_ = l_Std_Async_ContextAsync_background(
        v_00_u03b1_3767_,
        v_action_3768_,
        v_prio_3769_,
        v_a_3770_,
    );
    lean_dec_ref(v_a_3770_);
    return v_res_3772_;
}
pub unsafe fn l_Std_Async_ContextAsync_disown___redArg___lam__0(
    mut v_action_3773_: *mut LeanObject,
    mut v_a_3774_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3776_: *mut LeanObject = core::ptr::null_mut();
    v___x_3776_ = lean_apply_2(v_action_3773_, v_a_3774_, lean_box(0));
    return v___x_3776_;
}
pub unsafe fn l_Std_Async_ContextAsync_disown___redArg___lam__0___boxed(
    mut v_action_3777_: *mut LeanObject,
    mut v_a_3778_: *mut LeanObject,
    mut v___y_3779_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3780_: *mut LeanObject = core::ptr::null_mut();
    v_res_3780_ = l_Std_Async_ContextAsync_disown___redArg___lam__0(v_action_3777_, v_a_3778_);
    return v_res_3780_;
}
pub unsafe fn l_Std_Async_ContextAsync_disown___redArg___lam__1(
    mut v_action_3781_: *mut LeanObject,
    mut v_prio_3782_: *mut LeanObject,
    mut v_x_3783_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3788_: u8 = 0;
    let mut v___x_3790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3793_: u8 = 0;
    let mut v_a_3794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3798_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3783_) == 0 {
                    lean_dec(v_prio_3782_);
                    lean_dec_ref(v_action_3781_);
                    v_a_3785_ = lean_ctor_get(v_x_3783_, 0);
                    v_isSharedCheck_3793_ = (!lean_is_exclusive(v_x_3783_)) as u8;
                    if v_isSharedCheck_3793_ == 0 {
                        v___x_3787_ = v_x_3783_;
                        v_isShared_3788_ = v_isSharedCheck_3793_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3785_);
                        lean_dec(v_x_3783_);
                        v___x_3787_ = lean_box(0);
                        v_isShared_3788_ = v_isSharedCheck_3793_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3794_ = lean_ctor_get(v_x_3783_, 0);
                    lean_inc(v_a_3794_);
                    lean_dec_ref_known(v_x_3783_, 1);
                    v___f_3795_ = lean_alloc_closure(
                        l_Std_Async_ContextAsync_disown___redArg___lam__0___boxed
                            as *mut core::ffi::c_void,
                        3,
                        2,
                    );
                    lean_closure_set(v___f_3795_, 0, v_action_3781_);
                    lean_closure_set(v___f_3795_, 1, v_a_3794_);
                    v___x_3796_ = lean_alloc_closure(
                        l_Std_Async_BaseAsync_toRawBaseIO___boxed as *mut core::ffi::c_void,
                        3,
                        2,
                    );
                    lean_closure_set(v___x_3796_, 0, lean_box(0));
                    lean_closure_set(v___x_3796_, 1, v___f_3795_);
                    v___x_3797_ = lean_io_as_task(v___x_3796_, v_prio_3782_);
                    lean_dec_ref(v___x_3797_);
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
                    v_reuseFailAlloc_3792_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3792_, 0, v_a_3785_);
                    v___x_3790_ = v_reuseFailAlloc_3792_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3791_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3791_, 0, v___x_3790_);
                return v___x_3791_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_disown___redArg___lam__1___boxed(
    mut v_action_3799_: *mut LeanObject,
    mut v_prio_3800_: *mut LeanObject,
    mut v_x_3801_: *mut LeanObject,
    mut v___y_3802_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3803_: *mut LeanObject = core::ptr::null_mut();
    v_res_3803_ =
        l_Std_Async_ContextAsync_disown___redArg___lam__1(v_action_3799_, v_prio_3800_, v_x_3801_);
    return v_res_3803_;
}
pub unsafe fn l_Std_Async_ContextAsync_disown___redArg(
    mut v_action_3804_: *mut LeanObject,
    mut v_prio_3805_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3812_: u8 = 0;
    let mut v___x_3813_: *mut LeanObject = core::ptr::null_mut();
    v___x_3807_ = l_Std_CancellationContext_new();
    v___f_3808_ = lean_alloc_closure(
        l_Std_Async_ContextAsync_disown___redArg___lam__1___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_3808_, 0, v_action_3804_);
    lean_closure_set(v___f_3808_, 1, v_prio_3805_);
    v___x_3809_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_3809_, 0, v___x_3807_);
    v___x_3810_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3810_, 0, v___x_3809_);
    v___x_3811_ = lean_unsigned_to_nat(0);
    v___x_3812_ = 0;
    v___x_3813_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_3811_,
        v___x_3812_,
        v___x_3810_,
        v___f_3808_,
    );
    return v___x_3813_;
}
pub unsafe fn l_Std_Async_ContextAsync_disown___redArg___boxed(
    mut v_action_3814_: *mut LeanObject,
    mut v_prio_3815_: *mut LeanObject,
    mut v_a_3816_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3817_: *mut LeanObject = core::ptr::null_mut();
    v_res_3817_ = l_Std_Async_ContextAsync_disown___redArg(v_action_3814_, v_prio_3815_);
    return v_res_3817_;
}
pub unsafe fn l_Std_Async_ContextAsync_disown(
    mut v_00_u03b1_3818_: *mut LeanObject,
    mut v_action_3819_: *mut LeanObject,
    mut v_prio_3820_: *mut LeanObject,
    mut v_a_3821_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3828_: u8 = 0;
    let mut v___x_3829_: *mut LeanObject = core::ptr::null_mut();
    v___x_3823_ = l_Std_CancellationContext_new();
    v___f_3824_ = lean_alloc_closure(
        l_Std_Async_ContextAsync_disown___redArg___lam__1___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_3824_, 0, v_action_3819_);
    lean_closure_set(v___f_3824_, 1, v_prio_3820_);
    v___x_3825_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_3825_, 0, v___x_3823_);
    v___x_3826_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3826_, 0, v___x_3825_);
    v___x_3827_ = lean_unsigned_to_nat(0);
    v___x_3828_ = 0;
    v___x_3829_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_3827_,
        v___x_3828_,
        v___x_3826_,
        v___f_3824_,
    );
    return v___x_3829_;
}
pub unsafe fn l_Std_Async_ContextAsync_disown___boxed(
    mut v_00_u03b1_3830_: *mut LeanObject,
    mut v_action_3831_: *mut LeanObject,
    mut v_prio_3832_: *mut LeanObject,
    mut v_a_3833_: *mut LeanObject,
    mut v_a_3834_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3835_: *mut LeanObject = core::ptr::null_mut();
    v_res_3835_ =
        l_Std_Async_ContextAsync_disown(v_00_u03b1_3830_, v_action_3831_, v_prio_3832_, v_a_3833_);
    lean_dec_ref(v_a_3833_);
    return v_res_3835_;
}
pub unsafe fn l_Std_Async_ContextAsync_raceAll___redArg___lam__0(
    mut v_a_3836_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3837_: *mut LeanObject = core::ptr::null_mut();
    v___x_3837_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_3837_, 0, v_a_3836_);
    return v___x_3837_;
}
pub unsafe fn l_Std_Async_ContextAsync_raceAll___redArg___lam__2(
    mut v_a_3838_: *mut LeanObject,
    mut v_x_3839_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3844_: u8 = 0;
    let mut v___x_3846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3849_: u8 = 0;
    let mut v___x_3850_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3839_) == 0 {
                    lean_dec_ref(v_a_3838_);
                    v_a_3841_ = lean_ctor_get(v_x_3839_, 0);
                    v_isSharedCheck_3849_ = (!lean_is_exclusive(v_x_3839_)) as u8;
                    if v_isSharedCheck_3849_ == 0 {
                        v___x_3843_ = v_x_3839_;
                        v_isShared_3844_ = v_isSharedCheck_3849_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3841_);
                        lean_dec(v_x_3839_);
                        v___x_3843_ = lean_box(0);
                        v_isShared_3844_ = v_isSharedCheck_3849_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v_x_3839_, 1);
                    v___x_3850_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3850_, 0, v_a_3838_);
                    return v___x_3850_;
                }
            }
            1 => {
                if v_isShared_3844_ == 0 {
                    v___x_3846_ = v___x_3843_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3848_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3848_, 0, v_a_3841_);
                    v___x_3846_ = v_reuseFailAlloc_3848_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3847_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3847_, 0, v___x_3846_);
                return v___x_3847_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_raceAll___redArg___lam__2___boxed(
    mut v_a_3851_: *mut LeanObject,
    mut v_x_3852_: *mut LeanObject,
    mut v___y_3853_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3854_: *mut LeanObject = core::ptr::null_mut();
    v_res_3854_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__2(v_a_3851_, v_x_3852_);
    return v_res_3854_;
}
pub unsafe fn l_Std_Async_ContextAsync_raceAll___redArg___lam__1(
    mut v_a_3855_: *mut LeanObject,
    mut v_x_3856_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3861_: u8 = 0;
    let mut v___x_3863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3866_: u8 = 0;
    let mut v_a_3867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3870_: u8 = 0;
    let mut v___x_3871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: u8 = 0;
    let mut v___x_3879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3881_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3856_) == 0 {
                    lean_dec_ref(v_a_3855_);
                    v_a_3858_ = lean_ctor_get(v_x_3856_, 0);
                    v_isSharedCheck_3866_ = (!lean_is_exclusive(v_x_3856_)) as u8;
                    if v_isSharedCheck_3866_ == 0 {
                        v___x_3860_ = v_x_3856_;
                        v_isShared_3861_ = v_isSharedCheck_3866_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3858_);
                        lean_dec(v_x_3856_);
                        v___x_3860_ = lean_box(0);
                        v_isShared_3861_ = v_isSharedCheck_3866_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3867_ = lean_ctor_get(v_x_3856_, 0);
                    v_isSharedCheck_3881_ = (!lean_is_exclusive(v_x_3856_)) as u8;
                    if v_isSharedCheck_3881_ == 0 {
                        v___x_3869_ = v_x_3856_;
                        v_isShared_3870_ = v_isSharedCheck_3881_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3867_);
                        lean_dec(v_x_3856_);
                        v___x_3869_ = lean_box(0);
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
                    v_reuseFailAlloc_3865_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3865_, 0, v_a_3858_);
                    v___x_3863_ = v_reuseFailAlloc_3865_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3864_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3864_, 0, v___x_3863_);
                return v___x_3864_;
            }
            3 => {
                v___x_3871_ = lean_box(2);
                v___x_3872_ = l_Std_CancellationContext_cancel(v_a_3855_, v___x_3871_);
                v___f_3873_ = lean_alloc_closure(
                    l_Std_Async_ContextAsync_raceAll___redArg___lam__2___boxed
                        as *mut core::ffi::c_void,
                    3,
                    1,
                );
                lean_closure_set(v___f_3873_, 0, v_a_3867_);
                if v_isShared_3870_ == 0 {
                    lean_ctor_set(v___x_3869_, 0, v___x_3872_);
                    v___x_3875_ = v___x_3869_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3880_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3880_, 0, v___x_3872_);
                    v___x_3875_ = v_reuseFailAlloc_3880_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3876_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3876_, 0, v___x_3875_);
                v___x_3877_ = lean_unsigned_to_nat(0);
                v___x_3878_ = 0;
                v___x_3879_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
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
    mut v_a_3882_: *mut LeanObject,
    mut v_x_3883_: *mut LeanObject,
    mut v___y_3884_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3885_: *mut LeanObject = core::ptr::null_mut();
    v_res_3885_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__1(v_a_3882_, v_x_3883_);
    return v_res_3885_;
}
pub unsafe fn l_Std_Async_ContextAsync_raceAll___redArg___lam__3(
    mut v_a_3886_: *mut LeanObject,
    mut v_x_3887_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3892_: u8 = 0;
    let mut v___x_3894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3898_: u8 = 0;
    let mut v___x_3899_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3887_) == 0 {
                    v_a_3889_ = lean_ctor_get(v_x_3887_, 0);
                    v_isSharedCheck_3898_ = (!lean_is_exclusive(v_x_3887_)) as u8;
                    if v_isSharedCheck_3898_ == 0 {
                        v___x_3891_ = v_x_3887_;
                        v_isShared_3892_ = v_isSharedCheck_3898_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3889_);
                        lean_dec(v_x_3887_);
                        v___x_3891_ = lean_box(0);
                        v_isShared_3892_ = v_isSharedCheck_3898_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_3899_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3899_, 0, v_x_3887_);
                    return v___x_3899_;
                }
            }
            1 => {
                if v_isShared_3892_ == 0 {
                    v___x_3894_ = v___x_3891_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3897_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3897_, 0, v_a_3889_);
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
    mut v_a_3900_: *mut LeanObject,
    mut v_x_3901_: *mut LeanObject,
    mut v___y_3902_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3903_: *mut LeanObject = core::ptr::null_mut();
    v_res_3903_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__3(v_a_3900_, v_x_3901_);
    lean_dec(v_a_3900_);
    return v_res_3903_;
}
pub unsafe fn l_Std_Async_ContextAsync_raceAll___redArg___lam__4(
    mut v_a_3904_: *mut LeanObject,
    mut v_x_3905_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3910_: u8 = 0;
    let mut v___x_3912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3915_: u8 = 0;
    let mut v___x_3916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3905_) == 0 {
                    v_a_3907_ = lean_ctor_get(v_x_3905_, 0);
                    v_isSharedCheck_3915_ = (!lean_is_exclusive(v_x_3905_)) as u8;
                    if v_isSharedCheck_3915_ == 0 {
                        v___x_3909_ = v_x_3905_;
                        v_isShared_3910_ = v_isSharedCheck_3915_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3907_);
                        lean_dec(v_x_3905_);
                        v___x_3909_ = lean_box(0);
                        v_isShared_3910_ = v_isSharedCheck_3915_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_3916_ = lean_io_promise_resolve(v_x_3905_, v_a_3904_);
                    v___x_3917_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3917_, 0, v___x_3916_);
                    v___x_3918_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3918_, 0, v___x_3917_);
                    return v___x_3918_;
                }
            }
            1 => {
                if v_isShared_3910_ == 0 {
                    v___x_3912_ = v___x_3909_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3914_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3914_, 0, v_a_3907_);
                    v___x_3912_ = v_reuseFailAlloc_3914_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3913_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3913_, 0, v___x_3912_);
                return v___x_3913_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_raceAll___redArg___lam__4___boxed(
    mut v_a_3919_: *mut LeanObject,
    mut v_x_3920_: *mut LeanObject,
    mut v___y_3921_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3922_: *mut LeanObject = core::ptr::null_mut();
    v_res_3922_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__4(v_a_3919_, v_x_3920_);
    lean_dec(v_a_3919_);
    return v_res_3922_;
}
pub unsafe fn l_Std_Async_ContextAsync_raceAll___redArg___lam__5(
    mut v_a_3923_: *mut LeanObject,
    mut v_x_3924_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3929_: u8 = 0;
    let mut v___x_3930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3936_: u8 = 0;
    let mut v_unused_3937_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3924_) == 0 {
                    lean_dec_ref(v_a_3923_);
                    v___x_3926_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3926_, 0, v_x_3924_);
                    return v___x_3926_;
                } else {
                    v_isSharedCheck_3936_ = (!lean_is_exclusive(v_x_3924_)) as u8;
                    if v_isSharedCheck_3936_ == 0 {
                        v_unused_3937_ = lean_ctor_get(v_x_3924_, 0);
                        lean_dec(v_unused_3937_);
                        v___x_3928_ = v_x_3924_;
                        v_isShared_3929_ = v_isSharedCheck_3936_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_x_3924_);
                        v___x_3928_ = lean_box(0);
                        v_isShared_3929_ = v_isSharedCheck_3936_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3930_ = lean_box(2);
                v___x_3931_ = l_Std_CancellationContext_cancel(v_a_3923_, v___x_3930_);
                if v_isShared_3929_ == 0 {
                    lean_ctor_set(v___x_3928_, 0, v___x_3931_);
                    v___x_3933_ = v___x_3928_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3935_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3935_, 0, v___x_3931_);
                    v___x_3933_ = v_reuseFailAlloc_3935_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3934_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3934_, 0, v___x_3933_);
                return v___x_3934_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_raceAll___redArg___lam__5___boxed(
    mut v_a_3938_: *mut LeanObject,
    mut v_x_3939_: *mut LeanObject,
    mut v___y_3940_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3941_: *mut LeanObject = core::ptr::null_mut();
    v_res_3941_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__5(v_a_3938_, v_x_3939_);
    return v_res_3941_;
}
pub unsafe fn l_Std_Async_ContextAsync_raceAll___redArg___lam__6(
    mut v_a_3942_: *mut LeanObject,
    mut v___x_3943_: *mut LeanObject,
    mut v___f_3944_: *mut LeanObject,
    mut v___f_3945_: *mut LeanObject,
    mut v___f_3946_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3949_: u8 = 0;
    let mut v___x_3950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3952_: *mut LeanObject = core::ptr::null_mut();
    v___x_3948_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_3948_, 0, v_a_3942_);
    v___x_3949_ = 0;
    lean_inc_n(v___x_3943_, 2);
    v___x_3950_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_3943_,
        v___x_3949_,
        v___x_3948_,
        v___f_3944_,
    );
    v___x_3951_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_3943_,
        v___x_3949_,
        v___x_3950_,
        v___f_3945_,
    );
    v___x_3952_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_3943_,
        v___x_3949_,
        v___x_3951_,
        v___f_3946_,
    );
    return v___x_3952_;
}
pub unsafe fn l_Std_Async_ContextAsync_raceAll___redArg___lam__6___boxed(
    mut v_a_3953_: *mut LeanObject,
    mut v___x_3954_: *mut LeanObject,
    mut v___f_3955_: *mut LeanObject,
    mut v___f_3956_: *mut LeanObject,
    mut v___f_3957_: *mut LeanObject,
    mut v___y_3958_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3959_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_a_3960_: *mut LeanObject,
    mut v___x_3961_: *mut LeanObject,
    mut v___f_3962_: *mut LeanObject,
    mut v___f_3963_: *mut LeanObject,
    mut v_x_3964_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3969_: u8 = 0;
    let mut v___x_3971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3974_: u8 = 0;
    let mut v_a_3975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3980_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3964_) == 0 {
                    lean_dec_ref(v___f_3963_);
                    lean_dec_ref(v___f_3962_);
                    lean_dec(v___x_3961_);
                    lean_dec_ref(v_a_3960_);
                    v_a_3966_ = lean_ctor_get(v_x_3964_, 0);
                    v_isSharedCheck_3974_ = (!lean_is_exclusive(v_x_3964_)) as u8;
                    if v_isSharedCheck_3974_ == 0 {
                        v___x_3968_ = v_x_3964_;
                        v_isShared_3969_ = v_isSharedCheck_3974_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3966_);
                        lean_dec(v_x_3964_);
                        v___x_3968_ = lean_box(0);
                        v_isShared_3969_ = v_isSharedCheck_3974_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3975_ = lean_ctor_get(v_x_3964_, 0);
                    lean_inc(v_a_3975_);
                    lean_dec_ref_known(v_x_3964_, 1);
                    v___f_3976_ = lean_alloc_closure(
                        l_Std_Async_ContextAsync_raceAll___redArg___lam__5___boxed
                            as *mut core::ffi::c_void,
                        3,
                        1,
                    );
                    lean_closure_set(v___f_3976_, 0, v_a_3975_);
                    lean_inc(v___x_3961_);
                    v___f_3977_ = lean_alloc_closure(
                        l_Std_Async_ContextAsync_raceAll___redArg___lam__6___boxed
                            as *mut core::ffi::c_void,
                        6,
                        5,
                    );
                    lean_closure_set(v___f_3977_, 0, v_a_3960_);
                    lean_closure_set(v___f_3977_, 1, v___x_3961_);
                    lean_closure_set(v___f_3977_, 2, v___f_3962_);
                    lean_closure_set(v___f_3977_, 3, v___f_3963_);
                    lean_closure_set(v___f_3977_, 4, v___f_3976_);
                    v___x_3978_ = lean_alloc_closure(
                        l_Std_Async_BaseAsync_toRawBaseIO___boxed as *mut core::ffi::c_void,
                        3,
                        2,
                    );
                    lean_closure_set(v___x_3978_, 0, lean_box(0));
                    lean_closure_set(v___x_3978_, 1, v___f_3977_);
                    v___x_3979_ = lean_io_as_task(v___x_3978_, v___x_3961_);
                    lean_dec_ref(v___x_3979_);
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
                    v_reuseFailAlloc_3973_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3973_, 0, v_a_3966_);
                    v___x_3971_ = v_reuseFailAlloc_3973_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3972_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3972_, 0, v___x_3971_);
                return v___x_3972_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_raceAll___redArg___lam__7___boxed(
    mut v_a_3981_: *mut LeanObject,
    mut v___x_3982_: *mut LeanObject,
    mut v___f_3983_: *mut LeanObject,
    mut v___f_3984_: *mut LeanObject,
    mut v_x_3985_: *mut LeanObject,
    mut v___y_3986_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3987_: *mut LeanObject = core::ptr::null_mut();
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
    mut v___x_3988_: *mut LeanObject,
    mut v___f_3989_: *mut LeanObject,
    mut v_x_3990_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3995_: u8 = 0;
    let mut v___x_3997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4000_: u8 = 0;
    let mut v_a_4001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4004_: u8 = 0;
    let mut v___x_4005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4009_: u8 = 0;
    let mut v___x_4010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4012_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3990_) == 0 {
                    lean_dec_ref(v___f_3989_);
                    lean_dec(v___x_3988_);
                    v_a_3992_ = lean_ctor_get(v_x_3990_, 0);
                    v_isSharedCheck_4000_ = (!lean_is_exclusive(v_x_3990_)) as u8;
                    if v_isSharedCheck_4000_ == 0 {
                        v___x_3994_ = v_x_3990_;
                        v_isShared_3995_ = v_isSharedCheck_4000_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3992_);
                        lean_dec(v_x_3990_);
                        v___x_3994_ = lean_box(0);
                        v_isShared_3995_ = v_isSharedCheck_4000_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4001_ = lean_ctor_get(v_x_3990_, 0);
                    v_isSharedCheck_4012_ = (!lean_is_exclusive(v_x_3990_)) as u8;
                    if v_isSharedCheck_4012_ == 0 {
                        v___x_4003_ = v_x_3990_;
                        v_isShared_4004_ = v_isSharedCheck_4012_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4001_);
                        lean_dec(v_x_3990_);
                        v___x_4003_ = lean_box(0);
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
                    v_reuseFailAlloc_3999_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3999_, 0, v_a_3992_);
                    v___x_3997_ = v_reuseFailAlloc_3999_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3998_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3998_, 0, v___x_3997_);
                return v___x_3998_;
            }
            3 => {
                v___x_4005_ = l_Std_CancellationContext_fork(v_a_4001_);
                if v_isShared_4004_ == 0 {
                    lean_ctor_set(v___x_4003_, 0, v___x_4005_);
                    v___x_4007_ = v___x_4003_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4011_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4011_, 0, v___x_4005_);
                    v___x_4007_ = v_reuseFailAlloc_4011_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4008_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4008_, 0, v___x_4007_);
                v___x_4009_ = 0;
                v___x_4010_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
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
    mut v___x_4013_: *mut LeanObject,
    mut v___f_4014_: *mut LeanObject,
    mut v_x_4015_: *mut LeanObject,
    mut v___y_4016_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4017_: *mut LeanObject = core::ptr::null_mut();
    v_res_4017_ =
        l_Std_Async_ContextAsync_raceAll___redArg___lam__8(v___x_4013_, v___f_4014_, v_x_4015_);
    return v_res_4017_;
}
pub unsafe fn l_Std_Async_ContextAsync_raceAll___redArg___lam__9(
    mut v___f_4018_: *mut LeanObject,
    mut v___f_4019_: *mut LeanObject,
    mut v___y_4020_: *mut LeanObject,
    mut v_x_4021_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_4023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4026_: u8 = 0;
    let mut v___x_4028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4031_: u8 = 0;
    let mut v_a_4032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4035_: u8 = 0;
    let mut v___x_4036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4042_: u8 = 0;
    let mut v___x_4043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4045_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4021_) == 0 {
                    lean_dec_ref(v___f_4019_);
                    lean_dec_ref(v___f_4018_);
                    v_a_4023_ = lean_ctor_get(v_x_4021_, 0);
                    v_isSharedCheck_4031_ = (!lean_is_exclusive(v_x_4021_)) as u8;
                    if v_isSharedCheck_4031_ == 0 {
                        v___x_4025_ = v_x_4021_;
                        v_isShared_4026_ = v_isSharedCheck_4031_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4023_);
                        lean_dec(v_x_4021_);
                        v___x_4025_ = lean_box(0);
                        v_isShared_4026_ = v_isSharedCheck_4031_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4032_ = lean_ctor_get(v_x_4021_, 0);
                    v_isSharedCheck_4045_ = (!lean_is_exclusive(v_x_4021_)) as u8;
                    if v_isSharedCheck_4045_ == 0 {
                        v___x_4034_ = v_x_4021_;
                        v_isShared_4035_ = v_isSharedCheck_4045_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4032_);
                        lean_dec(v_x_4021_);
                        v___x_4034_ = lean_box(0);
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
                    v_reuseFailAlloc_4030_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4030_, 0, v_a_4023_);
                    v___x_4028_ = v_reuseFailAlloc_4030_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4029_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4029_, 0, v___x_4028_);
                return v___x_4029_;
            }
            3 => {
                v___x_4036_ = lean_unsigned_to_nat(0);
                v___f_4037_ = lean_alloc_closure(
                    l_Std_Async_ContextAsync_raceAll___redArg___lam__7___boxed
                        as *mut core::ffi::c_void,
                    6,
                    4,
                );
                lean_closure_set(v___f_4037_, 0, v_a_4032_);
                lean_closure_set(v___f_4037_, 1, v___x_4036_);
                lean_closure_set(v___f_4037_, 2, v___f_4018_);
                lean_closure_set(v___f_4037_, 3, v___f_4019_);
                v___f_4038_ = lean_alloc_closure(
                    l_Std_Async_ContextAsync_raceAll___redArg___lam__8___boxed
                        as *mut core::ffi::c_void,
                    4,
                    2,
                );
                lean_closure_set(v___f_4038_, 0, v___x_4036_);
                lean_closure_set(v___f_4038_, 1, v___f_4037_);
                lean_inc_ref(v___y_4020_);
                if v_isShared_4035_ == 0 {
                    lean_ctor_set(v___x_4034_, 0, v___y_4020_);
                    v___x_4040_ = v___x_4034_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4044_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4044_, 0, v___y_4020_);
                    v___x_4040_ = v_reuseFailAlloc_4044_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4041_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4041_, 0, v___x_4040_);
                v___x_4042_ = 0;
                v___x_4043_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
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
    mut v___f_4046_: *mut LeanObject,
    mut v___f_4047_: *mut LeanObject,
    mut v___y_4048_: *mut LeanObject,
    mut v_x_4049_: *mut LeanObject,
    mut v___y_4050_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4051_: *mut LeanObject = core::ptr::null_mut();
    v_res_4051_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__9(
        v___f_4046_,
        v___f_4047_,
        v___y_4048_,
        v_x_4049_,
    );
    lean_dec_ref(v___y_4048_);
    return v_res_4051_;
}
pub unsafe fn l_Std_Async_ContextAsync_raceAll___redArg___lam__10(
    mut v_x_4052_: *mut LeanObject,
    mut v_a_4053_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4055_: *mut LeanObject = core::ptr::null_mut();
    v___x_4055_ = lean_apply_2(v_x_4052_, v_a_4053_, lean_box(0));
    return v___x_4055_;
}
pub unsafe fn l_Std_Async_ContextAsync_raceAll___redArg___lam__10___boxed(
    mut v_x_4056_: *mut LeanObject,
    mut v_a_4057_: *mut LeanObject,
    mut v___y_4058_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4059_: *mut LeanObject = core::ptr::null_mut();
    v_res_4059_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__10(v_x_4056_, v_a_4057_);
    return v_res_4059_;
}
pub unsafe fn l_Std_Async_ContextAsync_raceAll___redArg___lam__11(
    mut v_x_4060_: *mut LeanObject,
    mut v_prio_4061_: *mut LeanObject,
    mut v___f_4062_: *mut LeanObject,
    mut v___f_4063_: *mut LeanObject,
    mut v_x_4064_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_4066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4069_: u8 = 0;
    let mut v___x_4071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4074_: u8 = 0;
    let mut v_a_4075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4078_: u8 = 0;
    let mut v___f_4079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4083_: u8 = 0;
    let mut v___x_4084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4088_: u8 = 0;
    let mut v___x_4089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4091_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4064_) == 0 {
                    lean_dec_ref(v___f_4063_);
                    lean_dec_ref(v___f_4062_);
                    lean_dec(v_prio_4061_);
                    lean_dec_ref(v_x_4060_);
                    v_a_4066_ = lean_ctor_get(v_x_4064_, 0);
                    v_isSharedCheck_4074_ = (!lean_is_exclusive(v_x_4064_)) as u8;
                    if v_isSharedCheck_4074_ == 0 {
                        v___x_4068_ = v_x_4064_;
                        v_isShared_4069_ = v_isSharedCheck_4074_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4066_);
                        lean_dec(v_x_4064_);
                        v___x_4068_ = lean_box(0);
                        v_isShared_4069_ = v_isSharedCheck_4074_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4075_ = lean_ctor_get(v_x_4064_, 0);
                    v_isSharedCheck_4091_ = (!lean_is_exclusive(v_x_4064_)) as u8;
                    if v_isSharedCheck_4091_ == 0 {
                        v___x_4077_ = v_x_4064_;
                        v_isShared_4078_ = v_isSharedCheck_4091_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4075_);
                        lean_dec(v_x_4064_);
                        v___x_4077_ = lean_box(0);
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
                    v_reuseFailAlloc_4073_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4073_, 0, v_a_4066_);
                    v___x_4071_ = v_reuseFailAlloc_4073_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4072_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4072_, 0, v___x_4071_);
                return v___x_4072_;
            }
            3 => {
                v___f_4079_ = lean_alloc_closure(
                    l_Std_Async_ContextAsync_raceAll___redArg___lam__10___boxed
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___f_4079_, 0, v_x_4060_);
                lean_closure_set(v___f_4079_, 1, v_a_4075_);
                v___x_4080_ = lean_alloc_closure(
                    l_Std_Async_BaseAsync_toRawBaseIO___boxed as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___x_4080_, 0, lean_box(0));
                lean_closure_set(v___x_4080_, 1, v___f_4079_);
                v___x_4081_ = lean_io_as_task(v___x_4080_, v_prio_4061_);
                v___x_4082_ = lean_unsigned_to_nat(0);
                v___x_4083_ = 1;
                v___x_4084_ = lean_task_bind(v___x_4081_, v___f_4062_, v___x_4082_, v___x_4083_);
                if v_isShared_4078_ == 0 {
                    lean_ctor_set(v___x_4077_, 0, v___x_4084_);
                    v___x_4086_ = v___x_4077_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4090_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4090_, 0, v___x_4084_);
                    v___x_4086_ = v_reuseFailAlloc_4090_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4087_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4087_, 0, v___x_4086_);
                v___x_4088_ = 0;
                v___x_4089_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
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
    mut v_x_4092_: *mut LeanObject,
    mut v_prio_4093_: *mut LeanObject,
    mut v___f_4094_: *mut LeanObject,
    mut v___f_4095_: *mut LeanObject,
    mut v_x_4096_: *mut LeanObject,
    mut v___y_4097_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4098_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_a_4099_: *mut LeanObject,
    mut v___f_4100_: *mut LeanObject,
    mut v___f_4101_: *mut LeanObject,
    mut v_prio_4102_: *mut LeanObject,
    mut v___f_4103_: *mut LeanObject,
    mut v_x_4104_: *mut LeanObject,
    mut v___y_4105_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4113_: u8 = 0;
    let mut v___x_4114_: *mut LeanObject = core::ptr::null_mut();
    v___x_4107_ = l_Std_CancellationContext_fork(v_a_4099_);
    lean_inc_ref(v___y_4105_);
    v___f_4108_ = lean_alloc_closure(
        l_Std_Async_ContextAsync_raceAll___redArg___lam__9___boxed as *mut core::ffi::c_void,
        5,
        3,
    );
    lean_closure_set(v___f_4108_, 0, v___f_4100_);
    lean_closure_set(v___f_4108_, 1, v___f_4101_);
    lean_closure_set(v___f_4108_, 2, v___y_4105_);
    v___f_4109_ = lean_alloc_closure(
        l_Std_Async_ContextAsync_raceAll___redArg___lam__11___boxed as *mut core::ffi::c_void,
        6,
        4,
    );
    lean_closure_set(v___f_4109_, 0, v_x_4104_);
    lean_closure_set(v___f_4109_, 1, v_prio_4102_);
    lean_closure_set(v___f_4109_, 2, v___f_4103_);
    lean_closure_set(v___f_4109_, 3, v___f_4108_);
    v___x_4110_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_4110_, 0, v___x_4107_);
    v___x_4111_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4111_, 0, v___x_4110_);
    v___x_4112_ = lean_unsigned_to_nat(0);
    v___x_4113_ = 0;
    v___x_4114_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_4112_,
        v___x_4113_,
        v___x_4111_,
        v___f_4109_,
    );
    return v___x_4114_;
}
pub unsafe fn l_Std_Async_ContextAsync_raceAll___redArg___lam__12___boxed(
    mut v_a_4115_: *mut LeanObject,
    mut v___f_4116_: *mut LeanObject,
    mut v___f_4117_: *mut LeanObject,
    mut v_prio_4118_: *mut LeanObject,
    mut v___f_4119_: *mut LeanObject,
    mut v_x_4120_: *mut LeanObject,
    mut v___y_4121_: *mut LeanObject,
    mut v___y_4122_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4123_: *mut LeanObject = core::ptr::null_mut();
    v_res_4123_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__12(
        v_a_4115_,
        v___f_4116_,
        v___f_4117_,
        v_prio_4118_,
        v___f_4119_,
        v_x_4120_,
        v___y_4121_,
    );
    lean_dec_ref(v___y_4121_);
    return v_res_4123_;
}
pub unsafe fn l_Std_Async_ContextAsync_raceAll___redArg___lam__13(
    mut v_a_4124_: *mut LeanObject,
    mut v___f_4125_: *mut LeanObject,
    mut v___f_4126_: *mut LeanObject,
    mut v_x_4127_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_4129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4132_: u8 = 0;
    let mut v___x_4134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4137_: u8 = 0;
    let mut v___x_4138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4140_: u8 = 0;
    let mut v___x_4141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4143_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4127_) == 0 {
                    lean_dec_ref(v___f_4126_);
                    lean_dec_ref(v___f_4125_);
                    v_a_4129_ = lean_ctor_get(v_x_4127_, 0);
                    v_isSharedCheck_4137_ = (!lean_is_exclusive(v_x_4127_)) as u8;
                    if v_isSharedCheck_4137_ == 0 {
                        v___x_4131_ = v_x_4127_;
                        v_isShared_4132_ = v_isSharedCheck_4137_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4129_);
                        lean_dec(v_x_4127_);
                        v___x_4131_ = lean_box(0);
                        v_isShared_4132_ = v_isSharedCheck_4137_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v_x_4127_, 1);
                    v___x_4138_ = l_IO_Promise_result_x21___redArg(v_a_4124_);
                    v___x_4139_ = lean_unsigned_to_nat(0);
                    v___x_4140_ = 0;
                    v___x_4141_ = lean_task_map(v___f_4125_, v___x_4138_, v___x_4139_, v___x_4140_);
                    v___x_4142_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4142_, 0, v___x_4141_);
                    v___x_4143_ =
                        l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                            lean_box(0),
                            lean_box(0),
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
                    v_reuseFailAlloc_4136_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4136_, 0, v_a_4129_);
                    v___x_4134_ = v_reuseFailAlloc_4136_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4135_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4135_, 0, v___x_4134_);
                return v___x_4135_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_raceAll___redArg___lam__13___boxed(
    mut v_a_4144_: *mut LeanObject,
    mut v___f_4145_: *mut LeanObject,
    mut v___f_4146_: *mut LeanObject,
    mut v_x_4147_: *mut LeanObject,
    mut v___y_4148_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4149_: *mut LeanObject = core::ptr::null_mut();
    v_res_4149_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__13(
        v_a_4144_,
        v___f_4145_,
        v___f_4146_,
        v_x_4147_,
    );
    lean_dec(v_a_4144_);
    return v_res_4149_;
}
pub unsafe fn l_Std_Async_ContextAsync_raceAll___redArg___lam__14(
    mut v_a_4150_: *mut LeanObject,
    mut v_prio_4151_: *mut LeanObject,
    mut v___f_4152_: *mut LeanObject,
    mut v_inst_4153_: *mut LeanObject,
    mut v_xs_4154_: *mut LeanObject,
    mut v_a_4155_: *mut LeanObject,
    mut v___f_4156_: *mut LeanObject,
    mut v___f_4157_: *mut LeanObject,
    mut v_x_4158_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_4160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4163_: u8 = 0;
    let mut v___x_4165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4168_: u8 = 0;
    let mut v_a_4169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4176_: u8 = 0;
    let mut v___x_4177_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4158_) == 0 {
                    lean_dec_ref(v___f_4157_);
                    lean_dec_ref(v___f_4156_);
                    lean_dec(v_xs_4154_);
                    lean_dec_ref(v_inst_4153_);
                    lean_dec_ref(v___f_4152_);
                    lean_dec(v_prio_4151_);
                    lean_dec_ref(v_a_4150_);
                    v_a_4160_ = lean_ctor_get(v_x_4158_, 0);
                    v_isSharedCheck_4168_ = (!lean_is_exclusive(v_x_4158_)) as u8;
                    if v_isSharedCheck_4168_ == 0 {
                        v___x_4162_ = v_x_4158_;
                        v_isShared_4163_ = v_isSharedCheck_4168_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4160_);
                        lean_dec(v_x_4158_);
                        v___x_4162_ = lean_box(0);
                        v_isShared_4163_ = v_isSharedCheck_4168_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4169_ = lean_ctor_get(v_x_4158_, 0);
                    lean_inc_n(v_a_4169_, 3);
                    lean_dec_ref_known(v_x_4158_, 1);
                    v___f_4170_ = lean_alloc_closure(
                        l_Std_Async_ContextAsync_raceAll___redArg___lam__3___boxed
                            as *mut core::ffi::c_void,
                        3,
                        1,
                    );
                    lean_closure_set(v___f_4170_, 0, v_a_4169_);
                    v___f_4171_ = lean_alloc_closure(
                        l_Std_Async_ContextAsync_raceAll___redArg___lam__4___boxed
                            as *mut core::ffi::c_void,
                        3,
                        1,
                    );
                    lean_closure_set(v___f_4171_, 0, v_a_4169_);
                    v___f_4172_ = lean_alloc_closure(
                        l_Std_Async_ContextAsync_raceAll___redArg___lam__12___boxed
                            as *mut core::ffi::c_void,
                        8,
                        5,
                    );
                    lean_closure_set(v___f_4172_, 0, v_a_4150_);
                    lean_closure_set(v___f_4172_, 1, v___f_4171_);
                    lean_closure_set(v___f_4172_, 2, v___f_4170_);
                    lean_closure_set(v___f_4172_, 3, v_prio_4151_);
                    lean_closure_set(v___f_4172_, 4, v___f_4152_);
                    lean_inc_ref(v_a_4155_);
                    v___x_4173_ = lean_apply_4(
                        v_inst_4153_,
                        v_xs_4154_,
                        v___f_4172_,
                        v_a_4155_,
                        lean_box(0),
                    );
                    v___f_4174_ = lean_alloc_closure(
                        l_Std_Async_ContextAsync_raceAll___redArg___lam__13___boxed
                            as *mut core::ffi::c_void,
                        5,
                        3,
                    );
                    lean_closure_set(v___f_4174_, 0, v_a_4169_);
                    lean_closure_set(v___f_4174_, 1, v___f_4156_);
                    lean_closure_set(v___f_4174_, 2, v___f_4157_);
                    v___x_4175_ = lean_unsigned_to_nat(0);
                    v___x_4176_ = 0;
                    v___x_4177_ =
                        l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                            lean_box(0),
                            lean_box(0),
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
                    v_reuseFailAlloc_4167_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4167_, 0, v_a_4160_);
                    v___x_4165_ = v_reuseFailAlloc_4167_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4166_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4166_, 0, v___x_4165_);
                return v___x_4166_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_raceAll___redArg___lam__14___boxed(
    mut v_a_4178_: *mut LeanObject,
    mut v_prio_4179_: *mut LeanObject,
    mut v___f_4180_: *mut LeanObject,
    mut v_inst_4181_: *mut LeanObject,
    mut v_xs_4182_: *mut LeanObject,
    mut v_a_4183_: *mut LeanObject,
    mut v___f_4184_: *mut LeanObject,
    mut v___f_4185_: *mut LeanObject,
    mut v_x_4186_: *mut LeanObject,
    mut v___y_4187_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4188_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_a_4183_);
    return v_res_4188_;
}
pub unsafe fn l_Std_Async_ContextAsync_raceAll___redArg___lam__15(
    mut v_prio_4189_: *mut LeanObject,
    mut v___f_4190_: *mut LeanObject,
    mut v_inst_4191_: *mut LeanObject,
    mut v_xs_4192_: *mut LeanObject,
    mut v_a_4193_: *mut LeanObject,
    mut v___f_4194_: *mut LeanObject,
    mut v_x_4195_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_4197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4200_: u8 = 0;
    let mut v___x_4202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4205_: u8 = 0;
    let mut v_a_4206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4209_: u8 = 0;
    let mut v___x_4210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4217_: u8 = 0;
    let mut v___x_4218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4220_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4195_) == 0 {
                    lean_dec_ref(v___f_4194_);
                    lean_dec(v_xs_4192_);
                    lean_dec_ref(v_inst_4191_);
                    lean_dec_ref(v___f_4190_);
                    lean_dec(v_prio_4189_);
                    v_a_4197_ = lean_ctor_get(v_x_4195_, 0);
                    v_isSharedCheck_4205_ = (!lean_is_exclusive(v_x_4195_)) as u8;
                    if v_isSharedCheck_4205_ == 0 {
                        v___x_4199_ = v_x_4195_;
                        v_isShared_4200_ = v_isSharedCheck_4205_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4197_);
                        lean_dec(v_x_4195_);
                        v___x_4199_ = lean_box(0);
                        v_isShared_4200_ = v_isSharedCheck_4205_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4206_ = lean_ctor_get(v_x_4195_, 0);
                    v_isSharedCheck_4220_ = (!lean_is_exclusive(v_x_4195_)) as u8;
                    if v_isSharedCheck_4220_ == 0 {
                        v___x_4208_ = v_x_4195_;
                        v_isShared_4209_ = v_isSharedCheck_4220_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4206_);
                        lean_dec(v_x_4195_);
                        v___x_4208_ = lean_box(0);
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
                    v_reuseFailAlloc_4204_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4204_, 0, v_a_4197_);
                    v___x_4202_ = v_reuseFailAlloc_4204_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4203_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4203_, 0, v___x_4202_);
                return v___x_4203_;
            }
            3 => {
                v___x_4210_ = lean_io_promise_new();
                lean_inc(v_a_4206_);
                v___f_4211_ = lean_alloc_closure(
                    l_Std_Async_ContextAsync_raceAll___redArg___lam__1___boxed
                        as *mut core::ffi::c_void,
                    3,
                    1,
                );
                lean_closure_set(v___f_4211_, 0, v_a_4206_);
                lean_inc_ref(v_a_4193_);
                v___f_4212_ = lean_alloc_closure(
                    l_Std_Async_ContextAsync_raceAll___redArg___lam__14___boxed
                        as *mut core::ffi::c_void,
                    10,
                    8,
                );
                lean_closure_set(v___f_4212_, 0, v_a_4206_);
                lean_closure_set(v___f_4212_, 1, v_prio_4189_);
                lean_closure_set(v___f_4212_, 2, v___f_4190_);
                lean_closure_set(v___f_4212_, 3, v_inst_4191_);
                lean_closure_set(v___f_4212_, 4, v_xs_4192_);
                lean_closure_set(v___f_4212_, 5, v_a_4193_);
                lean_closure_set(v___f_4212_, 6, v___f_4194_);
                lean_closure_set(v___f_4212_, 7, v___f_4211_);
                if v_isShared_4209_ == 0 {
                    lean_ctor_set(v___x_4208_, 0, v___x_4210_);
                    v___x_4214_ = v___x_4208_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4219_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4219_, 0, v___x_4210_);
                    v___x_4214_ = v_reuseFailAlloc_4219_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4215_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4215_, 0, v___x_4214_);
                v___x_4216_ = lean_unsigned_to_nat(0);
                v___x_4217_ = 0;
                v___x_4218_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
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
    mut v_prio_4221_: *mut LeanObject,
    mut v___f_4222_: *mut LeanObject,
    mut v_inst_4223_: *mut LeanObject,
    mut v_xs_4224_: *mut LeanObject,
    mut v_a_4225_: *mut LeanObject,
    mut v___f_4226_: *mut LeanObject,
    mut v_x_4227_: *mut LeanObject,
    mut v___y_4228_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4229_: *mut LeanObject = core::ptr::null_mut();
    v_res_4229_ = l_Std_Async_ContextAsync_raceAll___redArg___lam__15(
        v_prio_4221_,
        v___f_4222_,
        v_inst_4223_,
        v_xs_4224_,
        v_a_4225_,
        v___f_4226_,
        v_x_4227_,
    );
    lean_dec_ref(v_a_4225_);
    return v_res_4229_;
}
pub unsafe fn l_Std_Async_ContextAsync_raceAll___redArg(
    mut v_inst_4231_: *mut LeanObject,
    mut v_xs_4232_: *mut LeanObject,
    mut v_prio_4233_: *mut LeanObject,
    mut v_a_4234_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4242_: u8 = 0;
    let mut v___x_4243_: *mut LeanObject = core::ptr::null_mut();
    v___f_4236_ = l_Std_Async_ContextAsync_raceAll___redArg___closed__0;
    v___f_4237_ = l_Std_Async_ContextAsync_concurrently___redArg___closed__0;
    lean_inc_ref_n(v_a_4234_, 2);
    v___f_4238_ = lean_alloc_closure(
        l_Std_Async_ContextAsync_raceAll___redArg___lam__15___boxed as *mut core::ffi::c_void,
        8,
        6,
    );
    lean_closure_set(v___f_4238_, 0, v_prio_4233_);
    lean_closure_set(v___f_4238_, 1, v___f_4237_);
    lean_closure_set(v___f_4238_, 2, v_inst_4231_);
    lean_closure_set(v___f_4238_, 3, v_xs_4232_);
    lean_closure_set(v___f_4238_, 4, v_a_4234_);
    lean_closure_set(v___f_4238_, 5, v___f_4236_);
    v___x_4239_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_4239_, 0, v_a_4234_);
    v___x_4240_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4240_, 0, v___x_4239_);
    v___x_4241_ = lean_unsigned_to_nat(0);
    v___x_4242_ = 0;
    v___x_4243_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_4241_,
        v___x_4242_,
        v___x_4240_,
        v___f_4238_,
    );
    return v___x_4243_;
}
pub unsafe fn l_Std_Async_ContextAsync_raceAll___redArg___boxed(
    mut v_inst_4244_: *mut LeanObject,
    mut v_xs_4245_: *mut LeanObject,
    mut v_prio_4246_: *mut LeanObject,
    mut v_a_4247_: *mut LeanObject,
    mut v_a_4248_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4249_: *mut LeanObject = core::ptr::null_mut();
    v_res_4249_ = l_Std_Async_ContextAsync_raceAll___redArg(
        v_inst_4244_,
        v_xs_4245_,
        v_prio_4246_,
        v_a_4247_,
    );
    lean_dec_ref(v_a_4247_);
    return v_res_4249_;
}
pub unsafe fn l_Std_Async_ContextAsync_raceAll(
    mut v_c_4250_: *mut LeanObject,
    mut v_00_u03b1_4251_: *mut LeanObject,
    mut v_inst_4252_: *mut LeanObject,
    mut v_xs_4253_: *mut LeanObject,
    mut v_prio_4254_: *mut LeanObject,
    mut v_a_4255_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4257_: *mut LeanObject = core::ptr::null_mut();
    v___x_4257_ = l_Std_Async_ContextAsync_raceAll___redArg(
        v_inst_4252_,
        v_xs_4253_,
        v_prio_4254_,
        v_a_4255_,
    );
    return v___x_4257_;
}
pub unsafe fn l_Std_Async_ContextAsync_raceAll___boxed(
    mut v_c_4258_: *mut LeanObject,
    mut v_00_u03b1_4259_: *mut LeanObject,
    mut v_inst_4260_: *mut LeanObject,
    mut v_xs_4261_: *mut LeanObject,
    mut v_prio_4262_: *mut LeanObject,
    mut v_a_4263_: *mut LeanObject,
    mut v_a_4264_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4265_: *mut LeanObject = core::ptr::null_mut();
    v_res_4265_ = l_Std_Async_ContextAsync_raceAll(
        v_c_4258_,
        v_00_u03b1_4259_,
        v_inst_4260_,
        v_xs_4261_,
        v_prio_4262_,
        v_a_4263_,
    );
    lean_dec_ref(v_a_4263_);
    return v_res_4265_;
}
pub unsafe fn l_Std_Async_ContextAsync_async___redArg___lam__3(
    mut v___x_4266_: *mut LeanObject,
    mut v___f_4267_: *mut LeanObject,
    mut v___f_4268_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4271_: u8 = 0;
    let mut v___x_4272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4280_: u8 = 0;
    let mut v___x_4282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4284_: u8 = 0;
    let mut v_a_4285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4288_: u8 = 0;
    let mut v_fst_4289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4293_: u8 = 0;
    let mut v_a_4294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4297_: u8 = 0;
    let mut v___x_4298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4303_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4270_ = lean_unsigned_to_nat(0);
                v___x_4271_ = 0;
                v___x_4272_ = l_Std_Async_EAsync_tryFinally_x27___redArg(
                    v___x_4266_,
                    v___f_4267_,
                    v___x_4270_,
                    v___x_4271_,
                );
                if lean_obj_tag(v___x_4272_) == 0 {
                    lean_dec(v___f_4268_);
                    v_a_4276_ = lean_ctor_get(v___x_4272_, 0);
                    lean_inc(v_a_4276_);
                    lean_dec_ref_known(v___x_4272_, 1);
                    if lean_obj_tag(v_a_4276_) == 0 {
                        v_a_4277_ = lean_ctor_get(v_a_4276_, 0);
                        v_isSharedCheck_4284_ = (!lean_is_exclusive(v_a_4276_)) as u8;
                        if v_isSharedCheck_4284_ == 0 {
                            v___x_4279_ = v_a_4276_;
                            v_isShared_4280_ = v_isSharedCheck_4284_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_4277_);
                            lean_dec(v_a_4276_);
                            v___x_4279_ = lean_box(0);
                            v_isShared_4280_ = v_isSharedCheck_4284_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_a_4285_ = lean_ctor_get(v_a_4276_, 0);
                        v_isSharedCheck_4293_ = (!lean_is_exclusive(v_a_4276_)) as u8;
                        if v_isSharedCheck_4293_ == 0 {
                            v___x_4287_ = v_a_4276_;
                            v_isShared_4288_ = v_isSharedCheck_4293_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_4285_);
                            lean_dec(v_a_4276_);
                            v___x_4287_ = lean_box(0);
                            v_isShared_4288_ = v_isSharedCheck_4293_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_a_4294_ = lean_ctor_get(v___x_4272_, 0);
                    v_isSharedCheck_4303_ = (!lean_is_exclusive(v___x_4272_)) as u8;
                    if v_isSharedCheck_4303_ == 0 {
                        v___x_4296_ = v___x_4272_;
                        v_isShared_4297_ = v_isSharedCheck_4303_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_4294_);
                        lean_dec(v___x_4272_);
                        v___x_4296_ = lean_box(0);
                        v_isShared_4297_ = v_isSharedCheck_4303_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4275_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4275_, 0, v___y_4274_);
                return v___x_4275_;
            }
            2 => {
                if v_isShared_4280_ == 0 {
                    v___x_4282_ = v___x_4279_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4283_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4283_, 0, v_a_4277_);
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
                v_fst_4289_ = lean_ctor_get(v_a_4285_, 0);
                lean_inc(v_fst_4289_);
                lean_dec(v_a_4285_);
                if v_isShared_4288_ == 0 {
                    lean_ctor_set(v___x_4287_, 0, v_fst_4289_);
                    v___x_4291_ = v___x_4287_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4292_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4292_, 0, v_fst_4289_);
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
                v___x_4298_ = lean_alloc_closure(l_Except_map as *mut core::ffi::c_void, 5, 4);
                lean_closure_set(v___x_4298_, 0, lean_box(0));
                lean_closure_set(v___x_4298_, 1, lean_box(0));
                lean_closure_set(v___x_4298_, 2, lean_box(0));
                lean_closure_set(v___x_4298_, 3, v___f_4268_);
                v___x_4299_ = lean_task_map(v___x_4298_, v_a_4294_, v___x_4270_, v___x_4271_);
                if v_isShared_4297_ == 0 {
                    lean_ctor_set(v___x_4296_, 0, v___x_4299_);
                    v___x_4301_ = v___x_4296_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4302_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4302_, 0, v___x_4299_);
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
    mut v___x_4304_: *mut LeanObject,
    mut v___f_4305_: *mut LeanObject,
    mut v___f_4306_: *mut LeanObject,
    mut v___y_4307_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4308_: *mut LeanObject = core::ptr::null_mut();
    v_res_4308_ =
        l_Std_Async_ContextAsync_async___redArg___lam__3(v___x_4304_, v___f_4305_, v___f_4306_);
    return v_res_4308_;
}
pub unsafe fn l_Std_Async_ContextAsync_async___redArg___lam__0(
    mut v_x_4309_: *mut LeanObject,
    mut v___f_4310_: *mut LeanObject,
    mut v_prio_4311_: *mut LeanObject,
    mut v___f_4312_: *mut LeanObject,
    mut v_x_4313_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_4315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4318_: u8 = 0;
    let mut v___x_4320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4323_: u8 = 0;
    let mut v_a_4324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4327_: u8 = 0;
    let mut v___x_4328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: u8 = 0;
    let mut v___x_4336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4341_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4313_) == 0 {
                    lean_dec_ref(v___f_4312_);
                    lean_dec(v_prio_4311_);
                    lean_dec(v___f_4310_);
                    lean_dec_ref(v_x_4309_);
                    v_a_4315_ = lean_ctor_get(v_x_4313_, 0);
                    v_isSharedCheck_4323_ = (!lean_is_exclusive(v_x_4313_)) as u8;
                    if v_isSharedCheck_4323_ == 0 {
                        v___x_4317_ = v_x_4313_;
                        v_isShared_4318_ = v_isSharedCheck_4323_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4315_);
                        lean_dec(v_x_4313_);
                        v___x_4317_ = lean_box(0);
                        v_isShared_4318_ = v_isSharedCheck_4323_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4324_ = lean_ctor_get(v_x_4313_, 0);
                    v_isSharedCheck_4341_ = (!lean_is_exclusive(v_x_4313_)) as u8;
                    if v_isSharedCheck_4341_ == 0 {
                        v___x_4326_ = v_x_4313_;
                        v_isShared_4327_ = v_isSharedCheck_4341_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4324_);
                        lean_dec(v_x_4313_);
                        v___x_4326_ = lean_box(0);
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
                    v_reuseFailAlloc_4322_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4322_, 0, v_a_4315_);
                    v___x_4320_ = v_reuseFailAlloc_4322_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4321_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4321_, 0, v___x_4320_);
                return v___x_4321_;
            }
            3 => {
                lean_inc(v_a_4324_);
                v___x_4328_ = lean_apply_1(v_x_4309_, v_a_4324_);
                v___x_4329_ = lean_box(2);
                v___f_4330_ = lean_alloc_closure(
                    l_Std_Async_ContextAsync_concurrently___redArg___lam__3___boxed
                        as *mut core::ffi::c_void,
                    4,
                    2,
                );
                lean_closure_set(v___f_4330_, 0, v_a_4324_);
                lean_closure_set(v___f_4330_, 1, v___x_4329_);
                v___f_4331_ = lean_alloc_closure(
                    l_Std_Async_ContextAsync_async___redArg___lam__3___boxed
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                lean_closure_set(v___f_4331_, 0, v___x_4328_);
                lean_closure_set(v___f_4331_, 1, v___f_4330_);
                lean_closure_set(v___f_4331_, 2, v___f_4310_);
                v___x_4332_ = lean_alloc_closure(
                    l_Std_Async_BaseAsync_toRawBaseIO___boxed as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___x_4332_, 0, lean_box(0));
                lean_closure_set(v___x_4332_, 1, v___f_4331_);
                v___x_4333_ = lean_io_as_task(v___x_4332_, v_prio_4311_);
                v___x_4334_ = lean_unsigned_to_nat(0);
                v___x_4335_ = 1;
                v___x_4336_ = lean_task_bind(v___x_4333_, v___f_4312_, v___x_4334_, v___x_4335_);
                if v_isShared_4327_ == 0 {
                    lean_ctor_set(v___x_4326_, 0, v___x_4336_);
                    v___x_4338_ = v___x_4326_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4340_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4340_, 0, v___x_4336_);
                    v___x_4338_ = v_reuseFailAlloc_4340_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4339_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4339_, 0, v___x_4338_);
                return v___x_4339_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_async___redArg___lam__0___boxed(
    mut v_x_4342_: *mut LeanObject,
    mut v___f_4343_: *mut LeanObject,
    mut v_prio_4344_: *mut LeanObject,
    mut v___f_4345_: *mut LeanObject,
    mut v_x_4346_: *mut LeanObject,
    mut v___y_4347_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4348_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_x_4349_: *mut LeanObject,
    mut v_prio_4350_: *mut LeanObject,
    mut v_ctx_4351_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4360_: u8 = 0;
    let mut v___x_4361_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_ctx_4351_);
    v___x_4353_ = l_Std_CancellationContext_fork(v_ctx_4351_);
    v___f_4354_ = l_Std_Async_ContextAsync_concurrently___redArg___closed__1;
    v___f_4355_ = l_Std_Async_ContextAsync_concurrently___redArg___closed__0;
    v___f_4356_ = lean_alloc_closure(
        l_Std_Async_ContextAsync_async___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        4,
    );
    lean_closure_set(v___f_4356_, 0, v_x_4349_);
    lean_closure_set(v___f_4356_, 1, v___f_4354_);
    lean_closure_set(v___f_4356_, 2, v_prio_4350_);
    lean_closure_set(v___f_4356_, 3, v___f_4355_);
    v___x_4357_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_4357_, 0, v___x_4353_);
    v___x_4358_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4358_, 0, v___x_4357_);
    v___x_4359_ = lean_unsigned_to_nat(0);
    v___x_4360_ = 0;
    v___x_4361_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_4359_,
        v___x_4360_,
        v___x_4358_,
        v___f_4356_,
    );
    return v___x_4361_;
}
pub unsafe fn l_Std_Async_ContextAsync_async___redArg___boxed(
    mut v_x_4362_: *mut LeanObject,
    mut v_prio_4363_: *mut LeanObject,
    mut v_ctx_4364_: *mut LeanObject,
    mut v_a_4365_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4366_: *mut LeanObject = core::ptr::null_mut();
    v_res_4366_ = l_Std_Async_ContextAsync_async___redArg(v_x_4362_, v_prio_4363_, v_ctx_4364_);
    lean_dec_ref(v_ctx_4364_);
    return v_res_4366_;
}
pub unsafe fn l_Std_Async_ContextAsync_async(
    mut v_00_u03b1_4367_: *mut LeanObject,
    mut v_x_4368_: *mut LeanObject,
    mut v_prio_4369_: *mut LeanObject,
    mut v_ctx_4370_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4379_: u8 = 0;
    let mut v___x_4380_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_ctx_4370_);
    v___x_4372_ = l_Std_CancellationContext_fork(v_ctx_4370_);
    v___f_4373_ = l_Std_Async_ContextAsync_concurrently___redArg___closed__1;
    v___f_4374_ = l_Std_Async_ContextAsync_concurrently___redArg___closed__0;
    v___f_4375_ = lean_alloc_closure(
        l_Std_Async_ContextAsync_async___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        4,
    );
    lean_closure_set(v___f_4375_, 0, v_x_4368_);
    lean_closure_set(v___f_4375_, 1, v___f_4373_);
    lean_closure_set(v___f_4375_, 2, v_prio_4369_);
    lean_closure_set(v___f_4375_, 3, v___f_4374_);
    v___x_4376_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_4376_, 0, v___x_4372_);
    v___x_4377_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4377_, 0, v___x_4376_);
    v___x_4378_ = lean_unsigned_to_nat(0);
    v___x_4379_ = 0;
    v___x_4380_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_4378_,
        v___x_4379_,
        v___x_4377_,
        v___f_4375_,
    );
    return v___x_4380_;
}
pub unsafe fn l_Std_Async_ContextAsync_async___boxed(
    mut v_00_u03b1_4381_: *mut LeanObject,
    mut v_x_4382_: *mut LeanObject,
    mut v_prio_4383_: *mut LeanObject,
    mut v_ctx_4384_: *mut LeanObject,
    mut v_a_4385_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4386_: *mut LeanObject = core::ptr::null_mut();
    v_res_4386_ =
        l_Std_Async_ContextAsync_async(v_00_u03b1_4381_, v_x_4382_, v_prio_4383_, v_ctx_4384_);
    lean_dec_ref(v_ctx_4384_);
    return v_res_4386_;
}
pub unsafe fn l_Std_Async_ContextAsync_instMonadAsyncAsyncTask___lam__5(
    mut v___f_4387_: *mut LeanObject,
    mut v___f_4388_: *mut LeanObject,
    mut v_00_u03b1_4389_: *mut LeanObject,
    mut v_x_4390_: *mut LeanObject,
    mut v_prio_4391_: *mut LeanObject,
    mut v___y_4392_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4399_: u8 = 0;
    let mut v___x_4400_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v___y_4392_);
    v___x_4394_ = l_Std_CancellationContext_fork(v___y_4392_);
    v___f_4395_ = lean_alloc_closure(
        l_Std_Async_ContextAsync_async___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        4,
    );
    lean_closure_set(v___f_4395_, 0, v_x_4390_);
    lean_closure_set(v___f_4395_, 1, v___f_4387_);
    lean_closure_set(v___f_4395_, 2, v_prio_4391_);
    lean_closure_set(v___f_4395_, 3, v___f_4388_);
    v___x_4396_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_4396_, 0, v___x_4394_);
    v___x_4397_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4397_, 0, v___x_4396_);
    v___x_4398_ = lean_unsigned_to_nat(0);
    v___x_4399_ = 0;
    v___x_4400_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_4398_,
        v___x_4399_,
        v___x_4397_,
        v___f_4395_,
    );
    return v___x_4400_;
}
pub unsafe fn l_Std_Async_ContextAsync_instMonadAsyncAsyncTask___lam__5___boxed(
    mut v___f_4401_: *mut LeanObject,
    mut v___f_4402_: *mut LeanObject,
    mut v_00_u03b1_4403_: *mut LeanObject,
    mut v_x_4404_: *mut LeanObject,
    mut v_prio_4405_: *mut LeanObject,
    mut v___y_4406_: *mut LeanObject,
    mut v___y_4407_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4408_: *mut LeanObject = core::ptr::null_mut();
    v_res_4408_ = l_Std_Async_ContextAsync_instMonadAsyncAsyncTask___lam__5(
        v___f_4401_,
        v___f_4402_,
        v_00_u03b1_4403_,
        v_x_4404_,
        v_prio_4405_,
        v___y_4406_,
    );
    lean_dec_ref(v___y_4406_);
    return v_res_4408_;
}
pub unsafe fn l_Std_Async_ContextAsync_instFunctor___lam__0(
    mut v_00_u03b1_4413_: *mut LeanObject,
    mut v_00_u03b2_4414_: *mut LeanObject,
    mut v_f_4415_: *mut LeanObject,
    mut v_x_4416_: *mut LeanObject,
    mut v_ctx_4417_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4427_: u8 = 0;
    let mut v___x_4429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4431_: u8 = 0;
    let mut v_a_4432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4435_: u8 = 0;
    let mut v___x_4436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4440_: u8 = 0;
    let mut v_a_4441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4444_: u8 = 0;
    let mut v___x_4445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4447_: u8 = 0;
    let mut v___x_4448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4452_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4419_ = lean_apply_2(v_x_4416_, v_ctx_4417_, lean_box(0));
                if lean_obj_tag(v___x_4419_) == 0 {
                    v_a_4423_ = lean_ctor_get(v___x_4419_, 0);
                    lean_inc(v_a_4423_);
                    lean_dec_ref_known(v___x_4419_, 1);
                    if lean_obj_tag(v_a_4423_) == 0 {
                        lean_dec(v_f_4415_);
                        v_a_4424_ = lean_ctor_get(v_a_4423_, 0);
                        v_isSharedCheck_4431_ = (!lean_is_exclusive(v_a_4423_)) as u8;
                        if v_isSharedCheck_4431_ == 0 {
                            v___x_4426_ = v_a_4423_;
                            v_isShared_4427_ = v_isSharedCheck_4431_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_4424_);
                            lean_dec(v_a_4423_);
                            v___x_4426_ = lean_box(0);
                            v_isShared_4427_ = v_isSharedCheck_4431_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_a_4432_ = lean_ctor_get(v_a_4423_, 0);
                        v_isSharedCheck_4440_ = (!lean_is_exclusive(v_a_4423_)) as u8;
                        if v_isSharedCheck_4440_ == 0 {
                            v___x_4434_ = v_a_4423_;
                            v_isShared_4435_ = v_isSharedCheck_4440_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_4432_);
                            lean_dec(v_a_4423_);
                            v___x_4434_ = lean_box(0);
                            v_isShared_4435_ = v_isSharedCheck_4440_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_a_4441_ = lean_ctor_get(v___x_4419_, 0);
                    v_isSharedCheck_4452_ = (!lean_is_exclusive(v___x_4419_)) as u8;
                    if v_isSharedCheck_4452_ == 0 {
                        v___x_4443_ = v___x_4419_;
                        v_isShared_4444_ = v_isSharedCheck_4452_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_4441_);
                        lean_dec(v___x_4419_);
                        v___x_4443_ = lean_box(0);
                        v_isShared_4444_ = v_isSharedCheck_4452_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4422_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4422_, 0, v___y_4421_);
                return v___x_4422_;
            }
            2 => {
                if v_isShared_4427_ == 0 {
                    v___x_4429_ = v___x_4426_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4430_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4430_, 0, v_a_4424_);
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
                v___x_4436_ = lean_apply_1(v_f_4415_, v_a_4432_);
                if v_isShared_4435_ == 0 {
                    lean_ctor_set(v___x_4434_, 0, v___x_4436_);
                    v___x_4438_ = v___x_4434_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4439_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4439_, 0, v___x_4436_);
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
                v___x_4445_ = lean_alloc_closure(l_Except_map as *mut core::ffi::c_void, 5, 4);
                lean_closure_set(v___x_4445_, 0, lean_box(0));
                lean_closure_set(v___x_4445_, 1, lean_box(0));
                lean_closure_set(v___x_4445_, 2, lean_box(0));
                lean_closure_set(v___x_4445_, 3, v_f_4415_);
                v___x_4446_ = lean_unsigned_to_nat(0);
                v___x_4447_ = 0;
                v___x_4448_ = lean_task_map(v___x_4445_, v_a_4441_, v___x_4446_, v___x_4447_);
                if v_isShared_4444_ == 0 {
                    lean_ctor_set(v___x_4443_, 0, v___x_4448_);
                    v___x_4450_ = v___x_4443_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4451_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4451_, 0, v___x_4448_);
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
    mut v_00_u03b1_4453_: *mut LeanObject,
    mut v_00_u03b2_4454_: *mut LeanObject,
    mut v_f_4455_: *mut LeanObject,
    mut v_x_4456_: *mut LeanObject,
    mut v_ctx_4457_: *mut LeanObject,
    mut v___y_4458_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4459_: *mut LeanObject = core::ptr::null_mut();
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
    mut v___f_4460_: *mut LeanObject,
    mut v_00_u03b1_4461_: *mut LeanObject,
    mut v_00_u03b2_4462_: *mut LeanObject,
    mut v___y_4463_: *mut LeanObject,
    mut v___y_4464_: *mut LeanObject,
    mut v___y_4465_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4468_: *mut LeanObject = core::ptr::null_mut();
    v___x_4467_ = lean_alloc_closure(l_Function_const___boxed as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___x_4467_, 0, lean_box(0));
    lean_closure_set(v___x_4467_, 1, lean_box(0));
    lean_closure_set(v___x_4467_, 2, v___y_4463_);
    lean_inc_ref(v___y_4465_);
    v___x_4468_ = lean_apply_6(
        v___f_4460_,
        lean_box(0),
        lean_box(0),
        v___x_4467_,
        v___y_4464_,
        v___y_4465_,
        lean_box(0),
    );
    return v___x_4468_;
}
pub unsafe fn l_Std_Async_ContextAsync_instFunctor___lam__1___boxed(
    mut v___f_4469_: *mut LeanObject,
    mut v_00_u03b1_4470_: *mut LeanObject,
    mut v_00_u03b2_4471_: *mut LeanObject,
    mut v___y_4472_: *mut LeanObject,
    mut v___y_4473_: *mut LeanObject,
    mut v___y_4474_: *mut LeanObject,
    mut v___y_4475_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4476_: *mut LeanObject = core::ptr::null_mut();
    v_res_4476_ = l_Std_Async_ContextAsync_instFunctor___lam__1(
        v___f_4469_,
        v_00_u03b1_4470_,
        v_00_u03b2_4471_,
        v___y_4472_,
        v___y_4473_,
        v___y_4474_,
    );
    lean_dec_ref(v___y_4474_);
    return v_res_4476_;
}
pub unsafe fn l_Std_Async_ContextAsync_instMonad___lam__0(
    mut v_00_u03b1_4484_: *mut LeanObject,
    mut v_a_4485_: *mut LeanObject,
    mut v_x_4486_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4489_: *mut LeanObject = core::ptr::null_mut();
    v___x_4488_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_4488_, 0, v_a_4485_);
    v___x_4489_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4489_, 0, v___x_4488_);
    return v___x_4489_;
}
pub unsafe fn l_Std_Async_ContextAsync_instMonad___lam__0___boxed(
    mut v_00_u03b1_4490_: *mut LeanObject,
    mut v_a_4491_: *mut LeanObject,
    mut v_x_4492_: *mut LeanObject,
    mut v___y_4493_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4494_: *mut LeanObject = core::ptr::null_mut();
    v_res_4494_ =
        l_Std_Async_ContextAsync_instMonad___lam__0(v_00_u03b1_4490_, v_a_4491_, v_x_4492_);
    lean_dec_ref(v_x_4492_);
    return v_res_4494_;
}
pub unsafe fn l_Std_Async_ContextAsync_instMonad___lam__1(
    mut v_f_4495_: *mut LeanObject,
    mut v_ctx_4496_: *mut LeanObject,
    mut v_x_4497_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_4499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4502_: u8 = 0;
    let mut v___x_4504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4507_: u8 = 0;
    let mut v_a_4508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4509_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4497_) == 0 {
                    lean_dec_ref(v_ctx_4496_);
                    lean_dec_ref(v_f_4495_);
                    v_a_4499_ = lean_ctor_get(v_x_4497_, 0);
                    v_isSharedCheck_4507_ = (!lean_is_exclusive(v_x_4497_)) as u8;
                    if v_isSharedCheck_4507_ == 0 {
                        v___x_4501_ = v_x_4497_;
                        v_isShared_4502_ = v_isSharedCheck_4507_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4499_);
                        lean_dec(v_x_4497_);
                        v___x_4501_ = lean_box(0);
                        v_isShared_4502_ = v_isSharedCheck_4507_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4508_ = lean_ctor_get(v_x_4497_, 0);
                    lean_inc(v_a_4508_);
                    lean_dec_ref_known(v_x_4497_, 1);
                    v___x_4509_ = lean_apply_3(v_f_4495_, v_a_4508_, v_ctx_4496_, lean_box(0));
                    return v___x_4509_;
                }
            }
            1 => {
                if v_isShared_4502_ == 0 {
                    v___x_4504_ = v___x_4501_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4506_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4506_, 0, v_a_4499_);
                    v___x_4504_ = v_reuseFailAlloc_4506_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4505_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4505_, 0, v___x_4504_);
                return v___x_4505_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_instMonad___lam__1___boxed(
    mut v_f_4510_: *mut LeanObject,
    mut v_ctx_4511_: *mut LeanObject,
    mut v_x_4512_: *mut LeanObject,
    mut v___y_4513_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4514_: *mut LeanObject = core::ptr::null_mut();
    v_res_4514_ = l_Std_Async_ContextAsync_instMonad___lam__1(v_f_4510_, v_ctx_4511_, v_x_4512_);
    return v_res_4514_;
}
pub unsafe fn l_Std_Async_ContextAsync_instMonad___lam__2(
    mut v_00_u03b1_4515_: *mut LeanObject,
    mut v_00_u03b2_4516_: *mut LeanObject,
    mut v_x_4517_: *mut LeanObject,
    mut v_f_4518_: *mut LeanObject,
    mut v_ctx_4519_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4524_: u8 = 0;
    let mut v___x_4525_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_ctx_4519_);
    v___x_4521_ = lean_apply_2(v_x_4517_, v_ctx_4519_, lean_box(0));
    v___f_4522_ = lean_alloc_closure(
        l_Std_Async_ContextAsync_instMonad___lam__1___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_4522_, 0, v_f_4518_);
    lean_closure_set(v___f_4522_, 1, v_ctx_4519_);
    v___x_4523_ = lean_unsigned_to_nat(0);
    v___x_4524_ = 0;
    v___x_4525_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_4523_,
        v___x_4524_,
        v___x_4521_,
        v___f_4522_,
    );
    return v___x_4525_;
}
pub unsafe fn l_Std_Async_ContextAsync_instMonad___lam__2___boxed(
    mut v_00_u03b1_4526_: *mut LeanObject,
    mut v_00_u03b2_4527_: *mut LeanObject,
    mut v_x_4528_: *mut LeanObject,
    mut v_f_4529_: *mut LeanObject,
    mut v_ctx_4530_: *mut LeanObject,
    mut v___y_4531_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4532_: *mut LeanObject = core::ptr::null_mut();
    v_res_4532_ = l_Std_Async_ContextAsync_instMonad___lam__2(
        v_00_u03b1_4526_,
        v_00_u03b2_4527_,
        v_x_4528_,
        v_f_4529_,
        v_ctx_4530_,
    );
    return v_res_4532_;
}
pub unsafe fn _init_l_Std_Async_ContextAsync_instMonad() -> *mut LeanObject {
    let mut v___x_4535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_4537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_4538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_4539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_4540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4547_: *mut LeanObject = core::ptr::null_mut();
    v___x_4535_ = l_Std_Async_ContextAsync_instFunctor;
    v___x_4536_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__1_once),
        _init_l_Std_Async_ContextAsync_concurrentlyAll___redArg___closed__1,
    );
    v_toApplicative_4537_ = lean_ctor_get(v___x_4536_, 0);
    v_toSeq_4538_ = lean_ctor_get(v_toApplicative_4537_, 2);
    v_toSeqLeft_4539_ = lean_ctor_get(v_toApplicative_4537_, 3);
    v_toSeqRight_4540_ = lean_ctor_get(v_toApplicative_4537_, 4);
    v___f_4541_ = l_Std_Async_ContextAsync_instMonad___closed__0;
    v___f_4542_ = l_Std_Async_ContextAsync_instMonad___closed__1;
    lean_inc(v_toSeqRight_4540_);
    v___f_4543_ = lean_alloc_closure(
        l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_4543_, 0, v_toSeqRight_4540_);
    lean_inc(v_toSeqLeft_4539_);
    v___f_4544_ = lean_alloc_closure(
        l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_4544_, 0, v_toSeqLeft_4539_);
    lean_inc(v_toSeq_4538_);
    v___f_4545_ = lean_alloc_closure(
        l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_4545_, 0, v_toSeq_4538_);
    v___x_4546_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_4546_, 0, v___x_4535_);
    lean_ctor_set(v___x_4546_, 1, v___f_4541_);
    lean_ctor_set(v___x_4546_, 2, v___f_4545_);
    lean_ctor_set(v___x_4546_, 3, v___f_4544_);
    lean_ctor_set(v___x_4546_, 4, v___f_4543_);
    v___x_4547_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4547_, 0, v___x_4546_);
    lean_ctor_set(v___x_4547_, 1, v___f_4542_);
    return v___x_4547_;
}
pub unsafe fn l_Std_Async_ContextAsync_instMonadLiftIO___lam__0(
    mut v_a_4548_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4549_: *mut LeanObject = core::ptr::null_mut();
    v___x_4549_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_4549_, 0, v_a_4548_);
    return v___x_4549_;
}
pub unsafe fn l_Std_Async_ContextAsync_instMonadLiftIO___lam__1(
    mut v___f_4550_: *mut LeanObject,
    mut v_x_4551_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_4553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4556_: u8 = 0;
    let mut v___x_4558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4561_: u8 = 0;
    let mut v_a_4562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4566_: u8 = 0;
    let mut v___x_4568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4571_: u8 = 0;
    let mut v_a_4572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4574_: u8 = 0;
    let mut v___x_4575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4576_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4551_) == 0 {
                    lean_dec_ref(v___f_4550_);
                    v_a_4553_ = lean_ctor_get(v_x_4551_, 0);
                    v_isSharedCheck_4561_ = (!lean_is_exclusive(v_x_4551_)) as u8;
                    if v_isSharedCheck_4561_ == 0 {
                        v___x_4555_ = v_x_4551_;
                        v_isShared_4556_ = v_isSharedCheck_4561_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4553_);
                        lean_dec(v_x_4551_);
                        v___x_4555_ = lean_box(0);
                        v_isShared_4556_ = v_isSharedCheck_4561_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4562_ = lean_ctor_get(v_x_4551_, 0);
                    lean_inc(v_a_4562_);
                    lean_dec_ref_known(v_x_4551_, 1);
                    if lean_obj_tag(v_a_4562_) == 0 {
                        lean_dec_ref(v___f_4550_);
                        v_a_4563_ = lean_ctor_get(v_a_4562_, 0);
                        v_isSharedCheck_4571_ = (!lean_is_exclusive(v_a_4562_)) as u8;
                        if v_isSharedCheck_4571_ == 0 {
                            v___x_4565_ = v_a_4562_;
                            v_isShared_4566_ = v_isSharedCheck_4571_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_4563_);
                            lean_dec(v_a_4562_);
                            v___x_4565_ = lean_box(0);
                            v_isShared_4566_ = v_isSharedCheck_4571_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_4572_ = lean_ctor_get(v_a_4562_, 0);
                        lean_inc(v_a_4572_);
                        lean_dec_ref_known(v_a_4562_, 1);
                        v___x_4573_ = lean_unsigned_to_nat(0);
                        v___x_4574_ = 0;
                        v___x_4575_ =
                            lean_task_map(v___f_4550_, v_a_4572_, v___x_4573_, v___x_4574_);
                        v___x_4576_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_4576_, 0, v___x_4575_);
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
                    v_reuseFailAlloc_4560_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4560_, 0, v_a_4553_);
                    v___x_4558_ = v_reuseFailAlloc_4560_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4559_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4559_, 0, v___x_4558_);
                return v___x_4559_;
            }
            3 => {
                if v_isShared_4566_ == 0 {
                    v___x_4568_ = v___x_4565_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4570_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4570_, 0, v_a_4563_);
                    v___x_4568_ = v_reuseFailAlloc_4570_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4569_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4569_, 0, v___x_4568_);
                return v___x_4569_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_instMonadLiftIO___lam__1___boxed(
    mut v___f_4577_: *mut LeanObject,
    mut v_x_4578_: *mut LeanObject,
    mut v___y_4579_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4580_: *mut LeanObject = core::ptr::null_mut();
    v_res_4580_ = l_Std_Async_ContextAsync_instMonadLiftIO___lam__1(v___f_4577_, v_x_4578_);
    return v_res_4580_;
}
pub unsafe fn l_Std_Async_ContextAsync_instMonadLiftIO___lam__2(
    mut v___f_4581_: *mut LeanObject,
    mut v_00_u03b1_4582_: *mut LeanObject,
    mut v_x_4583_: *mut LeanObject,
    mut v_x_4584_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_val_4587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4591_: u8 = 0;
    let mut v___x_4592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4597_: u8 = 0;
    let mut v___x_4598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4602_: u8 = 0;
    let mut v_a_4603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4606_: u8 = 0;
    let mut v___x_4608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4610_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4593_ = lean_apply_1(v_x_4583_, lean_box(0));
                if lean_obj_tag(v___x_4593_) == 0 {
                    v_a_4594_ = lean_ctor_get(v___x_4593_, 0);
                    v_isSharedCheck_4602_ = (!lean_is_exclusive(v___x_4593_)) as u8;
                    if v_isSharedCheck_4602_ == 0 {
                        v___x_4596_ = v___x_4593_;
                        v_isShared_4597_ = v_isSharedCheck_4602_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_4594_);
                        lean_dec(v___x_4593_);
                        v___x_4596_ = lean_box(0);
                        v_isShared_4597_ = v_isSharedCheck_4602_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_4603_ = lean_ctor_get(v___x_4593_, 0);
                    v_isSharedCheck_4610_ = (!lean_is_exclusive(v___x_4593_)) as u8;
                    if v_isSharedCheck_4610_ == 0 {
                        v___x_4605_ = v___x_4593_;
                        v_isShared_4606_ = v_isSharedCheck_4610_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_4603_);
                        lean_dec(v___x_4593_);
                        v___x_4605_ = lean_box(0);
                        v_isShared_4606_ = v_isSharedCheck_4610_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4588_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4588_, 0, v_val_4587_);
                v___x_4589_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4589_, 0, v___x_4588_);
                v___x_4590_ = lean_unsigned_to_nat(0);
                v___x_4591_ = 0;
                v___x_4592_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
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
                    lean_ctor_set_tag(v___x_4596_, 1);
                    lean_ctor_set(v___x_4596_, 0, v___x_4598_);
                    v___x_4600_ = v___x_4596_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4601_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4601_, 0, v___x_4598_);
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
                    lean_ctor_set_tag(v___x_4605_, 0);
                    v___x_4608_ = v___x_4605_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4609_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4609_, 0, v_a_4603_);
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
    mut v___f_4611_: *mut LeanObject,
    mut v_00_u03b1_4612_: *mut LeanObject,
    mut v_x_4613_: *mut LeanObject,
    mut v_x_4614_: *mut LeanObject,
    mut v___y_4615_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4616_: *mut LeanObject = core::ptr::null_mut();
    v_res_4616_ = l_Std_Async_ContextAsync_instMonadLiftIO___lam__2(
        v___f_4611_,
        v_00_u03b1_4612_,
        v_x_4613_,
        v_x_4614_,
    );
    lean_dec_ref(v_x_4614_);
    return v_res_4616_;
}
pub unsafe fn l_Std_Async_ContextAsync_instMonadLiftBaseIO___lam__0(
    mut v_00_u03b1_4623_: *mut LeanObject,
    mut v_x_4624_: *mut LeanObject,
    mut v_x_4625_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4629_: *mut LeanObject = core::ptr::null_mut();
    v___x_4627_ = lean_apply_1(v_x_4624_, lean_box(0));
    v___x_4628_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_4628_, 0, v___x_4627_);
    v___x_4629_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4629_, 0, v___x_4628_);
    return v___x_4629_;
}
pub unsafe fn l_Std_Async_ContextAsync_instMonadLiftBaseIO___lam__0___boxed(
    mut v_00_u03b1_4630_: *mut LeanObject,
    mut v_x_4631_: *mut LeanObject,
    mut v_x_4632_: *mut LeanObject,
    mut v___y_4633_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4634_: *mut LeanObject = core::ptr::null_mut();
    v_res_4634_ = l_Std_Async_ContextAsync_instMonadLiftBaseIO___lam__0(
        v_00_u03b1_4630_,
        v_x_4631_,
        v_x_4632_,
    );
    lean_dec_ref(v_x_4632_);
    return v_res_4634_;
}
pub unsafe fn l_Std_Async_ContextAsync_instMonadExceptError___lam__0(
    mut v_00_u03b1_4637_: *mut LeanObject,
    mut v_e_4638_: *mut LeanObject,
    mut v_x_4639_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4642_: *mut LeanObject = core::ptr::null_mut();
    v___x_4641_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4641_, 0, v_e_4638_);
    v___x_4642_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4642_, 0, v___x_4641_);
    return v___x_4642_;
}
pub unsafe fn l_Std_Async_ContextAsync_instMonadExceptError___lam__0___boxed(
    mut v_00_u03b1_4643_: *mut LeanObject,
    mut v_e_4644_: *mut LeanObject,
    mut v_x_4645_: *mut LeanObject,
    mut v___y_4646_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4647_: *mut LeanObject = core::ptr::null_mut();
    v_res_4647_ = l_Std_Async_ContextAsync_instMonadExceptError___lam__0(
        v_00_u03b1_4643_,
        v_e_4644_,
        v_x_4645_,
    );
    lean_dec_ref(v_x_4645_);
    return v_res_4647_;
}
pub unsafe fn l_Std_Async_ContextAsync_instMonadExceptError___lam__1(
    mut v_h_4648_: *mut LeanObject,
    mut v_ctx_4649_: *mut LeanObject,
    mut v_x_4650_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_4650_) == 0 {
        let mut v_a_4652_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4653_: *mut LeanObject = core::ptr::null_mut();
        v_a_4652_ = lean_ctor_get(v_x_4650_, 0);
        lean_inc(v_a_4652_);
        lean_dec_ref_known(v_x_4650_, 1);
        v___x_4653_ = lean_apply_3(v_h_4648_, v_a_4652_, v_ctx_4649_, lean_box(0));
        return v___x_4653_;
    } else {
        let mut v___x_4654_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_ctx_4649_);
        lean_dec_ref(v_h_4648_);
        v___x_4654_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_4654_, 0, v_x_4650_);
        return v___x_4654_;
    }
}
pub unsafe fn l_Std_Async_ContextAsync_instMonadExceptError___lam__1___boxed(
    mut v_h_4655_: *mut LeanObject,
    mut v_ctx_4656_: *mut LeanObject,
    mut v_x_4657_: *mut LeanObject,
    mut v___y_4658_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4659_: *mut LeanObject = core::ptr::null_mut();
    v_res_4659_ =
        l_Std_Async_ContextAsync_instMonadExceptError___lam__1(v_h_4655_, v_ctx_4656_, v_x_4657_);
    return v_res_4659_;
}
pub unsafe fn l_Std_Async_ContextAsync_instMonadExceptError___lam__2(
    mut v_00_u03b1_4660_: *mut LeanObject,
    mut v_x_4661_: *mut LeanObject,
    mut v_h_4662_: *mut LeanObject,
    mut v_ctx_4663_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4668_: u8 = 0;
    let mut v___x_4669_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_ctx_4663_);
    v___x_4665_ = lean_apply_2(v_x_4661_, v_ctx_4663_, lean_box(0));
    v___f_4666_ = lean_alloc_closure(
        l_Std_Async_ContextAsync_instMonadExceptError___lam__1___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_4666_, 0, v_h_4662_);
    lean_closure_set(v___f_4666_, 1, v_ctx_4663_);
    v___x_4667_ = lean_unsigned_to_nat(0);
    v___x_4668_ = 0;
    v___x_4669_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_4667_,
        v___x_4668_,
        v___x_4665_,
        v___f_4666_,
    );
    return v___x_4669_;
}
pub unsafe fn l_Std_Async_ContextAsync_instMonadExceptError___lam__2___boxed(
    mut v_00_u03b1_4670_: *mut LeanObject,
    mut v_x_4671_: *mut LeanObject,
    mut v_h_4672_: *mut LeanObject,
    mut v_ctx_4673_: *mut LeanObject,
    mut v___y_4674_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4675_: *mut LeanObject = core::ptr::null_mut();
    v_res_4675_ = l_Std_Async_ContextAsync_instMonadExceptError___lam__2(
        v_00_u03b1_4670_,
        v_x_4671_,
        v_h_4672_,
        v_ctx_4673_,
    );
    return v_res_4675_;
}
pub unsafe fn l_Std_Async_ContextAsync_instMonadFinally___lam__0(
    mut v_f_4682_: *mut LeanObject,
    mut v_ctx_4683_: *mut LeanObject,
    mut v_opt_4684_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4686_: *mut LeanObject = core::ptr::null_mut();
    v___x_4686_ = lean_apply_3(v_f_4682_, v_opt_4684_, v_ctx_4683_, lean_box(0));
    return v___x_4686_;
}
pub unsafe fn l_Std_Async_ContextAsync_instMonadFinally___lam__0___boxed(
    mut v_f_4687_: *mut LeanObject,
    mut v_ctx_4688_: *mut LeanObject,
    mut v_opt_4689_: *mut LeanObject,
    mut v___y_4690_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4691_: *mut LeanObject = core::ptr::null_mut();
    v_res_4691_ =
        l_Std_Async_ContextAsync_instMonadFinally___lam__0(v_f_4687_, v_ctx_4688_, v_opt_4689_);
    return v_res_4691_;
}
pub unsafe fn l_Std_Async_ContextAsync_instMonadFinally___lam__1(
    mut v_00_u03b1_4692_: *mut LeanObject,
    mut v_00_u03b2_4693_: *mut LeanObject,
    mut v_x_4694_: *mut LeanObject,
    mut v_f_4695_: *mut LeanObject,
    mut v_ctx_4696_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4701_: u8 = 0;
    let mut v___x_4702_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_ctx_4696_);
    v___f_4698_ = lean_alloc_closure(
        l_Std_Async_ContextAsync_instMonadFinally___lam__0___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_4698_, 0, v_f_4695_);
    lean_closure_set(v___f_4698_, 1, v_ctx_4696_);
    v___x_4699_ = lean_apply_1(v_x_4694_, v_ctx_4696_);
    v___x_4700_ = lean_unsigned_to_nat(0);
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
    mut v_00_u03b1_4703_: *mut LeanObject,
    mut v_00_u03b2_4704_: *mut LeanObject,
    mut v_x_4705_: *mut LeanObject,
    mut v_f_4706_: *mut LeanObject,
    mut v_ctx_4707_: *mut LeanObject,
    mut v___y_4708_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4709_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_x_4719_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4721_: *mut LeanObject = core::ptr::null_mut();
    v___x_4721_ = l_Std_Async_ContextAsync_instInhabited___lam__0___closed__3;
    return v___x_4721_;
}
pub unsafe fn l_Std_Async_ContextAsync_instInhabited___lam__0___boxed(
    mut v_x_4722_: *mut LeanObject,
    mut v___y_4723_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4724_: *mut LeanObject = core::ptr::null_mut();
    v_res_4724_ = l_Std_Async_ContextAsync_instInhabited___lam__0(v_x_4722_);
    lean_dec_ref(v_x_4722_);
    return v_res_4724_;
}
pub unsafe fn l_Std_Async_ContextAsync_instInhabited(
    mut v_00_u03b1_4726_: *mut LeanObject,
    mut v_inst_4727_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4728_: *mut LeanObject = core::ptr::null_mut();
    v___f_4728_ = l_Std_Async_ContextAsync_instInhabited___closed__0;
    return v___f_4728_;
}
pub unsafe fn l_Std_Async_ContextAsync_instInhabited___boxed(
    mut v_00_u03b1_4729_: *mut LeanObject,
    mut v_inst_4730_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4731_: *mut LeanObject = core::ptr::null_mut();
    v_res_4731_ = l_Std_Async_ContextAsync_instInhabited(v_00_u03b1_4729_, v_inst_4730_);
    lean_dec(v_inst_4730_);
    return v_res_4731_;
}
pub unsafe fn l_Std_Async_ContextAsync_instMonadAwaitAsyncTask___lam__0(
    mut v_00_u03b1_4732_: *mut LeanObject,
    mut v_t_4733_: *mut LeanObject,
    mut v_x_4734_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4736_: *mut LeanObject = core::ptr::null_mut();
    v___x_4736_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_4736_, 0, v_t_4733_);
    return v___x_4736_;
}
pub unsafe fn l_Std_Async_ContextAsync_instMonadAwaitAsyncTask___lam__0___boxed(
    mut v_00_u03b1_4737_: *mut LeanObject,
    mut v_t_4738_: *mut LeanObject,
    mut v_x_4739_: *mut LeanObject,
    mut v___y_4740_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4741_: *mut LeanObject = core::ptr::null_mut();
    v_res_4741_ = l_Std_Async_ContextAsync_instMonadAwaitAsyncTask___lam__0(
        v_00_u03b1_4737_,
        v_t_4738_,
        v_x_4739_,
    );
    lean_dec_ref(v_x_4739_);
    return v_res_4741_;
}
pub unsafe fn l_Std_Async_ContextAsync_race___redArg___lam__3(
    mut v_x_4744_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_4746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4749_: u8 = 0;
    let mut v___x_4751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4754_: u8 = 0;
    let mut v_a_4755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4756_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4744_) == 0 {
                    v_a_4746_ = lean_ctor_get(v_x_4744_, 0);
                    v_isSharedCheck_4754_ = (!lean_is_exclusive(v_x_4744_)) as u8;
                    if v_isSharedCheck_4754_ == 0 {
                        v___x_4748_ = v_x_4744_;
                        v_isShared_4749_ = v_isSharedCheck_4754_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4746_);
                        lean_dec(v_x_4744_);
                        v___x_4748_ = lean_box(0);
                        v_isShared_4749_ = v_isSharedCheck_4754_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4755_ = lean_ctor_get(v_x_4744_, 0);
                    lean_inc(v_a_4755_);
                    lean_dec_ref_known(v_x_4744_, 1);
                    v___x_4756_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4756_, 0, v_a_4755_);
                    return v___x_4756_;
                }
            }
            1 => {
                if v_isShared_4749_ == 0 {
                    v___x_4751_ = v___x_4748_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4753_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4753_, 0, v_a_4746_);
                    v___x_4751_ = v_reuseFailAlloc_4753_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4752_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4752_, 0, v___x_4751_);
                return v___x_4752_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_race___redArg___lam__3___boxed(
    mut v_x_4757_: *mut LeanObject,
    mut v___y_4758_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4759_: *mut LeanObject = core::ptr::null_mut();
    v_res_4759_ = l_Std_Async_ContextAsync_race___redArg___lam__3(v_x_4757_);
    return v_res_4759_;
}
pub unsafe fn l_Std_Async_ContextAsync_race___redArg___lam__6(
    mut v___f_4760_: *mut LeanObject,
    mut v___f_4761_: *mut LeanObject,
    mut v_prio_4762_: *mut LeanObject,
    mut v___f_4763_: *mut LeanObject,
    mut v_x_4764_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_4766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4769_: u8 = 0;
    let mut v___x_4771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4774_: u8 = 0;
    let mut v_a_4775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4778_: u8 = 0;
    let mut v___x_4779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4785_: u8 = 0;
    let mut v___x_4786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4791_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4764_) == 0 {
                    lean_dec_ref(v___f_4763_);
                    lean_dec(v_prio_4762_);
                    lean_dec(v___f_4761_);
                    lean_dec_ref(v___f_4760_);
                    v_a_4766_ = lean_ctor_get(v_x_4764_, 0);
                    v_isSharedCheck_4774_ = (!lean_is_exclusive(v_x_4764_)) as u8;
                    if v_isSharedCheck_4774_ == 0 {
                        v___x_4768_ = v_x_4764_;
                        v_isShared_4769_ = v_isSharedCheck_4774_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4766_);
                        lean_dec(v_x_4764_);
                        v___x_4768_ = lean_box(0);
                        v_isShared_4769_ = v_isSharedCheck_4774_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4775_ = lean_ctor_get(v_x_4764_, 0);
                    v_isSharedCheck_4791_ = (!lean_is_exclusive(v_x_4764_)) as u8;
                    if v_isSharedCheck_4791_ == 0 {
                        v___x_4777_ = v_x_4764_;
                        v_isShared_4778_ = v_isSharedCheck_4791_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4775_);
                        lean_dec(v_x_4764_);
                        v___x_4777_ = lean_box(0);
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
                    v_reuseFailAlloc_4773_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4773_, 0, v_a_4766_);
                    v___x_4771_ = v_reuseFailAlloc_4773_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4772_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4772_, 0, v___x_4771_);
                return v___x_4772_;
            }
            3 => {
                v___x_4779_ = lean_box(2);
                v___f_4780_ = lean_alloc_closure(
                    l_Std_Async_ContextAsync_concurrently___redArg___lam__3___boxed
                        as *mut core::ffi::c_void,
                    4,
                    2,
                );
                lean_closure_set(v___f_4780_, 0, v_a_4775_);
                lean_closure_set(v___f_4780_, 1, v___x_4779_);
                v___f_4781_ = lean_alloc_closure(
                    l_Std_Async_ContextAsync_concurrently___redArg___lam__5___boxed
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                lean_closure_set(v___f_4781_, 0, v___f_4760_);
                lean_closure_set(v___f_4781_, 1, v___f_4780_);
                lean_closure_set(v___f_4781_, 2, v___f_4761_);
                v___x_4782_ = lean_alloc_closure(
                    l_Std_Async_BaseAsync_toRawBaseIO___boxed as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___x_4782_, 0, lean_box(0));
                lean_closure_set(v___x_4782_, 1, v___f_4781_);
                v___x_4783_ = lean_io_as_task(v___x_4782_, v_prio_4762_);
                v___x_4784_ = lean_unsigned_to_nat(0);
                v___x_4785_ = 1;
                v___x_4786_ = lean_task_bind(v___x_4783_, v___f_4763_, v___x_4784_, v___x_4785_);
                if v_isShared_4778_ == 0 {
                    lean_ctor_set(v___x_4777_, 0, v___x_4786_);
                    v___x_4788_ = v___x_4777_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4790_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4790_, 0, v___x_4786_);
                    v___x_4788_ = v_reuseFailAlloc_4790_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4789_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4789_, 0, v___x_4788_);
                return v___x_4789_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ContextAsync_race___redArg___lam__6___boxed(
    mut v___f_4792_: *mut LeanObject,
    mut v___f_4793_: *mut LeanObject,
    mut v_prio_4794_: *mut LeanObject,
    mut v___f_4795_: *mut LeanObject,
    mut v_x_4796_: *mut LeanObject,
    mut v___y_4797_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4798_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_y_4799_: *mut LeanObject,
    mut v_a_4800_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4802_: *mut LeanObject = core::ptr::null_mut();
    v___x_4802_ = lean_apply_2(v_y_4799_, v_a_4800_, lean_box(0));
    return v___x_4802_;
}
pub unsafe fn l_Std_Async_ContextAsync_race___redArg___lam__0___boxed(
    mut v_y_4803_: *mut LeanObject,
    mut v_a_4804_: *mut LeanObject,
    mut v___y_4805_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4806_: *mut LeanObject = core::ptr::null_mut();
    v_res_4806_ = l_Std_Async_ContextAsync_race___redArg___lam__0(v_y_4803_, v_a_4804_);
    return v_res_4806_;
}
pub unsafe fn l_Std_Async_ContextAsync_race___redArg___lam__5(
    mut v_a_4807_: *mut LeanObject,
    mut v_a_4808_: *mut LeanObject,
    mut v_result_4809_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4813_: *mut LeanObject = core::ptr::null_mut();
    v___x_4811_ = lean_io_promise_resolve(v_result_4809_, v_a_4807_);
    v___x_4812_ = lean_box(2);
    v___x_4813_ = l_Std_CancellationContext_cancel(v_a_4808_, v___x_4812_);
    return v___x_4813_;
}
pub unsafe fn l_Std_Async_ContextAsync_race___redArg___lam__5___boxed(
    mut v_a_4814_: *mut LeanObject,
    mut v_a_4815_: *mut LeanObject,
    mut v_result_4816_: *mut LeanObject,
    mut v___y_4817_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4818_: *mut LeanObject = core::ptr::null_mut();
    v_res_4818_ =
        l_Std_Async_ContextAsync_race___redArg___lam__5(v_a_4814_, v_a_4815_, v_result_4816_);
    lean_dec(v_a_4814_);
    return v_res_4818_;
}
pub unsafe fn l_Std_Async_ContextAsync_race___redArg___lam__4(
    mut v_a_4819_: *mut LeanObject,
    mut v___f_4820_: *mut LeanObject,
    mut v___x_4821_: *mut LeanObject,
    mut v___x_4822_: u8,
    mut v___f_4823_: *mut LeanObject,
    mut v_x_4824_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_4826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4829_: u8 = 0;
    let mut v___x_4831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4834_: u8 = 0;
    let mut v___x_4836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4837_: u8 = 0;
    let mut v___x_4838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4844_: u8 = 0;
    let mut v_unused_4845_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4824_) == 0 {
                    lean_dec_ref(v___f_4823_);
                    lean_dec(v___x_4821_);
                    lean_dec_ref(v___f_4820_);
                    lean_dec_ref(v_a_4819_);
                    v_a_4826_ = lean_ctor_get(v_x_4824_, 0);
                    v_isSharedCheck_4834_ = (!lean_is_exclusive(v_x_4824_)) as u8;
                    if v_isSharedCheck_4834_ == 0 {
                        v___x_4828_ = v_x_4824_;
                        v_isShared_4829_ = v_isSharedCheck_4834_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4826_);
                        lean_dec(v_x_4824_);
                        v___x_4828_ = lean_box(0);
                        v_isShared_4829_ = v_isSharedCheck_4834_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_isSharedCheck_4844_ = (!lean_is_exclusive(v_x_4824_)) as u8;
                    if v_isSharedCheck_4844_ == 0 {
                        v_unused_4845_ = lean_ctor_get(v_x_4824_, 0);
                        lean_dec(v_unused_4845_);
                        v___x_4836_ = v_x_4824_;
                        v_isShared_4837_ = v_isSharedCheck_4844_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v_x_4824_);
                        v___x_4836_ = lean_box(0);
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
                    v_reuseFailAlloc_4833_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4833_, 0, v_a_4826_);
                    v___x_4831_ = v_reuseFailAlloc_4833_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4832_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4832_, 0, v___x_4831_);
                return v___x_4832_;
            }
            3 => {
                lean_inc(v___x_4821_);
                v___x_4838_ =
                    l_BaseIO_chainTask___redArg(v_a_4819_, v___f_4820_, v___x_4821_, v___x_4822_);
                if v_isShared_4837_ == 0 {
                    lean_ctor_set(v___x_4836_, 0, v___x_4838_);
                    v___x_4840_ = v___x_4836_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4843_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4843_, 0, v___x_4838_);
                    v___x_4840_ = v_reuseFailAlloc_4843_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4841_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4841_, 0, v___x_4840_);
                v___x_4842_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
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
    mut v_a_4846_: *mut LeanObject,
    mut v___f_4847_: *mut LeanObject,
    mut v___x_4848_: *mut LeanObject,
    mut v___x_4849_: *mut LeanObject,
    mut v___f_4850_: *mut LeanObject,
    mut v_x_4851_: *mut LeanObject,
    mut v___y_4852_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4305__boxed_4853_: u8 = 0;
    let mut v_res_4854_: *mut LeanObject = core::ptr::null_mut();
    v___x_4305__boxed_4853_ = (lean_unbox(v___x_4849_) as u8);
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
    mut v_a_4855_: *mut LeanObject,
    mut v_a_4856_: *mut LeanObject,
    mut v_a_4857_: *mut LeanObject,
    mut v___f_4858_: *mut LeanObject,
    mut v___f_4859_: *mut LeanObject,
    mut v_a_4860_: *mut LeanObject,
    mut v_x_4861_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_4863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4866_: u8 = 0;
    let mut v___x_4868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4871_: u8 = 0;
    let mut v_a_4872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4875_: u8 = 0;
    let mut v___f_4876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4878_: u8 = 0;
    let mut v___x_4879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4889_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4861_) == 0 {
                    lean_dec_ref(v_a_4860_);
                    lean_dec_ref(v___f_4859_);
                    lean_dec_ref(v___f_4858_);
                    lean_dec_ref(v_a_4857_);
                    lean_dec_ref(v_a_4856_);
                    lean_dec_ref(v_a_4855_);
                    v_a_4863_ = lean_ctor_get(v_x_4861_, 0);
                    v_isSharedCheck_4871_ = (!lean_is_exclusive(v_x_4861_)) as u8;
                    if v_isSharedCheck_4871_ == 0 {
                        v___x_4865_ = v_x_4861_;
                        v_isShared_4866_ = v_isSharedCheck_4871_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4863_);
                        lean_dec(v_x_4861_);
                        v___x_4865_ = lean_box(0);
                        v_isShared_4866_ = v_isSharedCheck_4871_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4872_ = lean_ctor_get(v_x_4861_, 0);
                    v_isSharedCheck_4889_ = (!lean_is_exclusive(v_x_4861_)) as u8;
                    if v_isSharedCheck_4889_ == 0 {
                        v___x_4874_ = v_x_4861_;
                        v_isShared_4875_ = v_isSharedCheck_4889_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4872_);
                        lean_dec(v_x_4861_);
                        v___x_4874_ = lean_box(0);
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
                    v_reuseFailAlloc_4870_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4870_, 0, v_a_4863_);
                    v___x_4868_ = v_reuseFailAlloc_4870_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4869_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4869_, 0, v___x_4868_);
                return v___x_4869_;
            }
            3 => {
                lean_inc_n(v_a_4872_, 2);
                v___f_4876_ = lean_alloc_closure(
                    l_Std_Async_ContextAsync_race___redArg___lam__5___boxed
                        as *mut core::ffi::c_void,
                    4,
                    2,
                );
                lean_closure_set(v___f_4876_, 0, v_a_4872_);
                lean_closure_set(v___f_4876_, 1, v_a_4855_);
                v___x_4877_ = lean_unsigned_to_nat(0);
                v___x_4878_ = 0;
                v___x_4879_ =
                    l_BaseIO_chainTask___redArg(v_a_4856_, v___f_4876_, v___x_4877_, v___x_4878_);
                v___f_4880_ = lean_alloc_closure(
                    l_Std_Async_ContextAsync_race___redArg___lam__5___boxed
                        as *mut core::ffi::c_void,
                    4,
                    2,
                );
                lean_closure_set(v___f_4880_, 0, v_a_4872_);
                lean_closure_set(v___f_4880_, 1, v_a_4857_);
                v___f_4881_ = lean_alloc_closure(
                    l_Std_Async_ContextAsync_raceAll___redArg___lam__13___boxed
                        as *mut core::ffi::c_void,
                    5,
                    3,
                );
                lean_closure_set(v___f_4881_, 0, v_a_4872_);
                lean_closure_set(v___f_4881_, 1, v___f_4858_);
                lean_closure_set(v___f_4881_, 2, v___f_4859_);
                v___x_4882_ = lean_box((v___x_4878_) as usize);
                v___f_4883_ = lean_alloc_closure(
                    l_Std_Async_ContextAsync_race___redArg___lam__4___boxed
                        as *mut core::ffi::c_void,
                    7,
                    5,
                );
                lean_closure_set(v___f_4883_, 0, v_a_4860_);
                lean_closure_set(v___f_4883_, 1, v___f_4880_);
                lean_closure_set(v___f_4883_, 2, v___x_4877_);
                lean_closure_set(v___f_4883_, 3, v___x_4882_);
                lean_closure_set(v___f_4883_, 4, v___f_4881_);
                if v_isShared_4875_ == 0 {
                    lean_ctor_set(v___x_4874_, 0, v___x_4879_);
                    v___x_4885_ = v___x_4874_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4888_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4888_, 0, v___x_4879_);
                    v___x_4885_ = v_reuseFailAlloc_4888_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4886_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4886_, 0, v___x_4885_);
                v___x_4887_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
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
    mut v_a_4890_: *mut LeanObject,
    mut v_a_4891_: *mut LeanObject,
    mut v_a_4892_: *mut LeanObject,
    mut v___f_4893_: *mut LeanObject,
    mut v___f_4894_: *mut LeanObject,
    mut v_a_4895_: *mut LeanObject,
    mut v_x_4896_: *mut LeanObject,
    mut v___y_4897_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4898_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_a_4899_: *mut LeanObject,
    mut v_a_4900_: *mut LeanObject,
    mut v_a_4901_: *mut LeanObject,
    mut v___f_4902_: *mut LeanObject,
    mut v___f_4903_: *mut LeanObject,
    mut v_x_4904_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_4906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4909_: u8 = 0;
    let mut v___x_4911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4914_: u8 = 0;
    let mut v_a_4915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4918_: u8 = 0;
    let mut v___x_4919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4925_: u8 = 0;
    let mut v___x_4926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4928_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4904_) == 0 {
                    lean_dec_ref(v___f_4903_);
                    lean_dec_ref(v___f_4902_);
                    lean_dec_ref(v_a_4901_);
                    lean_dec_ref(v_a_4900_);
                    lean_dec_ref(v_a_4899_);
                    v_a_4906_ = lean_ctor_get(v_x_4904_, 0);
                    v_isSharedCheck_4914_ = (!lean_is_exclusive(v_x_4904_)) as u8;
                    if v_isSharedCheck_4914_ == 0 {
                        v___x_4908_ = v_x_4904_;
                        v_isShared_4909_ = v_isSharedCheck_4914_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4906_);
                        lean_dec(v_x_4904_);
                        v___x_4908_ = lean_box(0);
                        v_isShared_4909_ = v_isSharedCheck_4914_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4915_ = lean_ctor_get(v_x_4904_, 0);
                    v_isSharedCheck_4928_ = (!lean_is_exclusive(v_x_4904_)) as u8;
                    if v_isSharedCheck_4928_ == 0 {
                        v___x_4917_ = v_x_4904_;
                        v_isShared_4918_ = v_isSharedCheck_4928_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4915_);
                        lean_dec(v_x_4904_);
                        v___x_4917_ = lean_box(0);
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
                    v_reuseFailAlloc_4913_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4913_, 0, v_a_4906_);
                    v___x_4911_ = v_reuseFailAlloc_4913_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4912_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4912_, 0, v___x_4911_);
                return v___x_4912_;
            }
            3 => {
                v___x_4919_ = lean_io_promise_new();
                v___f_4920_ = lean_alloc_closure(
                    l_Std_Async_ContextAsync_race___redArg___lam__1___boxed
                        as *mut core::ffi::c_void,
                    8,
                    6,
                );
                lean_closure_set(v___f_4920_, 0, v_a_4899_);
                lean_closure_set(v___f_4920_, 1, v_a_4900_);
                lean_closure_set(v___f_4920_, 2, v_a_4901_);
                lean_closure_set(v___f_4920_, 3, v___f_4902_);
                lean_closure_set(v___f_4920_, 4, v___f_4903_);
                lean_closure_set(v___f_4920_, 5, v_a_4915_);
                if v_isShared_4918_ == 0 {
                    lean_ctor_set(v___x_4917_, 0, v___x_4919_);
                    v___x_4922_ = v___x_4917_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4927_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4927_, 0, v___x_4919_);
                    v___x_4922_ = v_reuseFailAlloc_4927_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4923_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4923_, 0, v___x_4922_);
                v___x_4924_ = lean_unsigned_to_nat(0);
                v___x_4925_ = 0;
                v___x_4926_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
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
    mut v_a_4929_: *mut LeanObject,
    mut v_a_4930_: *mut LeanObject,
    mut v_a_4931_: *mut LeanObject,
    mut v___f_4932_: *mut LeanObject,
    mut v___f_4933_: *mut LeanObject,
    mut v_x_4934_: *mut LeanObject,
    mut v___y_4935_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4936_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_a_4937_: *mut LeanObject,
    mut v___f_4938_: *mut LeanObject,
    mut v_a_4939_: *mut LeanObject,
    mut v_a_4940_: *mut LeanObject,
    mut v___f_4941_: *mut LeanObject,
    mut v___f_4942_: *mut LeanObject,
    mut v_x_4943_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_4945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4948_: u8 = 0;
    let mut v___x_4950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4953_: u8 = 0;
    let mut v_a_4954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4957_: u8 = 0;
    let mut v___x_4958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4963_: u8 = 0;
    let mut v___x_4964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4968_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4943_) == 0 {
                    lean_dec_ref(v___f_4942_);
                    lean_dec_ref(v___f_4941_);
                    lean_dec_ref(v_a_4940_);
                    lean_dec_ref(v_a_4939_);
                    lean_dec_ref(v___f_4938_);
                    v_a_4945_ = lean_ctor_get(v_x_4943_, 0);
                    v_isSharedCheck_4953_ = (!lean_is_exclusive(v_x_4943_)) as u8;
                    if v_isSharedCheck_4953_ == 0 {
                        v___x_4947_ = v_x_4943_;
                        v_isShared_4948_ = v_isSharedCheck_4953_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4945_);
                        lean_dec(v_x_4943_);
                        v___x_4947_ = lean_box(0);
                        v_isShared_4948_ = v_isSharedCheck_4953_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4954_ = lean_ctor_get(v_x_4943_, 0);
                    v_isSharedCheck_4968_ = (!lean_is_exclusive(v_x_4943_)) as u8;
                    if v_isSharedCheck_4968_ == 0 {
                        v___x_4956_ = v_x_4943_;
                        v_isShared_4957_ = v_isSharedCheck_4968_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4954_);
                        lean_dec(v_x_4943_);
                        v___x_4956_ = lean_box(0);
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
                    v_reuseFailAlloc_4952_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4952_, 0, v_a_4945_);
                    v___x_4950_ = v_reuseFailAlloc_4952_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4951_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4951_, 0, v___x_4950_);
                return v___x_4951_;
            }
            3 => {
                lean_inc_ref(v_a_4937_);
                v___x_4958_ = l_Std_CancellationContext_fork(v_a_4937_);
                if v_isShared_4957_ == 0 {
                    lean_ctor_set(v___x_4956_, 0, v___x_4958_);
                    v___x_4960_ = v___x_4956_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4967_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4967_, 0, v___x_4958_);
                    v___x_4960_ = v_reuseFailAlloc_4967_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4961_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4961_, 0, v___x_4960_);
                v___x_4962_ = lean_unsigned_to_nat(0);
                v___x_4963_ = 0;
                v___x_4964_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
                    v___x_4962_,
                    v___x_4963_,
                    v___x_4961_,
                    v___f_4938_,
                );
                v___f_4965_ = lean_alloc_closure(
                    l_Std_Async_ContextAsync_race___redArg___lam__2___boxed
                        as *mut core::ffi::c_void,
                    7,
                    5,
                );
                lean_closure_set(v___f_4965_, 0, v_a_4939_);
                lean_closure_set(v___f_4965_, 1, v_a_4954_);
                lean_closure_set(v___f_4965_, 2, v_a_4940_);
                lean_closure_set(v___f_4965_, 3, v___f_4941_);
                lean_closure_set(v___f_4965_, 4, v___f_4942_);
                v___x_4966_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
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
    mut v_a_4969_: *mut LeanObject,
    mut v___f_4970_: *mut LeanObject,
    mut v_a_4971_: *mut LeanObject,
    mut v_a_4972_: *mut LeanObject,
    mut v___f_4973_: *mut LeanObject,
    mut v___f_4974_: *mut LeanObject,
    mut v_x_4975_: *mut LeanObject,
    mut v___y_4976_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4977_: *mut LeanObject = core::ptr::null_mut();
    v_res_4977_ = l_Std_Async_ContextAsync_race___redArg___lam__7(
        v_a_4969_,
        v___f_4970_,
        v_a_4971_,
        v_a_4972_,
        v___f_4973_,
        v___f_4974_,
        v_x_4975_,
    );
    lean_dec_ref(v_a_4969_);
    return v_res_4977_;
}
pub unsafe fn l_Std_Async_ContextAsync_race___redArg___lam__8(
    mut v_a_4978_: *mut LeanObject,
    mut v___f_4979_: *mut LeanObject,
    mut v_y_4980_: *mut LeanObject,
    mut v___f_4981_: *mut LeanObject,
    mut v_prio_4982_: *mut LeanObject,
    mut v___f_4983_: *mut LeanObject,
    mut v_a_4984_: *mut LeanObject,
    mut v___f_4985_: *mut LeanObject,
    mut v___f_4986_: *mut LeanObject,
    mut v_x_4987_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_4989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4992_: u8 = 0;
    let mut v___x_4994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4997_: u8 = 0;
    let mut v_a_4998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5001_: u8 = 0;
    let mut v___x_5002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5007_: u8 = 0;
    let mut v___x_5008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5014_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4987_) == 0 {
                    lean_dec_ref(v___f_4986_);
                    lean_dec_ref(v___f_4985_);
                    lean_dec_ref(v_a_4984_);
                    lean_dec_ref(v___f_4983_);
                    lean_dec(v_prio_4982_);
                    lean_dec(v___f_4981_);
                    lean_dec_ref(v_y_4980_);
                    lean_dec_ref(v___f_4979_);
                    v_a_4989_ = lean_ctor_get(v_x_4987_, 0);
                    v_isSharedCheck_4997_ = (!lean_is_exclusive(v_x_4987_)) as u8;
                    if v_isSharedCheck_4997_ == 0 {
                        v___x_4991_ = v_x_4987_;
                        v_isShared_4992_ = v_isSharedCheck_4997_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4989_);
                        lean_dec(v_x_4987_);
                        v___x_4991_ = lean_box(0);
                        v_isShared_4992_ = v_isSharedCheck_4997_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4998_ = lean_ctor_get(v_x_4987_, 0);
                    v_isSharedCheck_5014_ = (!lean_is_exclusive(v_x_4987_)) as u8;
                    if v_isSharedCheck_5014_ == 0 {
                        v___x_5000_ = v_x_4987_;
                        v_isShared_5001_ = v_isSharedCheck_5014_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4998_);
                        lean_dec(v_x_4987_);
                        v___x_5000_ = lean_box(0);
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
                    v_reuseFailAlloc_4996_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4996_, 0, v_a_4989_);
                    v___x_4994_ = v_reuseFailAlloc_4996_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4995_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4995_, 0, v___x_4994_);
                return v___x_4995_;
            }
            3 => {
                lean_inc_ref(v_a_4978_);
                v___x_5002_ = l_Std_CancellationContext_fork(v_a_4978_);
                if v_isShared_5001_ == 0 {
                    lean_ctor_set(v___x_5000_, 0, v___x_5002_);
                    v___x_5004_ = v___x_5000_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5013_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5013_, 0, v___x_5002_);
                    v___x_5004_ = v_reuseFailAlloc_5013_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5005_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5005_, 0, v___x_5004_);
                v___x_5006_ = lean_unsigned_to_nat(0);
                v___x_5007_ = 0;
                v___x_5008_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
                    v___x_5006_,
                    v___x_5007_,
                    v___x_5005_,
                    v___f_4979_,
                );
                lean_inc(v_a_4998_);
                v___f_5009_ = lean_alloc_closure(
                    l_Std_Async_ContextAsync_race___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___f_5009_, 0, v_y_4980_);
                lean_closure_set(v___f_5009_, 1, v_a_4998_);
                v___f_5010_ = lean_alloc_closure(
                    l_Std_Async_ContextAsync_race___redArg___lam__6___boxed
                        as *mut core::ffi::c_void,
                    6,
                    4,
                );
                lean_closure_set(v___f_5010_, 0, v___f_5009_);
                lean_closure_set(v___f_5010_, 1, v___f_4981_);
                lean_closure_set(v___f_5010_, 2, v_prio_4982_);
                lean_closure_set(v___f_5010_, 3, v___f_4983_);
                lean_inc_ref(v_a_4978_);
                v___f_5011_ = lean_alloc_closure(
                    l_Std_Async_ContextAsync_race___redArg___lam__7___boxed
                        as *mut core::ffi::c_void,
                    8,
                    6,
                );
                lean_closure_set(v___f_5011_, 0, v_a_4978_);
                lean_closure_set(v___f_5011_, 1, v___f_5010_);
                lean_closure_set(v___f_5011_, 2, v_a_4998_);
                lean_closure_set(v___f_5011_, 3, v_a_4984_);
                lean_closure_set(v___f_5011_, 4, v___f_4985_);
                lean_closure_set(v___f_5011_, 5, v___f_4986_);
                v___x_5012_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
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
    mut v_a_5015_: *mut LeanObject,
    mut v___f_5016_: *mut LeanObject,
    mut v_y_5017_: *mut LeanObject,
    mut v___f_5018_: *mut LeanObject,
    mut v_prio_5019_: *mut LeanObject,
    mut v___f_5020_: *mut LeanObject,
    mut v_a_5021_: *mut LeanObject,
    mut v___f_5022_: *mut LeanObject,
    mut v___f_5023_: *mut LeanObject,
    mut v_x_5024_: *mut LeanObject,
    mut v___y_5025_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5026_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_a_5015_);
    return v_res_5026_;
}
pub unsafe fn l_Std_Async_ContextAsync_race___redArg___lam__9(
    mut v_a_5027_: *mut LeanObject,
    mut v_x_5028_: *mut LeanObject,
    mut v___f_5029_: *mut LeanObject,
    mut v_prio_5030_: *mut LeanObject,
    mut v___f_5031_: *mut LeanObject,
    mut v_a_5032_: *mut LeanObject,
    mut v_y_5033_: *mut LeanObject,
    mut v___f_5034_: *mut LeanObject,
    mut v___f_5035_: *mut LeanObject,
    mut v___f_5036_: *mut LeanObject,
    mut v___f_5037_: *mut LeanObject,
    mut v_x_5038_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_5040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5043_: u8 = 0;
    let mut v___x_5045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5048_: u8 = 0;
    let mut v_a_5049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5052_: u8 = 0;
    let mut v___x_5053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5061_: u8 = 0;
    let mut v___x_5062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5064_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5038_) == 0 {
                    lean_dec_ref(v___f_5037_);
                    lean_dec_ref(v___f_5036_);
                    lean_dec_ref(v___f_5035_);
                    lean_dec(v___f_5034_);
                    lean_dec_ref(v_y_5033_);
                    lean_dec_ref(v___f_5031_);
                    lean_dec(v_prio_5030_);
                    lean_dec(v___f_5029_);
                    lean_dec_ref(v_x_5028_);
                    lean_dec_ref(v_a_5027_);
                    v_a_5040_ = lean_ctor_get(v_x_5038_, 0);
                    v_isSharedCheck_5048_ = (!lean_is_exclusive(v_x_5038_)) as u8;
                    if v_isSharedCheck_5048_ == 0 {
                        v___x_5042_ = v_x_5038_;
                        v_isShared_5043_ = v_isSharedCheck_5048_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5040_);
                        lean_dec(v_x_5038_);
                        v___x_5042_ = lean_box(0);
                        v_isShared_5043_ = v_isSharedCheck_5048_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5049_ = lean_ctor_get(v_x_5038_, 0);
                    v_isSharedCheck_5064_ = (!lean_is_exclusive(v_x_5038_)) as u8;
                    if v_isSharedCheck_5064_ == 0 {
                        v___x_5051_ = v_x_5038_;
                        v_isShared_5052_ = v_isSharedCheck_5064_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5049_);
                        lean_dec(v_x_5038_);
                        v___x_5051_ = lean_box(0);
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
                    v_reuseFailAlloc_5047_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5047_, 0, v_a_5040_);
                    v___x_5045_ = v_reuseFailAlloc_5047_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5046_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5046_, 0, v___x_5045_);
                return v___x_5046_;
            }
            3 => {
                v___x_5053_ = l_Std_CancellationContext_fork(v_a_5027_);
                lean_inc(v_a_5049_);
                v___f_5054_ = lean_alloc_closure(
                    l_Std_Async_ContextAsync_raceAll___redArg___lam__10___boxed
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___f_5054_, 0, v_x_5028_);
                lean_closure_set(v___f_5054_, 1, v_a_5049_);
                lean_inc(v_prio_5030_);
                v___f_5055_ = lean_alloc_closure(
                    l_Std_Async_ContextAsync_race___redArg___lam__6___boxed
                        as *mut core::ffi::c_void,
                    6,
                    4,
                );
                lean_closure_set(v___f_5055_, 0, v___f_5054_);
                lean_closure_set(v___f_5055_, 1, v___f_5029_);
                lean_closure_set(v___f_5055_, 2, v_prio_5030_);
                lean_closure_set(v___f_5055_, 3, v___f_5031_);
                lean_inc_ref(v_a_5032_);
                v___f_5056_ = lean_alloc_closure(
                    l_Std_Async_ContextAsync_race___redArg___lam__8___boxed
                        as *mut core::ffi::c_void,
                    11,
                    9,
                );
                lean_closure_set(v___f_5056_, 0, v_a_5032_);
                lean_closure_set(v___f_5056_, 1, v___f_5055_);
                lean_closure_set(v___f_5056_, 2, v_y_5033_);
                lean_closure_set(v___f_5056_, 3, v___f_5034_);
                lean_closure_set(v___f_5056_, 4, v_prio_5030_);
                lean_closure_set(v___f_5056_, 5, v___f_5035_);
                lean_closure_set(v___f_5056_, 6, v_a_5049_);
                lean_closure_set(v___f_5056_, 7, v___f_5036_);
                lean_closure_set(v___f_5056_, 8, v___f_5037_);
                if v_isShared_5052_ == 0 {
                    lean_ctor_set(v___x_5051_, 0, v___x_5053_);
                    v___x_5058_ = v___x_5051_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5063_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5063_, 0, v___x_5053_);
                    v___x_5058_ = v_reuseFailAlloc_5063_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5059_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5059_, 0, v___x_5058_);
                v___x_5060_ = lean_unsigned_to_nat(0);
                v___x_5061_ = 0;
                v___x_5062_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
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
    mut v_a_5065_: *mut LeanObject,
    mut v_x_5066_: *mut LeanObject,
    mut v___f_5067_: *mut LeanObject,
    mut v_prio_5068_: *mut LeanObject,
    mut v___f_5069_: *mut LeanObject,
    mut v_a_5070_: *mut LeanObject,
    mut v_y_5071_: *mut LeanObject,
    mut v___f_5072_: *mut LeanObject,
    mut v___f_5073_: *mut LeanObject,
    mut v___f_5074_: *mut LeanObject,
    mut v___f_5075_: *mut LeanObject,
    mut v_x_5076_: *mut LeanObject,
    mut v___y_5077_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5078_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_a_5070_);
    return v_res_5078_;
}
pub unsafe fn l_Std_Async_ContextAsync_race___redArg___lam__10(
    mut v_x_5079_: *mut LeanObject,
    mut v___f_5080_: *mut LeanObject,
    mut v_prio_5081_: *mut LeanObject,
    mut v___f_5082_: *mut LeanObject,
    mut v_a_5083_: *mut LeanObject,
    mut v_y_5084_: *mut LeanObject,
    mut v___f_5085_: *mut LeanObject,
    mut v___f_5086_: *mut LeanObject,
    mut v___f_5087_: *mut LeanObject,
    mut v___f_5088_: *mut LeanObject,
    mut v_x_5089_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_5091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5094_: u8 = 0;
    let mut v___x_5096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5099_: u8 = 0;
    let mut v_a_5100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5103_: u8 = 0;
    let mut v___x_5104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5110_: u8 = 0;
    let mut v___x_5111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5113_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5089_) == 0 {
                    lean_dec_ref(v___f_5088_);
                    lean_dec_ref(v___f_5087_);
                    lean_dec_ref(v___f_5086_);
                    lean_dec(v___f_5085_);
                    lean_dec_ref(v_y_5084_);
                    lean_dec_ref(v___f_5082_);
                    lean_dec(v_prio_5081_);
                    lean_dec(v___f_5080_);
                    lean_dec_ref(v_x_5079_);
                    v_a_5091_ = lean_ctor_get(v_x_5089_, 0);
                    v_isSharedCheck_5099_ = (!lean_is_exclusive(v_x_5089_)) as u8;
                    if v_isSharedCheck_5099_ == 0 {
                        v___x_5093_ = v_x_5089_;
                        v_isShared_5094_ = v_isSharedCheck_5099_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5091_);
                        lean_dec(v_x_5089_);
                        v___x_5093_ = lean_box(0);
                        v_isShared_5094_ = v_isSharedCheck_5099_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5100_ = lean_ctor_get(v_x_5089_, 0);
                    v_isSharedCheck_5113_ = (!lean_is_exclusive(v_x_5089_)) as u8;
                    if v_isSharedCheck_5113_ == 0 {
                        v___x_5102_ = v_x_5089_;
                        v_isShared_5103_ = v_isSharedCheck_5113_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5100_);
                        lean_dec(v_x_5089_);
                        v___x_5102_ = lean_box(0);
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
                    v_reuseFailAlloc_5098_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5098_, 0, v_a_5091_);
                    v___x_5096_ = v_reuseFailAlloc_5098_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5097_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5097_, 0, v___x_5096_);
                return v___x_5097_;
            }
            3 => {
                lean_inc(v_a_5100_);
                v___x_5104_ = l_Std_CancellationContext_fork(v_a_5100_);
                lean_inc_ref(v_a_5083_);
                v___f_5105_ = lean_alloc_closure(
                    l_Std_Async_ContextAsync_race___redArg___lam__9___boxed
                        as *mut core::ffi::c_void,
                    13,
                    11,
                );
                lean_closure_set(v___f_5105_, 0, v_a_5100_);
                lean_closure_set(v___f_5105_, 1, v_x_5079_);
                lean_closure_set(v___f_5105_, 2, v___f_5080_);
                lean_closure_set(v___f_5105_, 3, v_prio_5081_);
                lean_closure_set(v___f_5105_, 4, v___f_5082_);
                lean_closure_set(v___f_5105_, 5, v_a_5083_);
                lean_closure_set(v___f_5105_, 6, v_y_5084_);
                lean_closure_set(v___f_5105_, 7, v___f_5085_);
                lean_closure_set(v___f_5105_, 8, v___f_5086_);
                lean_closure_set(v___f_5105_, 9, v___f_5087_);
                lean_closure_set(v___f_5105_, 10, v___f_5088_);
                if v_isShared_5103_ == 0 {
                    lean_ctor_set(v___x_5102_, 0, v___x_5104_);
                    v___x_5107_ = v___x_5102_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5112_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5112_, 0, v___x_5104_);
                    v___x_5107_ = v_reuseFailAlloc_5112_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5108_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5108_, 0, v___x_5107_);
                v___x_5109_ = lean_unsigned_to_nat(0);
                v___x_5110_ = 0;
                v___x_5111_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
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
    mut v_x_5114_: *mut LeanObject,
    mut v___f_5115_: *mut LeanObject,
    mut v_prio_5116_: *mut LeanObject,
    mut v___f_5117_: *mut LeanObject,
    mut v_a_5118_: *mut LeanObject,
    mut v_y_5119_: *mut LeanObject,
    mut v___f_5120_: *mut LeanObject,
    mut v___f_5121_: *mut LeanObject,
    mut v___f_5122_: *mut LeanObject,
    mut v___f_5123_: *mut LeanObject,
    mut v_x_5124_: *mut LeanObject,
    mut v___y_5125_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5126_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_a_5118_);
    return v_res_5126_;
}
pub unsafe fn l_Std_Async_ContextAsync_race___redArg(
    mut v_x_5128_: *mut LeanObject,
    mut v_y_5129_: *mut LeanObject,
    mut v_prio_5130_: *mut LeanObject,
    mut v_a_5131_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5141_: u8 = 0;
    let mut v___x_5142_: *mut LeanObject = core::ptr::null_mut();
    v___f_5133_ = l_Std_Async_ContextAsync_concurrently___redArg___closed__1;
    v___f_5134_ = l_Std_Async_ContextAsync_concurrently___redArg___closed__0;
    v___f_5135_ = l_Std_Async_ContextAsync_raceAll___redArg___closed__0;
    v___f_5136_ = l_Std_Async_ContextAsync_race___redArg___closed__0;
    lean_inc_ref_n(v_a_5131_, 2);
    v___f_5137_ = lean_alloc_closure(
        l_Std_Async_ContextAsync_race___redArg___lam__10___boxed as *mut core::ffi::c_void,
        12,
        10,
    );
    lean_closure_set(v___f_5137_, 0, v_x_5128_);
    lean_closure_set(v___f_5137_, 1, v___f_5133_);
    lean_closure_set(v___f_5137_, 2, v_prio_5130_);
    lean_closure_set(v___f_5137_, 3, v___f_5134_);
    lean_closure_set(v___f_5137_, 4, v_a_5131_);
    lean_closure_set(v___f_5137_, 5, v_y_5129_);
    lean_closure_set(v___f_5137_, 6, v___f_5133_);
    lean_closure_set(v___f_5137_, 7, v___f_5134_);
    lean_closure_set(v___f_5137_, 8, v___f_5135_);
    lean_closure_set(v___f_5137_, 9, v___f_5136_);
    v___x_5138_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_5138_, 0, v_a_5131_);
    v___x_5139_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5139_, 0, v___x_5138_);
    v___x_5140_ = lean_unsigned_to_nat(0);
    v___x_5141_ = 0;
    v___x_5142_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_5140_,
        v___x_5141_,
        v___x_5139_,
        v___f_5137_,
    );
    return v___x_5142_;
}
pub unsafe fn l_Std_Async_ContextAsync_race___redArg___boxed(
    mut v_x_5143_: *mut LeanObject,
    mut v_y_5144_: *mut LeanObject,
    mut v_prio_5145_: *mut LeanObject,
    mut v_a_5146_: *mut LeanObject,
    mut v_a_5147_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5148_: *mut LeanObject = core::ptr::null_mut();
    v_res_5148_ =
        l_Std_Async_ContextAsync_race___redArg(v_x_5143_, v_y_5144_, v_prio_5145_, v_a_5146_);
    lean_dec_ref(v_a_5146_);
    return v_res_5148_;
}
pub unsafe fn l_Std_Async_ContextAsync_race(
    mut v_00_u03b1_5149_: *mut LeanObject,
    mut v_inst_5150_: *mut LeanObject,
    mut v_x_5151_: *mut LeanObject,
    mut v_y_5152_: *mut LeanObject,
    mut v_prio_5153_: *mut LeanObject,
    mut v_a_5154_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5164_: u8 = 0;
    let mut v___x_5165_: *mut LeanObject = core::ptr::null_mut();
    v___f_5156_ = l_Std_Async_ContextAsync_concurrently___redArg___closed__1;
    v___f_5157_ = l_Std_Async_ContextAsync_concurrently___redArg___closed__0;
    v___f_5158_ = l_Std_Async_ContextAsync_raceAll___redArg___closed__0;
    v___f_5159_ = l_Std_Async_ContextAsync_race___redArg___closed__0;
    lean_inc_ref_n(v_a_5154_, 2);
    v___f_5160_ = lean_alloc_closure(
        l_Std_Async_ContextAsync_race___redArg___lam__10___boxed as *mut core::ffi::c_void,
        12,
        10,
    );
    lean_closure_set(v___f_5160_, 0, v_x_5151_);
    lean_closure_set(v___f_5160_, 1, v___f_5156_);
    lean_closure_set(v___f_5160_, 2, v_prio_5153_);
    lean_closure_set(v___f_5160_, 3, v___f_5157_);
    lean_closure_set(v___f_5160_, 4, v_a_5154_);
    lean_closure_set(v___f_5160_, 5, v_y_5152_);
    lean_closure_set(v___f_5160_, 6, v___f_5156_);
    lean_closure_set(v___f_5160_, 7, v___f_5157_);
    lean_closure_set(v___f_5160_, 8, v___f_5158_);
    lean_closure_set(v___f_5160_, 9, v___f_5159_);
    v___x_5161_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_5161_, 0, v_a_5154_);
    v___x_5162_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5162_, 0, v___x_5161_);
    v___x_5163_ = lean_unsigned_to_nat(0);
    v___x_5164_ = 0;
    v___x_5165_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_5163_,
        v___x_5164_,
        v___x_5162_,
        v___f_5160_,
    );
    return v___x_5165_;
}
pub unsafe fn l_Std_Async_ContextAsync_race___boxed(
    mut v_00_u03b1_5166_: *mut LeanObject,
    mut v_inst_5167_: *mut LeanObject,
    mut v_x_5168_: *mut LeanObject,
    mut v_y_5169_: *mut LeanObject,
    mut v_prio_5170_: *mut LeanObject,
    mut v_a_5171_: *mut LeanObject,
    mut v_a_5172_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5173_: *mut LeanObject = core::ptr::null_mut();
    v_res_5173_ = l_Std_Async_ContextAsync_race(
        v_00_u03b1_5166_,
        v_inst_5167_,
        v_x_5168_,
        v_y_5169_,
        v_prio_5170_,
        v_a_5171_,
    );
    lean_dec_ref(v_a_5171_);
    lean_dec(v_inst_5167_);
    return v_res_5173_;
}
pub unsafe fn l_Std_Async_Selector_cancelled(mut v_a_5174_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_5176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5180_: u8 = 0;
    let mut v___x_5181_: *mut LeanObject = core::ptr::null_mut();
    v___f_5176_ = l_Std_Async_ContextAsync_doneSelector___closed__0;
    lean_inc_ref(v_a_5174_);
    v___x_5177_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_5177_, 0, v_a_5174_);
    v___x_5178_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5178_, 0, v___x_5177_);
    v___x_5179_ = lean_unsigned_to_nat(0);
    v___x_5180_ = 0;
    v___x_5181_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_5179_,
        v___x_5180_,
        v___x_5178_,
        v___f_5176_,
    );
    return v___x_5181_;
}
pub unsafe fn l_Std_Async_Selector_cancelled___boxed(
    mut v_a_5182_: *mut LeanObject,
    mut v_a_5183_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5184_: *mut LeanObject = core::ptr::null_mut();
    v_res_5184_ = l_Std_Async_Selector_cancelled(v_a_5182_);
    lean_dec_ref(v_a_5182_);
    return v_res_5184_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Async_ContextAsync(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Internal_UV(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Async_Timer(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Sync_CancellationContext(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Std_Async_ContextAsync_instMonad = _init_l_Std_Async_ContextAsync_instMonad();
    lean_mark_persistent(l_Std_Async_ContextAsync_instMonad);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Async_ContextAsync(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Async_ContextAsync(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Internal_UV(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Async_Timer(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Sync_CancellationContext(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Async_ContextAsync(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Async_ContextAsync(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Async_ContextAsync(builtin);
}
