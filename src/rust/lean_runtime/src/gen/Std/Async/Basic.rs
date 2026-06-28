// Lean compiler output
// Module: Std.Async.Basic
// Imports: Init.System.Promise Init.While
use crate::r#gen::Init::Control::Basic::l_Functor_mapRev___redArg;
use crate::r#gen::Init::Control::Except::{l_Except_map, l_Except_pure};
use crate::r#gen::Init::Data::Array::Basic::l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map;
use crate::r#gen::Init::Prelude::{
    l_Function_comp, l_Function_const___boxed, l_MonadExcept_orElse,
    l_instMonadLiftT___lam__0___boxed, l_liftM,
};
use crate::r#gen::Init::System::IO::{
    l_BaseIO_chainTask___redArg, l_instMonadBaseIO___aux__5___boxed,
};
use crate::r#gen::Init::System::IOError::lean_mk_io_user_error;
use crate::r#gen::Init::System::Promise::{
    initialize_Init_System_Promise, l_IO_Promise_result_x21___redArg,
    runtime_initialize_Init_System_Promise,
};
use crate::r#gen::Init::While::{initialize_Init_While, runtime_initialize_Init_While};
use crate::lean_imports_rs::Init::Core::{
    lean_task_bind, lean_task_get_own, lean_task_map, lean_task_pure,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_array_size;
use crate::lean_imports_rs::Init::System::IO::{
    lean_io_as_task, lean_io_bind_task, lean_io_get_task_state, lean_io_map_task,
};
use crate::lean_imports_rs::Init::System::Promise::{
    lean_io_promise_new, lean_io_promise_resolve, lean_io_promise_result_opt,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_apply_4, lean_apply_5, lean_box, lean_closure_set,
    lean_ctor_get, lean_ctor_set, lean_ctor_set_tag, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unbox,
    lean_unsigned_to_nat,
};
pub static l_Std_Async_instMonadAwaitExceptTOfMonad___redArg___closed__0_value: LeanClosureObject<
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
    m_fun: l_Std_Async_instMonadAwaitExceptTOfMonad___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Async_instMonadAwaitExceptTOfMonad___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_instMonadAwaitExceptTOfMonad___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Async_instMonadAsyncStateTOfMonadOfFunctor___redArg___closed__0_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Async_instMonadAsyncStateTOfMonadOfFunctor___redArg___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Async_instMonadAsyncStateTOfMonadOfFunctor___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_instMonadAsyncStateTOfMonadOfFunctor___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Async_ETask_ofPurePromise___redArg___closed__0_value: LeanClosureObject<2> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 2) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Except_pure as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 2,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Std_Async_ETask_ofPurePromise___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_ETask_ofPurePromise___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Async_ETask_instFunctor___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Async_ETask_instFunctor___lam__1 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_ETask_instFunctor___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_ETask_instFunctor___closed__0_value) as *mut LeanObject;
pub static l_Std_Async_ETask_instFunctor___closed__1_value: LeanClosureObject<1> =
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
        m_fun: l_Std_Async_ETask_instFunctor___lam__0 as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_ETask_instFunctor___closed__0_value) as *mut LeanObject,
        ],
    };
static mut l_Std_Async_ETask_instFunctor___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_ETask_instFunctor___closed__1_value) as *mut LeanObject;
pub static l_Std_Async_ETask_instFunctor___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Async_ETask_instFunctor___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Async_ETask_instFunctor___closed__1_value) as *mut LeanObject,
    ],
};
static mut l_Std_Async_ETask_instFunctor___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_ETask_instFunctor___closed__2_value) as *mut LeanObject;
pub static l_Std_Async_ETask_instMonad___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Async_ETask_instMonad___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_ETask_instMonad___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_ETask_instMonad___closed__0_value) as *mut LeanObject;
pub static l_Std_Async_ETask_instMonad___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Async_ETask_instMonad___lam__3 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_ETask_instMonad___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_ETask_instMonad___closed__1_value) as *mut LeanObject;
pub static l_Std_Async_ETask_instMonad___closed__2_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Async_ETask_instMonad___lam__5 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_ETask_instMonad___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_ETask_instMonad___closed__2_value) as *mut LeanObject;
pub static l_Std_Async_ETask_instMonad___closed__3_value: LeanClosureObject<2> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 2) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Async_ETask_instMonad___lam__7 as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 2,
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_ETask_instMonad___closed__0_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Async_ETask_instMonad___closed__2_value) as *mut LeanObject,
        ],
    };
static mut l_Std_Async_ETask_instMonad___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_ETask_instMonad___closed__3_value) as *mut LeanObject;
pub static l_Std_Async_ETask_instMonad___closed__4_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Async_ETask_instMonad___lam__9 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_ETask_instMonad___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_ETask_instMonad___closed__4_value) as *mut LeanObject;
static mut l_Std_Async_ETask_instMonad___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Async_ETask_instMonad___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Async_ETask_instMonad___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Async_ETask_instMonad___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Async_ETask_instMonad___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Async_ETask_instMonad___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Async_MaybeTask_joinTask___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Async_MaybeTask_joinTask___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_MaybeTask_joinTask___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_MaybeTask_joinTask___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Async_MaybeTask_instFunctor___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Async_MaybeTask_instFunctor___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_MaybeTask_instFunctor___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_MaybeTask_instFunctor___closed__0_value) as *mut LeanObject;
pub static l_Std_Async_MaybeTask_instFunctor___closed__1_value: LeanClosureObject<1> =
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
        m_fun: l_Std_Async_MaybeTask_instFunctor___lam__1 as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_MaybeTask_instFunctor___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Async_MaybeTask_instFunctor___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_MaybeTask_instFunctor___closed__1_value) as *mut LeanObject;
pub static l_Std_Async_MaybeTask_instFunctor___closed__2_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_Async_MaybeTask_instFunctor___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Async_MaybeTask_instFunctor___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Async_MaybeTask_instFunctor___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_MaybeTask_instFunctor___closed__2_value) as *mut LeanObject;
pub static mut l_Std_Async_MaybeTask_instFunctor: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_MaybeTask_instFunctor___closed__2_value) as *mut LeanObject;
pub static l_Std_Async_MaybeTask_instMonad___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Async_MaybeTask_instMonad___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_MaybeTask_instMonad___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_MaybeTask_instMonad___closed__0_value) as *mut LeanObject;
pub static l_Std_Async_MaybeTask_instMonad___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Async_MaybeTask_instMonad___lam__3 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_MaybeTask_instMonad___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_MaybeTask_instMonad___closed__1_value) as *mut LeanObject;
pub static l_Std_Async_MaybeTask_instMonad___closed__2_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Async_MaybeTask_instMonad___lam__5 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_MaybeTask_instMonad___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_MaybeTask_instMonad___closed__2_value) as *mut LeanObject;
pub static l_Std_Async_MaybeTask_instMonad___closed__3_value: LeanClosureObject<1> =
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
        m_fun: l_Std_Async_MaybeTask_instMonad___lam__7 as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_MaybeTask_instMonad___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Async_MaybeTask_instMonad___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_MaybeTask_instMonad___closed__3_value) as *mut LeanObject;
pub static l_Std_Async_MaybeTask_instMonad___closed__4_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Async_MaybeTask_instMonad___lam__10 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_MaybeTask_instMonad___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_MaybeTask_instMonad___closed__4_value) as *mut LeanObject;
pub static l_Std_Async_MaybeTask_instMonad___closed__5_value: LeanCtorObject<5> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Async_MaybeTask_instFunctor___closed__2_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Async_MaybeTask_instMonad___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Async_MaybeTask_instMonad___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Async_MaybeTask_instMonad___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Async_MaybeTask_instMonad___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Std_Async_MaybeTask_instMonad___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_MaybeTask_instMonad___closed__5_value) as *mut LeanObject;
pub static l_Std_Async_MaybeTask_instMonad___closed__6_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Async_MaybeTask_instMonad___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Async_MaybeTask_instMonad___closed__2_value) as *mut LeanObject,
    ],
};
static mut l_Std_Async_MaybeTask_instMonad___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_MaybeTask_instMonad___closed__6_value) as *mut LeanObject;
pub static mut l_Std_Async_MaybeTask_instMonad: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_MaybeTask_instMonad___closed__6_value) as *mut LeanObject;
pub static l_Std_Async_BaseAsync_instFunctor___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Async_BaseAsync_instFunctor___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_BaseAsync_instFunctor___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_BaseAsync_instFunctor___closed__0_value) as *mut LeanObject;
pub static l_Std_Async_BaseAsync_instFunctor___closed__1_value: LeanClosureObject<1> =
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
        m_fun: l_Std_Async_BaseAsync_instFunctor___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_BaseAsync_instFunctor___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Async_BaseAsync_instFunctor___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_BaseAsync_instFunctor___closed__1_value) as *mut LeanObject;
pub static l_Std_Async_BaseAsync_instFunctor___closed__2_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_Async_BaseAsync_instFunctor___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Async_BaseAsync_instFunctor___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Async_BaseAsync_instFunctor___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_BaseAsync_instFunctor___closed__2_value) as *mut LeanObject;
pub static mut l_Std_Async_BaseAsync_instFunctor: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_BaseAsync_instFunctor___closed__2_value) as *mut LeanObject;
pub static l_Std_Async_BaseAsync_instMonad___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Async_BaseAsync_instMonad___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_BaseAsync_instMonad___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_BaseAsync_instMonad___closed__0_value) as *mut LeanObject;
pub static l_Std_Async_BaseAsync_instMonad___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Async_BaseAsync_instMonad___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_BaseAsync_instMonad___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_BaseAsync_instMonad___closed__1_value) as *mut LeanObject;
pub static l_Std_Async_BaseAsync_instMonad___closed__2_value: LeanClosureObject<1> =
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
        m_fun: l_Std_Async_BaseAsync_instMonad___lam__5___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_BaseAsync_instMonad___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Async_BaseAsync_instMonad___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_BaseAsync_instMonad___closed__2_value) as *mut LeanObject;
pub static l_Std_Async_BaseAsync_instMonad___closed__3_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Async_BaseAsync_instMonad___lam__7___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_BaseAsync_instMonad___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_BaseAsync_instMonad___closed__3_value) as *mut LeanObject;
pub static l_Std_Async_BaseAsync_instMonad___closed__4_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Async_BaseAsync_pure___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_BaseAsync_instMonad___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_BaseAsync_instMonad___closed__4_value) as *mut LeanObject;
pub static l_Std_Async_BaseAsync_instMonad___closed__5_value: LeanCtorObject<5> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Async_BaseAsync_instFunctor___closed__2_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Async_BaseAsync_instMonad___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Async_BaseAsync_instMonad___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Async_BaseAsync_instMonad___closed__2_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Async_BaseAsync_instMonad___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_Std_Async_BaseAsync_instMonad___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_BaseAsync_instMonad___closed__5_value) as *mut LeanObject;
pub static l_Std_Async_BaseAsync_instMonad___closed__6_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Async_BaseAsync_instMonad___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Async_BaseAsync_instMonad___closed__1_value) as *mut LeanObject,
    ],
};
static mut l_Std_Async_BaseAsync_instMonad___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_BaseAsync_instMonad___closed__6_value) as *mut LeanObject;
pub static mut l_Std_Async_BaseAsync_instMonad: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_BaseAsync_instMonad___closed__6_value) as *mut LeanObject;
pub static l_Std_Async_BaseAsync_instMonadLiftBaseIO___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Async_BaseAsync_lift___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_BaseAsync_instMonadLiftBaseIO___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_BaseAsync_instMonadLiftBaseIO___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Async_BaseAsync_instMonadLiftBaseIO: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_BaseAsync_instMonadLiftBaseIO___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Async_BaseAsync_instMonadAwaitTask___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Async_BaseAsync_await___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_BaseAsync_instMonadAwaitTask___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_BaseAsync_instMonadAwaitTask___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Async_BaseAsync_instMonadAwaitTask: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_BaseAsync_instMonadAwaitTask___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Async_BaseAsync_instMonadAsyncTask___closed__0_value: LeanClosureObject<1> =
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
        m_fun: l_Std_Async_BaseAsync_instMonadAsyncTask___lam__1___boxed
            as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_MaybeTask_joinTask___redArg___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Async_BaseAsync_instMonadAsyncTask___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_BaseAsync_instMonadAsyncTask___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Async_BaseAsync_instMonadAsyncTask: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_BaseAsync_instMonadAsyncTask___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Async_BaseAsync_instMonadFinally___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Async_BaseAsync_instMonadFinally___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_BaseAsync_instMonadFinally___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_BaseAsync_instMonadFinally___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Async_BaseAsync_instMonadFinally: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_BaseAsync_instMonadFinally___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Async_BaseAsync_race___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_instMonadLiftT___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_BaseAsync_race___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_BaseAsync_race___redArg___closed__0_value) as *mut LeanObject;
pub static l_Std_Async_BaseAsync_concurrentlyAll___redArg___lam__0___closed__0_value:
    LeanClosureObject<1> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Async_BaseAsync_await___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_Std_Async_BaseAsync_concurrentlyAll___redArg___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_BaseAsync_concurrentlyAll___redArg___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Async_BaseAsync_concurrentlyAll___redArg___closed__0_value: LeanClosureObject<1> =
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
        m_fun: l_Std_Async_BaseAsync_concurrentlyAll___redArg___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_BaseAsync_instMonad___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Async_BaseAsync_concurrentlyAll___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_BaseAsync_concurrentlyAll___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Async_EAsync_asTask___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Async_EAsync_asTask___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_EAsync_asTask___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_EAsync_asTask___redArg___closed__0_value) as *mut LeanObject;
pub static l_Std_Async_EAsync_instFunctor___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Async_EAsync_instFunctor___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_EAsync_instFunctor___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_EAsync_instFunctor___closed__0_value) as *mut LeanObject;
pub static l_Std_Async_EAsync_instFunctor___closed__1_value: LeanClosureObject<1> =
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
        m_fun: l_Std_Async_EAsync_instFunctor___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_EAsync_instFunctor___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Async_EAsync_instFunctor___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_EAsync_instFunctor___closed__1_value) as *mut LeanObject;
pub static l_Std_Async_EAsync_instFunctor___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Async_EAsync_instFunctor___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Async_EAsync_instFunctor___closed__1_value) as *mut LeanObject,
    ],
};
static mut l_Std_Async_EAsync_instFunctor___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_EAsync_instFunctor___closed__2_value) as *mut LeanObject;
pub static l_Std_Async_EAsync_instMonad___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Async_EAsync_instMonad___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_EAsync_instMonad___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_EAsync_instMonad___closed__0_value) as *mut LeanObject;
pub static l_Std_Async_EAsync_instMonad___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Async_EAsync_instMonad___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_EAsync_instMonad___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_EAsync_instMonad___closed__1_value) as *mut LeanObject;
pub static l_Std_Async_EAsync_instMonad___closed__2_value: LeanClosureObject<1> =
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
        m_fun: l_Std_Async_EAsync_instMonad___lam__5___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_EAsync_instMonad___closed__0_value) as *mut LeanObject,
        ],
    };
static mut l_Std_Async_EAsync_instMonad___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_EAsync_instMonad___closed__2_value) as *mut LeanObject;
pub static l_Std_Async_EAsync_instMonad___closed__3_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Async_EAsync_instMonad___lam__7___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_EAsync_instMonad___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_EAsync_instMonad___closed__3_value) as *mut LeanObject;
static mut l_Std_Async_EAsync_instMonad___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Async_EAsync_instMonad___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Async_EAsync_instMonad___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Async_EAsync_instMonad___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Async_EAsync_instMonad___closed__6_value: LeanClosureObject<1> =
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
        m_fun: l_Std_Async_EAsync_bind___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Std_Async_EAsync_instMonad___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_EAsync_instMonad___closed__6_value) as *mut LeanObject;
static mut l_Std_Async_EAsync_instMonad___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Async_EAsync_instMonad___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Async_EAsync_instMonadLiftEIO___closed__0_value: LeanClosureObject<1> =
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
        m_fun: l_Std_Async_EAsync_lift___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Std_Async_EAsync_instMonadLiftEIO___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_EAsync_instMonadLiftEIO___closed__0_value) as *mut LeanObject;
pub static l_Std_Async_EAsync_instMonadExcept___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Async_EAsync_instMonadExcept___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_EAsync_instMonadExcept___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_EAsync_instMonadExcept___closed__0_value) as *mut LeanObject;
pub static l_Std_Async_EAsync_instMonadExcept___closed__1_value: LeanClosureObject<1> =
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
        m_fun: l_Std_Async_EAsync_throw___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Std_Async_EAsync_instMonadExcept___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_EAsync_instMonadExcept___closed__1_value) as *mut LeanObject;
pub static l_Std_Async_EAsync_instMonadExcept___closed__2_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_Async_EAsync_instMonadExcept___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Async_EAsync_instMonadExcept___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Async_EAsync_instMonadExcept___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_EAsync_instMonadExcept___closed__2_value) as *mut LeanObject;
pub static l_Std_Async_EAsync_instMonadExceptOf___closed__0_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_Async_EAsync_instMonadExcept___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Async_EAsync_instMonadExcept___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Async_EAsync_instMonadExceptOf___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_EAsync_instMonadExceptOf___closed__0_value) as *mut LeanObject;
pub static l_Std_Async_EAsync_instMonadFinally___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Async_EAsync_instMonadFinally___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_EAsync_instMonadFinally___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_EAsync_instMonadFinally___closed__0_value) as *mut LeanObject;
static mut l_Std_Async_EAsync_instOrElse___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Async_EAsync_instOrElse___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Async_EAsync_instOrElse___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Async_EAsync_instOrElse___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Async_EAsync_instMonadAwaitETask___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Async_EAsync_instMonadAwaitETask___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_EAsync_instMonadAwaitETask___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_EAsync_instMonadAwaitETask___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Async_EAsync_instMonadAwaitTask___closed__0_value: LeanClosureObject<1> =
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
        m_fun: l_Std_Async_EAsync_instMonadAwaitTask___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 1,
        m_objs: [core::ptr::addr_of!(
            l_Std_Async_instMonadAwaitExceptTOfMonad___redArg___closed__0_value
        ) as *mut LeanObject],
    };
static mut l_Std_Async_EAsync_instMonadAwaitTask___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_EAsync_instMonadAwaitTask___closed__0_value) as *mut LeanObject;
pub static l_Std_Async_EAsync_instMonadAwaitAsyncTaskError___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Async_EAsync_instMonadAwaitAsyncTaskError___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_EAsync_instMonadAwaitAsyncTaskError___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_EAsync_instMonadAwaitAsyncTaskError___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Async_EAsync_instMonadAwaitAsyncTaskError: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_EAsync_instMonadAwaitAsyncTaskError___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Async_EAsync_instMonadAwaitPromise___closed__0_value: LeanClosureObject<1> =
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
        m_fun: l_Std_Async_EAsync_instMonadAwaitPromise___lam__1___boxed
            as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 1,
        m_objs: [core::ptr::addr_of!(
            l_Std_Async_instMonadAwaitExceptTOfMonad___redArg___closed__0_value
        ) as *mut LeanObject],
    };
static mut l_Std_Async_EAsync_instMonadAwaitPromise___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_EAsync_instMonadAwaitPromise___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Async_EAsync_instMonadAsyncETask___closed__0_value: LeanClosureObject<1> =
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
        m_fun: l_Std_Async_EAsync_instMonadAsyncETask___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_EAsync_asTask___redArg___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Async_EAsync_instMonadAsyncETask___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_EAsync_instMonadAsyncETask___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___closed__1_value: LeanClosureObject<1> =
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
        m_fun: l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___lam__1___boxed
            as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 1,
        m_objs: [core::ptr::addr_of!(
            l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___closed__0_value
        ) as *mut LeanObject],
    };
static mut l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___closed__1_value)
        as *mut LeanObject;
pub static mut l_Std_Async_EAsync_instMonadAsyncAsyncTaskError: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___closed__1_value)
        as *mut LeanObject;
pub static l_Std_Async_EAsync_instMonadLiftBaseIO___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Async_EAsync_instMonadLiftBaseIO___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_EAsync_instMonadLiftBaseIO___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_EAsync_instMonadLiftBaseIO___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Async_EAsync_instMonadLiftEIO__1___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Async_EAsync_instMonadLiftEIO__1___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_EAsync_instMonadLiftEIO__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_EAsync_instMonadLiftEIO__1___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Async_EAsync_instMonadLiftBaseAsync___closed__0_value: LeanClosureObject<1> =
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
        m_fun: l_Std_Async_EAsync_instMonadLiftBaseAsync___lam__1___boxed
            as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 1,
        m_objs: [core::ptr::addr_of!(
            l_Std_Async_instMonadAwaitExceptTOfMonad___redArg___closed__0_value
        ) as *mut LeanObject],
    };
static mut l_Std_Async_EAsync_instMonadLiftBaseAsync___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_EAsync_instMonadLiftBaseAsync___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Async_EAsync_instForInLoopUnit___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Async_EAsync_instForInLoopUnit___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_EAsync_instForInLoopUnit___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_EAsync_instForInLoopUnit___closed__0_value) as *mut LeanObject;
pub static l_Std_Async_EAsync_race___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Async_EAsync_race___redArg___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_EAsync_race___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_EAsync_race___redArg___closed__0_value) as *mut LeanObject;
pub static l_Std_Async_EAsync_race___redArg___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Async_EAsync_race___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_EAsync_race___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_EAsync_race___redArg___closed__1_value) as *mut LeanObject;
static mut l_Std_Async_EAsync_concurrentlyAll___redArg___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Async_EAsync_concurrentlyAll___redArg___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Async_EAsync_concurrentlyAll___redArg___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Async_EAsync_concurrentlyAll___redArg___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_EAsync_concurrentlyAll___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_EAsync_concurrentlyAll___redArg___closed__1_value)
        as *mut LeanObject;
static mut l_Std_Async_EAsync_concurrentlyAll___redArg___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Async_EAsync_concurrentlyAll___redArg___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Async_Async_ofIOTask___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Async_Async_ofIOTask___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_Async_ofIOTask___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_Async_ofIOTask___redArg___closed__0_value) as *mut LeanObject;
pub static l_Std_Async_Async_ofIOTask___redArg___closed__1_value: LeanClosureObject<1> =
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
        m_fun: l_Std_Async_Async_ofIOTask___redArg___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_Async_ofIOTask___redArg___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Async_Async_ofIOTask___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_Async_ofIOTask___redArg___closed__1_value) as *mut LeanObject;
pub static mut l_Std_Async_Async_instMonadAsyncAsyncTask: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___closed__1_value)
        as *mut LeanObject;
pub static l_Std_Async_Async_instMonadAwaitAsyncTask___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Async_Async_instMonadAwaitAsyncTask___aux__1___boxed
            as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_Async_instMonadAwaitAsyncTask___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_Async_instMonadAwaitAsyncTask___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Async_Async_instMonadAwaitAsyncTask: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_Async_instMonadAwaitAsyncTask___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Async_Async_instMonadAwaitPromise___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Async_Async_instMonadAwaitPromise___aux__1___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_Async_instMonadAwaitPromise___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_Async_instMonadAwaitPromise___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Async_Async_instMonadAwaitPromise: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_Async_instMonadAwaitPromise___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Async_Async_race___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Async_Async_race___redArg___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_Async_race___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_Async_race___redArg___closed__0_value) as *mut LeanObject;
pub static l_Std_Async_Async_race___redArg___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Async_Async_race___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Async_Async_race___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_Async_race___redArg___closed__1_value) as *mut LeanObject;
pub static l_Std_Async_Async_concurrentlyAll___redArg___lam__0___closed__0_value:
    LeanClosureObject<1> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Async_Async_instMonadAwaitAsyncTask___aux__1___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_Std_Async_Async_concurrentlyAll___redArg___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_Async_concurrentlyAll___redArg___lam__0___closed__0_value)
        as *mut LeanObject;
static mut l_Std_Async_Async_concurrentlyAll___redArg___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Async_Async_concurrentlyAll___redArg___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Std_Async_instMonadAwaitStateTOfMonad___redArg___lam__0(
    mut v___y_5563_: *mut LeanObject,
    mut v_toPure_5564_: *mut LeanObject,
    mut v_a_5565_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5567_: *mut LeanObject = core::ptr::null_mut();
    v___x_5566_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_5566_, 0, v_a_5565_);
    lean_ctor_set(v___x_5566_, 1, v___y_5563_);
    v___x_5567_ = lean_apply_2(v_toPure_5564_, lean_box(0), v___x_5566_);
    return v___x_5567_;
}
pub unsafe fn l_Std_Async_instMonadAwaitStateTOfMonad___redArg___lam__1(
    mut v_inst_5568_: *mut LeanObject,
    mut v_inst_5569_: *mut LeanObject,
    mut v_00_u03b1_5570_: *mut LeanObject,
    mut v___y_5571_: *mut LeanObject,
    mut v___y_5572_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_5573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_5574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_5575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5578_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_5573_ = lean_ctor_get(v_inst_5568_, 0);
    lean_inc_ref(v_toApplicative_5573_);
    v_toBind_5574_ = lean_ctor_get(v_inst_5568_, 1);
    lean_inc(v_toBind_5574_);
    lean_dec_ref(v_inst_5568_);
    v_toPure_5575_ = lean_ctor_get(v_toApplicative_5573_, 1);
    lean_inc(v_toPure_5575_);
    lean_dec_ref(v_toApplicative_5573_);
    v___x_5576_ = lean_apply_2(v_inst_5569_, lean_box(0), v___y_5571_);
    v___f_5577_ = lean_alloc_closure(
        l_Std_Async_instMonadAwaitStateTOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_5577_, 0, v___y_5572_);
    lean_closure_set(v___f_5577_, 1, v_toPure_5575_);
    v___x_5578_ = lean_apply_4(
        v_toBind_5574_,
        lean_box(0),
        lean_box(0),
        v___x_5576_,
        v___f_5577_,
    );
    return v___x_5578_;
}
pub unsafe fn l_Std_Async_instMonadAwaitStateTOfMonad___redArg(
    mut v_inst_5579_: *mut LeanObject,
    mut v_inst_5580_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5581_: *mut LeanObject = core::ptr::null_mut();
    v___f_5581_ = lean_alloc_closure(
        l_Std_Async_instMonadAwaitStateTOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_5581_, 0, v_inst_5579_);
    lean_closure_set(v___f_5581_, 1, v_inst_5580_);
    return v___f_5581_;
}
pub unsafe fn l_Std_Async_instMonadAwaitStateTOfMonad(
    mut v_m_5582_: *mut LeanObject,
    mut v_t_5583_: *mut LeanObject,
    mut v_n_5584_: *mut LeanObject,
    mut v_inst_5585_: *mut LeanObject,
    mut v_inst_5586_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5587_: *mut LeanObject = core::ptr::null_mut();
    v___f_5587_ = lean_alloc_closure(
        l_Std_Async_instMonadAwaitStateTOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_5587_, 0, v_inst_5585_);
    lean_closure_set(v___f_5587_, 1, v_inst_5586_);
    return v___f_5587_;
}
pub unsafe fn l_Std_Async_instMonadAwaitExceptTOfMonad___redArg___lam__0(
    mut v_a_5588_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5589_: *mut LeanObject = core::ptr::null_mut();
    v___x_5589_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_5589_, 0, v_a_5588_);
    return v___x_5589_;
}
pub unsafe fn l_Std_Async_instMonadAwaitExceptTOfMonad___redArg___lam__1(
    mut v_inst_5590_: *mut LeanObject,
    mut v_inst_5591_: *mut LeanObject,
    mut v___f_5592_: *mut LeanObject,
    mut v_00_u03b1_5593_: *mut LeanObject,
    mut v___y_5594_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_5595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_5596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_5597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5599_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_5595_ = lean_ctor_get(v_inst_5590_, 0);
    lean_inc_ref(v_toApplicative_5595_);
    lean_dec_ref(v_inst_5590_);
    v_toFunctor_5596_ = lean_ctor_get(v_toApplicative_5595_, 0);
    lean_inc_ref(v_toFunctor_5596_);
    lean_dec_ref(v_toApplicative_5595_);
    v_map_5597_ = lean_ctor_get(v_toFunctor_5596_, 0);
    lean_inc(v_map_5597_);
    lean_dec_ref(v_toFunctor_5596_);
    v___x_5598_ = lean_apply_2(v_inst_5591_, lean_box(0), v___y_5594_);
    v___x_5599_ = lean_apply_4(
        v_map_5597_,
        lean_box(0),
        lean_box(0),
        v___f_5592_,
        v___x_5598_,
    );
    return v___x_5599_;
}
pub unsafe fn l_Std_Async_instMonadAwaitExceptTOfMonad___redArg(
    mut v_inst_5601_: *mut LeanObject,
    mut v_inst_5602_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5604_: *mut LeanObject = core::ptr::null_mut();
    v___f_5603_ = l_Std_Async_instMonadAwaitExceptTOfMonad___redArg___closed__0;
    v___f_5604_ = lean_alloc_closure(
        l_Std_Async_instMonadAwaitExceptTOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        3,
    );
    lean_closure_set(v___f_5604_, 0, v_inst_5601_);
    lean_closure_set(v___f_5604_, 1, v_inst_5602_);
    lean_closure_set(v___f_5604_, 2, v___f_5603_);
    return v___f_5604_;
}
pub unsafe fn l_Std_Async_instMonadAwaitExceptTOfMonad(
    mut v_m_5605_: *mut LeanObject,
    mut v_t_5606_: *mut LeanObject,
    mut v_n_5607_: *mut LeanObject,
    mut v_inst_5608_: *mut LeanObject,
    mut v_inst_5609_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5610_: *mut LeanObject = core::ptr::null_mut();
    v___x_5610_ = l_Std_Async_instMonadAwaitExceptTOfMonad___redArg(v_inst_5608_, v_inst_5609_);
    return v___x_5610_;
}
pub unsafe fn l_Std_Async_instMonadAwaitReaderTOfMonad___redArg___lam__0(
    mut v_inst_5611_: *mut LeanObject,
    mut v_00_u03b1_5612_: *mut LeanObject,
    mut v___y_5613_: *mut LeanObject,
    mut v___y_5614_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5615_: *mut LeanObject = core::ptr::null_mut();
    v___x_5615_ = lean_apply_2(v_inst_5611_, lean_box(0), v___y_5613_);
    return v___x_5615_;
}
pub unsafe fn l_Std_Async_instMonadAwaitReaderTOfMonad___redArg___lam__0___boxed(
    mut v_inst_5616_: *mut LeanObject,
    mut v_00_u03b1_5617_: *mut LeanObject,
    mut v___y_5618_: *mut LeanObject,
    mut v___y_5619_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5620_: *mut LeanObject = core::ptr::null_mut();
    v_res_5620_ = l_Std_Async_instMonadAwaitReaderTOfMonad___redArg___lam__0(
        v_inst_5616_,
        v_00_u03b1_5617_,
        v___y_5618_,
        v___y_5619_,
    );
    lean_dec(v___y_5619_);
    return v_res_5620_;
}
pub unsafe fn l_Std_Async_instMonadAwaitReaderTOfMonad___redArg(
    mut v_inst_5621_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5622_: *mut LeanObject = core::ptr::null_mut();
    v___f_5622_ = lean_alloc_closure(
        l_Std_Async_instMonadAwaitReaderTOfMonad___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_5622_, 0, v_inst_5621_);
    return v___f_5622_;
}
pub unsafe fn l_Std_Async_instMonadAwaitReaderTOfMonad(
    mut v_m_5623_: *mut LeanObject,
    mut v_t_5624_: *mut LeanObject,
    mut v_n_5625_: *mut LeanObject,
    mut v_inst_5626_: *mut LeanObject,
    mut v_inst_5627_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5628_: *mut LeanObject = core::ptr::null_mut();
    v___f_5628_ = lean_alloc_closure(
        l_Std_Async_instMonadAwaitReaderTOfMonad___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_5628_, 0, v_inst_5627_);
    return v___f_5628_;
}
pub unsafe fn l_Std_Async_instMonadAwaitReaderTOfMonad___boxed(
    mut v_m_5629_: *mut LeanObject,
    mut v_t_5630_: *mut LeanObject,
    mut v_n_5631_: *mut LeanObject,
    mut v_inst_5632_: *mut LeanObject,
    mut v_inst_5633_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5634_: *mut LeanObject = core::ptr::null_mut();
    v_res_5634_ = l_Std_Async_instMonadAwaitReaderTOfMonad(
        v_m_5629_,
        v_t_5630_,
        v_n_5631_,
        v_inst_5632_,
        v_inst_5633_,
    );
    lean_dec_ref(v_inst_5632_);
    return v_res_5634_;
}
pub unsafe fn l_Std_Async_instMonadAwaitStateRefT_x27___redArg(
    mut v_inst_5635_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5636_: *mut LeanObject = core::ptr::null_mut();
    v___f_5636_ = lean_alloc_closure(
        l_Std_Async_instMonadAwaitReaderTOfMonad___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_5636_, 0, v_inst_5635_);
    return v___f_5636_;
}
pub unsafe fn l_Std_Async_instMonadAwaitStateRefT_x27(
    mut v_t_5637_: *mut LeanObject,
    mut v_m_5638_: *mut LeanObject,
    mut v_s_5639_: *mut LeanObject,
    mut v_n_5640_: *mut LeanObject,
    mut v_inst_5641_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5642_: *mut LeanObject = core::ptr::null_mut();
    v___f_5642_ = lean_alloc_closure(
        l_Std_Async_instMonadAwaitReaderTOfMonad___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_5642_, 0, v_inst_5641_);
    return v___f_5642_;
}
pub unsafe fn l_Std_Async_instMonadAwaitStateTOfMonad__1___redArg(
    mut v_inst_5643_: *mut LeanObject,
    mut v_inst_5644_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5645_: *mut LeanObject = core::ptr::null_mut();
    v___f_5645_ = lean_alloc_closure(
        l_Std_Async_instMonadAwaitStateTOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_5645_, 0, v_inst_5643_);
    lean_closure_set(v___f_5645_, 1, v_inst_5644_);
    return v___f_5645_;
}
pub unsafe fn l_Std_Async_instMonadAwaitStateTOfMonad__1(
    mut v_m_5646_: *mut LeanObject,
    mut v_t_5647_: *mut LeanObject,
    mut v_s_5648_: *mut LeanObject,
    mut v_inst_5649_: *mut LeanObject,
    mut v_inst_5650_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5651_: *mut LeanObject = core::ptr::null_mut();
    v___f_5651_ = lean_alloc_closure(
        l_Std_Async_instMonadAwaitStateTOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_5651_, 0, v_inst_5649_);
    lean_closure_set(v___f_5651_, 1, v_inst_5650_);
    return v___f_5651_;
}
pub unsafe fn l_Std_Async_instMonadAsyncReaderT___redArg___lam__0(
    mut v_inst_5652_: *mut LeanObject,
    mut v_00_u03b1_5653_: *mut LeanObject,
    mut v_p_5654_: *mut LeanObject,
    mut v_prio_5655_: *mut LeanObject,
    mut v___y_5656_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5658_: *mut LeanObject = core::ptr::null_mut();
    v___x_5657_ = lean_apply_1(v_p_5654_, v___y_5656_);
    v___x_5658_ = lean_apply_3(v_inst_5652_, lean_box(0), v___x_5657_, v_prio_5655_);
    return v___x_5658_;
}
pub unsafe fn l_Std_Async_instMonadAsyncReaderT___redArg(
    mut v_inst_5659_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5660_: *mut LeanObject = core::ptr::null_mut();
    v___f_5660_ = lean_alloc_closure(
        l_Std_Async_instMonadAsyncReaderT___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_5660_, 0, v_inst_5659_);
    return v___f_5660_;
}
pub unsafe fn l_Std_Async_instMonadAsyncReaderT(
    mut v_t_5661_: *mut LeanObject,
    mut v_m_5662_: *mut LeanObject,
    mut v_n_5663_: *mut LeanObject,
    mut v_inst_5664_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5665_: *mut LeanObject = core::ptr::null_mut();
    v___f_5665_ = lean_alloc_closure(
        l_Std_Async_instMonadAsyncReaderT___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_5665_, 0, v_inst_5664_);
    return v___f_5665_;
}
pub unsafe fn l_Std_Async_instMonadAsyncStateRefT_x27___redArg(
    mut v_inst_5666_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5667_: *mut LeanObject = core::ptr::null_mut();
    v___f_5667_ = lean_alloc_closure(
        l_Std_Async_instMonadAsyncReaderT___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_5667_, 0, v_inst_5666_);
    return v___f_5667_;
}
pub unsafe fn l_Std_Async_instMonadAsyncStateRefT_x27(
    mut v_t_5668_: *mut LeanObject,
    mut v_m_5669_: *mut LeanObject,
    mut v_s_5670_: *mut LeanObject,
    mut v_n_5671_: *mut LeanObject,
    mut v_inst_5672_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5673_: *mut LeanObject = core::ptr::null_mut();
    v___f_5673_ = lean_alloc_closure(
        l_Std_Async_instMonadAsyncReaderT___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_5673_, 0, v_inst_5672_);
    return v___f_5673_;
}
pub unsafe fn l_Std_Async_instMonadAsyncStateTOfMonadOfFunctor___redArg___lam__0(
    mut v_self_5674_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_5675_: *mut LeanObject = core::ptr::null_mut();
    v_fst_5675_ = lean_ctor_get(v_self_5674_, 0);
    lean_inc(v_fst_5675_);
    return v_fst_5675_;
}
pub unsafe fn l_Std_Async_instMonadAsyncStateTOfMonadOfFunctor___redArg___lam__0___boxed(
    mut v_self_5676_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5677_: *mut LeanObject = core::ptr::null_mut();
    v_res_5677_ = l_Std_Async_instMonadAsyncStateTOfMonadOfFunctor___redArg___lam__0(v_self_5676_);
    lean_dec_ref(v_self_5676_);
    return v_res_5677_;
}
pub unsafe fn l_Std_Async_instMonadAsyncStateTOfMonadOfFunctor___redArg___lam__1(
    mut v_inst_5678_: *mut LeanObject,
    mut v___f_5679_: *mut LeanObject,
    mut v_s_5680_: *mut LeanObject,
    mut v_toPure_5681_: *mut LeanObject,
    mut v_t_5682_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5685_: *mut LeanObject = core::ptr::null_mut();
    v___x_5683_ = l_Functor_mapRev___redArg(v_inst_5678_, v_t_5682_, v___f_5679_);
    v___x_5684_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_5684_, 0, v___x_5683_);
    lean_ctor_set(v___x_5684_, 1, v_s_5680_);
    v___x_5685_ = lean_apply_2(v_toPure_5681_, lean_box(0), v___x_5684_);
    return v___x_5685_;
}
pub unsafe fn l_Std_Async_instMonadAsyncStateTOfMonadOfFunctor___redArg___lam__2(
    mut v_inst_5686_: *mut LeanObject,
    mut v___f_5687_: *mut LeanObject,
    mut v_toPure_5688_: *mut LeanObject,
    mut v_inst_5689_: *mut LeanObject,
    mut v_toBind_5690_: *mut LeanObject,
    mut v_00_u03b1_5691_: *mut LeanObject,
    mut v_p_5692_: *mut LeanObject,
    mut v_prio_5693_: *mut LeanObject,
    mut v_s_5694_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5698_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_s_5694_);
    v___f_5695_ = lean_alloc_closure(
        l_Std_Async_instMonadAsyncStateTOfMonadOfFunctor___redArg___lam__1
            as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_5695_, 0, v_inst_5686_);
    lean_closure_set(v___f_5695_, 1, v___f_5687_);
    lean_closure_set(v___f_5695_, 2, v_s_5694_);
    lean_closure_set(v___f_5695_, 3, v_toPure_5688_);
    v___x_5696_ = lean_apply_1(v_p_5692_, v_s_5694_);
    v___x_5697_ = lean_apply_3(v_inst_5689_, lean_box(0), v___x_5696_, v_prio_5693_);
    v___x_5698_ = lean_apply_4(
        v_toBind_5690_,
        lean_box(0),
        lean_box(0),
        v___x_5697_,
        v___f_5695_,
    );
    return v___x_5698_;
}
pub unsafe fn l_Std_Async_instMonadAsyncStateTOfMonadOfFunctor___redArg(
    mut v_inst_5700_: *mut LeanObject,
    mut v_inst_5701_: *mut LeanObject,
    mut v_inst_5702_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_5703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_5704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_5705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5707_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_5703_ = lean_ctor_get(v_inst_5700_, 0);
    lean_inc_ref(v_toApplicative_5703_);
    v_toBind_5704_ = lean_ctor_get(v_inst_5700_, 1);
    lean_inc(v_toBind_5704_);
    lean_dec_ref(v_inst_5700_);
    v_toPure_5705_ = lean_ctor_get(v_toApplicative_5703_, 1);
    lean_inc(v_toPure_5705_);
    lean_dec_ref(v_toApplicative_5703_);
    v___f_5706_ = l_Std_Async_instMonadAsyncStateTOfMonadOfFunctor___redArg___closed__0;
    v___f_5707_ = lean_alloc_closure(
        l_Std_Async_instMonadAsyncStateTOfMonadOfFunctor___redArg___lam__2
            as *mut core::ffi::c_void,
        9,
        5,
    );
    lean_closure_set(v___f_5707_, 0, v_inst_5701_);
    lean_closure_set(v___f_5707_, 1, v___f_5706_);
    lean_closure_set(v___f_5707_, 2, v_toPure_5705_);
    lean_closure_set(v___f_5707_, 3, v_inst_5702_);
    lean_closure_set(v___f_5707_, 4, v_toBind_5704_);
    return v___f_5707_;
}
pub unsafe fn l_Std_Async_instMonadAsyncStateTOfMonadOfFunctor(
    mut v_m_5708_: *mut LeanObject,
    mut v_t_5709_: *mut LeanObject,
    mut v_s_5710_: *mut LeanObject,
    mut v_inst_5711_: *mut LeanObject,
    mut v_inst_5712_: *mut LeanObject,
    mut v_inst_5713_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5714_: *mut LeanObject = core::ptr::null_mut();
    v___x_5714_ = l_Std_Async_instMonadAsyncStateTOfMonadOfFunctor___redArg(
        v_inst_5711_,
        v_inst_5712_,
        v_inst_5713_,
    );
    return v___x_5714_;
}
pub unsafe fn l_Std_Async_ETask_pure___redArg(mut v_x_5715_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_5716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5717_: *mut LeanObject = core::ptr::null_mut();
    v___x_5716_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_5716_, 0, v_x_5715_);
    v___x_5717_ = lean_task_pure(v___x_5716_);
    return v___x_5717_;
}
pub unsafe fn l_Std_Async_ETask_pure(
    mut v_00_u03b1_5718_: *mut LeanObject,
    mut v_00_u03b5_5719_: *mut LeanObject,
    mut v_x_5720_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5722_: *mut LeanObject = core::ptr::null_mut();
    v___x_5721_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_5721_, 0, v_x_5720_);
    v___x_5722_ = lean_task_pure(v___x_5721_);
    return v___x_5722_;
}
pub unsafe fn l_Std_Async_ETask_map___redArg___lam__0(
    mut v_f_5723_: *mut LeanObject,
    mut v_x_5724_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_5725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5728_: u8 = 0;
    let mut v___x_5730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5732_: u8 = 0;
    let mut v_a_5733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5736_: u8 = 0;
    let mut v___x_5737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5741_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5724_) == 0 {
                    lean_dec(v_f_5723_);
                    v_a_5725_ = lean_ctor_get(v_x_5724_, 0);
                    v_isSharedCheck_5732_ = (!lean_is_exclusive(v_x_5724_)) as u8;
                    if v_isSharedCheck_5732_ == 0 {
                        v___x_5727_ = v_x_5724_;
                        v_isShared_5728_ = v_isSharedCheck_5732_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5725_);
                        lean_dec(v_x_5724_);
                        v___x_5727_ = lean_box(0);
                        v_isShared_5728_ = v_isSharedCheck_5732_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5733_ = lean_ctor_get(v_x_5724_, 0);
                    v_isSharedCheck_5741_ = (!lean_is_exclusive(v_x_5724_)) as u8;
                    if v_isSharedCheck_5741_ == 0 {
                        v___x_5735_ = v_x_5724_;
                        v_isShared_5736_ = v_isSharedCheck_5741_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5733_);
                        lean_dec(v_x_5724_);
                        v___x_5735_ = lean_box(0);
                        v_isShared_5736_ = v_isSharedCheck_5741_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5728_ == 0 {
                    v___x_5730_ = v___x_5727_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5731_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5731_, 0, v_a_5725_);
                    v___x_5730_ = v_reuseFailAlloc_5731_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5730_;
            }
            3 => {
                v___x_5737_ = lean_apply_1(v_f_5723_, v_a_5733_);
                if v_isShared_5736_ == 0 {
                    lean_ctor_set(v___x_5735_, 0, v___x_5737_);
                    v___x_5739_ = v___x_5735_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5740_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5740_, 0, v___x_5737_);
                    v___x_5739_ = v_reuseFailAlloc_5740_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5739_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ETask_map___redArg(
    mut v_f_5742_: *mut LeanObject,
    mut v_x_5743_: *mut LeanObject,
    mut v_prio_5744_: *mut LeanObject,
    mut v_sync_5745_: u8,
) -> *mut LeanObject {
    let mut v___f_5746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5747_: *mut LeanObject = core::ptr::null_mut();
    v___f_5746_ = lean_alloc_closure(
        l_Std_Async_ETask_map___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_5746_, 0, v_f_5742_);
    v___x_5747_ = lean_task_map(v___f_5746_, v_x_5743_, v_prio_5744_, v_sync_5745_);
    return v___x_5747_;
}
pub unsafe fn l_Std_Async_ETask_map___redArg___boxed(
    mut v_f_5748_: *mut LeanObject,
    mut v_x_5749_: *mut LeanObject,
    mut v_prio_5750_: *mut LeanObject,
    mut v_sync_5751_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sync_boxed_5752_: u8 = 0;
    let mut v_res_5753_: *mut LeanObject = core::ptr::null_mut();
    v_sync_boxed_5752_ = (lean_unbox(v_sync_5751_) as u8);
    v_res_5753_ =
        l_Std_Async_ETask_map___redArg(v_f_5748_, v_x_5749_, v_prio_5750_, v_sync_boxed_5752_);
    return v_res_5753_;
}
pub unsafe fn l_Std_Async_ETask_map(
    mut v_00_u03b1_5754_: *mut LeanObject,
    mut v_00_u03b2_5755_: *mut LeanObject,
    mut v_00_u03b5_5756_: *mut LeanObject,
    mut v_f_5757_: *mut LeanObject,
    mut v_x_5758_: *mut LeanObject,
    mut v_prio_5759_: *mut LeanObject,
    mut v_sync_5760_: u8,
) -> *mut LeanObject {
    let mut v___f_5761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5762_: *mut LeanObject = core::ptr::null_mut();
    v___f_5761_ = lean_alloc_closure(
        l_Std_Async_ETask_map___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_5761_, 0, v_f_5757_);
    v___x_5762_ = lean_task_map(v___f_5761_, v_x_5758_, v_prio_5759_, v_sync_5760_);
    return v___x_5762_;
}
pub unsafe fn l_Std_Async_ETask_map___boxed(
    mut v_00_u03b1_5763_: *mut LeanObject,
    mut v_00_u03b2_5764_: *mut LeanObject,
    mut v_00_u03b5_5765_: *mut LeanObject,
    mut v_f_5766_: *mut LeanObject,
    mut v_x_5767_: *mut LeanObject,
    mut v_prio_5768_: *mut LeanObject,
    mut v_sync_5769_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sync_boxed_5770_: u8 = 0;
    let mut v_res_5771_: *mut LeanObject = core::ptr::null_mut();
    v_sync_boxed_5770_ = (lean_unbox(v_sync_5769_) as u8);
    v_res_5771_ = l_Std_Async_ETask_map(
        v_00_u03b1_5763_,
        v_00_u03b2_5764_,
        v_00_u03b5_5765_,
        v_f_5766_,
        v_x_5767_,
        v_prio_5768_,
        v_sync_boxed_5770_,
    );
    return v_res_5771_;
}
pub unsafe fn l_Std_Async_ETask_bind___redArg___lam__0(
    mut v_f_5772_: *mut LeanObject,
    mut v_x_5773_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_5774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5777_: u8 = 0;
    let mut v___x_5779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5782_: u8 = 0;
    let mut v_a_5783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5784_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5773_) == 0 {
                    lean_dec_ref(v_f_5772_);
                    v_a_5774_ = lean_ctor_get(v_x_5773_, 0);
                    v_isSharedCheck_5782_ = (!lean_is_exclusive(v_x_5773_)) as u8;
                    if v_isSharedCheck_5782_ == 0 {
                        v___x_5776_ = v_x_5773_;
                        v_isShared_5777_ = v_isSharedCheck_5782_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5774_);
                        lean_dec(v_x_5773_);
                        v___x_5776_ = lean_box(0);
                        v_isShared_5777_ = v_isSharedCheck_5782_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5783_ = lean_ctor_get(v_x_5773_, 0);
                    lean_inc(v_a_5783_);
                    lean_dec_ref_known(v_x_5773_, 1);
                    v___x_5784_ = lean_apply_1(v_f_5772_, v_a_5783_);
                    return v___x_5784_;
                }
            }
            1 => {
                if v_isShared_5777_ == 0 {
                    v___x_5779_ = v___x_5776_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5781_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5781_, 0, v_a_5774_);
                    v___x_5779_ = v_reuseFailAlloc_5781_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5780_ = lean_task_pure(v___x_5779_);
                return v___x_5780_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ETask_bind___redArg(
    mut v_x_5785_: *mut LeanObject,
    mut v_f_5786_: *mut LeanObject,
    mut v_prio_5787_: *mut LeanObject,
    mut v_sync_5788_: u8,
) -> *mut LeanObject {
    let mut v___f_5789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5790_: *mut LeanObject = core::ptr::null_mut();
    v___f_5789_ = lean_alloc_closure(
        l_Std_Async_ETask_bind___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_5789_, 0, v_f_5786_);
    v___x_5790_ = lean_task_bind(v_x_5785_, v___f_5789_, v_prio_5787_, v_sync_5788_);
    return v___x_5790_;
}
pub unsafe fn l_Std_Async_ETask_bind___redArg___boxed(
    mut v_x_5791_: *mut LeanObject,
    mut v_f_5792_: *mut LeanObject,
    mut v_prio_5793_: *mut LeanObject,
    mut v_sync_5794_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sync_boxed_5795_: u8 = 0;
    let mut v_res_5796_: *mut LeanObject = core::ptr::null_mut();
    v_sync_boxed_5795_ = (lean_unbox(v_sync_5794_) as u8);
    v_res_5796_ =
        l_Std_Async_ETask_bind___redArg(v_x_5791_, v_f_5792_, v_prio_5793_, v_sync_boxed_5795_);
    return v_res_5796_;
}
pub unsafe fn l_Std_Async_ETask_bind(
    mut v_00_u03b5_5797_: *mut LeanObject,
    mut v_00_u03b1_5798_: *mut LeanObject,
    mut v_00_u03b2_5799_: *mut LeanObject,
    mut v_x_5800_: *mut LeanObject,
    mut v_f_5801_: *mut LeanObject,
    mut v_prio_5802_: *mut LeanObject,
    mut v_sync_5803_: u8,
) -> *mut LeanObject {
    let mut v___f_5804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5805_: *mut LeanObject = core::ptr::null_mut();
    v___f_5804_ = lean_alloc_closure(
        l_Std_Async_ETask_bind___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_5804_, 0, v_f_5801_);
    v___x_5805_ = lean_task_bind(v_x_5800_, v___f_5804_, v_prio_5802_, v_sync_5803_);
    return v___x_5805_;
}
pub unsafe fn l_Std_Async_ETask_bind___boxed(
    mut v_00_u03b5_5806_: *mut LeanObject,
    mut v_00_u03b1_5807_: *mut LeanObject,
    mut v_00_u03b2_5808_: *mut LeanObject,
    mut v_x_5809_: *mut LeanObject,
    mut v_f_5810_: *mut LeanObject,
    mut v_prio_5811_: *mut LeanObject,
    mut v_sync_5812_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sync_boxed_5813_: u8 = 0;
    let mut v_res_5814_: *mut LeanObject = core::ptr::null_mut();
    v_sync_boxed_5813_ = (lean_unbox(v_sync_5812_) as u8);
    v_res_5814_ = l_Std_Async_ETask_bind(
        v_00_u03b5_5806_,
        v_00_u03b1_5807_,
        v_00_u03b2_5808_,
        v_x_5809_,
        v_f_5810_,
        v_prio_5811_,
        v_sync_boxed_5813_,
    );
    return v_res_5814_;
}
pub unsafe fn l_Std_Async_ETask_bindEIO___redArg___lam__0(
    mut v_f_5815_: *mut LeanObject,
    mut v_a_5816_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_5819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5826_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_5816_) == 0 {
                    lean_dec_ref(v_f_5815_);
                    v_a_5822_ = lean_ctor_get(v_a_5816_, 0);
                    lean_inc(v_a_5822_);
                    lean_dec_ref_known(v_a_5816_, 1);
                    v_a_5819_ = v_a_5822_;
                    state = 1;
                    continue;
                } else {
                    v_a_5823_ = lean_ctor_get(v_a_5816_, 0);
                    lean_inc(v_a_5823_);
                    lean_dec_ref_known(v_a_5816_, 1);
                    v___x_5824_ = lean_apply_2(v_f_5815_, v_a_5823_, lean_box(0));
                    if lean_obj_tag(v___x_5824_) == 0 {
                        v_a_5825_ = lean_ctor_get(v___x_5824_, 0);
                        lean_inc(v_a_5825_);
                        lean_dec_ref_known(v___x_5824_, 1);
                        return v_a_5825_;
                    } else {
                        v_a_5826_ = lean_ctor_get(v___x_5824_, 0);
                        lean_inc(v_a_5826_);
                        lean_dec_ref_known(v___x_5824_, 1);
                        v_a_5819_ = v_a_5826_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5820_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5820_, 0, v_a_5819_);
                v___x_5821_ = lean_task_pure(v___x_5820_);
                return v___x_5821_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ETask_bindEIO___redArg___lam__0___boxed(
    mut v_f_5827_: *mut LeanObject,
    mut v_a_5828_: *mut LeanObject,
    mut v___y_5829_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5830_: *mut LeanObject = core::ptr::null_mut();
    v_res_5830_ = l_Std_Async_ETask_bindEIO___redArg___lam__0(v_f_5827_, v_a_5828_);
    return v_res_5830_;
}
pub unsafe fn l_Std_Async_ETask_bindEIO___redArg(
    mut v_x_5831_: *mut LeanObject,
    mut v_f_5832_: *mut LeanObject,
    mut v_prio_5833_: *mut LeanObject,
    mut v_sync_5834_: u8,
) -> *mut LeanObject {
    let mut v___f_5836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5838_: *mut LeanObject = core::ptr::null_mut();
    v___f_5836_ = lean_alloc_closure(
        l_Std_Async_ETask_bindEIO___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_5836_, 0, v_f_5832_);
    v___x_5837_ = lean_io_bind_task(v_x_5831_, v___f_5836_, v_prio_5833_, v_sync_5834_);
    v___x_5838_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5838_, 0, v___x_5837_);
    return v___x_5838_;
}
pub unsafe fn l_Std_Async_ETask_bindEIO___redArg___boxed(
    mut v_x_5839_: *mut LeanObject,
    mut v_f_5840_: *mut LeanObject,
    mut v_prio_5841_: *mut LeanObject,
    mut v_sync_5842_: *mut LeanObject,
    mut v_a_5843_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sync_boxed_5844_: u8 = 0;
    let mut v_res_5845_: *mut LeanObject = core::ptr::null_mut();
    v_sync_boxed_5844_ = (lean_unbox(v_sync_5842_) as u8);
    v_res_5845_ =
        l_Std_Async_ETask_bindEIO___redArg(v_x_5839_, v_f_5840_, v_prio_5841_, v_sync_boxed_5844_);
    return v_res_5845_;
}
pub unsafe fn l_Std_Async_ETask_bindEIO(
    mut v_00_u03b5_5846_: *mut LeanObject,
    mut v_00_u03b1_5847_: *mut LeanObject,
    mut v_00_u03b2_5848_: *mut LeanObject,
    mut v_x_5849_: *mut LeanObject,
    mut v_f_5850_: *mut LeanObject,
    mut v_prio_5851_: *mut LeanObject,
    mut v_sync_5852_: u8,
) -> *mut LeanObject {
    let mut v___f_5854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5856_: *mut LeanObject = core::ptr::null_mut();
    v___f_5854_ = lean_alloc_closure(
        l_Std_Async_ETask_bindEIO___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_5854_, 0, v_f_5850_);
    v___x_5855_ = lean_io_bind_task(v_x_5849_, v___f_5854_, v_prio_5851_, v_sync_5852_);
    v___x_5856_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5856_, 0, v___x_5855_);
    return v___x_5856_;
}
pub unsafe fn l_Std_Async_ETask_bindEIO___boxed(
    mut v_00_u03b5_5857_: *mut LeanObject,
    mut v_00_u03b1_5858_: *mut LeanObject,
    mut v_00_u03b2_5859_: *mut LeanObject,
    mut v_x_5860_: *mut LeanObject,
    mut v_f_5861_: *mut LeanObject,
    mut v_prio_5862_: *mut LeanObject,
    mut v_sync_5863_: *mut LeanObject,
    mut v_a_5864_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sync_boxed_5865_: u8 = 0;
    let mut v_res_5866_: *mut LeanObject = core::ptr::null_mut();
    v_sync_boxed_5865_ = (lean_unbox(v_sync_5863_) as u8);
    v_res_5866_ = l_Std_Async_ETask_bindEIO(
        v_00_u03b5_5857_,
        v_00_u03b1_5858_,
        v_00_u03b2_5859_,
        v_x_5860_,
        v_f_5861_,
        v_prio_5862_,
        v_sync_boxed_5865_,
    );
    return v_res_5866_;
}
pub unsafe fn l_Std_Async_ETask_mapEIO___redArg___lam__0(
    mut v_f_5867_: *mut LeanObject,
    mut v_a_5868_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_5871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5877_: u8 = 0;
    let mut v___x_5878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5884_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_5868_) == 0 {
                    lean_dec_ref(v_f_5867_);
                    v_a_5873_ = lean_ctor_get(v_a_5868_, 0);
                    lean_inc(v_a_5873_);
                    lean_dec_ref_known(v_a_5868_, 1);
                    v_a_5871_ = v_a_5873_;
                    state = 1;
                    continue;
                } else {
                    v_a_5874_ = lean_ctor_get(v_a_5868_, 0);
                    v_isSharedCheck_5884_ = (!lean_is_exclusive(v_a_5868_)) as u8;
                    if v_isSharedCheck_5884_ == 0 {
                        v___x_5876_ = v_a_5868_;
                        v_isShared_5877_ = v_isSharedCheck_5884_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_5874_);
                        lean_dec(v_a_5868_);
                        v___x_5876_ = lean_box(0);
                        v_isShared_5877_ = v_isSharedCheck_5884_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5872_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5872_, 0, v_a_5871_);
                return v___x_5872_;
            }
            2 => {
                v___x_5878_ = lean_apply_2(v_f_5867_, v_a_5874_, lean_box(0));
                if lean_obj_tag(v___x_5878_) == 0 {
                    v_a_5879_ = lean_ctor_get(v___x_5878_, 0);
                    lean_inc(v_a_5879_);
                    lean_dec_ref_known(v___x_5878_, 1);
                    if v_isShared_5877_ == 0 {
                        lean_ctor_set(v___x_5876_, 0, v_a_5879_);
                        v___x_5881_ = v___x_5876_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5882_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5882_, 0, v_a_5879_);
                        v___x_5881_ = v_reuseFailAlloc_5882_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5876_);
                    v_a_5883_ = lean_ctor_get(v___x_5878_, 0);
                    lean_inc(v_a_5883_);
                    lean_dec_ref_known(v___x_5878_, 1);
                    v_a_5871_ = v_a_5883_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                return v___x_5881_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ETask_mapEIO___redArg___lam__0___boxed(
    mut v_f_5885_: *mut LeanObject,
    mut v_a_5886_: *mut LeanObject,
    mut v___y_5887_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5888_: *mut LeanObject = core::ptr::null_mut();
    v_res_5888_ = l_Std_Async_ETask_mapEIO___redArg___lam__0(v_f_5885_, v_a_5886_);
    return v_res_5888_;
}
pub unsafe fn l_Std_Async_ETask_mapEIO___redArg(
    mut v_f_5889_: *mut LeanObject,
    mut v_x_5890_: *mut LeanObject,
    mut v_prio_5891_: *mut LeanObject,
    mut v_sync_5892_: u8,
) -> *mut LeanObject {
    let mut v___f_5894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5895_: *mut LeanObject = core::ptr::null_mut();
    v___f_5894_ = lean_alloc_closure(
        l_Std_Async_ETask_mapEIO___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_5894_, 0, v_f_5889_);
    v___x_5895_ = lean_io_map_task(v___f_5894_, v_x_5890_, v_prio_5891_, v_sync_5892_);
    return v___x_5895_;
}
pub unsafe fn l_Std_Async_ETask_mapEIO___redArg___boxed(
    mut v_f_5896_: *mut LeanObject,
    mut v_x_5897_: *mut LeanObject,
    mut v_prio_5898_: *mut LeanObject,
    mut v_sync_5899_: *mut LeanObject,
    mut v_a_5900_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sync_boxed_5901_: u8 = 0;
    let mut v_res_5902_: *mut LeanObject = core::ptr::null_mut();
    v_sync_boxed_5901_ = (lean_unbox(v_sync_5899_) as u8);
    v_res_5902_ =
        l_Std_Async_ETask_mapEIO___redArg(v_f_5896_, v_x_5897_, v_prio_5898_, v_sync_boxed_5901_);
    return v_res_5902_;
}
pub unsafe fn l_Std_Async_ETask_mapEIO(
    mut v_00_u03b1_5903_: *mut LeanObject,
    mut v_00_u03b5_5904_: *mut LeanObject,
    mut v_00_u03b2_5905_: *mut LeanObject,
    mut v_f_5906_: *mut LeanObject,
    mut v_x_5907_: *mut LeanObject,
    mut v_prio_5908_: *mut LeanObject,
    mut v_sync_5909_: u8,
) -> *mut LeanObject {
    let mut v___f_5911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5912_: *mut LeanObject = core::ptr::null_mut();
    v___f_5911_ = lean_alloc_closure(
        l_Std_Async_ETask_mapEIO___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_5911_, 0, v_f_5906_);
    v___x_5912_ = lean_io_map_task(v___f_5911_, v_x_5907_, v_prio_5908_, v_sync_5909_);
    return v___x_5912_;
}
pub unsafe fn l_Std_Async_ETask_mapEIO___boxed(
    mut v_00_u03b1_5913_: *mut LeanObject,
    mut v_00_u03b5_5914_: *mut LeanObject,
    mut v_00_u03b2_5915_: *mut LeanObject,
    mut v_f_5916_: *mut LeanObject,
    mut v_x_5917_: *mut LeanObject,
    mut v_prio_5918_: *mut LeanObject,
    mut v_sync_5919_: *mut LeanObject,
    mut v_a_5920_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sync_boxed_5921_: u8 = 0;
    let mut v_res_5922_: *mut LeanObject = core::ptr::null_mut();
    v_sync_boxed_5921_ = (lean_unbox(v_sync_5919_) as u8);
    v_res_5922_ = l_Std_Async_ETask_mapEIO(
        v_00_u03b1_5913_,
        v_00_u03b5_5914_,
        v_00_u03b2_5915_,
        v_f_5916_,
        v_x_5917_,
        v_prio_5918_,
        v_sync_boxed_5921_,
    );
    return v_res_5922_;
}
pub unsafe fn l_Std_Async_ETask_block___redArg(mut v_x_5923_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_5925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5929_: u8 = 0;
    let mut v___x_5931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5933_: u8 = 0;
    let mut v_a_5934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5937_: u8 = 0;
    let mut v___x_5939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5941_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5925_ = lean_task_get_own(v_x_5923_);
                if lean_obj_tag(v___x_5925_) == 0 {
                    v_a_5926_ = lean_ctor_get(v___x_5925_, 0);
                    v_isSharedCheck_5933_ = (!lean_is_exclusive(v___x_5925_)) as u8;
                    if v_isSharedCheck_5933_ == 0 {
                        v___x_5928_ = v___x_5925_;
                        v_isShared_5929_ = v_isSharedCheck_5933_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5926_);
                        lean_dec(v___x_5925_);
                        v___x_5928_ = lean_box(0);
                        v_isShared_5929_ = v_isSharedCheck_5933_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5934_ = lean_ctor_get(v___x_5925_, 0);
                    v_isSharedCheck_5941_ = (!lean_is_exclusive(v___x_5925_)) as u8;
                    if v_isSharedCheck_5941_ == 0 {
                        v___x_5936_ = v___x_5925_;
                        v_isShared_5937_ = v_isSharedCheck_5941_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5934_);
                        lean_dec(v___x_5925_);
                        v___x_5936_ = lean_box(0);
                        v_isShared_5937_ = v_isSharedCheck_5941_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5929_ == 0 {
                    lean_ctor_set_tag(v___x_5928_, 1);
                    v___x_5931_ = v___x_5928_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5932_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5932_, 0, v_a_5926_);
                    v___x_5931_ = v_reuseFailAlloc_5932_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5931_;
            }
            3 => {
                if v_isShared_5937_ == 0 {
                    lean_ctor_set_tag(v___x_5936_, 0);
                    v___x_5939_ = v___x_5936_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5940_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5940_, 0, v_a_5934_);
                    v___x_5939_ = v_reuseFailAlloc_5940_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5939_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ETask_block___redArg___boxed(
    mut v_x_5942_: *mut LeanObject,
    mut v_a_5943_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5944_: *mut LeanObject = core::ptr::null_mut();
    v_res_5944_ = l_Std_Async_ETask_block___redArg(v_x_5942_);
    return v_res_5944_;
}
pub unsafe fn l_Std_Async_ETask_block(
    mut v_00_u03b5_5945_: *mut LeanObject,
    mut v_00_u03b1_5946_: *mut LeanObject,
    mut v_x_5947_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5953_: u8 = 0;
    let mut v___x_5955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5957_: u8 = 0;
    let mut v_a_5958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5961_: u8 = 0;
    let mut v___x_5963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5965_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5949_ = lean_task_get_own(v_x_5947_);
                if lean_obj_tag(v___x_5949_) == 0 {
                    v_a_5950_ = lean_ctor_get(v___x_5949_, 0);
                    v_isSharedCheck_5957_ = (!lean_is_exclusive(v___x_5949_)) as u8;
                    if v_isSharedCheck_5957_ == 0 {
                        v___x_5952_ = v___x_5949_;
                        v_isShared_5953_ = v_isSharedCheck_5957_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5950_);
                        lean_dec(v___x_5949_);
                        v___x_5952_ = lean_box(0);
                        v_isShared_5953_ = v_isSharedCheck_5957_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5958_ = lean_ctor_get(v___x_5949_, 0);
                    v_isSharedCheck_5965_ = (!lean_is_exclusive(v___x_5949_)) as u8;
                    if v_isSharedCheck_5965_ == 0 {
                        v___x_5960_ = v___x_5949_;
                        v_isShared_5961_ = v_isSharedCheck_5965_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5958_);
                        lean_dec(v___x_5949_);
                        v___x_5960_ = lean_box(0);
                        v_isShared_5961_ = v_isSharedCheck_5965_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5953_ == 0 {
                    lean_ctor_set_tag(v___x_5952_, 1);
                    v___x_5955_ = v___x_5952_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5956_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5956_, 0, v_a_5950_);
                    v___x_5955_ = v_reuseFailAlloc_5956_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5955_;
            }
            3 => {
                if v_isShared_5961_ == 0 {
                    lean_ctor_set_tag(v___x_5960_, 0);
                    v___x_5963_ = v___x_5960_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5964_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5964_, 0, v_a_5958_);
                    v___x_5963_ = v_reuseFailAlloc_5964_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5963_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ETask_block___boxed(
    mut v_00_u03b5_5966_: *mut LeanObject,
    mut v_00_u03b1_5967_: *mut LeanObject,
    mut v_x_5968_: *mut LeanObject,
    mut v_a_5969_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5970_: *mut LeanObject = core::ptr::null_mut();
    v_res_5970_ = l_Std_Async_ETask_block(v_00_u03b5_5966_, v_00_u03b1_5967_, v_x_5968_);
    return v_res_5970_;
}
pub unsafe fn l_Std_Async_ETask_ofPromise_x21___redArg(
    mut v_x_5971_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5972_: *mut LeanObject = core::ptr::null_mut();
    v___x_5972_ = l_IO_Promise_result_x21___redArg(v_x_5971_);
    return v___x_5972_;
}
pub unsafe fn l_Std_Async_ETask_ofPromise_x21___redArg___boxed(
    mut v_x_5973_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5974_: *mut LeanObject = core::ptr::null_mut();
    v_res_5974_ = l_Std_Async_ETask_ofPromise_x21___redArg(v_x_5973_);
    lean_dec(v_x_5973_);
    return v_res_5974_;
}
pub unsafe fn l_Std_Async_ETask_ofPromise_x21(
    mut v_00_u03b5_5975_: *mut LeanObject,
    mut v_00_u03b1_5976_: *mut LeanObject,
    mut v_x_5977_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5978_: *mut LeanObject = core::ptr::null_mut();
    v___x_5978_ = l_IO_Promise_result_x21___redArg(v_x_5977_);
    return v___x_5978_;
}
pub unsafe fn l_Std_Async_ETask_ofPromise_x21___boxed(
    mut v_00_u03b5_5979_: *mut LeanObject,
    mut v_00_u03b1_5980_: *mut LeanObject,
    mut v_x_5981_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5982_: *mut LeanObject = core::ptr::null_mut();
    v_res_5982_ = l_Std_Async_ETask_ofPromise_x21(v_00_u03b5_5979_, v_00_u03b1_5980_, v_x_5981_);
    lean_dec(v_x_5981_);
    return v_res_5982_;
}
pub unsafe fn l_Std_Async_ETask_ofPurePromise___redArg(
    mut v_x_5984_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5988_: u8 = 0;
    let mut v___x_5989_: *mut LeanObject = core::ptr::null_mut();
    v___x_5985_ = l_Std_Async_ETask_ofPurePromise___redArg___closed__0;
    v___x_5986_ = l_IO_Promise_result_x21___redArg(v_x_5984_);
    v___x_5987_ = lean_unsigned_to_nat(0);
    v___x_5988_ = 1;
    v___x_5989_ = lean_task_map(v___x_5985_, v___x_5986_, v___x_5987_, v___x_5988_);
    return v___x_5989_;
}
pub unsafe fn l_Std_Async_ETask_ofPurePromise___redArg___boxed(
    mut v_x_5990_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5991_: *mut LeanObject = core::ptr::null_mut();
    v_res_5991_ = l_Std_Async_ETask_ofPurePromise___redArg(v_x_5990_);
    lean_dec(v_x_5990_);
    return v_res_5991_;
}
pub unsafe fn l_Std_Async_ETask_ofPurePromise(
    mut v_00_u03b1_5992_: *mut LeanObject,
    mut v_00_u03b5_5993_: *mut LeanObject,
    mut v_x_5994_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5998_: u8 = 0;
    let mut v___x_5999_: *mut LeanObject = core::ptr::null_mut();
    v___x_5995_ = l_Std_Async_ETask_ofPurePromise___redArg___closed__0;
    v___x_5996_ = l_IO_Promise_result_x21___redArg(v_x_5994_);
    v___x_5997_ = lean_unsigned_to_nat(0);
    v___x_5998_ = 1;
    v___x_5999_ = lean_task_map(v___x_5995_, v___x_5996_, v___x_5997_, v___x_5998_);
    return v___x_5999_;
}
pub unsafe fn l_Std_Async_ETask_ofPurePromise___boxed(
    mut v_00_u03b1_6000_: *mut LeanObject,
    mut v_00_u03b5_6001_: *mut LeanObject,
    mut v_x_6002_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6003_: *mut LeanObject = core::ptr::null_mut();
    v_res_6003_ = l_Std_Async_ETask_ofPurePromise(v_00_u03b1_6000_, v_00_u03b5_6001_, v_x_6002_);
    lean_dec(v_x_6002_);
    return v_res_6003_;
}
pub unsafe fn l_Std_Async_ETask_getState___redArg(mut v_x_6004_: *mut LeanObject) -> u8 {
    let mut v___x_6006_: u8 = 0;
    v___x_6006_ = lean_io_get_task_state(v_x_6004_);
    return v___x_6006_;
}
pub unsafe fn l_Std_Async_ETask_getState___redArg___boxed(
    mut v_x_6007_: *mut LeanObject,
    mut v_a_6008_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6009_: u8 = 0;
    let mut v_r_6010_: *mut LeanObject = core::ptr::null_mut();
    v_res_6009_ = l_Std_Async_ETask_getState___redArg(v_x_6007_);
    lean_dec_ref(v_x_6007_);
    v_r_6010_ = lean_box((v_res_6009_) as usize);
    return v_r_6010_;
}
pub unsafe fn l_Std_Async_ETask_getState(
    mut v_00_u03b5_6011_: *mut LeanObject,
    mut v_00_u03b1_6012_: *mut LeanObject,
    mut v_x_6013_: *mut LeanObject,
) -> u8 {
    let mut v___x_6015_: u8 = 0;
    v___x_6015_ = lean_io_get_task_state(v_x_6013_);
    return v___x_6015_;
}
pub unsafe fn l_Std_Async_ETask_getState___boxed(
    mut v_00_u03b5_6016_: *mut LeanObject,
    mut v_00_u03b1_6017_: *mut LeanObject,
    mut v_x_6018_: *mut LeanObject,
    mut v_a_6019_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6020_: u8 = 0;
    let mut v_r_6021_: *mut LeanObject = core::ptr::null_mut();
    v_res_6020_ = l_Std_Async_ETask_getState(v_00_u03b5_6016_, v_00_u03b1_6017_, v_x_6018_);
    lean_dec_ref(v_x_6018_);
    v_r_6021_ = lean_box((v_res_6020_) as usize);
    return v_r_6021_;
}
pub unsafe fn l_Std_Async_ETask_instFunctor___lam__1(
    mut v_00_u03b1_6022_: *mut LeanObject,
    mut v_00_u03b2_6023_: *mut LeanObject,
    mut v_f_6024_: *mut LeanObject,
    mut v_x_6025_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_6026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6028_: u8 = 0;
    let mut v___x_6029_: *mut LeanObject = core::ptr::null_mut();
    v___f_6026_ = lean_alloc_closure(
        l_Std_Async_ETask_map___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_6026_, 0, v_f_6024_);
    v___x_6027_ = lean_unsigned_to_nat(0);
    v___x_6028_ = 0;
    v___x_6029_ = lean_task_map(v___f_6026_, v_x_6025_, v___x_6027_, v___x_6028_);
    return v___x_6029_;
}
pub unsafe fn l_Std_Async_ETask_instFunctor___lam__0(
    mut v___f_6030_: *mut LeanObject,
    mut v_00_u03b1_6031_: *mut LeanObject,
    mut v_00_u03b2_6032_: *mut LeanObject,
    mut v___y_6033_: *mut LeanObject,
    mut v___y_6034_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6036_: *mut LeanObject = core::ptr::null_mut();
    v___x_6035_ = lean_alloc_closure(l_Function_const___boxed as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___x_6035_, 0, lean_box(0));
    lean_closure_set(v___x_6035_, 1, lean_box(0));
    lean_closure_set(v___x_6035_, 2, v___y_6033_);
    v___x_6036_ = lean_apply_4(
        v___f_6030_,
        lean_box(0),
        lean_box(0),
        v___x_6035_,
        v___y_6034_,
    );
    return v___x_6036_;
}
pub unsafe fn l_Std_Async_ETask_instFunctor(
    mut v_00_u03b5_6043_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6044_: *mut LeanObject = core::ptr::null_mut();
    v___x_6044_ = l_Std_Async_ETask_instFunctor___closed__2;
    return v___x_6044_;
}
pub unsafe fn l_Std_Async_ETask_instMonad___lam__0(
    mut v_00_u03b1_6045_: *mut LeanObject,
    mut v___y_6046_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6048_: *mut LeanObject = core::ptr::null_mut();
    v___x_6047_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_6047_, 0, v___y_6046_);
    v___x_6048_ = lean_task_pure(v___x_6047_);
    return v___x_6048_;
}
pub unsafe fn l_Std_Async_ETask_instMonad___lam__1(
    mut v_a_6049_: *mut LeanObject,
    mut v_x_6050_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_6051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6054_: u8 = 0;
    let mut v___x_6056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6058_: u8 = 0;
    let mut v_a_6059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6062_: u8 = 0;
    let mut v___x_6063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6067_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6050_) == 0 {
                    lean_dec(v_a_6049_);
                    v_a_6051_ = lean_ctor_get(v_x_6050_, 0);
                    v_isSharedCheck_6058_ = (!lean_is_exclusive(v_x_6050_)) as u8;
                    if v_isSharedCheck_6058_ == 0 {
                        v___x_6053_ = v_x_6050_;
                        v_isShared_6054_ = v_isSharedCheck_6058_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6051_);
                        lean_dec(v_x_6050_);
                        v___x_6053_ = lean_box(0);
                        v_isShared_6054_ = v_isSharedCheck_6058_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6059_ = lean_ctor_get(v_x_6050_, 0);
                    v_isSharedCheck_6067_ = (!lean_is_exclusive(v_x_6050_)) as u8;
                    if v_isSharedCheck_6067_ == 0 {
                        v___x_6061_ = v_x_6050_;
                        v_isShared_6062_ = v_isSharedCheck_6067_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6059_);
                        lean_dec(v_x_6050_);
                        v___x_6061_ = lean_box(0);
                        v_isShared_6062_ = v_isSharedCheck_6067_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6054_ == 0 {
                    v___x_6056_ = v___x_6053_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6057_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6057_, 0, v_a_6051_);
                    v___x_6056_ = v_reuseFailAlloc_6057_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6056_;
            }
            3 => {
                v___x_6063_ = lean_apply_1(v_a_6049_, v_a_6059_);
                if v_isShared_6062_ == 0 {
                    lean_ctor_set(v___x_6061_, 0, v___x_6063_);
                    v___x_6065_ = v___x_6061_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6066_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6066_, 0, v___x_6063_);
                    v___x_6065_ = v_reuseFailAlloc_6066_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6065_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ETask_instMonad___lam__2(
    mut v_x_6068_: *mut LeanObject,
    mut v_x_6069_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_6070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6073_: u8 = 0;
    let mut v___x_6075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6078_: u8 = 0;
    let mut v_a_6079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6084_: u8 = 0;
    let mut v___x_6085_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6069_) == 0 {
                    lean_dec_ref(v_x_6068_);
                    v_a_6070_ = lean_ctor_get(v_x_6069_, 0);
                    v_isSharedCheck_6078_ = (!lean_is_exclusive(v_x_6069_)) as u8;
                    if v_isSharedCheck_6078_ == 0 {
                        v___x_6072_ = v_x_6069_;
                        v_isShared_6073_ = v_isSharedCheck_6078_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6070_);
                        lean_dec(v_x_6069_);
                        v___x_6072_ = lean_box(0);
                        v_isShared_6073_ = v_isSharedCheck_6078_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6079_ = lean_ctor_get(v_x_6069_, 0);
                    lean_inc(v_a_6079_);
                    lean_dec_ref_known(v_x_6069_, 1);
                    v___f_6080_ = lean_alloc_closure(
                        l_Std_Async_ETask_instMonad___lam__1 as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    lean_closure_set(v___f_6080_, 0, v_a_6079_);
                    v___x_6081_ = lean_box(0);
                    v___x_6082_ = lean_apply_1(v_x_6068_, v___x_6081_);
                    v___x_6083_ = lean_unsigned_to_nat(0);
                    v___x_6084_ = 0;
                    v___x_6085_ = lean_task_map(v___f_6080_, v___x_6082_, v___x_6083_, v___x_6084_);
                    return v___x_6085_;
                }
            }
            1 => {
                if v_isShared_6073_ == 0 {
                    v___x_6075_ = v___x_6072_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6077_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6077_, 0, v_a_6070_);
                    v___x_6075_ = v_reuseFailAlloc_6077_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6076_ = lean_task_pure(v___x_6075_);
                return v___x_6076_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ETask_instMonad___lam__3(
    mut v_00_u03b1_6086_: *mut LeanObject,
    mut v_00_u03b2_6087_: *mut LeanObject,
    mut v_f_6088_: *mut LeanObject,
    mut v_x_6089_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_6090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6092_: u8 = 0;
    let mut v___x_6093_: *mut LeanObject = core::ptr::null_mut();
    v___f_6090_ = lean_alloc_closure(
        l_Std_Async_ETask_instMonad___lam__2 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_6090_, 0, v_x_6089_);
    v___x_6091_ = lean_unsigned_to_nat(0);
    v___x_6092_ = 0;
    v___x_6093_ = lean_task_bind(v_f_6088_, v___f_6090_, v___x_6091_, v___x_6092_);
    return v___x_6093_;
}
pub unsafe fn l_Std_Async_ETask_instMonad___lam__5(
    mut v_00_u03b1_6094_: *mut LeanObject,
    mut v_00_u03b2_6095_: *mut LeanObject,
    mut v_x_6096_: *mut LeanObject,
    mut v_f_6097_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_6098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6100_: u8 = 0;
    let mut v___x_6101_: *mut LeanObject = core::ptr::null_mut();
    v___f_6098_ = lean_alloc_closure(
        l_Std_Async_ETask_bind___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_6098_, 0, v_f_6097_);
    v___x_6099_ = lean_unsigned_to_nat(0);
    v___x_6100_ = 0;
    v___x_6101_ = lean_task_bind(v_x_6096_, v___f_6098_, v___x_6099_, v___x_6100_);
    return v___x_6101_;
}
pub unsafe fn l_Std_Async_ETask_instMonad___lam__4(
    mut v___f_6102_: *mut LeanObject,
    mut v_a_6103_: *mut LeanObject,
    mut v_x_6104_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6105_: *mut LeanObject = core::ptr::null_mut();
    v___x_6105_ = lean_apply_2(v___f_6102_, lean_box(0), v_a_6103_);
    return v___x_6105_;
}
pub unsafe fn l_Std_Async_ETask_instMonad___lam__4___boxed(
    mut v___f_6106_: *mut LeanObject,
    mut v_a_6107_: *mut LeanObject,
    mut v_x_6108_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6109_: *mut LeanObject = core::ptr::null_mut();
    v_res_6109_ = l_Std_Async_ETask_instMonad___lam__4(v___f_6106_, v_a_6107_, v_x_6108_);
    lean_dec(v_x_6108_);
    return v_res_6109_;
}
pub unsafe fn l_Std_Async_ETask_instMonad___lam__6(
    mut v___f_6110_: *mut LeanObject,
    mut v_y_6111_: *mut LeanObject,
    mut v___f_6112_: *mut LeanObject,
    mut v_a_6113_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_6114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6117_: *mut LeanObject = core::ptr::null_mut();
    v___f_6114_ = lean_alloc_closure(
        l_Std_Async_ETask_instMonad___lam__4___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_6114_, 0, v___f_6110_);
    lean_closure_set(v___f_6114_, 1, v_a_6113_);
    v___x_6115_ = lean_box(0);
    v___x_6116_ = lean_apply_1(v_y_6111_, v___x_6115_);
    v___x_6117_ = lean_apply_4(
        v___f_6112_,
        lean_box(0),
        lean_box(0),
        v___x_6116_,
        v___f_6114_,
    );
    return v___x_6117_;
}
pub unsafe fn l_Std_Async_ETask_instMonad___lam__7(
    mut v___f_6118_: *mut LeanObject,
    mut v___f_6119_: *mut LeanObject,
    mut v_00_u03b1_6120_: *mut LeanObject,
    mut v_00_u03b2_6121_: *mut LeanObject,
    mut v_x_6122_: *mut LeanObject,
    mut v_y_6123_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_6124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6125_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v___f_6119_);
    v___f_6124_ = lean_alloc_closure(
        l_Std_Async_ETask_instMonad___lam__6 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_6124_, 0, v___f_6118_);
    lean_closure_set(v___f_6124_, 1, v_y_6123_);
    lean_closure_set(v___f_6124_, 2, v___f_6119_);
    v___x_6125_ = lean_apply_4(
        v___f_6119_,
        lean_box(0),
        lean_box(0),
        v_x_6122_,
        v___f_6124_,
    );
    return v___x_6125_;
}
pub unsafe fn l_Std_Async_ETask_instMonad___lam__8(
    mut v_y_6126_: *mut LeanObject,
    mut v_x_6127_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_6128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6131_: u8 = 0;
    let mut v___x_6133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6136_: u8 = 0;
    let mut v___x_6137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6138_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6127_) == 0 {
                    lean_dec_ref(v_y_6126_);
                    v_a_6128_ = lean_ctor_get(v_x_6127_, 0);
                    v_isSharedCheck_6136_ = (!lean_is_exclusive(v_x_6127_)) as u8;
                    if v_isSharedCheck_6136_ == 0 {
                        v___x_6130_ = v_x_6127_;
                        v_isShared_6131_ = v_isSharedCheck_6136_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6128_);
                        lean_dec(v_x_6127_);
                        v___x_6130_ = lean_box(0);
                        v_isShared_6131_ = v_isSharedCheck_6136_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v_x_6127_, 1);
                    v___x_6137_ = lean_box(0);
                    v___x_6138_ = lean_apply_1(v_y_6126_, v___x_6137_);
                    return v___x_6138_;
                }
            }
            1 => {
                if v_isShared_6131_ == 0 {
                    v___x_6133_ = v___x_6130_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6135_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6135_, 0, v_a_6128_);
                    v___x_6133_ = v_reuseFailAlloc_6135_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6134_ = lean_task_pure(v___x_6133_);
                return v___x_6134_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_ETask_instMonad___lam__9(
    mut v_00_u03b1_6139_: *mut LeanObject,
    mut v_00_u03b2_6140_: *mut LeanObject,
    mut v_x_6141_: *mut LeanObject,
    mut v_y_6142_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_6143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6145_: u8 = 0;
    let mut v___x_6146_: *mut LeanObject = core::ptr::null_mut();
    v___f_6143_ = lean_alloc_closure(
        l_Std_Async_ETask_instMonad___lam__8 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_6143_, 0, v_y_6142_);
    v___x_6144_ = lean_unsigned_to_nat(0);
    v___x_6145_ = 0;
    v___x_6146_ = lean_task_bind(v_x_6141_, v___f_6143_, v___x_6144_, v___x_6145_);
    return v___x_6146_;
}
pub unsafe fn _init_l_Std_Async_ETask_instMonad___closed__5() -> *mut LeanObject {
    let mut v___x_6154_: *mut LeanObject = core::ptr::null_mut();
    v___x_6154_ = l_Std_Async_ETask_instFunctor(lean_box(0));
    return v___x_6154_;
}
pub unsafe fn _init_l_Std_Async_ETask_instMonad___closed__6() -> *mut LeanObject {
    let mut v___f_6155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6160_: *mut LeanObject = core::ptr::null_mut();
    v___f_6155_ = l_Std_Async_ETask_instMonad___closed__4;
    v___f_6156_ = l_Std_Async_ETask_instMonad___closed__3;
    v___f_6157_ = l_Std_Async_ETask_instMonad___closed__1;
    v___f_6158_ = l_Std_Async_ETask_instMonad___closed__0;
    v___x_6159_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_ETask_instMonad___closed__5),
        core::ptr::addr_of_mut!(l_Std_Async_ETask_instMonad___closed__5_once),
        _init_l_Std_Async_ETask_instMonad___closed__5,
    );
    v___x_6160_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_6160_, 0, v___x_6159_);
    lean_ctor_set(v___x_6160_, 1, v___f_6158_);
    lean_ctor_set(v___x_6160_, 2, v___f_6157_);
    lean_ctor_set(v___x_6160_, 3, v___f_6156_);
    lean_ctor_set(v___x_6160_, 4, v___f_6155_);
    return v___x_6160_;
}
pub unsafe fn _init_l_Std_Async_ETask_instMonad___closed__7() -> *mut LeanObject {
    let mut v___f_6161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6163_: *mut LeanObject = core::ptr::null_mut();
    v___f_6161_ = l_Std_Async_ETask_instMonad___closed__2;
    v___x_6162_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_ETask_instMonad___closed__6),
        core::ptr::addr_of_mut!(l_Std_Async_ETask_instMonad___closed__6_once),
        _init_l_Std_Async_ETask_instMonad___closed__6,
    );
    v___x_6163_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_6163_, 0, v___x_6162_);
    lean_ctor_set(v___x_6163_, 1, v___f_6161_);
    return v___x_6163_;
}
pub unsafe fn l_Std_Async_ETask_instMonad(
    mut v_00_u03b5_6164_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6165_: *mut LeanObject = core::ptr::null_mut();
    v___x_6165_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_ETask_instMonad___closed__7),
        core::ptr::addr_of_mut!(l_Std_Async_ETask_instMonad___closed__7_once),
        _init_l_Std_Async_ETask_instMonad___closed__7,
    );
    return v___x_6165_;
}
pub unsafe fn l_Std_Async_AsyncTask_mapIO___redArg___lam__0(
    mut v_f_6166_: *mut LeanObject,
    mut v_a_6167_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_6170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6176_: u8 = 0;
    let mut v___x_6177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6183_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_6167_) == 0 {
                    lean_dec_ref(v_f_6166_);
                    v_a_6172_ = lean_ctor_get(v_a_6167_, 0);
                    lean_inc(v_a_6172_);
                    lean_dec_ref_known(v_a_6167_, 1);
                    v_a_6170_ = v_a_6172_;
                    state = 1;
                    continue;
                } else {
                    v_a_6173_ = lean_ctor_get(v_a_6167_, 0);
                    v_isSharedCheck_6183_ = (!lean_is_exclusive(v_a_6167_)) as u8;
                    if v_isSharedCheck_6183_ == 0 {
                        v___x_6175_ = v_a_6167_;
                        v_isShared_6176_ = v_isSharedCheck_6183_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_6173_);
                        lean_dec(v_a_6167_);
                        v___x_6175_ = lean_box(0);
                        v_isShared_6176_ = v_isSharedCheck_6183_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6171_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6171_, 0, v_a_6170_);
                return v___x_6171_;
            }
            2 => {
                v___x_6177_ = lean_apply_2(v_f_6166_, v_a_6173_, lean_box(0));
                if lean_obj_tag(v___x_6177_) == 0 {
                    v_a_6178_ = lean_ctor_get(v___x_6177_, 0);
                    lean_inc(v_a_6178_);
                    lean_dec_ref_known(v___x_6177_, 1);
                    if v_isShared_6176_ == 0 {
                        lean_ctor_set(v___x_6175_, 0, v_a_6178_);
                        v___x_6180_ = v___x_6175_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6181_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6181_, 0, v_a_6178_);
                        v___x_6180_ = v_reuseFailAlloc_6181_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_6175_);
                    v_a_6182_ = lean_ctor_get(v___x_6177_, 0);
                    lean_inc(v_a_6182_);
                    lean_dec_ref_known(v___x_6177_, 1);
                    v_a_6170_ = v_a_6182_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                return v___x_6180_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_AsyncTask_mapIO___redArg___lam__0___boxed(
    mut v_f_6184_: *mut LeanObject,
    mut v_a_6185_: *mut LeanObject,
    mut v___y_6186_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6187_: *mut LeanObject = core::ptr::null_mut();
    v_res_6187_ = l_Std_Async_AsyncTask_mapIO___redArg___lam__0(v_f_6184_, v_a_6185_);
    return v_res_6187_;
}
pub unsafe fn l_Std_Async_AsyncTask_mapIO___redArg(
    mut v_f_6188_: *mut LeanObject,
    mut v_x_6189_: *mut LeanObject,
    mut v_prio_6190_: *mut LeanObject,
    mut v_sync_6191_: u8,
) -> *mut LeanObject {
    let mut v___f_6193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6194_: *mut LeanObject = core::ptr::null_mut();
    v___f_6193_ = lean_alloc_closure(
        l_Std_Async_AsyncTask_mapIO___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_6193_, 0, v_f_6188_);
    v___x_6194_ = lean_io_map_task(v___f_6193_, v_x_6189_, v_prio_6190_, v_sync_6191_);
    return v___x_6194_;
}
pub unsafe fn l_Std_Async_AsyncTask_mapIO___redArg___boxed(
    mut v_f_6195_: *mut LeanObject,
    mut v_x_6196_: *mut LeanObject,
    mut v_prio_6197_: *mut LeanObject,
    mut v_sync_6198_: *mut LeanObject,
    mut v_a_6199_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sync_boxed_6200_: u8 = 0;
    let mut v_res_6201_: *mut LeanObject = core::ptr::null_mut();
    v_sync_boxed_6200_ = (lean_unbox(v_sync_6198_) as u8);
    v_res_6201_ = l_Std_Async_AsyncTask_mapIO___redArg(
        v_f_6195_,
        v_x_6196_,
        v_prio_6197_,
        v_sync_boxed_6200_,
    );
    return v_res_6201_;
}
pub unsafe fn l_Std_Async_AsyncTask_mapIO(
    mut v_00_u03b1_6202_: *mut LeanObject,
    mut v_00_u03b2_6203_: *mut LeanObject,
    mut v_f_6204_: *mut LeanObject,
    mut v_x_6205_: *mut LeanObject,
    mut v_prio_6206_: *mut LeanObject,
    mut v_sync_6207_: u8,
) -> *mut LeanObject {
    let mut v___f_6209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6210_: *mut LeanObject = core::ptr::null_mut();
    v___f_6209_ = lean_alloc_closure(
        l_Std_Async_AsyncTask_mapIO___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_6209_, 0, v_f_6204_);
    v___x_6210_ = lean_io_map_task(v___f_6209_, v_x_6205_, v_prio_6206_, v_sync_6207_);
    return v___x_6210_;
}
pub unsafe fn l_Std_Async_AsyncTask_mapIO___boxed(
    mut v_00_u03b1_6211_: *mut LeanObject,
    mut v_00_u03b2_6212_: *mut LeanObject,
    mut v_f_6213_: *mut LeanObject,
    mut v_x_6214_: *mut LeanObject,
    mut v_prio_6215_: *mut LeanObject,
    mut v_sync_6216_: *mut LeanObject,
    mut v_a_6217_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sync_boxed_6218_: u8 = 0;
    let mut v_res_6219_: *mut LeanObject = core::ptr::null_mut();
    v_sync_boxed_6218_ = (lean_unbox(v_sync_6216_) as u8);
    v_res_6219_ = l_Std_Async_AsyncTask_mapIO(
        v_00_u03b1_6211_,
        v_00_u03b2_6212_,
        v_f_6213_,
        v_x_6214_,
        v_prio_6215_,
        v_sync_boxed_6218_,
    );
    return v_res_6219_;
}
pub unsafe fn l_Std_Async_AsyncTask_pure___redArg(
    mut v_x_6220_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6222_: *mut LeanObject = core::ptr::null_mut();
    v___x_6221_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_6221_, 0, v_x_6220_);
    v___x_6222_ = lean_task_pure(v___x_6221_);
    return v___x_6222_;
}
pub unsafe fn l_Std_Async_AsyncTask_pure(
    mut v_00_u03b1_6223_: *mut LeanObject,
    mut v_x_6224_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6226_: *mut LeanObject = core::ptr::null_mut();
    v___x_6225_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_6225_, 0, v_x_6224_);
    v___x_6226_ = lean_task_pure(v___x_6225_);
    return v___x_6226_;
}
pub unsafe fn l_Std_Async_AsyncTask_bind___redArg___lam__0(
    mut v_f_6227_: *mut LeanObject,
    mut v_x_6228_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_6229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6232_: u8 = 0;
    let mut v___x_6234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6237_: u8 = 0;
    let mut v_a_6238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6239_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6228_) == 0 {
                    lean_dec_ref(v_f_6227_);
                    v_a_6229_ = lean_ctor_get(v_x_6228_, 0);
                    v_isSharedCheck_6237_ = (!lean_is_exclusive(v_x_6228_)) as u8;
                    if v_isSharedCheck_6237_ == 0 {
                        v___x_6231_ = v_x_6228_;
                        v_isShared_6232_ = v_isSharedCheck_6237_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6229_);
                        lean_dec(v_x_6228_);
                        v___x_6231_ = lean_box(0);
                        v_isShared_6232_ = v_isSharedCheck_6237_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6238_ = lean_ctor_get(v_x_6228_, 0);
                    lean_inc(v_a_6238_);
                    lean_dec_ref_known(v_x_6228_, 1);
                    v___x_6239_ = lean_apply_1(v_f_6227_, v_a_6238_);
                    return v___x_6239_;
                }
            }
            1 => {
                if v_isShared_6232_ == 0 {
                    v___x_6234_ = v___x_6231_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6236_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6236_, 0, v_a_6229_);
                    v___x_6234_ = v_reuseFailAlloc_6236_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6235_ = lean_task_pure(v___x_6234_);
                return v___x_6235_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_AsyncTask_bind___redArg(
    mut v_x_6240_: *mut LeanObject,
    mut v_f_6241_: *mut LeanObject,
    mut v_prio_6242_: *mut LeanObject,
    mut v_sync_6243_: u8,
) -> *mut LeanObject {
    let mut v___f_6244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6245_: *mut LeanObject = core::ptr::null_mut();
    v___f_6244_ = lean_alloc_closure(
        l_Std_Async_AsyncTask_bind___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_6244_, 0, v_f_6241_);
    v___x_6245_ = lean_task_bind(v_x_6240_, v___f_6244_, v_prio_6242_, v_sync_6243_);
    return v___x_6245_;
}
pub unsafe fn l_Std_Async_AsyncTask_bind___redArg___boxed(
    mut v_x_6246_: *mut LeanObject,
    mut v_f_6247_: *mut LeanObject,
    mut v_prio_6248_: *mut LeanObject,
    mut v_sync_6249_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sync_boxed_6250_: u8 = 0;
    let mut v_res_6251_: *mut LeanObject = core::ptr::null_mut();
    v_sync_boxed_6250_ = (lean_unbox(v_sync_6249_) as u8);
    v_res_6251_ =
        l_Std_Async_AsyncTask_bind___redArg(v_x_6246_, v_f_6247_, v_prio_6248_, v_sync_boxed_6250_);
    return v_res_6251_;
}
pub unsafe fn l_Std_Async_AsyncTask_bind(
    mut v_00_u03b1_6252_: *mut LeanObject,
    mut v_00_u03b2_6253_: *mut LeanObject,
    mut v_x_6254_: *mut LeanObject,
    mut v_f_6255_: *mut LeanObject,
    mut v_prio_6256_: *mut LeanObject,
    mut v_sync_6257_: u8,
) -> *mut LeanObject {
    let mut v___f_6258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6259_: *mut LeanObject = core::ptr::null_mut();
    v___f_6258_ = lean_alloc_closure(
        l_Std_Async_AsyncTask_bind___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_6258_, 0, v_f_6255_);
    v___x_6259_ = lean_task_bind(v_x_6254_, v___f_6258_, v_prio_6256_, v_sync_6257_);
    return v___x_6259_;
}
pub unsafe fn l_Std_Async_AsyncTask_bind___boxed(
    mut v_00_u03b1_6260_: *mut LeanObject,
    mut v_00_u03b2_6261_: *mut LeanObject,
    mut v_x_6262_: *mut LeanObject,
    mut v_f_6263_: *mut LeanObject,
    mut v_prio_6264_: *mut LeanObject,
    mut v_sync_6265_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sync_boxed_6266_: u8 = 0;
    let mut v_res_6267_: *mut LeanObject = core::ptr::null_mut();
    v_sync_boxed_6266_ = (lean_unbox(v_sync_6265_) as u8);
    v_res_6267_ = l_Std_Async_AsyncTask_bind(
        v_00_u03b1_6260_,
        v_00_u03b2_6261_,
        v_x_6262_,
        v_f_6263_,
        v_prio_6264_,
        v_sync_boxed_6266_,
    );
    return v_res_6267_;
}
pub unsafe fn l_Std_Async_AsyncTask_map___redArg___lam__0(
    mut v_f_6268_: *mut LeanObject,
    mut v_x_6269_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_6270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6273_: u8 = 0;
    let mut v___x_6275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6277_: u8 = 0;
    let mut v_a_6278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6281_: u8 = 0;
    let mut v___x_6282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6286_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6269_) == 0 {
                    lean_dec(v_f_6268_);
                    v_a_6270_ = lean_ctor_get(v_x_6269_, 0);
                    v_isSharedCheck_6277_ = (!lean_is_exclusive(v_x_6269_)) as u8;
                    if v_isSharedCheck_6277_ == 0 {
                        v___x_6272_ = v_x_6269_;
                        v_isShared_6273_ = v_isSharedCheck_6277_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6270_);
                        lean_dec(v_x_6269_);
                        v___x_6272_ = lean_box(0);
                        v_isShared_6273_ = v_isSharedCheck_6277_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6278_ = lean_ctor_get(v_x_6269_, 0);
                    v_isSharedCheck_6286_ = (!lean_is_exclusive(v_x_6269_)) as u8;
                    if v_isSharedCheck_6286_ == 0 {
                        v___x_6280_ = v_x_6269_;
                        v_isShared_6281_ = v_isSharedCheck_6286_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6278_);
                        lean_dec(v_x_6269_);
                        v___x_6280_ = lean_box(0);
                        v_isShared_6281_ = v_isSharedCheck_6286_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6273_ == 0 {
                    v___x_6275_ = v___x_6272_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6276_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6276_, 0, v_a_6270_);
                    v___x_6275_ = v_reuseFailAlloc_6276_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6275_;
            }
            3 => {
                v___x_6282_ = lean_apply_1(v_f_6268_, v_a_6278_);
                if v_isShared_6281_ == 0 {
                    lean_ctor_set(v___x_6280_, 0, v___x_6282_);
                    v___x_6284_ = v___x_6280_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6285_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6285_, 0, v___x_6282_);
                    v___x_6284_ = v_reuseFailAlloc_6285_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6284_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_AsyncTask_map___redArg(
    mut v_f_6287_: *mut LeanObject,
    mut v_x_6288_: *mut LeanObject,
    mut v_prio_6289_: *mut LeanObject,
    mut v_sync_6290_: u8,
) -> *mut LeanObject {
    let mut v___f_6291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6292_: *mut LeanObject = core::ptr::null_mut();
    v___f_6291_ = lean_alloc_closure(
        l_Std_Async_AsyncTask_map___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_6291_, 0, v_f_6287_);
    v___x_6292_ = lean_task_map(v___f_6291_, v_x_6288_, v_prio_6289_, v_sync_6290_);
    return v___x_6292_;
}
pub unsafe fn l_Std_Async_AsyncTask_map___redArg___boxed(
    mut v_f_6293_: *mut LeanObject,
    mut v_x_6294_: *mut LeanObject,
    mut v_prio_6295_: *mut LeanObject,
    mut v_sync_6296_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sync_boxed_6297_: u8 = 0;
    let mut v_res_6298_: *mut LeanObject = core::ptr::null_mut();
    v_sync_boxed_6297_ = (lean_unbox(v_sync_6296_) as u8);
    v_res_6298_ =
        l_Std_Async_AsyncTask_map___redArg(v_f_6293_, v_x_6294_, v_prio_6295_, v_sync_boxed_6297_);
    return v_res_6298_;
}
pub unsafe fn l_Std_Async_AsyncTask_map(
    mut v_00_u03b1_6299_: *mut LeanObject,
    mut v_00_u03b2_6300_: *mut LeanObject,
    mut v_f_6301_: *mut LeanObject,
    mut v_x_6302_: *mut LeanObject,
    mut v_prio_6303_: *mut LeanObject,
    mut v_sync_6304_: u8,
) -> *mut LeanObject {
    let mut v___f_6305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6306_: *mut LeanObject = core::ptr::null_mut();
    v___f_6305_ = lean_alloc_closure(
        l_Std_Async_AsyncTask_map___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_6305_, 0, v_f_6301_);
    v___x_6306_ = lean_task_map(v___f_6305_, v_x_6302_, v_prio_6303_, v_sync_6304_);
    return v___x_6306_;
}
pub unsafe fn l_Std_Async_AsyncTask_map___boxed(
    mut v_00_u03b1_6307_: *mut LeanObject,
    mut v_00_u03b2_6308_: *mut LeanObject,
    mut v_f_6309_: *mut LeanObject,
    mut v_x_6310_: *mut LeanObject,
    mut v_prio_6311_: *mut LeanObject,
    mut v_sync_6312_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sync_boxed_6313_: u8 = 0;
    let mut v_res_6314_: *mut LeanObject = core::ptr::null_mut();
    v_sync_boxed_6313_ = (lean_unbox(v_sync_6312_) as u8);
    v_res_6314_ = l_Std_Async_AsyncTask_map(
        v_00_u03b1_6307_,
        v_00_u03b2_6308_,
        v_f_6309_,
        v_x_6310_,
        v_prio_6311_,
        v_sync_boxed_6313_,
    );
    return v_res_6314_;
}
pub unsafe fn l_Std_Async_AsyncTask_bindIO___redArg___lam__0(
    mut v_f_6315_: *mut LeanObject,
    mut v_a_6316_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_6319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6326_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_6316_) == 0 {
                    lean_dec_ref(v_f_6315_);
                    v_a_6322_ = lean_ctor_get(v_a_6316_, 0);
                    lean_inc(v_a_6322_);
                    lean_dec_ref_known(v_a_6316_, 1);
                    v_a_6319_ = v_a_6322_;
                    state = 1;
                    continue;
                } else {
                    v_a_6323_ = lean_ctor_get(v_a_6316_, 0);
                    lean_inc(v_a_6323_);
                    lean_dec_ref_known(v_a_6316_, 1);
                    v___x_6324_ = lean_apply_2(v_f_6315_, v_a_6323_, lean_box(0));
                    if lean_obj_tag(v___x_6324_) == 0 {
                        v_a_6325_ = lean_ctor_get(v___x_6324_, 0);
                        lean_inc(v_a_6325_);
                        lean_dec_ref_known(v___x_6324_, 1);
                        return v_a_6325_;
                    } else {
                        v_a_6326_ = lean_ctor_get(v___x_6324_, 0);
                        lean_inc(v_a_6326_);
                        lean_dec_ref_known(v___x_6324_, 1);
                        v_a_6319_ = v_a_6326_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6320_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6320_, 0, v_a_6319_);
                v___x_6321_ = lean_task_pure(v___x_6320_);
                return v___x_6321_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_AsyncTask_bindIO___redArg___lam__0___boxed(
    mut v_f_6327_: *mut LeanObject,
    mut v_a_6328_: *mut LeanObject,
    mut v___y_6329_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6330_: *mut LeanObject = core::ptr::null_mut();
    v_res_6330_ = l_Std_Async_AsyncTask_bindIO___redArg___lam__0(v_f_6327_, v_a_6328_);
    return v_res_6330_;
}
pub unsafe fn l_Std_Async_AsyncTask_bindIO___redArg(
    mut v_x_6331_: *mut LeanObject,
    mut v_f_6332_: *mut LeanObject,
    mut v_prio_6333_: *mut LeanObject,
    mut v_sync_6334_: u8,
) -> *mut LeanObject {
    let mut v___f_6336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6337_: *mut LeanObject = core::ptr::null_mut();
    v___f_6336_ = lean_alloc_closure(
        l_Std_Async_AsyncTask_bindIO___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_6336_, 0, v_f_6332_);
    v___x_6337_ = lean_io_bind_task(v_x_6331_, v___f_6336_, v_prio_6333_, v_sync_6334_);
    return v___x_6337_;
}
pub unsafe fn l_Std_Async_AsyncTask_bindIO___redArg___boxed(
    mut v_x_6338_: *mut LeanObject,
    mut v_f_6339_: *mut LeanObject,
    mut v_prio_6340_: *mut LeanObject,
    mut v_sync_6341_: *mut LeanObject,
    mut v_a_6342_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sync_boxed_6343_: u8 = 0;
    let mut v_res_6344_: *mut LeanObject = core::ptr::null_mut();
    v_sync_boxed_6343_ = (lean_unbox(v_sync_6341_) as u8);
    v_res_6344_ = l_Std_Async_AsyncTask_bindIO___redArg(
        v_x_6338_,
        v_f_6339_,
        v_prio_6340_,
        v_sync_boxed_6343_,
    );
    return v_res_6344_;
}
pub unsafe fn l_Std_Async_AsyncTask_bindIO(
    mut v_00_u03b1_6345_: *mut LeanObject,
    mut v_00_u03b2_6346_: *mut LeanObject,
    mut v_x_6347_: *mut LeanObject,
    mut v_f_6348_: *mut LeanObject,
    mut v_prio_6349_: *mut LeanObject,
    mut v_sync_6350_: u8,
) -> *mut LeanObject {
    let mut v___f_6352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6353_: *mut LeanObject = core::ptr::null_mut();
    v___f_6352_ = lean_alloc_closure(
        l_Std_Async_AsyncTask_bindIO___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_6352_, 0, v_f_6348_);
    v___x_6353_ = lean_io_bind_task(v_x_6347_, v___f_6352_, v_prio_6349_, v_sync_6350_);
    return v___x_6353_;
}
pub unsafe fn l_Std_Async_AsyncTask_bindIO___boxed(
    mut v_00_u03b1_6354_: *mut LeanObject,
    mut v_00_u03b2_6355_: *mut LeanObject,
    mut v_x_6356_: *mut LeanObject,
    mut v_f_6357_: *mut LeanObject,
    mut v_prio_6358_: *mut LeanObject,
    mut v_sync_6359_: *mut LeanObject,
    mut v_a_6360_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sync_boxed_6361_: u8 = 0;
    let mut v_res_6362_: *mut LeanObject = core::ptr::null_mut();
    v_sync_boxed_6361_ = (lean_unbox(v_sync_6359_) as u8);
    v_res_6362_ = l_Std_Async_AsyncTask_bindIO(
        v_00_u03b1_6354_,
        v_00_u03b2_6355_,
        v_x_6356_,
        v_f_6357_,
        v_prio_6358_,
        v_sync_boxed_6361_,
    );
    return v_res_6362_;
}
pub unsafe fn l_Std_Async_AsyncTask_mapTaskIO___redArg(
    mut v_f_6363_: *mut LeanObject,
    mut v_x_6364_: *mut LeanObject,
    mut v_prio_6365_: *mut LeanObject,
    mut v_sync_6366_: u8,
) -> *mut LeanObject {
    let mut v___f_6368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6369_: *mut LeanObject = core::ptr::null_mut();
    v___f_6368_ = lean_alloc_closure(
        l_Std_Async_AsyncTask_mapIO___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_6368_, 0, v_f_6363_);
    v___x_6369_ = lean_io_map_task(v___f_6368_, v_x_6364_, v_prio_6365_, v_sync_6366_);
    return v___x_6369_;
}
pub unsafe fn l_Std_Async_AsyncTask_mapTaskIO___redArg___boxed(
    mut v_f_6370_: *mut LeanObject,
    mut v_x_6371_: *mut LeanObject,
    mut v_prio_6372_: *mut LeanObject,
    mut v_sync_6373_: *mut LeanObject,
    mut v_a_6374_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sync_boxed_6375_: u8 = 0;
    let mut v_res_6376_: *mut LeanObject = core::ptr::null_mut();
    v_sync_boxed_6375_ = (lean_unbox(v_sync_6373_) as u8);
    v_res_6376_ = l_Std_Async_AsyncTask_mapTaskIO___redArg(
        v_f_6370_,
        v_x_6371_,
        v_prio_6372_,
        v_sync_boxed_6375_,
    );
    return v_res_6376_;
}
pub unsafe fn l_Std_Async_AsyncTask_mapTaskIO(
    mut v_00_u03b1_6377_: *mut LeanObject,
    mut v_00_u03b2_6378_: *mut LeanObject,
    mut v_f_6379_: *mut LeanObject,
    mut v_x_6380_: *mut LeanObject,
    mut v_prio_6381_: *mut LeanObject,
    mut v_sync_6382_: u8,
) -> *mut LeanObject {
    let mut v___f_6384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6385_: *mut LeanObject = core::ptr::null_mut();
    v___f_6384_ = lean_alloc_closure(
        l_Std_Async_AsyncTask_mapIO___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_6384_, 0, v_f_6379_);
    v___x_6385_ = lean_io_map_task(v___f_6384_, v_x_6380_, v_prio_6381_, v_sync_6382_);
    return v___x_6385_;
}
pub unsafe fn l_Std_Async_AsyncTask_mapTaskIO___boxed(
    mut v_00_u03b1_6386_: *mut LeanObject,
    mut v_00_u03b2_6387_: *mut LeanObject,
    mut v_f_6388_: *mut LeanObject,
    mut v_x_6389_: *mut LeanObject,
    mut v_prio_6390_: *mut LeanObject,
    mut v_sync_6391_: *mut LeanObject,
    mut v_a_6392_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sync_boxed_6393_: u8 = 0;
    let mut v_res_6394_: *mut LeanObject = core::ptr::null_mut();
    v_sync_boxed_6393_ = (lean_unbox(v_sync_6391_) as u8);
    v_res_6394_ = l_Std_Async_AsyncTask_mapTaskIO(
        v_00_u03b1_6386_,
        v_00_u03b2_6387_,
        v_f_6388_,
        v_x_6389_,
        v_prio_6390_,
        v_sync_boxed_6393_,
    );
    return v_res_6394_;
}
pub unsafe fn l_Std_Async_AsyncTask_block___redArg(
    mut v_x_6395_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6401_: u8 = 0;
    let mut v___x_6403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6405_: u8 = 0;
    let mut v_a_6406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6409_: u8 = 0;
    let mut v___x_6411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6413_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6397_ = lean_task_get_own(v_x_6395_);
                if lean_obj_tag(v___x_6397_) == 0 {
                    v_a_6398_ = lean_ctor_get(v___x_6397_, 0);
                    v_isSharedCheck_6405_ = (!lean_is_exclusive(v___x_6397_)) as u8;
                    if v_isSharedCheck_6405_ == 0 {
                        v___x_6400_ = v___x_6397_;
                        v_isShared_6401_ = v_isSharedCheck_6405_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6398_);
                        lean_dec(v___x_6397_);
                        v___x_6400_ = lean_box(0);
                        v_isShared_6401_ = v_isSharedCheck_6405_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6406_ = lean_ctor_get(v___x_6397_, 0);
                    v_isSharedCheck_6413_ = (!lean_is_exclusive(v___x_6397_)) as u8;
                    if v_isSharedCheck_6413_ == 0 {
                        v___x_6408_ = v___x_6397_;
                        v_isShared_6409_ = v_isSharedCheck_6413_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6406_);
                        lean_dec(v___x_6397_);
                        v___x_6408_ = lean_box(0);
                        v_isShared_6409_ = v_isSharedCheck_6413_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6401_ == 0 {
                    lean_ctor_set_tag(v___x_6400_, 1);
                    v___x_6403_ = v___x_6400_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6404_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6404_, 0, v_a_6398_);
                    v___x_6403_ = v_reuseFailAlloc_6404_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6403_;
            }
            3 => {
                if v_isShared_6409_ == 0 {
                    lean_ctor_set_tag(v___x_6408_, 0);
                    v___x_6411_ = v___x_6408_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6412_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6412_, 0, v_a_6406_);
                    v___x_6411_ = v_reuseFailAlloc_6412_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6411_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_AsyncTask_block___redArg___boxed(
    mut v_x_6414_: *mut LeanObject,
    mut v_a_6415_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6416_: *mut LeanObject = core::ptr::null_mut();
    v_res_6416_ = l_Std_Async_AsyncTask_block___redArg(v_x_6414_);
    return v_res_6416_;
}
pub unsafe fn l_Std_Async_AsyncTask_block(
    mut v_00_u03b1_6417_: *mut LeanObject,
    mut v_x_6418_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6420_: *mut LeanObject = core::ptr::null_mut();
    v___x_6420_ = l_Std_Async_AsyncTask_block___redArg(v_x_6418_);
    return v___x_6420_;
}
pub unsafe fn l_Std_Async_AsyncTask_block___boxed(
    mut v_00_u03b1_6421_: *mut LeanObject,
    mut v_x_6422_: *mut LeanObject,
    mut v_a_6423_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6424_: *mut LeanObject = core::ptr::null_mut();
    v_res_6424_ = l_Std_Async_AsyncTask_block(v_00_u03b1_6421_, v_x_6422_);
    return v_res_6424_;
}
pub unsafe fn l_Std_Async_AsyncTask_ofPromise___redArg___lam__0(
    mut v_error_6425_: *mut LeanObject,
    mut v_x_6426_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_6426_) == 0 {
        let mut v___x_6427_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6428_: *mut LeanObject = core::ptr::null_mut();
        v___x_6427_ = lean_mk_io_user_error(v_error_6425_);
        v___x_6428_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_6428_, 0, v___x_6427_);
        return v___x_6428_;
    } else {
        let mut v_val_6429_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_error_6425_);
        v_val_6429_ = lean_ctor_get(v_x_6426_, 0);
        lean_inc(v_val_6429_);
        return v_val_6429_;
    }
}
pub unsafe fn l_Std_Async_AsyncTask_ofPromise___redArg___lam__0___boxed(
    mut v_error_6430_: *mut LeanObject,
    mut v_x_6431_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6432_: *mut LeanObject = core::ptr::null_mut();
    v_res_6432_ = l_Std_Async_AsyncTask_ofPromise___redArg___lam__0(v_error_6430_, v_x_6431_);
    lean_dec(v_x_6431_);
    return v_res_6432_;
}
pub unsafe fn l_Std_Async_AsyncTask_ofPromise___redArg(
    mut v_x_6433_: *mut LeanObject,
    mut v_error_6434_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_6435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6438_: u8 = 0;
    let mut v___x_6439_: *mut LeanObject = core::ptr::null_mut();
    v___f_6435_ = lean_alloc_closure(
        l_Std_Async_AsyncTask_ofPromise___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_6435_, 0, v_error_6434_);
    v___x_6436_ = lean_io_promise_result_opt(v_x_6433_);
    v___x_6437_ = lean_unsigned_to_nat(0);
    v___x_6438_ = 0;
    v___x_6439_ = lean_task_map(v___f_6435_, v___x_6436_, v___x_6437_, v___x_6438_);
    return v___x_6439_;
}
pub unsafe fn l_Std_Async_AsyncTask_ofPromise___redArg___boxed(
    mut v_x_6440_: *mut LeanObject,
    mut v_error_6441_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6442_: *mut LeanObject = core::ptr::null_mut();
    v_res_6442_ = l_Std_Async_AsyncTask_ofPromise___redArg(v_x_6440_, v_error_6441_);
    lean_dec(v_x_6440_);
    return v_res_6442_;
}
pub unsafe fn l_Std_Async_AsyncTask_ofPromise(
    mut v_00_u03b1_6443_: *mut LeanObject,
    mut v_x_6444_: *mut LeanObject,
    mut v_error_6445_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_6446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6449_: u8 = 0;
    let mut v___x_6450_: *mut LeanObject = core::ptr::null_mut();
    v___f_6446_ = lean_alloc_closure(
        l_Std_Async_AsyncTask_ofPromise___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_6446_, 0, v_error_6445_);
    v___x_6447_ = lean_io_promise_result_opt(v_x_6444_);
    v___x_6448_ = lean_unsigned_to_nat(0);
    v___x_6449_ = 0;
    v___x_6450_ = lean_task_map(v___f_6446_, v___x_6447_, v___x_6448_, v___x_6449_);
    return v___x_6450_;
}
pub unsafe fn l_Std_Async_AsyncTask_ofPromise___boxed(
    mut v_00_u03b1_6451_: *mut LeanObject,
    mut v_x_6452_: *mut LeanObject,
    mut v_error_6453_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6454_: *mut LeanObject = core::ptr::null_mut();
    v_res_6454_ = l_Std_Async_AsyncTask_ofPromise(v_00_u03b1_6451_, v_x_6452_, v_error_6453_);
    lean_dec(v_x_6452_);
    return v_res_6454_;
}
pub unsafe fn l_Std_Async_AsyncTask_ofPurePromise___redArg___lam__0(
    mut v_error_6455_: *mut LeanObject,
    mut v_x_6456_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6462_: u8 = 0;
    let mut v___x_6464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6466_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6456_) == 0 {
                    v___x_6457_ = lean_mk_io_user_error(v_error_6455_);
                    v___x_6458_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6458_, 0, v___x_6457_);
                    return v___x_6458_;
                } else {
                    lean_dec_ref(v_error_6455_);
                    v_val_6459_ = lean_ctor_get(v_x_6456_, 0);
                    v_isSharedCheck_6466_ = (!lean_is_exclusive(v_x_6456_)) as u8;
                    if v_isSharedCheck_6466_ == 0 {
                        v___x_6461_ = v_x_6456_;
                        v_isShared_6462_ = v_isSharedCheck_6466_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_6459_);
                        lean_dec(v_x_6456_);
                        v___x_6461_ = lean_box(0);
                        v_isShared_6462_ = v_isSharedCheck_6466_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6462_ == 0 {
                    v___x_6464_ = v___x_6461_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6465_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6465_, 0, v_val_6459_);
                    v___x_6464_ = v_reuseFailAlloc_6465_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6464_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_AsyncTask_ofPurePromise___redArg(
    mut v_x_6467_: *mut LeanObject,
    mut v_error_6468_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_6469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6472_: u8 = 0;
    let mut v___x_6473_: *mut LeanObject = core::ptr::null_mut();
    v___f_6469_ = lean_alloc_closure(
        l_Std_Async_AsyncTask_ofPurePromise___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_6469_, 0, v_error_6468_);
    v___x_6470_ = lean_io_promise_result_opt(v_x_6467_);
    v___x_6471_ = lean_unsigned_to_nat(0);
    v___x_6472_ = 1;
    v___x_6473_ = lean_task_map(v___f_6469_, v___x_6470_, v___x_6471_, v___x_6472_);
    return v___x_6473_;
}
pub unsafe fn l_Std_Async_AsyncTask_ofPurePromise___redArg___boxed(
    mut v_x_6474_: *mut LeanObject,
    mut v_error_6475_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6476_: *mut LeanObject = core::ptr::null_mut();
    v_res_6476_ = l_Std_Async_AsyncTask_ofPurePromise___redArg(v_x_6474_, v_error_6475_);
    lean_dec(v_x_6474_);
    return v_res_6476_;
}
pub unsafe fn l_Std_Async_AsyncTask_ofPurePromise(
    mut v_00_u03b1_6477_: *mut LeanObject,
    mut v_x_6478_: *mut LeanObject,
    mut v_error_6479_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_6480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6483_: u8 = 0;
    let mut v___x_6484_: *mut LeanObject = core::ptr::null_mut();
    v___f_6480_ = lean_alloc_closure(
        l_Std_Async_AsyncTask_ofPurePromise___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_6480_, 0, v_error_6479_);
    v___x_6481_ = lean_io_promise_result_opt(v_x_6478_);
    v___x_6482_ = lean_unsigned_to_nat(0);
    v___x_6483_ = 1;
    v___x_6484_ = lean_task_map(v___f_6480_, v___x_6481_, v___x_6482_, v___x_6483_);
    return v___x_6484_;
}
pub unsafe fn l_Std_Async_AsyncTask_ofPurePromise___boxed(
    mut v_00_u03b1_6485_: *mut LeanObject,
    mut v_x_6486_: *mut LeanObject,
    mut v_error_6487_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6488_: *mut LeanObject = core::ptr::null_mut();
    v_res_6488_ = l_Std_Async_AsyncTask_ofPurePromise(v_00_u03b1_6485_, v_x_6486_, v_error_6487_);
    lean_dec(v_x_6486_);
    return v_res_6488_;
}
pub unsafe fn l_Std_Async_AsyncTask_getState___redArg(mut v_x_6489_: *mut LeanObject) -> u8 {
    let mut v___x_6491_: u8 = 0;
    v___x_6491_ = lean_io_get_task_state(v_x_6489_);
    return v___x_6491_;
}
pub unsafe fn l_Std_Async_AsyncTask_getState___redArg___boxed(
    mut v_x_6492_: *mut LeanObject,
    mut v_a_6493_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6494_: u8 = 0;
    let mut v_r_6495_: *mut LeanObject = core::ptr::null_mut();
    v_res_6494_ = l_Std_Async_AsyncTask_getState___redArg(v_x_6492_);
    lean_dec_ref(v_x_6492_);
    v_r_6495_ = lean_box((v_res_6494_) as usize);
    return v_r_6495_;
}
pub unsafe fn l_Std_Async_AsyncTask_getState(
    mut v_00_u03b1_6496_: *mut LeanObject,
    mut v_x_6497_: *mut LeanObject,
) -> u8 {
    let mut v___x_6499_: u8 = 0;
    v___x_6499_ = lean_io_get_task_state(v_x_6497_);
    return v___x_6499_;
}
pub unsafe fn l_Std_Async_AsyncTask_getState___boxed(
    mut v_00_u03b1_6500_: *mut LeanObject,
    mut v_x_6501_: *mut LeanObject,
    mut v_a_6502_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6503_: u8 = 0;
    let mut v_r_6504_: *mut LeanObject = core::ptr::null_mut();
    v_res_6503_ = l_Std_Async_AsyncTask_getState(v_00_u03b1_6500_, v_x_6501_);
    lean_dec_ref(v_x_6501_);
    v_r_6504_ = lean_box((v_res_6503_) as usize);
    return v_r_6504_;
}
pub unsafe fn l_Std_Async_MaybeTask_ctorIdx___redArg(
    mut v_x_6505_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_6505_) == 0 {
        let mut v___x_6506_: *mut LeanObject = core::ptr::null_mut();
        v___x_6506_ = lean_unsigned_to_nat(0);
        return v___x_6506_;
    } else {
        let mut v___x_6507_: *mut LeanObject = core::ptr::null_mut();
        v___x_6507_ = lean_unsigned_to_nat(1);
        return v___x_6507_;
    }
}
pub unsafe fn l_Std_Async_MaybeTask_ctorIdx___redArg___boxed(
    mut v_x_6508_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6509_: *mut LeanObject = core::ptr::null_mut();
    v_res_6509_ = l_Std_Async_MaybeTask_ctorIdx___redArg(v_x_6508_);
    lean_dec_ref(v_x_6508_);
    return v_res_6509_;
}
pub unsafe fn l_Std_Async_MaybeTask_ctorIdx(
    mut v_00_u03b1_6510_: *mut LeanObject,
    mut v_x_6511_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6512_: *mut LeanObject = core::ptr::null_mut();
    v___x_6512_ = l_Std_Async_MaybeTask_ctorIdx___redArg(v_x_6511_);
    return v___x_6512_;
}
pub unsafe fn l_Std_Async_MaybeTask_ctorIdx___boxed(
    mut v_00_u03b1_6513_: *mut LeanObject,
    mut v_x_6514_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6515_: *mut LeanObject = core::ptr::null_mut();
    v_res_6515_ = l_Std_Async_MaybeTask_ctorIdx(v_00_u03b1_6513_, v_x_6514_);
    lean_dec_ref(v_x_6514_);
    return v_res_6515_;
}
pub unsafe fn l_Std_Async_MaybeTask_ctorElim___redArg(
    mut v_t_6516_: *mut LeanObject,
    mut v_k_6517_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_6516_) == 0 {
        let mut v_a_6518_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6519_: *mut LeanObject = core::ptr::null_mut();
        v_a_6518_ = lean_ctor_get(v_t_6516_, 0);
        lean_inc(v_a_6518_);
        lean_dec_ref_known(v_t_6516_, 1);
        v___x_6519_ = lean_apply_1(v_k_6517_, v_a_6518_);
        return v___x_6519_;
    } else {
        let mut v_a_6520_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6521_: *mut LeanObject = core::ptr::null_mut();
        v_a_6520_ = lean_ctor_get(v_t_6516_, 0);
        lean_inc_ref(v_a_6520_);
        lean_dec_ref_known(v_t_6516_, 1);
        v___x_6521_ = lean_apply_1(v_k_6517_, v_a_6520_);
        return v___x_6521_;
    }
}
pub unsafe fn l_Std_Async_MaybeTask_ctorElim(
    mut v_00_u03b1_6522_: *mut LeanObject,
    mut v_motive_6523_: *mut LeanObject,
    mut v_ctorIdx_6524_: *mut LeanObject,
    mut v_t_6525_: *mut LeanObject,
    mut v_h_6526_: *mut LeanObject,
    mut v_k_6527_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6528_: *mut LeanObject = core::ptr::null_mut();
    v___x_6528_ = l_Std_Async_MaybeTask_ctorElim___redArg(v_t_6525_, v_k_6527_);
    return v___x_6528_;
}
pub unsafe fn l_Std_Async_MaybeTask_ctorElim___boxed(
    mut v_00_u03b1_6529_: *mut LeanObject,
    mut v_motive_6530_: *mut LeanObject,
    mut v_ctorIdx_6531_: *mut LeanObject,
    mut v_t_6532_: *mut LeanObject,
    mut v_h_6533_: *mut LeanObject,
    mut v_k_6534_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6535_: *mut LeanObject = core::ptr::null_mut();
    v_res_6535_ = l_Std_Async_MaybeTask_ctorElim(
        v_00_u03b1_6529_,
        v_motive_6530_,
        v_ctorIdx_6531_,
        v_t_6532_,
        v_h_6533_,
        v_k_6534_,
    );
    lean_dec(v_ctorIdx_6531_);
    return v_res_6535_;
}
pub unsafe fn l_Std_Async_MaybeTask_pure_elim___redArg(
    mut v_t_6536_: *mut LeanObject,
    mut v_pure_6537_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6538_: *mut LeanObject = core::ptr::null_mut();
    v___x_6538_ = l_Std_Async_MaybeTask_ctorElim___redArg(v_t_6536_, v_pure_6537_);
    return v___x_6538_;
}
pub unsafe fn l_Std_Async_MaybeTask_pure_elim(
    mut v_00_u03b1_6539_: *mut LeanObject,
    mut v_motive_6540_: *mut LeanObject,
    mut v_t_6541_: *mut LeanObject,
    mut v_h_6542_: *mut LeanObject,
    mut v_pure_6543_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6544_: *mut LeanObject = core::ptr::null_mut();
    v___x_6544_ = l_Std_Async_MaybeTask_ctorElim___redArg(v_t_6541_, v_pure_6543_);
    return v___x_6544_;
}
pub unsafe fn l_Std_Async_MaybeTask_ofTask_elim___redArg(
    mut v_t_6545_: *mut LeanObject,
    mut v_ofTask_6546_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6547_: *mut LeanObject = core::ptr::null_mut();
    v___x_6547_ = l_Std_Async_MaybeTask_ctorElim___redArg(v_t_6545_, v_ofTask_6546_);
    return v___x_6547_;
}
pub unsafe fn l_Std_Async_MaybeTask_ofTask_elim(
    mut v_00_u03b1_6548_: *mut LeanObject,
    mut v_motive_6549_: *mut LeanObject,
    mut v_t_6550_: *mut LeanObject,
    mut v_h_6551_: *mut LeanObject,
    mut v_ofTask_6552_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6553_: *mut LeanObject = core::ptr::null_mut();
    v___x_6553_ = l_Std_Async_MaybeTask_ctorElim___redArg(v_t_6550_, v_ofTask_6552_);
    return v___x_6553_;
}
pub unsafe fn l_Std_Async_MaybeTask_toTask___redArg(
    mut v_x_6554_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_6554_) == 0 {
        let mut v_a_6555_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6556_: *mut LeanObject = core::ptr::null_mut();
        v_a_6555_ = lean_ctor_get(v_x_6554_, 0);
        lean_inc(v_a_6555_);
        lean_dec_ref_known(v_x_6554_, 1);
        v___x_6556_ = lean_task_pure(v_a_6555_);
        return v___x_6556_;
    } else {
        let mut v_a_6557_: *mut LeanObject = core::ptr::null_mut();
        v_a_6557_ = lean_ctor_get(v_x_6554_, 0);
        lean_inc_ref(v_a_6557_);
        lean_dec_ref_known(v_x_6554_, 1);
        return v_a_6557_;
    }
}
pub unsafe fn l_Std_Async_MaybeTask_toTask(
    mut v_00_u03b1_6558_: *mut LeanObject,
    mut v_x_6559_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_6559_) == 0 {
        let mut v_a_6560_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6561_: *mut LeanObject = core::ptr::null_mut();
        v_a_6560_ = lean_ctor_get(v_x_6559_, 0);
        lean_inc(v_a_6560_);
        lean_dec_ref_known(v_x_6559_, 1);
        v___x_6561_ = lean_task_pure(v_a_6560_);
        return v___x_6561_;
    } else {
        let mut v_a_6562_: *mut LeanObject = core::ptr::null_mut();
        v_a_6562_ = lean_ctor_get(v_x_6559_, 0);
        lean_inc_ref(v_a_6562_);
        lean_dec_ref_known(v_x_6559_, 1);
        return v_a_6562_;
    }
}
pub unsafe fn l_Std_Async_MaybeTask_get___redArg(
    mut v_x_6563_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_6563_) == 0 {
        let mut v_a_6564_: *mut LeanObject = core::ptr::null_mut();
        v_a_6564_ = lean_ctor_get(v_x_6563_, 0);
        lean_inc(v_a_6564_);
        lean_dec_ref_known(v_x_6563_, 1);
        return v_a_6564_;
    } else {
        let mut v_a_6565_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6566_: *mut LeanObject = core::ptr::null_mut();
        v_a_6565_ = lean_ctor_get(v_x_6563_, 0);
        lean_inc_ref(v_a_6565_);
        lean_dec_ref_known(v_x_6563_, 1);
        v___x_6566_ = lean_task_get_own(v_a_6565_);
        return v___x_6566_;
    }
}
pub unsafe fn l_Std_Async_MaybeTask_get(
    mut v_00_u03b1_6567_: *mut LeanObject,
    mut v_x_6568_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_6568_) == 0 {
        let mut v_a_6569_: *mut LeanObject = core::ptr::null_mut();
        v_a_6569_ = lean_ctor_get(v_x_6568_, 0);
        lean_inc(v_a_6569_);
        lean_dec_ref_known(v_x_6568_, 1);
        return v_a_6569_;
    } else {
        let mut v_a_6570_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6571_: *mut LeanObject = core::ptr::null_mut();
        v_a_6570_ = lean_ctor_get(v_x_6568_, 0);
        lean_inc_ref(v_a_6570_);
        lean_dec_ref_known(v_x_6568_, 1);
        v___x_6571_ = lean_task_get_own(v_a_6570_);
        return v___x_6571_;
    }
}
pub unsafe fn l_Std_Async_MaybeTask_map___redArg(
    mut v_f_6572_: *mut LeanObject,
    mut v_prio_6573_: *mut LeanObject,
    mut v_sync_6574_: u8,
    mut v_x_6575_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_6576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6579_: u8 = 0;
    let mut v___x_6580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6584_: u8 = 0;
    let mut v_a_6585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6588_: u8 = 0;
    let mut v___x_6589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6593_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6575_) == 0 {
                    lean_dec(v_prio_6573_);
                    v_a_6576_ = lean_ctor_get(v_x_6575_, 0);
                    v_isSharedCheck_6584_ = (!lean_is_exclusive(v_x_6575_)) as u8;
                    if v_isSharedCheck_6584_ == 0 {
                        v___x_6578_ = v_x_6575_;
                        v_isShared_6579_ = v_isSharedCheck_6584_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6576_);
                        lean_dec(v_x_6575_);
                        v___x_6578_ = lean_box(0);
                        v_isShared_6579_ = v_isSharedCheck_6584_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6585_ = lean_ctor_get(v_x_6575_, 0);
                    v_isSharedCheck_6593_ = (!lean_is_exclusive(v_x_6575_)) as u8;
                    if v_isSharedCheck_6593_ == 0 {
                        v___x_6587_ = v_x_6575_;
                        v_isShared_6588_ = v_isSharedCheck_6593_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6585_);
                        lean_dec(v_x_6575_);
                        v___x_6587_ = lean_box(0);
                        v_isShared_6588_ = v_isSharedCheck_6593_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6580_ = lean_apply_1(v_f_6572_, v_a_6576_);
                if v_isShared_6579_ == 0 {
                    lean_ctor_set(v___x_6578_, 0, v___x_6580_);
                    v___x_6582_ = v___x_6578_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6583_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6583_, 0, v___x_6580_);
                    v___x_6582_ = v_reuseFailAlloc_6583_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6582_;
            }
            3 => {
                v___x_6589_ = lean_task_map(v_f_6572_, v_a_6585_, v_prio_6573_, v_sync_6574_);
                if v_isShared_6588_ == 0 {
                    lean_ctor_set(v___x_6587_, 0, v___x_6589_);
                    v___x_6591_ = v___x_6587_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6592_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6592_, 0, v___x_6589_);
                    v___x_6591_ = v_reuseFailAlloc_6592_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6591_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_MaybeTask_map___redArg___boxed(
    mut v_f_6594_: *mut LeanObject,
    mut v_prio_6595_: *mut LeanObject,
    mut v_sync_6596_: *mut LeanObject,
    mut v_x_6597_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sync_boxed_6598_: u8 = 0;
    let mut v_res_6599_: *mut LeanObject = core::ptr::null_mut();
    v_sync_boxed_6598_ = (lean_unbox(v_sync_6596_) as u8);
    v_res_6599_ =
        l_Std_Async_MaybeTask_map___redArg(v_f_6594_, v_prio_6595_, v_sync_boxed_6598_, v_x_6597_);
    return v_res_6599_;
}
pub unsafe fn l_Std_Async_MaybeTask_map(
    mut v_00_u03b1_6600_: *mut LeanObject,
    mut v_00_u03b2_6601_: *mut LeanObject,
    mut v_f_6602_: *mut LeanObject,
    mut v_prio_6603_: *mut LeanObject,
    mut v_sync_6604_: u8,
    mut v_x_6605_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_6606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6609_: u8 = 0;
    let mut v___x_6610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6614_: u8 = 0;
    let mut v_a_6615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6618_: u8 = 0;
    let mut v___x_6619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6623_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6605_) == 0 {
                    lean_dec(v_prio_6603_);
                    v_a_6606_ = lean_ctor_get(v_x_6605_, 0);
                    v_isSharedCheck_6614_ = (!lean_is_exclusive(v_x_6605_)) as u8;
                    if v_isSharedCheck_6614_ == 0 {
                        v___x_6608_ = v_x_6605_;
                        v_isShared_6609_ = v_isSharedCheck_6614_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6606_);
                        lean_dec(v_x_6605_);
                        v___x_6608_ = lean_box(0);
                        v_isShared_6609_ = v_isSharedCheck_6614_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6615_ = lean_ctor_get(v_x_6605_, 0);
                    v_isSharedCheck_6623_ = (!lean_is_exclusive(v_x_6605_)) as u8;
                    if v_isSharedCheck_6623_ == 0 {
                        v___x_6617_ = v_x_6605_;
                        v_isShared_6618_ = v_isSharedCheck_6623_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6615_);
                        lean_dec(v_x_6605_);
                        v___x_6617_ = lean_box(0);
                        v_isShared_6618_ = v_isSharedCheck_6623_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6610_ = lean_apply_1(v_f_6602_, v_a_6606_);
                if v_isShared_6609_ == 0 {
                    lean_ctor_set(v___x_6608_, 0, v___x_6610_);
                    v___x_6612_ = v___x_6608_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6613_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6613_, 0, v___x_6610_);
                    v___x_6612_ = v_reuseFailAlloc_6613_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6612_;
            }
            3 => {
                v___x_6619_ = lean_task_map(v_f_6602_, v_a_6615_, v_prio_6603_, v_sync_6604_);
                if v_isShared_6618_ == 0 {
                    lean_ctor_set(v___x_6617_, 0, v___x_6619_);
                    v___x_6621_ = v___x_6617_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6622_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6622_, 0, v___x_6619_);
                    v___x_6621_ = v_reuseFailAlloc_6622_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6621_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_MaybeTask_map___boxed(
    mut v_00_u03b1_6624_: *mut LeanObject,
    mut v_00_u03b2_6625_: *mut LeanObject,
    mut v_f_6626_: *mut LeanObject,
    mut v_prio_6627_: *mut LeanObject,
    mut v_sync_6628_: *mut LeanObject,
    mut v_x_6629_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sync_boxed_6630_: u8 = 0;
    let mut v_res_6631_: *mut LeanObject = core::ptr::null_mut();
    v_sync_boxed_6630_ = (lean_unbox(v_sync_6628_) as u8);
    v_res_6631_ = l_Std_Async_MaybeTask_map(
        v_00_u03b1_6624_,
        v_00_u03b2_6625_,
        v_f_6626_,
        v_prio_6627_,
        v_sync_boxed_6630_,
        v_x_6629_,
    );
    return v_res_6631_;
}
pub unsafe fn l_Std_Async_MaybeTask_bind___redArg___lam__0(
    mut v_f_6632_: *mut LeanObject,
    mut v_x_6633_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6634_: *mut LeanObject = core::ptr::null_mut();
    v___x_6634_ = lean_apply_1(v_f_6632_, v_x_6633_);
    if lean_obj_tag(v___x_6634_) == 0 {
        let mut v_a_6635_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6636_: *mut LeanObject = core::ptr::null_mut();
        v_a_6635_ = lean_ctor_get(v___x_6634_, 0);
        lean_inc(v_a_6635_);
        lean_dec_ref_known(v___x_6634_, 1);
        v___x_6636_ = lean_task_pure(v_a_6635_);
        return v___x_6636_;
    } else {
        let mut v_a_6637_: *mut LeanObject = core::ptr::null_mut();
        v_a_6637_ = lean_ctor_get(v___x_6634_, 0);
        lean_inc_ref(v_a_6637_);
        lean_dec_ref_known(v___x_6634_, 1);
        return v_a_6637_;
    }
}
pub unsafe fn l_Std_Async_MaybeTask_bind___redArg(
    mut v_t_6638_: *mut LeanObject,
    mut v_f_6639_: *mut LeanObject,
    mut v_prio_6640_: *mut LeanObject,
    mut v_sync_6641_: u8,
) -> *mut LeanObject {
    let mut v_a_6642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6647_: u8 = 0;
    let mut v___f_6648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6653_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_6638_) == 0 {
                    lean_dec(v_prio_6640_);
                    v_a_6642_ = lean_ctor_get(v_t_6638_, 0);
                    lean_inc(v_a_6642_);
                    lean_dec_ref_known(v_t_6638_, 1);
                    v___x_6643_ = lean_apply_1(v_f_6639_, v_a_6642_);
                    return v___x_6643_;
                } else {
                    v_a_6644_ = lean_ctor_get(v_t_6638_, 0);
                    v_isSharedCheck_6653_ = (!lean_is_exclusive(v_t_6638_)) as u8;
                    if v_isSharedCheck_6653_ == 0 {
                        v___x_6646_ = v_t_6638_;
                        v_isShared_6647_ = v_isSharedCheck_6653_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6644_);
                        lean_dec(v_t_6638_);
                        v___x_6646_ = lean_box(0);
                        v_isShared_6647_ = v_isSharedCheck_6653_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___f_6648_ = lean_alloc_closure(
                    l_Std_Async_MaybeTask_bind___redArg___lam__0 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_6648_, 0, v_f_6639_);
                v___x_6649_ = lean_task_bind(v_a_6644_, v___f_6648_, v_prio_6640_, v_sync_6641_);
                if v_isShared_6647_ == 0 {
                    lean_ctor_set(v___x_6646_, 0, v___x_6649_);
                    v___x_6651_ = v___x_6646_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6652_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6652_, 0, v___x_6649_);
                    v___x_6651_ = v_reuseFailAlloc_6652_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6651_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_MaybeTask_bind___redArg___boxed(
    mut v_t_6654_: *mut LeanObject,
    mut v_f_6655_: *mut LeanObject,
    mut v_prio_6656_: *mut LeanObject,
    mut v_sync_6657_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sync_boxed_6658_: u8 = 0;
    let mut v_res_6659_: *mut LeanObject = core::ptr::null_mut();
    v_sync_boxed_6658_ = (lean_unbox(v_sync_6657_) as u8);
    v_res_6659_ =
        l_Std_Async_MaybeTask_bind___redArg(v_t_6654_, v_f_6655_, v_prio_6656_, v_sync_boxed_6658_);
    return v_res_6659_;
}
pub unsafe fn l_Std_Async_MaybeTask_bind(
    mut v_00_u03b1_6660_: *mut LeanObject,
    mut v_00_u03b2_6661_: *mut LeanObject,
    mut v_t_6662_: *mut LeanObject,
    mut v_f_6663_: *mut LeanObject,
    mut v_prio_6664_: *mut LeanObject,
    mut v_sync_6665_: u8,
) -> *mut LeanObject {
    let mut v_a_6666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6671_: u8 = 0;
    let mut v___f_6672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6677_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_6662_) == 0 {
                    lean_dec(v_prio_6664_);
                    v_a_6666_ = lean_ctor_get(v_t_6662_, 0);
                    lean_inc(v_a_6666_);
                    lean_dec_ref_known(v_t_6662_, 1);
                    v___x_6667_ = lean_apply_1(v_f_6663_, v_a_6666_);
                    return v___x_6667_;
                } else {
                    v_a_6668_ = lean_ctor_get(v_t_6662_, 0);
                    v_isSharedCheck_6677_ = (!lean_is_exclusive(v_t_6662_)) as u8;
                    if v_isSharedCheck_6677_ == 0 {
                        v___x_6670_ = v_t_6662_;
                        v_isShared_6671_ = v_isSharedCheck_6677_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6668_);
                        lean_dec(v_t_6662_);
                        v___x_6670_ = lean_box(0);
                        v_isShared_6671_ = v_isSharedCheck_6677_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___f_6672_ = lean_alloc_closure(
                    l_Std_Async_MaybeTask_bind___redArg___lam__0 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_6672_, 0, v_f_6663_);
                v___x_6673_ = lean_task_bind(v_a_6668_, v___f_6672_, v_prio_6664_, v_sync_6665_);
                if v_isShared_6671_ == 0 {
                    lean_ctor_set(v___x_6670_, 0, v___x_6673_);
                    v___x_6675_ = v___x_6670_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6676_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6676_, 0, v___x_6673_);
                    v___x_6675_ = v_reuseFailAlloc_6676_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6675_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_MaybeTask_bind___boxed(
    mut v_00_u03b1_6678_: *mut LeanObject,
    mut v_00_u03b2_6679_: *mut LeanObject,
    mut v_t_6680_: *mut LeanObject,
    mut v_f_6681_: *mut LeanObject,
    mut v_prio_6682_: *mut LeanObject,
    mut v_sync_6683_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sync_boxed_6684_: u8 = 0;
    let mut v_res_6685_: *mut LeanObject = core::ptr::null_mut();
    v_sync_boxed_6684_ = (lean_unbox(v_sync_6683_) as u8);
    v_res_6685_ = l_Std_Async_MaybeTask_bind(
        v_00_u03b1_6678_,
        v_00_u03b2_6679_,
        v_t_6680_,
        v_f_6681_,
        v_prio_6682_,
        v_sync_boxed_6684_,
    );
    return v_res_6685_;
}
pub unsafe fn l_Std_Async_MaybeTask_joinTask___redArg___lam__0(
    mut v_x_6686_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_6686_) == 0 {
        let mut v_a_6687_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6688_: *mut LeanObject = core::ptr::null_mut();
        v_a_6687_ = lean_ctor_get(v_x_6686_, 0);
        lean_inc(v_a_6687_);
        lean_dec_ref_known(v_x_6686_, 1);
        v___x_6688_ = lean_task_pure(v_a_6687_);
        return v___x_6688_;
    } else {
        let mut v_a_6689_: *mut LeanObject = core::ptr::null_mut();
        v_a_6689_ = lean_ctor_get(v_x_6686_, 0);
        lean_inc_ref(v_a_6689_);
        lean_dec_ref_known(v_x_6686_, 1);
        return v_a_6689_;
    }
}
pub unsafe fn l_Std_Async_MaybeTask_joinTask___redArg(
    mut v_t_6691_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_6692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6694_: u8 = 0;
    let mut v___x_6695_: *mut LeanObject = core::ptr::null_mut();
    v___f_6692_ = l_Std_Async_MaybeTask_joinTask___redArg___closed__0;
    v___x_6693_ = lean_unsigned_to_nat(0);
    v___x_6694_ = 1;
    v___x_6695_ = lean_task_bind(v_t_6691_, v___f_6692_, v___x_6693_, v___x_6694_);
    return v___x_6695_;
}
pub unsafe fn l_Std_Async_MaybeTask_joinTask(
    mut v_00_u03b1_6696_: *mut LeanObject,
    mut v_t_6697_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_6698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6700_: u8 = 0;
    let mut v___x_6701_: *mut LeanObject = core::ptr::null_mut();
    v___f_6698_ = l_Std_Async_MaybeTask_joinTask___redArg___closed__0;
    v___x_6699_ = lean_unsigned_to_nat(0);
    v___x_6700_ = 1;
    v___x_6701_ = lean_task_bind(v_t_6697_, v___f_6698_, v___x_6699_, v___x_6700_);
    return v___x_6701_;
}
pub unsafe fn l_Std_Async_MaybeTask_instFunctor___lam__0(
    mut v_00_u03b1_6702_: *mut LeanObject,
    mut v_00_u03b2_6703_: *mut LeanObject,
    mut v_f_6704_: *mut LeanObject,
    mut v___y_6705_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_6706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6709_: u8 = 0;
    let mut v___x_6710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6714_: u8 = 0;
    let mut v_a_6715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6718_: u8 = 0;
    let mut v___x_6719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6720_: u8 = 0;
    let mut v___x_6721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6725_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v___y_6705_) == 0 {
                    v_a_6706_ = lean_ctor_get(v___y_6705_, 0);
                    v_isSharedCheck_6714_ = (!lean_is_exclusive(v___y_6705_)) as u8;
                    if v_isSharedCheck_6714_ == 0 {
                        v___x_6708_ = v___y_6705_;
                        v_isShared_6709_ = v_isSharedCheck_6714_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6706_);
                        lean_dec(v___y_6705_);
                        v___x_6708_ = lean_box(0);
                        v_isShared_6709_ = v_isSharedCheck_6714_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6715_ = lean_ctor_get(v___y_6705_, 0);
                    v_isSharedCheck_6725_ = (!lean_is_exclusive(v___y_6705_)) as u8;
                    if v_isSharedCheck_6725_ == 0 {
                        v___x_6717_ = v___y_6705_;
                        v_isShared_6718_ = v_isSharedCheck_6725_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6715_);
                        lean_dec(v___y_6705_);
                        v___x_6717_ = lean_box(0);
                        v_isShared_6718_ = v_isSharedCheck_6725_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6710_ = lean_apply_1(v_f_6704_, v_a_6706_);
                if v_isShared_6709_ == 0 {
                    lean_ctor_set(v___x_6708_, 0, v___x_6710_);
                    v___x_6712_ = v___x_6708_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6713_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6713_, 0, v___x_6710_);
                    v___x_6712_ = v_reuseFailAlloc_6713_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6712_;
            }
            3 => {
                v___x_6719_ = lean_unsigned_to_nat(0);
                v___x_6720_ = 0;
                v___x_6721_ = lean_task_map(v_f_6704_, v_a_6715_, v___x_6719_, v___x_6720_);
                if v_isShared_6718_ == 0 {
                    lean_ctor_set(v___x_6717_, 0, v___x_6721_);
                    v___x_6723_ = v___x_6717_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6724_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6724_, 0, v___x_6721_);
                    v___x_6723_ = v_reuseFailAlloc_6724_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6723_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_MaybeTask_instFunctor___lam__1(
    mut v___f_6726_: *mut LeanObject,
    mut v_00_u03b1_6727_: *mut LeanObject,
    mut v_00_u03b2_6728_: *mut LeanObject,
    mut v___y_6729_: *mut LeanObject,
    mut v___y_6730_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6732_: *mut LeanObject = core::ptr::null_mut();
    v___x_6731_ = lean_alloc_closure(l_Function_const___boxed as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___x_6731_, 0, lean_box(0));
    lean_closure_set(v___x_6731_, 1, lean_box(0));
    lean_closure_set(v___x_6731_, 2, v___y_6729_);
    v___x_6732_ = lean_apply_4(
        v___f_6726_,
        lean_box(0),
        lean_box(0),
        v___x_6731_,
        v___y_6730_,
    );
    return v___x_6732_;
}
pub unsafe fn l_Std_Async_MaybeTask_instMonad___lam__0(
    mut v_00_u03b1_6740_: *mut LeanObject,
    mut v___y_6741_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6742_: *mut LeanObject = core::ptr::null_mut();
    v___x_6742_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_6742_, 0, v___y_6741_);
    return v___x_6742_;
}
pub unsafe fn l_Std_Async_MaybeTask_instMonad___lam__1(
    mut v_x_6743_: *mut LeanObject,
    mut v_y_6744_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6750_: u8 = 0;
    let mut v___x_6751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6755_: u8 = 0;
    let mut v_a_6756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6759_: u8 = 0;
    let mut v___x_6760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6761_: u8 = 0;
    let mut v___x_6762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6766_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6745_ = lean_box(0);
                v___x_6746_ = lean_apply_1(v_x_6743_, v___x_6745_);
                if lean_obj_tag(v___x_6746_) == 0 {
                    v_a_6747_ = lean_ctor_get(v___x_6746_, 0);
                    v_isSharedCheck_6755_ = (!lean_is_exclusive(v___x_6746_)) as u8;
                    if v_isSharedCheck_6755_ == 0 {
                        v___x_6749_ = v___x_6746_;
                        v_isShared_6750_ = v_isSharedCheck_6755_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6747_);
                        lean_dec(v___x_6746_);
                        v___x_6749_ = lean_box(0);
                        v_isShared_6750_ = v_isSharedCheck_6755_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6756_ = lean_ctor_get(v___x_6746_, 0);
                    v_isSharedCheck_6766_ = (!lean_is_exclusive(v___x_6746_)) as u8;
                    if v_isSharedCheck_6766_ == 0 {
                        v___x_6758_ = v___x_6746_;
                        v_isShared_6759_ = v_isSharedCheck_6766_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6756_);
                        lean_dec(v___x_6746_);
                        v___x_6758_ = lean_box(0);
                        v_isShared_6759_ = v_isSharedCheck_6766_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6751_ = lean_apply_1(v_y_6744_, v_a_6747_);
                if v_isShared_6750_ == 0 {
                    lean_ctor_set(v___x_6749_, 0, v___x_6751_);
                    v___x_6753_ = v___x_6749_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6754_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6754_, 0, v___x_6751_);
                    v___x_6753_ = v_reuseFailAlloc_6754_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6753_;
            }
            3 => {
                v___x_6760_ = lean_unsigned_to_nat(0);
                v___x_6761_ = 0;
                v___x_6762_ = lean_task_map(v_y_6744_, v_a_6756_, v___x_6760_, v___x_6761_);
                if v_isShared_6759_ == 0 {
                    lean_ctor_set(v___x_6758_, 0, v___x_6762_);
                    v___x_6764_ = v___x_6758_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6765_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6765_, 0, v___x_6762_);
                    v___x_6764_ = v_reuseFailAlloc_6765_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6764_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_MaybeTask_instMonad___lam__2(
    mut v___f_6767_: *mut LeanObject,
    mut v_x_6768_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6769_: *mut LeanObject = core::ptr::null_mut();
    v___x_6769_ = lean_apply_1(v___f_6767_, v_x_6768_);
    if lean_obj_tag(v___x_6769_) == 0 {
        let mut v_a_6770_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6771_: *mut LeanObject = core::ptr::null_mut();
        v_a_6770_ = lean_ctor_get(v___x_6769_, 0);
        lean_inc(v_a_6770_);
        lean_dec_ref_known(v___x_6769_, 1);
        v___x_6771_ = lean_task_pure(v_a_6770_);
        return v___x_6771_;
    } else {
        let mut v_a_6772_: *mut LeanObject = core::ptr::null_mut();
        v_a_6772_ = lean_ctor_get(v___x_6769_, 0);
        lean_inc_ref(v_a_6772_);
        lean_dec_ref_known(v___x_6769_, 1);
        return v_a_6772_;
    }
}
pub unsafe fn l_Std_Async_MaybeTask_instMonad___lam__3(
    mut v_00_u03b1_6773_: *mut LeanObject,
    mut v_00_u03b2_6774_: *mut LeanObject,
    mut v_f_6775_: *mut LeanObject,
    mut v_x_6776_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_6777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6783_: u8 = 0;
    let mut v___f_6784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6786_: u8 = 0;
    let mut v___x_6787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6791_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_x_6776_);
                v___f_6777_ = lean_alloc_closure(
                    l_Std_Async_MaybeTask_instMonad___lam__1 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_6777_, 0, v_x_6776_);
                if lean_obj_tag(v_f_6775_) == 0 {
                    lean_dec_ref(v___f_6777_);
                    v_a_6778_ = lean_ctor_get(v_f_6775_, 0);
                    lean_inc(v_a_6778_);
                    lean_dec_ref_known(v_f_6775_, 1);
                    v___x_6779_ = l_Std_Async_MaybeTask_instMonad___lam__1(v_x_6776_, v_a_6778_);
                    return v___x_6779_;
                } else {
                    lean_dec_ref(v_x_6776_);
                    v_a_6780_ = lean_ctor_get(v_f_6775_, 0);
                    v_isSharedCheck_6791_ = (!lean_is_exclusive(v_f_6775_)) as u8;
                    if v_isSharedCheck_6791_ == 0 {
                        v___x_6782_ = v_f_6775_;
                        v_isShared_6783_ = v_isSharedCheck_6791_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6780_);
                        lean_dec(v_f_6775_);
                        v___x_6782_ = lean_box(0);
                        v_isShared_6783_ = v_isSharedCheck_6791_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___f_6784_ = lean_alloc_closure(
                    l_Std_Async_MaybeTask_instMonad___lam__2 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_6784_, 0, v___f_6777_);
                v___x_6785_ = lean_unsigned_to_nat(0);
                v___x_6786_ = 0;
                v___x_6787_ = lean_task_bind(v_a_6780_, v___f_6784_, v___x_6785_, v___x_6786_);
                if v_isShared_6783_ == 0 {
                    lean_ctor_set(v___x_6782_, 0, v___x_6787_);
                    v___x_6789_ = v___x_6782_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6790_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6790_, 0, v___x_6787_);
                    v___x_6789_ = v_reuseFailAlloc_6790_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6789_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_MaybeTask_instMonad___lam__5(
    mut v_00_u03b1_6792_: *mut LeanObject,
    mut v_00_u03b2_6793_: *mut LeanObject,
    mut v_t_6794_: *mut LeanObject,
    mut v_f_6795_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_6796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6801_: u8 = 0;
    let mut v___f_6802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6804_: u8 = 0;
    let mut v___x_6805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6809_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_6794_) == 0 {
                    v_a_6796_ = lean_ctor_get(v_t_6794_, 0);
                    lean_inc(v_a_6796_);
                    lean_dec_ref_known(v_t_6794_, 1);
                    v___x_6797_ = lean_apply_1(v_f_6795_, v_a_6796_);
                    return v___x_6797_;
                } else {
                    v_a_6798_ = lean_ctor_get(v_t_6794_, 0);
                    v_isSharedCheck_6809_ = (!lean_is_exclusive(v_t_6794_)) as u8;
                    if v_isSharedCheck_6809_ == 0 {
                        v___x_6800_ = v_t_6794_;
                        v_isShared_6801_ = v_isSharedCheck_6809_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6798_);
                        lean_dec(v_t_6794_);
                        v___x_6800_ = lean_box(0);
                        v_isShared_6801_ = v_isSharedCheck_6809_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___f_6802_ = lean_alloc_closure(
                    l_Std_Async_MaybeTask_bind___redArg___lam__0 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_6802_, 0, v_f_6795_);
                v___x_6803_ = lean_unsigned_to_nat(0);
                v___x_6804_ = 0;
                v___x_6805_ = lean_task_bind(v_a_6798_, v___f_6802_, v___x_6803_, v___x_6804_);
                if v_isShared_6801_ == 0 {
                    lean_ctor_set(v___x_6800_, 0, v___x_6805_);
                    v___x_6807_ = v___x_6800_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6808_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6808_, 0, v___x_6805_);
                    v___x_6807_ = v_reuseFailAlloc_6808_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6807_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_MaybeTask_instMonad___lam__4(
    mut v_a_6810_: *mut LeanObject,
    mut v_x_6811_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6812_: *mut LeanObject = core::ptr::null_mut();
    v___x_6812_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_6812_, 0, v_a_6810_);
    return v___x_6812_;
}
pub unsafe fn l_Std_Async_MaybeTask_instMonad___lam__4___boxed(
    mut v_a_6813_: *mut LeanObject,
    mut v_x_6814_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6815_: *mut LeanObject = core::ptr::null_mut();
    v_res_6815_ = l_Std_Async_MaybeTask_instMonad___lam__4(v_a_6813_, v_x_6814_);
    lean_dec(v_x_6814_);
    return v_res_6815_;
}
pub unsafe fn l_Std_Async_MaybeTask_instMonad___lam__6(
    mut v_y_6816_: *mut LeanObject,
    mut v___f_6817_: *mut LeanObject,
    mut v_a_6818_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_6819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6822_: *mut LeanObject = core::ptr::null_mut();
    v___f_6819_ = lean_alloc_closure(
        l_Std_Async_MaybeTask_instMonad___lam__4___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_6819_, 0, v_a_6818_);
    v___x_6820_ = lean_box(0);
    v___x_6821_ = lean_apply_1(v_y_6816_, v___x_6820_);
    v___x_6822_ = lean_apply_4(
        v___f_6817_,
        lean_box(0),
        lean_box(0),
        v___x_6821_,
        v___f_6819_,
    );
    return v___x_6822_;
}
pub unsafe fn l_Std_Async_MaybeTask_instMonad___lam__7(
    mut v___f_6823_: *mut LeanObject,
    mut v_00_u03b1_6824_: *mut LeanObject,
    mut v_00_u03b2_6825_: *mut LeanObject,
    mut v_x_6826_: *mut LeanObject,
    mut v_y_6827_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_6828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6829_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v___f_6823_);
    v___f_6828_ = lean_alloc_closure(
        l_Std_Async_MaybeTask_instMonad___lam__6 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_6828_, 0, v_y_6827_);
    lean_closure_set(v___f_6828_, 1, v___f_6823_);
    v___x_6829_ = lean_apply_4(
        v___f_6823_,
        lean_box(0),
        lean_box(0),
        v_x_6826_,
        v___f_6828_,
    );
    return v___x_6829_;
}
pub unsafe fn l_Std_Async_MaybeTask_instMonad___lam__8(
    mut v_y_6830_: *mut LeanObject,
    mut v_x_6831_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6833_: *mut LeanObject = core::ptr::null_mut();
    v___x_6832_ = lean_box(0);
    v___x_6833_ = lean_apply_1(v_y_6830_, v___x_6832_);
    return v___x_6833_;
}
pub unsafe fn l_Std_Async_MaybeTask_instMonad___lam__8___boxed(
    mut v_y_6834_: *mut LeanObject,
    mut v_x_6835_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6836_: *mut LeanObject = core::ptr::null_mut();
    v_res_6836_ = l_Std_Async_MaybeTask_instMonad___lam__8(v_y_6834_, v_x_6835_);
    lean_dec(v_x_6835_);
    return v_res_6836_;
}
pub unsafe fn l_Std_Async_MaybeTask_instMonad___lam__9(
    mut v___f_6837_: *mut LeanObject,
    mut v_x_6838_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6839_: *mut LeanObject = core::ptr::null_mut();
    v___x_6839_ = lean_apply_1(v___f_6837_, v_x_6838_);
    if lean_obj_tag(v___x_6839_) == 0 {
        let mut v_a_6840_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6841_: *mut LeanObject = core::ptr::null_mut();
        v_a_6840_ = lean_ctor_get(v___x_6839_, 0);
        lean_inc(v_a_6840_);
        lean_dec_ref_known(v___x_6839_, 1);
        v___x_6841_ = lean_task_pure(v_a_6840_);
        return v___x_6841_;
    } else {
        let mut v_a_6842_: *mut LeanObject = core::ptr::null_mut();
        v_a_6842_ = lean_ctor_get(v___x_6839_, 0);
        lean_inc_ref(v_a_6842_);
        lean_dec_ref_known(v___x_6839_, 1);
        return v_a_6842_;
    }
}
pub unsafe fn l_Std_Async_MaybeTask_instMonad___lam__10(
    mut v_00_u03b1_6843_: *mut LeanObject,
    mut v_00_u03b2_6844_: *mut LeanObject,
    mut v_x_6845_: *mut LeanObject,
    mut v_y_6846_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_6847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6853_: u8 = 0;
    let mut v___f_6854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6856_: u8 = 0;
    let mut v___x_6857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6861_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_y_6846_);
                v___f_6847_ = lean_alloc_closure(
                    l_Std_Async_MaybeTask_instMonad___lam__8___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_6847_, 0, v_y_6846_);
                if lean_obj_tag(v_x_6845_) == 0 {
                    lean_dec_ref(v___f_6847_);
                    v_a_6848_ = lean_ctor_get(v_x_6845_, 0);
                    lean_inc(v_a_6848_);
                    lean_dec_ref_known(v_x_6845_, 1);
                    v___x_6849_ = l_Std_Async_MaybeTask_instMonad___lam__8(v_y_6846_, v_a_6848_);
                    lean_dec(v_a_6848_);
                    return v___x_6849_;
                } else {
                    lean_dec_ref(v_y_6846_);
                    v_a_6850_ = lean_ctor_get(v_x_6845_, 0);
                    v_isSharedCheck_6861_ = (!lean_is_exclusive(v_x_6845_)) as u8;
                    if v_isSharedCheck_6861_ == 0 {
                        v___x_6852_ = v_x_6845_;
                        v_isShared_6853_ = v_isSharedCheck_6861_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6850_);
                        lean_dec(v_x_6845_);
                        v___x_6852_ = lean_box(0);
                        v_isShared_6853_ = v_isSharedCheck_6861_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___f_6854_ = lean_alloc_closure(
                    l_Std_Async_MaybeTask_instMonad___lam__9 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_6854_, 0, v___f_6847_);
                v___x_6855_ = lean_unsigned_to_nat(0);
                v___x_6856_ = 0;
                v___x_6857_ = lean_task_bind(v_a_6850_, v___f_6854_, v___x_6855_, v___x_6856_);
                if v_isShared_6853_ == 0 {
                    lean_ctor_set(v___x_6852_, 0, v___x_6857_);
                    v___x_6859_ = v___x_6852_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6860_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6860_, 0, v___x_6857_);
                    v___x_6859_ = v_reuseFailAlloc_6860_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6859_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_BaseAsync_mk___redArg(mut v_x_6878_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_6880_: *mut LeanObject = core::ptr::null_mut();
    v___x_6880_ = lean_apply_1(v_x_6878_, lean_box(0));
    return v___x_6880_;
}
pub unsafe fn l_Std_Async_BaseAsync_mk___redArg___boxed(
    mut v_x_6881_: *mut LeanObject,
    mut v_a_6882_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6883_: *mut LeanObject = core::ptr::null_mut();
    v_res_6883_ = l_Std_Async_BaseAsync_mk___redArg(v_x_6881_);
    return v_res_6883_;
}
pub unsafe fn l_Std_Async_BaseAsync_mk(
    mut v_00_u03b1_6884_: *mut LeanObject,
    mut v_x_6885_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6887_: *mut LeanObject = core::ptr::null_mut();
    v___x_6887_ = lean_apply_1(v_x_6885_, lean_box(0));
    return v___x_6887_;
}
pub unsafe fn l_Std_Async_BaseAsync_mk___boxed(
    mut v_00_u03b1_6888_: *mut LeanObject,
    mut v_x_6889_: *mut LeanObject,
    mut v_a_6890_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6891_: *mut LeanObject = core::ptr::null_mut();
    v_res_6891_ = l_Std_Async_BaseAsync_mk(v_00_u03b1_6888_, v_x_6889_);
    return v_res_6891_;
}
pub unsafe fn l_Std_Async_BaseAsync_toRawBaseIO___redArg(
    mut v_x_6892_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6894_: *mut LeanObject = core::ptr::null_mut();
    v___x_6894_ = lean_apply_1(v_x_6892_, lean_box(0));
    return v___x_6894_;
}
pub unsafe fn l_Std_Async_BaseAsync_toRawBaseIO___redArg___boxed(
    mut v_x_6895_: *mut LeanObject,
    mut v_a_6896_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6897_: *mut LeanObject = core::ptr::null_mut();
    v_res_6897_ = l_Std_Async_BaseAsync_toRawBaseIO___redArg(v_x_6895_);
    return v_res_6897_;
}
pub unsafe fn l_Std_Async_BaseAsync_toRawBaseIO(
    mut v_00_u03b1_6898_: *mut LeanObject,
    mut v_x_6899_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6901_: *mut LeanObject = core::ptr::null_mut();
    v___x_6901_ = lean_apply_1(v_x_6899_, lean_box(0));
    return v___x_6901_;
}
pub unsafe fn l_Std_Async_BaseAsync_toRawBaseIO___boxed(
    mut v_00_u03b1_6902_: *mut LeanObject,
    mut v_x_6903_: *mut LeanObject,
    mut v_a_6904_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6905_: *mut LeanObject = core::ptr::null_mut();
    v_res_6905_ = l_Std_Async_BaseAsync_toRawBaseIO(v_00_u03b1_6902_, v_x_6903_);
    return v_res_6905_;
}
pub unsafe fn l_Std_Async_BaseAsync_toBaseIO___redArg(
    mut v_x_6906_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6908_: *mut LeanObject = core::ptr::null_mut();
    v___x_6908_ = lean_apply_1(v_x_6906_, lean_box(0));
    if lean_obj_tag(v___x_6908_) == 0 {
        let mut v_a_6909_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6910_: *mut LeanObject = core::ptr::null_mut();
        v_a_6909_ = lean_ctor_get(v___x_6908_, 0);
        lean_inc(v_a_6909_);
        lean_dec_ref_known(v___x_6908_, 1);
        v___x_6910_ = lean_task_pure(v_a_6909_);
        return v___x_6910_;
    } else {
        let mut v_a_6911_: *mut LeanObject = core::ptr::null_mut();
        v_a_6911_ = lean_ctor_get(v___x_6908_, 0);
        lean_inc_ref(v_a_6911_);
        lean_dec_ref_known(v___x_6908_, 1);
        return v_a_6911_;
    }
}
pub unsafe fn l_Std_Async_BaseAsync_toBaseIO___redArg___boxed(
    mut v_x_6912_: *mut LeanObject,
    mut v_a_6913_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6914_: *mut LeanObject = core::ptr::null_mut();
    v_res_6914_ = l_Std_Async_BaseAsync_toBaseIO___redArg(v_x_6912_);
    return v_res_6914_;
}
pub unsafe fn l_Std_Async_BaseAsync_toBaseIO(
    mut v_00_u03b1_6915_: *mut LeanObject,
    mut v_x_6916_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6918_: *mut LeanObject = core::ptr::null_mut();
    v___x_6918_ = lean_apply_1(v_x_6916_, lean_box(0));
    if lean_obj_tag(v___x_6918_) == 0 {
        let mut v_a_6919_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6920_: *mut LeanObject = core::ptr::null_mut();
        v_a_6919_ = lean_ctor_get(v___x_6918_, 0);
        lean_inc(v_a_6919_);
        lean_dec_ref_known(v___x_6918_, 1);
        v___x_6920_ = lean_task_pure(v_a_6919_);
        return v___x_6920_;
    } else {
        let mut v_a_6921_: *mut LeanObject = core::ptr::null_mut();
        v_a_6921_ = lean_ctor_get(v___x_6918_, 0);
        lean_inc_ref(v_a_6921_);
        lean_dec_ref_known(v___x_6918_, 1);
        return v_a_6921_;
    }
}
pub unsafe fn l_Std_Async_BaseAsync_toBaseIO___boxed(
    mut v_00_u03b1_6922_: *mut LeanObject,
    mut v_x_6923_: *mut LeanObject,
    mut v_a_6924_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6925_: *mut LeanObject = core::ptr::null_mut();
    v_res_6925_ = l_Std_Async_BaseAsync_toBaseIO(v_00_u03b1_6922_, v_x_6923_);
    return v_res_6925_;
}
pub unsafe fn l_Std_Async_BaseAsync_ofTask___redArg(
    mut v_x_6926_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6928_: *mut LeanObject = core::ptr::null_mut();
    v___x_6928_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_6928_, 0, v_x_6926_);
    return v___x_6928_;
}
pub unsafe fn l_Std_Async_BaseAsync_ofTask___redArg___boxed(
    mut v_x_6929_: *mut LeanObject,
    mut v_a_6930_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6931_: *mut LeanObject = core::ptr::null_mut();
    v_res_6931_ = l_Std_Async_BaseAsync_ofTask___redArg(v_x_6929_);
    return v_res_6931_;
}
pub unsafe fn l_Std_Async_BaseAsync_ofTask(
    mut v_00_u03b1_6932_: *mut LeanObject,
    mut v_x_6933_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6935_: *mut LeanObject = core::ptr::null_mut();
    v___x_6935_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_6935_, 0, v_x_6933_);
    return v___x_6935_;
}
pub unsafe fn l_Std_Async_BaseAsync_ofTask___boxed(
    mut v_00_u03b1_6936_: *mut LeanObject,
    mut v_x_6937_: *mut LeanObject,
    mut v_a_6938_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6939_: *mut LeanObject = core::ptr::null_mut();
    v_res_6939_ = l_Std_Async_BaseAsync_ofTask(v_00_u03b1_6936_, v_x_6937_);
    return v_res_6939_;
}
pub unsafe fn l_Std_Async_BaseAsync_pure___redArg(
    mut v_a_6940_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6942_: *mut LeanObject = core::ptr::null_mut();
    v___x_6942_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_6942_, 0, v_a_6940_);
    return v___x_6942_;
}
pub unsafe fn l_Std_Async_BaseAsync_pure___redArg___boxed(
    mut v_a_6943_: *mut LeanObject,
    mut v_a_6944_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6945_: *mut LeanObject = core::ptr::null_mut();
    v_res_6945_ = l_Std_Async_BaseAsync_pure___redArg(v_a_6943_);
    return v_res_6945_;
}
pub unsafe fn l_Std_Async_BaseAsync_pure(
    mut v_00_u03b1_6946_: *mut LeanObject,
    mut v_a_6947_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6949_: *mut LeanObject = core::ptr::null_mut();
    v___x_6949_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_6949_, 0, v_a_6947_);
    return v___x_6949_;
}
pub unsafe fn l_Std_Async_BaseAsync_pure___boxed(
    mut v_00_u03b1_6950_: *mut LeanObject,
    mut v_a_6951_: *mut LeanObject,
    mut v_a_6952_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6953_: *mut LeanObject = core::ptr::null_mut();
    v_res_6953_ = l_Std_Async_BaseAsync_pure(v_00_u03b1_6950_, v_a_6951_);
    return v_res_6953_;
}
pub unsafe fn l_Std_Async_BaseAsync_map___redArg(
    mut v_f_6954_: *mut LeanObject,
    mut v_self_6955_: *mut LeanObject,
    mut v_prio_6956_: *mut LeanObject,
    mut v_sync_6957_: u8,
) -> *mut LeanObject {
    let mut v___x_6959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6963_: u8 = 0;
    let mut v___x_6964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6968_: u8 = 0;
    let mut v_a_6969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6972_: u8 = 0;
    let mut v___x_6973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6977_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6959_ = lean_apply_1(v_self_6955_, lean_box(0));
                if lean_obj_tag(v___x_6959_) == 0 {
                    lean_dec(v_prio_6956_);
                    v_a_6960_ = lean_ctor_get(v___x_6959_, 0);
                    v_isSharedCheck_6968_ = (!lean_is_exclusive(v___x_6959_)) as u8;
                    if v_isSharedCheck_6968_ == 0 {
                        v___x_6962_ = v___x_6959_;
                        v_isShared_6963_ = v_isSharedCheck_6968_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6960_);
                        lean_dec(v___x_6959_);
                        v___x_6962_ = lean_box(0);
                        v_isShared_6963_ = v_isSharedCheck_6968_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6969_ = lean_ctor_get(v___x_6959_, 0);
                    v_isSharedCheck_6977_ = (!lean_is_exclusive(v___x_6959_)) as u8;
                    if v_isSharedCheck_6977_ == 0 {
                        v___x_6971_ = v___x_6959_;
                        v_isShared_6972_ = v_isSharedCheck_6977_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6969_);
                        lean_dec(v___x_6959_);
                        v___x_6971_ = lean_box(0);
                        v_isShared_6972_ = v_isSharedCheck_6977_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6964_ = lean_apply_1(v_f_6954_, v_a_6960_);
                if v_isShared_6963_ == 0 {
                    lean_ctor_set(v___x_6962_, 0, v___x_6964_);
                    v___x_6966_ = v___x_6962_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6967_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6967_, 0, v___x_6964_);
                    v___x_6966_ = v_reuseFailAlloc_6967_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6966_;
            }
            3 => {
                v___x_6973_ = lean_task_map(v_f_6954_, v_a_6969_, v_prio_6956_, v_sync_6957_);
                if v_isShared_6972_ == 0 {
                    lean_ctor_set(v___x_6971_, 0, v___x_6973_);
                    v___x_6975_ = v___x_6971_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6976_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6976_, 0, v___x_6973_);
                    v___x_6975_ = v_reuseFailAlloc_6976_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6975_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_BaseAsync_map___redArg___boxed(
    mut v_f_6978_: *mut LeanObject,
    mut v_self_6979_: *mut LeanObject,
    mut v_prio_6980_: *mut LeanObject,
    mut v_sync_6981_: *mut LeanObject,
    mut v_a_6982_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sync_boxed_6983_: u8 = 0;
    let mut v_res_6984_: *mut LeanObject = core::ptr::null_mut();
    v_sync_boxed_6983_ = (lean_unbox(v_sync_6981_) as u8);
    v_res_6984_ = l_Std_Async_BaseAsync_map___redArg(
        v_f_6978_,
        v_self_6979_,
        v_prio_6980_,
        v_sync_boxed_6983_,
    );
    return v_res_6984_;
}
pub unsafe fn l_Std_Async_BaseAsync_map(
    mut v_00_u03b1_6985_: *mut LeanObject,
    mut v_00_u03b2_6986_: *mut LeanObject,
    mut v_f_6987_: *mut LeanObject,
    mut v_self_6988_: *mut LeanObject,
    mut v_prio_6989_: *mut LeanObject,
    mut v_sync_6990_: u8,
) -> *mut LeanObject {
    let mut v___x_6992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6996_: u8 = 0;
    let mut v___x_6997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7001_: u8 = 0;
    let mut v_a_7002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7005_: u8 = 0;
    let mut v___x_7006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7010_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6992_ = lean_apply_1(v_self_6988_, lean_box(0));
                if lean_obj_tag(v___x_6992_) == 0 {
                    lean_dec(v_prio_6989_);
                    v_a_6993_ = lean_ctor_get(v___x_6992_, 0);
                    v_isSharedCheck_7001_ = (!lean_is_exclusive(v___x_6992_)) as u8;
                    if v_isSharedCheck_7001_ == 0 {
                        v___x_6995_ = v___x_6992_;
                        v_isShared_6996_ = v_isSharedCheck_7001_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6993_);
                        lean_dec(v___x_6992_);
                        v___x_6995_ = lean_box(0);
                        v_isShared_6996_ = v_isSharedCheck_7001_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_7002_ = lean_ctor_get(v___x_6992_, 0);
                    v_isSharedCheck_7010_ = (!lean_is_exclusive(v___x_6992_)) as u8;
                    if v_isSharedCheck_7010_ == 0 {
                        v___x_7004_ = v___x_6992_;
                        v_isShared_7005_ = v_isSharedCheck_7010_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_7002_);
                        lean_dec(v___x_6992_);
                        v___x_7004_ = lean_box(0);
                        v_isShared_7005_ = v_isSharedCheck_7010_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6997_ = lean_apply_1(v_f_6987_, v_a_6993_);
                if v_isShared_6996_ == 0 {
                    lean_ctor_set(v___x_6995_, 0, v___x_6997_);
                    v___x_6999_ = v___x_6995_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7000_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7000_, 0, v___x_6997_);
                    v___x_6999_ = v_reuseFailAlloc_7000_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6999_;
            }
            3 => {
                v___x_7006_ = lean_task_map(v_f_6987_, v_a_7002_, v_prio_6989_, v_sync_6990_);
                if v_isShared_7005_ == 0 {
                    lean_ctor_set(v___x_7004_, 0, v___x_7006_);
                    v___x_7008_ = v___x_7004_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7009_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7009_, 0, v___x_7006_);
                    v___x_7008_ = v_reuseFailAlloc_7009_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7008_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_BaseAsync_map___boxed(
    mut v_00_u03b1_7011_: *mut LeanObject,
    mut v_00_u03b2_7012_: *mut LeanObject,
    mut v_f_7013_: *mut LeanObject,
    mut v_self_7014_: *mut LeanObject,
    mut v_prio_7015_: *mut LeanObject,
    mut v_sync_7016_: *mut LeanObject,
    mut v_a_7017_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sync_boxed_7018_: u8 = 0;
    let mut v_res_7019_: *mut LeanObject = core::ptr::null_mut();
    v_sync_boxed_7018_ = (lean_unbox(v_sync_7016_) as u8);
    v_res_7019_ = l_Std_Async_BaseAsync_map(
        v_00_u03b1_7011_,
        v_00_u03b2_7012_,
        v_f_7013_,
        v_self_7014_,
        v_prio_7015_,
        v_sync_boxed_7018_,
    );
    return v_res_7019_;
}
pub unsafe fn l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg___lam__0(
    mut v_f_7020_: *mut LeanObject,
    mut v_a_7021_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7023_: *mut LeanObject = core::ptr::null_mut();
    v___x_7023_ = lean_apply_2(v_f_7020_, v_a_7021_, lean_box(0));
    if lean_obj_tag(v___x_7023_) == 0 {
        let mut v_a_7024_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7025_: *mut LeanObject = core::ptr::null_mut();
        v_a_7024_ = lean_ctor_get(v___x_7023_, 0);
        lean_inc(v_a_7024_);
        lean_dec_ref_known(v___x_7023_, 1);
        v___x_7025_ = lean_task_pure(v_a_7024_);
        return v___x_7025_;
    } else {
        let mut v_a_7026_: *mut LeanObject = core::ptr::null_mut();
        v_a_7026_ = lean_ctor_get(v___x_7023_, 0);
        lean_inc_ref(v_a_7026_);
        lean_dec_ref_known(v___x_7023_, 1);
        return v_a_7026_;
    }
}
pub unsafe fn l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg___lam__0___boxed(
    mut v_f_7027_: *mut LeanObject,
    mut v_a_7028_: *mut LeanObject,
    mut v___y_7029_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7030_: *mut LeanObject = core::ptr::null_mut();
    v_res_7030_ =
        l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg___lam__0(
            v_f_7027_, v_a_7028_,
        );
    return v_res_7030_;
}
pub unsafe fn l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(
    mut v_prio_7031_: *mut LeanObject,
    mut v_sync_7032_: u8,
    mut v_t_7033_: *mut LeanObject,
    mut v_f_7034_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_7036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7041_: u8 = 0;
    let mut v___f_7042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7047_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_7033_) == 0 {
                    lean_dec(v_prio_7031_);
                    v_a_7036_ = lean_ctor_get(v_t_7033_, 0);
                    lean_inc(v_a_7036_);
                    lean_dec_ref_known(v_t_7033_, 1);
                    v___x_7037_ = lean_apply_2(v_f_7034_, v_a_7036_, lean_box(0));
                    return v___x_7037_;
                } else {
                    v_a_7038_ = lean_ctor_get(v_t_7033_, 0);
                    v_isSharedCheck_7047_ = (!lean_is_exclusive(v_t_7033_)) as u8;
                    if v_isSharedCheck_7047_ == 0 {
                        v___x_7040_ = v_t_7033_;
                        v_isShared_7041_ = v_isSharedCheck_7047_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7038_);
                        lean_dec(v_t_7033_);
                        v___x_7040_ = lean_box(0);
                        v_isShared_7041_ = v_isSharedCheck_7047_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___f_7042_ = lean_alloc_closure(l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg___lam__0___boxed as *mut core::ffi::c_void, 3, 1);
                lean_closure_set(v___f_7042_, 0, v_f_7034_);
                v___x_7043_ = lean_io_bind_task(v_a_7038_, v___f_7042_, v_prio_7031_, v_sync_7032_);
                if v_isShared_7041_ == 0 {
                    lean_ctor_set(v___x_7040_, 0, v___x_7043_);
                    v___x_7045_ = v___x_7040_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7046_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7046_, 0, v___x_7043_);
                    v___x_7045_ = v_reuseFailAlloc_7046_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7045_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg___boxed(
    mut v_prio_7048_: *mut LeanObject,
    mut v_sync_7049_: *mut LeanObject,
    mut v_t_7050_: *mut LeanObject,
    mut v_f_7051_: *mut LeanObject,
    mut v_a_7052_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sync_boxed_7053_: u8 = 0;
    let mut v_res_7054_: *mut LeanObject = core::ptr::null_mut();
    v_sync_boxed_7053_ = (lean_unbox(v_sync_7049_) as u8);
    v_res_7054_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(
        v_prio_7048_,
        v_sync_boxed_7053_,
        v_t_7050_,
        v_f_7051_,
    );
    return v_res_7054_;
}
pub unsafe fn l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
    mut v_00_u03b1_7055_: *mut LeanObject,
    mut v_00_u03b2_7056_: *mut LeanObject,
    mut v_prio_7057_: *mut LeanObject,
    mut v_sync_7058_: u8,
    mut v_t_7059_: *mut LeanObject,
    mut v_f_7060_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7062_: *mut LeanObject = core::ptr::null_mut();
    v___x_7062_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(
        v_prio_7057_,
        v_sync_7058_,
        v_t_7059_,
        v_f_7060_,
    );
    return v___x_7062_;
}
pub unsafe fn l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___boxed(
    mut v_00_u03b1_7063_: *mut LeanObject,
    mut v_00_u03b2_7064_: *mut LeanObject,
    mut v_prio_7065_: *mut LeanObject,
    mut v_sync_7066_: *mut LeanObject,
    mut v_t_7067_: *mut LeanObject,
    mut v_f_7068_: *mut LeanObject,
    mut v_a_7069_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sync_boxed_7070_: u8 = 0;
    let mut v_res_7071_: *mut LeanObject = core::ptr::null_mut();
    v_sync_boxed_7070_ = (lean_unbox(v_sync_7066_) as u8);
    v_res_7071_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        v_00_u03b1_7063_,
        v_00_u03b2_7064_,
        v_prio_7065_,
        v_sync_boxed_7070_,
        v_t_7067_,
        v_f_7068_,
    );
    return v_res_7071_;
}
pub unsafe fn l_Std_Async_BaseAsync_bind___redArg(
    mut v_self_7072_: *mut LeanObject,
    mut v_f_7073_: *mut LeanObject,
    mut v_prio_7074_: *mut LeanObject,
    mut v_sync_7075_: u8,
) -> *mut LeanObject {
    let mut v___x_7077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7078_: *mut LeanObject = core::ptr::null_mut();
    v___x_7077_ = lean_apply_1(v_self_7072_, lean_box(0));
    v___x_7078_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(
        v_prio_7074_,
        v_sync_7075_,
        v___x_7077_,
        v_f_7073_,
    );
    return v___x_7078_;
}
pub unsafe fn l_Std_Async_BaseAsync_bind___redArg___boxed(
    mut v_self_7079_: *mut LeanObject,
    mut v_f_7080_: *mut LeanObject,
    mut v_prio_7081_: *mut LeanObject,
    mut v_sync_7082_: *mut LeanObject,
    mut v_a_7083_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sync_boxed_7084_: u8 = 0;
    let mut v_res_7085_: *mut LeanObject = core::ptr::null_mut();
    v_sync_boxed_7084_ = (lean_unbox(v_sync_7082_) as u8);
    v_res_7085_ = l_Std_Async_BaseAsync_bind___redArg(
        v_self_7079_,
        v_f_7080_,
        v_prio_7081_,
        v_sync_boxed_7084_,
    );
    return v_res_7085_;
}
pub unsafe fn l_Std_Async_BaseAsync_bind(
    mut v_00_u03b1_7086_: *mut LeanObject,
    mut v_00_u03b2_7087_: *mut LeanObject,
    mut v_self_7088_: *mut LeanObject,
    mut v_f_7089_: *mut LeanObject,
    mut v_prio_7090_: *mut LeanObject,
    mut v_sync_7091_: u8,
) -> *mut LeanObject {
    let mut v___x_7093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7094_: *mut LeanObject = core::ptr::null_mut();
    v___x_7093_ = lean_apply_1(v_self_7088_, lean_box(0));
    v___x_7094_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(
        v_prio_7090_,
        v_sync_7091_,
        v___x_7093_,
        v_f_7089_,
    );
    return v___x_7094_;
}
pub unsafe fn l_Std_Async_BaseAsync_bind___boxed(
    mut v_00_u03b1_7095_: *mut LeanObject,
    mut v_00_u03b2_7096_: *mut LeanObject,
    mut v_self_7097_: *mut LeanObject,
    mut v_f_7098_: *mut LeanObject,
    mut v_prio_7099_: *mut LeanObject,
    mut v_sync_7100_: *mut LeanObject,
    mut v_a_7101_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sync_boxed_7102_: u8 = 0;
    let mut v_res_7103_: *mut LeanObject = core::ptr::null_mut();
    v_sync_boxed_7102_ = (lean_unbox(v_sync_7100_) as u8);
    v_res_7103_ = l_Std_Async_BaseAsync_bind(
        v_00_u03b1_7095_,
        v_00_u03b2_7096_,
        v_self_7097_,
        v_f_7098_,
        v_prio_7099_,
        v_sync_boxed_7102_,
    );
    return v_res_7103_;
}
pub unsafe fn l_Std_Async_BaseAsync_lift___redArg(
    mut v_x_7104_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7107_: *mut LeanObject = core::ptr::null_mut();
    v___x_7106_ = lean_apply_1(v_x_7104_, lean_box(0));
    v___x_7107_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_7107_, 0, v___x_7106_);
    return v___x_7107_;
}
pub unsafe fn l_Std_Async_BaseAsync_lift___redArg___boxed(
    mut v_x_7108_: *mut LeanObject,
    mut v_a_7109_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7110_: *mut LeanObject = core::ptr::null_mut();
    v_res_7110_ = l_Std_Async_BaseAsync_lift___redArg(v_x_7108_);
    return v_res_7110_;
}
pub unsafe fn l_Std_Async_BaseAsync_lift(
    mut v_00_u03b1_7111_: *mut LeanObject,
    mut v_x_7112_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7115_: *mut LeanObject = core::ptr::null_mut();
    v___x_7114_ = lean_apply_1(v_x_7112_, lean_box(0));
    v___x_7115_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_7115_, 0, v___x_7114_);
    return v___x_7115_;
}
pub unsafe fn l_Std_Async_BaseAsync_lift___boxed(
    mut v_00_u03b1_7116_: *mut LeanObject,
    mut v_x_7117_: *mut LeanObject,
    mut v_a_7118_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7119_: *mut LeanObject = core::ptr::null_mut();
    v_res_7119_ = l_Std_Async_BaseAsync_lift(v_00_u03b1_7116_, v_x_7117_);
    return v_res_7119_;
}
pub unsafe fn l_Std_Async_BaseAsync_wait___redArg(
    mut v_self_7120_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7128_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7122_ = lean_apply_1(v_self_7120_, lean_box(0));
                if lean_obj_tag(v___x_7122_) == 0 {
                    v_a_7126_ = lean_ctor_get(v___x_7122_, 0);
                    lean_inc(v_a_7126_);
                    lean_dec_ref_known(v___x_7122_, 1);
                    v___x_7127_ = lean_task_pure(v_a_7126_);
                    v_val_7124_ = v___x_7127_;
                    state = 1;
                    continue;
                } else {
                    v_a_7128_ = lean_ctor_get(v___x_7122_, 0);
                    lean_inc_ref(v_a_7128_);
                    lean_dec_ref_known(v___x_7122_, 1);
                    v_val_7124_ = v_a_7128_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_7125_ = lean_task_get_own(v_val_7124_);
                return v___x_7125_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_BaseAsync_wait___redArg___boxed(
    mut v_self_7129_: *mut LeanObject,
    mut v_a_7130_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7131_: *mut LeanObject = core::ptr::null_mut();
    v_res_7131_ = l_Std_Async_BaseAsync_wait___redArg(v_self_7129_);
    return v_res_7131_;
}
pub unsafe fn l_Std_Async_BaseAsync_wait(
    mut v_00_u03b1_7132_: *mut LeanObject,
    mut v_self_7133_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_val_7136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7141_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7138_ = lean_apply_1(v_self_7133_, lean_box(0));
                if lean_obj_tag(v___x_7138_) == 0 {
                    v_a_7139_ = lean_ctor_get(v___x_7138_, 0);
                    lean_inc(v_a_7139_);
                    lean_dec_ref_known(v___x_7138_, 1);
                    v___x_7140_ = lean_task_pure(v_a_7139_);
                    v_val_7136_ = v___x_7140_;
                    state = 1;
                    continue;
                } else {
                    v_a_7141_ = lean_ctor_get(v___x_7138_, 0);
                    lean_inc_ref(v_a_7141_);
                    lean_dec_ref_known(v___x_7138_, 1);
                    v_val_7136_ = v_a_7141_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_7137_ = lean_task_get_own(v_val_7136_);
                return v___x_7137_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_BaseAsync_wait___boxed(
    mut v_00_u03b1_7142_: *mut LeanObject,
    mut v_self_7143_: *mut LeanObject,
    mut v_a_7144_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7145_: *mut LeanObject = core::ptr::null_mut();
    v_res_7145_ = l_Std_Async_BaseAsync_wait(v_00_u03b1_7142_, v_self_7143_);
    return v_res_7145_;
}
pub unsafe fn l_Std_Async_BaseAsync_asTask___redArg(
    mut v_x_7146_: *mut LeanObject,
    mut v_prio_7147_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7153_: u8 = 0;
    let mut v___x_7154_: *mut LeanObject = core::ptr::null_mut();
    v___x_7149_ = lean_alloc_closure(
        l_Std_Async_BaseAsync_toRawBaseIO___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___x_7149_, 0, lean_box(0));
    lean_closure_set(v___x_7149_, 1, v_x_7146_);
    v___x_7150_ = lean_io_as_task(v___x_7149_, v_prio_7147_);
    v___f_7151_ = l_Std_Async_MaybeTask_joinTask___redArg___closed__0;
    v___x_7152_ = lean_unsigned_to_nat(0);
    v___x_7153_ = 1;
    v___x_7154_ = lean_task_bind(v___x_7150_, v___f_7151_, v___x_7152_, v___x_7153_);
    return v___x_7154_;
}
pub unsafe fn l_Std_Async_BaseAsync_asTask___redArg___boxed(
    mut v_x_7155_: *mut LeanObject,
    mut v_prio_7156_: *mut LeanObject,
    mut v_a_7157_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7158_: *mut LeanObject = core::ptr::null_mut();
    v_res_7158_ = l_Std_Async_BaseAsync_asTask___redArg(v_x_7155_, v_prio_7156_);
    return v_res_7158_;
}
pub unsafe fn l_Std_Async_BaseAsync_asTask(
    mut v_00_u03b1_7159_: *mut LeanObject,
    mut v_x_7160_: *mut LeanObject,
    mut v_prio_7161_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7167_: u8 = 0;
    let mut v___x_7168_: *mut LeanObject = core::ptr::null_mut();
    v___x_7163_ = lean_alloc_closure(
        l_Std_Async_BaseAsync_toRawBaseIO___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___x_7163_, 0, lean_box(0));
    lean_closure_set(v___x_7163_, 1, v_x_7160_);
    v___x_7164_ = lean_io_as_task(v___x_7163_, v_prio_7161_);
    v___f_7165_ = l_Std_Async_MaybeTask_joinTask___redArg___closed__0;
    v___x_7166_ = lean_unsigned_to_nat(0);
    v___x_7167_ = 1;
    v___x_7168_ = lean_task_bind(v___x_7164_, v___f_7165_, v___x_7166_, v___x_7167_);
    return v___x_7168_;
}
pub unsafe fn l_Std_Async_BaseAsync_asTask___boxed(
    mut v_00_u03b1_7169_: *mut LeanObject,
    mut v_x_7170_: *mut LeanObject,
    mut v_prio_7171_: *mut LeanObject,
    mut v_a_7172_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7173_: *mut LeanObject = core::ptr::null_mut();
    v_res_7173_ = l_Std_Async_BaseAsync_asTask(v_00_u03b1_7169_, v_x_7170_, v_prio_7171_);
    return v_res_7173_;
}
pub unsafe fn l_Std_Async_BaseAsync_await___redArg(
    mut v_t_7174_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7176_: *mut LeanObject = core::ptr::null_mut();
    v___x_7176_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_7176_, 0, v_t_7174_);
    return v___x_7176_;
}
pub unsafe fn l_Std_Async_BaseAsync_await___redArg___boxed(
    mut v_t_7177_: *mut LeanObject,
    mut v_a_7178_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7179_: *mut LeanObject = core::ptr::null_mut();
    v_res_7179_ = l_Std_Async_BaseAsync_await___redArg(v_t_7177_);
    return v_res_7179_;
}
pub unsafe fn l_Std_Async_BaseAsync_await(
    mut v_00_u03b1_7180_: *mut LeanObject,
    mut v_t_7181_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7183_: *mut LeanObject = core::ptr::null_mut();
    v___x_7183_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_7183_, 0, v_t_7181_);
    return v___x_7183_;
}
pub unsafe fn l_Std_Async_BaseAsync_await___boxed(
    mut v_00_u03b1_7184_: *mut LeanObject,
    mut v_t_7185_: *mut LeanObject,
    mut v_a_7186_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7187_: *mut LeanObject = core::ptr::null_mut();
    v_res_7187_ = l_Std_Async_BaseAsync_await(v_00_u03b1_7184_, v_t_7185_);
    return v_res_7187_;
}
pub unsafe fn l_Std_Async_BaseAsync_async___redArg(
    mut v_self_7188_: *mut LeanObject,
    mut v_prio_7189_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7195_: u8 = 0;
    let mut v___x_7196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7197_: *mut LeanObject = core::ptr::null_mut();
    v___x_7191_ = lean_alloc_closure(
        l_Std_Async_BaseAsync_toRawBaseIO___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___x_7191_, 0, lean_box(0));
    lean_closure_set(v___x_7191_, 1, v_self_7188_);
    v___x_7192_ = lean_io_as_task(v___x_7191_, v_prio_7189_);
    v___f_7193_ = l_Std_Async_MaybeTask_joinTask___redArg___closed__0;
    v___x_7194_ = lean_unsigned_to_nat(0);
    v___x_7195_ = 1;
    v___x_7196_ = lean_task_bind(v___x_7192_, v___f_7193_, v___x_7194_, v___x_7195_);
    v___x_7197_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_7197_, 0, v___x_7196_);
    return v___x_7197_;
}
pub unsafe fn l_Std_Async_BaseAsync_async___redArg___boxed(
    mut v_self_7198_: *mut LeanObject,
    mut v_prio_7199_: *mut LeanObject,
    mut v_a_7200_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7201_: *mut LeanObject = core::ptr::null_mut();
    v_res_7201_ = l_Std_Async_BaseAsync_async___redArg(v_self_7198_, v_prio_7199_);
    return v_res_7201_;
}
pub unsafe fn l_Std_Async_BaseAsync_async(
    mut v_00_u03b1_7202_: *mut LeanObject,
    mut v_self_7203_: *mut LeanObject,
    mut v_prio_7204_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7210_: u8 = 0;
    let mut v___x_7211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7212_: *mut LeanObject = core::ptr::null_mut();
    v___x_7206_ = lean_alloc_closure(
        l_Std_Async_BaseAsync_toRawBaseIO___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___x_7206_, 0, lean_box(0));
    lean_closure_set(v___x_7206_, 1, v_self_7203_);
    v___x_7207_ = lean_io_as_task(v___x_7206_, v_prio_7204_);
    v___f_7208_ = l_Std_Async_MaybeTask_joinTask___redArg___closed__0;
    v___x_7209_ = lean_unsigned_to_nat(0);
    v___x_7210_ = 1;
    v___x_7211_ = lean_task_bind(v___x_7207_, v___f_7208_, v___x_7209_, v___x_7210_);
    v___x_7212_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_7212_, 0, v___x_7211_);
    return v___x_7212_;
}
pub unsafe fn l_Std_Async_BaseAsync_async___boxed(
    mut v_00_u03b1_7213_: *mut LeanObject,
    mut v_self_7214_: *mut LeanObject,
    mut v_prio_7215_: *mut LeanObject,
    mut v_a_7216_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7217_: *mut LeanObject = core::ptr::null_mut();
    v_res_7217_ = l_Std_Async_BaseAsync_async(v_00_u03b1_7213_, v_self_7214_, v_prio_7215_);
    return v_res_7217_;
}
pub unsafe fn l_Std_Async_BaseAsync_instFunctor___lam__0(
    mut v_00_u03b1_7218_: *mut LeanObject,
    mut v_00_u03b2_7219_: *mut LeanObject,
    mut v_f_7220_: *mut LeanObject,
    mut v_self_7221_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7227_: u8 = 0;
    let mut v___x_7228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7232_: u8 = 0;
    let mut v_a_7233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7236_: u8 = 0;
    let mut v___x_7237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7238_: u8 = 0;
    let mut v___x_7239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7243_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7223_ = lean_apply_1(v_self_7221_, lean_box(0));
                if lean_obj_tag(v___x_7223_) == 0 {
                    v_a_7224_ = lean_ctor_get(v___x_7223_, 0);
                    v_isSharedCheck_7232_ = (!lean_is_exclusive(v___x_7223_)) as u8;
                    if v_isSharedCheck_7232_ == 0 {
                        v___x_7226_ = v___x_7223_;
                        v_isShared_7227_ = v_isSharedCheck_7232_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7224_);
                        lean_dec(v___x_7223_);
                        v___x_7226_ = lean_box(0);
                        v_isShared_7227_ = v_isSharedCheck_7232_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_7233_ = lean_ctor_get(v___x_7223_, 0);
                    v_isSharedCheck_7243_ = (!lean_is_exclusive(v___x_7223_)) as u8;
                    if v_isSharedCheck_7243_ == 0 {
                        v___x_7235_ = v___x_7223_;
                        v_isShared_7236_ = v_isSharedCheck_7243_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_7233_);
                        lean_dec(v___x_7223_);
                        v___x_7235_ = lean_box(0);
                        v_isShared_7236_ = v_isSharedCheck_7243_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7228_ = lean_apply_1(v_f_7220_, v_a_7224_);
                if v_isShared_7227_ == 0 {
                    lean_ctor_set(v___x_7226_, 0, v___x_7228_);
                    v___x_7230_ = v___x_7226_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7231_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7231_, 0, v___x_7228_);
                    v___x_7230_ = v_reuseFailAlloc_7231_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7230_;
            }
            3 => {
                v___x_7237_ = lean_unsigned_to_nat(0);
                v___x_7238_ = 0;
                v___x_7239_ = lean_task_map(v_f_7220_, v_a_7233_, v___x_7237_, v___x_7238_);
                if v_isShared_7236_ == 0 {
                    lean_ctor_set(v___x_7235_, 0, v___x_7239_);
                    v___x_7241_ = v___x_7235_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7242_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7242_, 0, v___x_7239_);
                    v___x_7241_ = v_reuseFailAlloc_7242_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7241_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_BaseAsync_instFunctor___lam__0___boxed(
    mut v_00_u03b1_7244_: *mut LeanObject,
    mut v_00_u03b2_7245_: *mut LeanObject,
    mut v_f_7246_: *mut LeanObject,
    mut v_self_7247_: *mut LeanObject,
    mut v___y_7248_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7249_: *mut LeanObject = core::ptr::null_mut();
    v_res_7249_ = l_Std_Async_BaseAsync_instFunctor___lam__0(
        v_00_u03b1_7244_,
        v_00_u03b2_7245_,
        v_f_7246_,
        v_self_7247_,
    );
    return v_res_7249_;
}
pub unsafe fn l_Std_Async_BaseAsync_instFunctor___lam__1(
    mut v___f_7250_: *mut LeanObject,
    mut v_00_u03b1_7251_: *mut LeanObject,
    mut v_00_u03b2_7252_: *mut LeanObject,
    mut v___y_7253_: *mut LeanObject,
    mut v___y_7254_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7257_: *mut LeanObject = core::ptr::null_mut();
    v___x_7256_ = lean_alloc_closure(l_Function_const___boxed as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___x_7256_, 0, lean_box(0));
    lean_closure_set(v___x_7256_, 1, lean_box(0));
    lean_closure_set(v___x_7256_, 2, v___y_7253_);
    v___x_7257_ = lean_apply_5(
        v___f_7250_,
        lean_box(0),
        lean_box(0),
        v___x_7256_,
        v___y_7254_,
        lean_box(0),
    );
    return v___x_7257_;
}
pub unsafe fn l_Std_Async_BaseAsync_instFunctor___lam__1___boxed(
    mut v___f_7258_: *mut LeanObject,
    mut v_00_u03b1_7259_: *mut LeanObject,
    mut v_00_u03b2_7260_: *mut LeanObject,
    mut v___y_7261_: *mut LeanObject,
    mut v___y_7262_: *mut LeanObject,
    mut v___y_7263_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7264_: *mut LeanObject = core::ptr::null_mut();
    v_res_7264_ = l_Std_Async_BaseAsync_instFunctor___lam__1(
        v___f_7258_,
        v_00_u03b1_7259_,
        v_00_u03b2_7260_,
        v___y_7261_,
        v___y_7262_,
    );
    return v_res_7264_;
}
pub unsafe fn l_Std_Async_BaseAsync_instMonad___lam__0(
    mut v_x_7272_: *mut LeanObject,
    mut v_y_7273_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7280_: u8 = 0;
    let mut v___x_7281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7285_: u8 = 0;
    let mut v_a_7286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7289_: u8 = 0;
    let mut v___x_7290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7291_: u8 = 0;
    let mut v___x_7292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7296_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7275_ = lean_box(0);
                v___x_7276_ = lean_apply_2(v_x_7272_, v___x_7275_, lean_box(0));
                if lean_obj_tag(v___x_7276_) == 0 {
                    v_a_7277_ = lean_ctor_get(v___x_7276_, 0);
                    v_isSharedCheck_7285_ = (!lean_is_exclusive(v___x_7276_)) as u8;
                    if v_isSharedCheck_7285_ == 0 {
                        v___x_7279_ = v___x_7276_;
                        v_isShared_7280_ = v_isSharedCheck_7285_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7277_);
                        lean_dec(v___x_7276_);
                        v___x_7279_ = lean_box(0);
                        v_isShared_7280_ = v_isSharedCheck_7285_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_7286_ = lean_ctor_get(v___x_7276_, 0);
                    v_isSharedCheck_7296_ = (!lean_is_exclusive(v___x_7276_)) as u8;
                    if v_isSharedCheck_7296_ == 0 {
                        v___x_7288_ = v___x_7276_;
                        v_isShared_7289_ = v_isSharedCheck_7296_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_7286_);
                        lean_dec(v___x_7276_);
                        v___x_7288_ = lean_box(0);
                        v_isShared_7289_ = v_isSharedCheck_7296_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7281_ = lean_apply_1(v_y_7273_, v_a_7277_);
                if v_isShared_7280_ == 0 {
                    lean_ctor_set(v___x_7279_, 0, v___x_7281_);
                    v___x_7283_ = v___x_7279_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7284_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7284_, 0, v___x_7281_);
                    v___x_7283_ = v_reuseFailAlloc_7284_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7283_;
            }
            3 => {
                v___x_7290_ = lean_unsigned_to_nat(0);
                v___x_7291_ = 0;
                v___x_7292_ = lean_task_map(v_y_7273_, v_a_7286_, v___x_7290_, v___x_7291_);
                if v_isShared_7289_ == 0 {
                    lean_ctor_set(v___x_7288_, 0, v___x_7292_);
                    v___x_7294_ = v___x_7288_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7295_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7295_, 0, v___x_7292_);
                    v___x_7294_ = v_reuseFailAlloc_7295_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7294_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_BaseAsync_instMonad___lam__0___boxed(
    mut v_x_7297_: *mut LeanObject,
    mut v_y_7298_: *mut LeanObject,
    mut v___y_7299_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7300_: *mut LeanObject = core::ptr::null_mut();
    v_res_7300_ = l_Std_Async_BaseAsync_instMonad___lam__0(v_x_7297_, v_y_7298_);
    return v_res_7300_;
}
pub unsafe fn l_Std_Async_BaseAsync_instMonad___lam__1(
    mut v_00_u03b1_7301_: *mut LeanObject,
    mut v_00_u03b2_7302_: *mut LeanObject,
    mut v_f_7303_: *mut LeanObject,
    mut v_x_7304_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7309_: u8 = 0;
    let mut v___x_7310_: *mut LeanObject = core::ptr::null_mut();
    v___x_7306_ = lean_apply_1(v_f_7303_, lean_box(0));
    v___f_7307_ = lean_alloc_closure(
        l_Std_Async_BaseAsync_instMonad___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_7307_, 0, v_x_7304_);
    v___x_7308_ = lean_unsigned_to_nat(0);
    v___x_7309_ = 0;
    v___x_7310_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(
        v___x_7308_,
        v___x_7309_,
        v___x_7306_,
        v___f_7307_,
    );
    return v___x_7310_;
}
pub unsafe fn l_Std_Async_BaseAsync_instMonad___lam__1___boxed(
    mut v_00_u03b1_7311_: *mut LeanObject,
    mut v_00_u03b2_7312_: *mut LeanObject,
    mut v_f_7313_: *mut LeanObject,
    mut v_x_7314_: *mut LeanObject,
    mut v___y_7315_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7316_: *mut LeanObject = core::ptr::null_mut();
    v_res_7316_ = l_Std_Async_BaseAsync_instMonad___lam__1(
        v_00_u03b1_7311_,
        v_00_u03b2_7312_,
        v_f_7313_,
        v_x_7314_,
    );
    return v_res_7316_;
}
pub unsafe fn l_Std_Async_BaseAsync_instMonad___lam__2(
    mut v_00_u03b1_7317_: *mut LeanObject,
    mut v_00_u03b2_7318_: *mut LeanObject,
    mut v_self_7319_: *mut LeanObject,
    mut v_f_7320_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7324_: u8 = 0;
    let mut v___x_7325_: *mut LeanObject = core::ptr::null_mut();
    v___x_7322_ = lean_apply_1(v_self_7319_, lean_box(0));
    v___x_7323_ = lean_unsigned_to_nat(0);
    v___x_7324_ = 0;
    v___x_7325_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(
        v___x_7323_,
        v___x_7324_,
        v___x_7322_,
        v_f_7320_,
    );
    return v___x_7325_;
}
pub unsafe fn l_Std_Async_BaseAsync_instMonad___lam__2___boxed(
    mut v_00_u03b1_7326_: *mut LeanObject,
    mut v_00_u03b2_7327_: *mut LeanObject,
    mut v_self_7328_: *mut LeanObject,
    mut v_f_7329_: *mut LeanObject,
    mut v___y_7330_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7331_: *mut LeanObject = core::ptr::null_mut();
    v_res_7331_ = l_Std_Async_BaseAsync_instMonad___lam__2(
        v_00_u03b1_7326_,
        v_00_u03b2_7327_,
        v_self_7328_,
        v_f_7329_,
    );
    return v_res_7331_;
}
pub unsafe fn l_Std_Async_BaseAsync_instMonad___lam__3(
    mut v_a_7332_: *mut LeanObject,
    mut v_x_7333_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7335_: *mut LeanObject = core::ptr::null_mut();
    v___x_7335_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_7335_, 0, v_a_7332_);
    return v___x_7335_;
}
pub unsafe fn l_Std_Async_BaseAsync_instMonad___lam__3___boxed(
    mut v_a_7336_: *mut LeanObject,
    mut v_x_7337_: *mut LeanObject,
    mut v___y_7338_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7339_: *mut LeanObject = core::ptr::null_mut();
    v_res_7339_ = l_Std_Async_BaseAsync_instMonad___lam__3(v_a_7336_, v_x_7337_);
    lean_dec(v_x_7337_);
    return v_res_7339_;
}
pub unsafe fn l_Std_Async_BaseAsync_instMonad___lam__4(
    mut v_y_7340_: *mut LeanObject,
    mut v___f_7341_: *mut LeanObject,
    mut v_a_7342_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_7344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7347_: *mut LeanObject = core::ptr::null_mut();
    v___f_7344_ = lean_alloc_closure(
        l_Std_Async_BaseAsync_instMonad___lam__3___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_7344_, 0, v_a_7342_);
    v___x_7345_ = lean_box(0);
    v___x_7346_ = lean_apply_1(v_y_7340_, v___x_7345_);
    v___x_7347_ = lean_apply_5(
        v___f_7341_,
        lean_box(0),
        lean_box(0),
        v___x_7346_,
        v___f_7344_,
        lean_box(0),
    );
    return v___x_7347_;
}
pub unsafe fn l_Std_Async_BaseAsync_instMonad___lam__4___boxed(
    mut v_y_7348_: *mut LeanObject,
    mut v___f_7349_: *mut LeanObject,
    mut v_a_7350_: *mut LeanObject,
    mut v___y_7351_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7352_: *mut LeanObject = core::ptr::null_mut();
    v_res_7352_ = l_Std_Async_BaseAsync_instMonad___lam__4(v_y_7348_, v___f_7349_, v_a_7350_);
    return v_res_7352_;
}
pub unsafe fn l_Std_Async_BaseAsync_instMonad___lam__5(
    mut v___f_7353_: *mut LeanObject,
    mut v_00_u03b1_7354_: *mut LeanObject,
    mut v_00_u03b2_7355_: *mut LeanObject,
    mut v_x_7356_: *mut LeanObject,
    mut v_y_7357_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_7359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7360_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v___f_7353_);
    v___f_7359_ = lean_alloc_closure(
        l_Std_Async_BaseAsync_instMonad___lam__4___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_7359_, 0, v_y_7357_);
    lean_closure_set(v___f_7359_, 1, v___f_7353_);
    v___x_7360_ = lean_apply_5(
        v___f_7353_,
        lean_box(0),
        lean_box(0),
        v_x_7356_,
        v___f_7359_,
        lean_box(0),
    );
    return v___x_7360_;
}
pub unsafe fn l_Std_Async_BaseAsync_instMonad___lam__5___boxed(
    mut v___f_7361_: *mut LeanObject,
    mut v_00_u03b1_7362_: *mut LeanObject,
    mut v_00_u03b2_7363_: *mut LeanObject,
    mut v_x_7364_: *mut LeanObject,
    mut v_y_7365_: *mut LeanObject,
    mut v___y_7366_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7367_: *mut LeanObject = core::ptr::null_mut();
    v_res_7367_ = l_Std_Async_BaseAsync_instMonad___lam__5(
        v___f_7361_,
        v_00_u03b1_7362_,
        v_00_u03b2_7363_,
        v_x_7364_,
        v_y_7365_,
    );
    return v_res_7367_;
}
pub unsafe fn l_Std_Async_BaseAsync_instMonad___lam__6(
    mut v_y_7368_: *mut LeanObject,
    mut v_x_7369_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7372_: *mut LeanObject = core::ptr::null_mut();
    v___x_7371_ = lean_box(0);
    v___x_7372_ = lean_apply_2(v_y_7368_, v___x_7371_, lean_box(0));
    return v___x_7372_;
}
pub unsafe fn l_Std_Async_BaseAsync_instMonad___lam__6___boxed(
    mut v_y_7373_: *mut LeanObject,
    mut v_x_7374_: *mut LeanObject,
    mut v___y_7375_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7376_: *mut LeanObject = core::ptr::null_mut();
    v_res_7376_ = l_Std_Async_BaseAsync_instMonad___lam__6(v_y_7373_, v_x_7374_);
    lean_dec(v_x_7374_);
    return v_res_7376_;
}
pub unsafe fn l_Std_Async_BaseAsync_instMonad___lam__7(
    mut v_00_u03b1_7377_: *mut LeanObject,
    mut v_00_u03b2_7378_: *mut LeanObject,
    mut v_x_7379_: *mut LeanObject,
    mut v_y_7380_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7385_: u8 = 0;
    let mut v___x_7386_: *mut LeanObject = core::ptr::null_mut();
    v___x_7382_ = lean_apply_1(v_x_7379_, lean_box(0));
    v___f_7383_ = lean_alloc_closure(
        l_Std_Async_BaseAsync_instMonad___lam__6___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_7383_, 0, v_y_7380_);
    v___x_7384_ = lean_unsigned_to_nat(0);
    v___x_7385_ = 0;
    v___x_7386_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(
        v___x_7384_,
        v___x_7385_,
        v___x_7382_,
        v___f_7383_,
    );
    return v___x_7386_;
}
pub unsafe fn l_Std_Async_BaseAsync_instMonad___lam__7___boxed(
    mut v_00_u03b1_7387_: *mut LeanObject,
    mut v_00_u03b2_7388_: *mut LeanObject,
    mut v_x_7389_: *mut LeanObject,
    mut v_y_7390_: *mut LeanObject,
    mut v___y_7391_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7392_: *mut LeanObject = core::ptr::null_mut();
    v_res_7392_ = l_Std_Async_BaseAsync_instMonad___lam__7(
        v_00_u03b1_7387_,
        v_00_u03b2_7388_,
        v_x_7389_,
        v_y_7390_,
    );
    return v_res_7392_;
}
pub unsafe fn l_Std_Async_BaseAsync_instMonadAsyncTask___lam__1(
    mut v___f_7413_: *mut LeanObject,
    mut v_00_u03b1_7414_: *mut LeanObject,
    mut v_t_7415_: *mut LeanObject,
    mut v_prio_7416_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7421_: u8 = 0;
    let mut v___x_7422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7423_: *mut LeanObject = core::ptr::null_mut();
    v___x_7418_ = lean_alloc_closure(
        l_Std_Async_BaseAsync_toRawBaseIO___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___x_7418_, 0, lean_box(0));
    lean_closure_set(v___x_7418_, 1, v_t_7415_);
    v___x_7419_ = lean_io_as_task(v___x_7418_, v_prio_7416_);
    v___x_7420_ = lean_unsigned_to_nat(0);
    v___x_7421_ = 1;
    v___x_7422_ = lean_task_bind(v___x_7419_, v___f_7413_, v___x_7420_, v___x_7421_);
    v___x_7423_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_7423_, 0, v___x_7422_);
    return v___x_7423_;
}
pub unsafe fn l_Std_Async_BaseAsync_instMonadAsyncTask___lam__1___boxed(
    mut v___f_7424_: *mut LeanObject,
    mut v_00_u03b1_7425_: *mut LeanObject,
    mut v_t_7426_: *mut LeanObject,
    mut v_prio_7427_: *mut LeanObject,
    mut v___y_7428_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7429_: *mut LeanObject = core::ptr::null_mut();
    v_res_7429_ = l_Std_Async_BaseAsync_instMonadAsyncTask___lam__1(
        v___f_7424_,
        v_00_u03b1_7425_,
        v_t_7426_,
        v_prio_7427_,
    );
    return v_res_7429_;
}
pub unsafe fn l_Std_Async_BaseAsync_instInhabited___redArg(
    mut v_inst_7433_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7436_: *mut LeanObject = core::ptr::null_mut();
    v___x_7434_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_7434_, 0, v_inst_7433_);
    v___x_7435_ = lean_alloc_closure(
        l_instMonadBaseIO___aux__5___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___x_7435_, 0, lean_box(0));
    lean_closure_set(v___x_7435_, 1, v___x_7434_);
    v___x_7436_ = lean_alloc_closure(
        l_Std_Async_BaseAsync_mk___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___x_7436_, 0, lean_box(0));
    lean_closure_set(v___x_7436_, 1, v___x_7435_);
    return v___x_7436_;
}
pub unsafe fn l_Std_Async_BaseAsync_instInhabited(
    mut v_00_u03b1_7437_: *mut LeanObject,
    mut v_inst_7438_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7439_: *mut LeanObject = core::ptr::null_mut();
    v___x_7439_ = l_Std_Async_BaseAsync_instInhabited___redArg(v_inst_7438_);
    return v___x_7439_;
}
pub unsafe fn l_Std_Async_BaseAsync_instMonadFinally___lam__0(
    mut v_res_7440_: *mut LeanObject,
    mut v_snd_7441_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7442_: *mut LeanObject = core::ptr::null_mut();
    v___x_7442_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_7442_, 0, v_res_7440_);
    lean_ctor_set(v___x_7442_, 1, v_snd_7441_);
    return v___x_7442_;
}
pub unsafe fn l_Std_Async_BaseAsync_instMonadFinally___lam__1(
    mut v_f_7443_: *mut LeanObject,
    mut v_res_7444_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7451_: u8 = 0;
    let mut v___x_7452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7456_: u8 = 0;
    let mut v_a_7457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7460_: u8 = 0;
    let mut v___f_7461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7463_: u8 = 0;
    let mut v___x_7464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7468_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_res_7444_);
                v___x_7446_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_7446_, 0, v_res_7444_);
                v___x_7447_ = lean_apply_2(v_f_7443_, v___x_7446_, lean_box(0));
                if lean_obj_tag(v___x_7447_) == 0 {
                    v_a_7448_ = lean_ctor_get(v___x_7447_, 0);
                    v_isSharedCheck_7456_ = (!lean_is_exclusive(v___x_7447_)) as u8;
                    if v_isSharedCheck_7456_ == 0 {
                        v___x_7450_ = v___x_7447_;
                        v_isShared_7451_ = v_isSharedCheck_7456_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7448_);
                        lean_dec(v___x_7447_);
                        v___x_7450_ = lean_box(0);
                        v_isShared_7451_ = v_isSharedCheck_7456_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_7457_ = lean_ctor_get(v___x_7447_, 0);
                    v_isSharedCheck_7468_ = (!lean_is_exclusive(v___x_7447_)) as u8;
                    if v_isSharedCheck_7468_ == 0 {
                        v___x_7459_ = v___x_7447_;
                        v_isShared_7460_ = v_isSharedCheck_7468_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_7457_);
                        lean_dec(v___x_7447_);
                        v___x_7459_ = lean_box(0);
                        v_isShared_7460_ = v_isSharedCheck_7468_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7452_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_7452_, 0, v_res_7444_);
                lean_ctor_set(v___x_7452_, 1, v_a_7448_);
                if v_isShared_7451_ == 0 {
                    lean_ctor_set(v___x_7450_, 0, v___x_7452_);
                    v___x_7454_ = v___x_7450_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7455_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7455_, 0, v___x_7452_);
                    v___x_7454_ = v_reuseFailAlloc_7455_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7454_;
            }
            3 => {
                v___f_7461_ = lean_alloc_closure(
                    l_Std_Async_BaseAsync_instMonadFinally___lam__0 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_7461_, 0, v_res_7444_);
                v___x_7462_ = lean_unsigned_to_nat(0);
                v___x_7463_ = 0;
                v___x_7464_ = lean_task_map(v___f_7461_, v_a_7457_, v___x_7462_, v___x_7463_);
                if v_isShared_7460_ == 0 {
                    lean_ctor_set(v___x_7459_, 0, v___x_7464_);
                    v___x_7466_ = v___x_7459_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7467_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7467_, 0, v___x_7464_);
                    v___x_7466_ = v_reuseFailAlloc_7467_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7466_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_BaseAsync_instMonadFinally___lam__1___boxed(
    mut v_f_7469_: *mut LeanObject,
    mut v_res_7470_: *mut LeanObject,
    mut v___y_7471_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7472_: *mut LeanObject = core::ptr::null_mut();
    v_res_7472_ = l_Std_Async_BaseAsync_instMonadFinally___lam__1(v_f_7469_, v_res_7470_);
    return v_res_7472_;
}
pub unsafe fn l_Std_Async_BaseAsync_instMonadFinally___lam__2(
    mut v_00_u03b1_7473_: *mut LeanObject,
    mut v_00_u03b2_7474_: *mut LeanObject,
    mut v_x_7475_: *mut LeanObject,
    mut v_f_7476_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7481_: u8 = 0;
    let mut v___x_7482_: *mut LeanObject = core::ptr::null_mut();
    v___x_7478_ = lean_apply_1(v_x_7475_, lean_box(0));
    v___f_7479_ = lean_alloc_closure(
        l_Std_Async_BaseAsync_instMonadFinally___lam__1___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_7479_, 0, v_f_7476_);
    v___x_7480_ = lean_unsigned_to_nat(0);
    v___x_7481_ = 0;
    v___x_7482_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(
        v___x_7480_,
        v___x_7481_,
        v___x_7478_,
        v___f_7479_,
    );
    return v___x_7482_;
}
pub unsafe fn l_Std_Async_BaseAsync_instMonadFinally___lam__2___boxed(
    mut v_00_u03b1_7483_: *mut LeanObject,
    mut v_00_u03b2_7484_: *mut LeanObject,
    mut v_x_7485_: *mut LeanObject,
    mut v_f_7486_: *mut LeanObject,
    mut v___y_7487_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7488_: *mut LeanObject = core::ptr::null_mut();
    v_res_7488_ = l_Std_Async_BaseAsync_instMonadFinally___lam__2(
        v_00_u03b1_7483_,
        v_00_u03b2_7484_,
        v_x_7485_,
        v_f_7486_,
    );
    return v_res_7488_;
}
pub unsafe fn l_Std_Async_BaseAsync_ofExcept___redArg(
    mut v_except_7491_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_7493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7496_: u8 = 0;
    let mut v___x_7498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7500_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_a_7493_ = lean_ctor_get(v_except_7491_, 0);
                v_isSharedCheck_7500_ = (!lean_is_exclusive(v_except_7491_)) as u8;
                if v_isSharedCheck_7500_ == 0 {
                    v___x_7495_ = v_except_7491_;
                    v_isShared_7496_ = v_isSharedCheck_7500_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_7493_);
                    lean_dec(v_except_7491_);
                    v___x_7495_ = lean_box(0);
                    v_isShared_7496_ = v_isSharedCheck_7500_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_7496_ == 0 {
                    lean_ctor_set_tag(v___x_7495_, 0);
                    v___x_7498_ = v___x_7495_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7499_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7499_, 0, v_a_7493_);
                    v___x_7498_ = v_reuseFailAlloc_7499_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7498_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_BaseAsync_ofExcept___redArg___boxed(
    mut v_except_7501_: *mut LeanObject,
    mut v_a_7502_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7503_: *mut LeanObject = core::ptr::null_mut();
    v_res_7503_ = l_Std_Async_BaseAsync_ofExcept___redArg(v_except_7501_);
    return v_res_7503_;
}
pub unsafe fn l_Std_Async_BaseAsync_ofExcept(
    mut v_00_u03b1_7504_: *mut LeanObject,
    mut v_except_7505_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_7507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7510_: u8 = 0;
    let mut v___x_7512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7514_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_a_7507_ = lean_ctor_get(v_except_7505_, 0);
                v_isSharedCheck_7514_ = (!lean_is_exclusive(v_except_7505_)) as u8;
                if v_isSharedCheck_7514_ == 0 {
                    v___x_7509_ = v_except_7505_;
                    v_isShared_7510_ = v_isSharedCheck_7514_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_7507_);
                    lean_dec(v_except_7505_);
                    v___x_7509_ = lean_box(0);
                    v_isShared_7510_ = v_isSharedCheck_7514_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_7510_ == 0 {
                    lean_ctor_set_tag(v___x_7509_, 0);
                    v___x_7512_ = v___x_7509_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7513_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7513_, 0, v_a_7507_);
                    v___x_7512_ = v_reuseFailAlloc_7513_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7512_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_BaseAsync_ofExcept___boxed(
    mut v_00_u03b1_7515_: *mut LeanObject,
    mut v_except_7516_: *mut LeanObject,
    mut v_a_7517_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7518_: *mut LeanObject = core::ptr::null_mut();
    v_res_7518_ = l_Std_Async_BaseAsync_ofExcept(v_00_u03b1_7515_, v_except_7516_);
    return v_res_7518_;
}
pub unsafe fn l_Std_Async_BaseAsync_concurrently___redArg___lam__1(
    mut v_resultX_7519_: *mut LeanObject,
    mut v_resultY_7520_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7523_: *mut LeanObject = core::ptr::null_mut();
    v___x_7522_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_7522_, 0, v_resultX_7519_);
    lean_ctor_set(v___x_7522_, 1, v_resultY_7520_);
    v___x_7523_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_7523_, 0, v___x_7522_);
    return v___x_7523_;
}
pub unsafe fn l_Std_Async_BaseAsync_concurrently___redArg___lam__1___boxed(
    mut v_resultX_7524_: *mut LeanObject,
    mut v_resultY_7525_: *mut LeanObject,
    mut v___y_7526_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7527_: *mut LeanObject = core::ptr::null_mut();
    v_res_7527_ =
        l_Std_Async_BaseAsync_concurrently___redArg___lam__1(v_resultX_7524_, v_resultY_7525_);
    return v_res_7527_;
}
pub unsafe fn l_Std_Async_BaseAsync_concurrently___redArg___lam__0(
    mut v_taskY_7528_: *mut LeanObject,
    mut v_resultX_7529_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_7531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7534_: u8 = 0;
    let mut v___x_7535_: *mut LeanObject = core::ptr::null_mut();
    v___f_7531_ = lean_alloc_closure(
        l_Std_Async_BaseAsync_concurrently___redArg___lam__1___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_7531_, 0, v_resultX_7529_);
    v___x_7532_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_7532_, 0, v_taskY_7528_);
    v___x_7533_ = lean_unsigned_to_nat(0);
    v___x_7534_ = 0;
    v___x_7535_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(
        v___x_7533_,
        v___x_7534_,
        v___x_7532_,
        v___f_7531_,
    );
    return v___x_7535_;
}
pub unsafe fn l_Std_Async_BaseAsync_concurrently___redArg___lam__0___boxed(
    mut v_taskY_7536_: *mut LeanObject,
    mut v_resultX_7537_: *mut LeanObject,
    mut v___y_7538_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7539_: *mut LeanObject = core::ptr::null_mut();
    v_res_7539_ =
        l_Std_Async_BaseAsync_concurrently___redArg___lam__0(v_taskY_7536_, v_resultX_7537_);
    return v_res_7539_;
}
pub unsafe fn l_Std_Async_BaseAsync_concurrently___redArg___lam__2(
    mut v_taskX_7540_: *mut LeanObject,
    mut v_taskY_7541_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_7543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7546_: u8 = 0;
    let mut v___x_7547_: *mut LeanObject = core::ptr::null_mut();
    v___f_7543_ = lean_alloc_closure(
        l_Std_Async_BaseAsync_concurrently___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_7543_, 0, v_taskY_7541_);
    v___x_7544_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_7544_, 0, v_taskX_7540_);
    v___x_7545_ = lean_unsigned_to_nat(0);
    v___x_7546_ = 0;
    v___x_7547_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(
        v___x_7545_,
        v___x_7546_,
        v___x_7544_,
        v___f_7543_,
    );
    return v___x_7547_;
}
pub unsafe fn l_Std_Async_BaseAsync_concurrently___redArg___lam__2___boxed(
    mut v_taskX_7548_: *mut LeanObject,
    mut v_taskY_7549_: *mut LeanObject,
    mut v___y_7550_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7551_: *mut LeanObject = core::ptr::null_mut();
    v_res_7551_ =
        l_Std_Async_BaseAsync_concurrently___redArg___lam__2(v_taskX_7548_, v_taskY_7549_);
    return v_res_7551_;
}
pub unsafe fn l_Std_Async_BaseAsync_concurrently___redArg___lam__3(
    mut v_y_7552_: *mut LeanObject,
    mut v_prio_7553_: *mut LeanObject,
    mut v___f_7554_: *mut LeanObject,
    mut v_taskX_7555_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7561_: u8 = 0;
    let mut v___x_7562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7564_: u8 = 0;
    let mut v___x_7565_: *mut LeanObject = core::ptr::null_mut();
    v___x_7557_ = lean_alloc_closure(
        l_Std_Async_BaseAsync_toRawBaseIO___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___x_7557_, 0, lean_box(0));
    lean_closure_set(v___x_7557_, 1, v_y_7552_);
    v___x_7558_ = lean_io_as_task(v___x_7557_, v_prio_7553_);
    v___f_7559_ = lean_alloc_closure(
        l_Std_Async_BaseAsync_concurrently___redArg___lam__2___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_7559_, 0, v_taskX_7555_);
    v___x_7560_ = lean_unsigned_to_nat(0);
    v___x_7561_ = 1;
    v___x_7562_ = lean_task_bind(v___x_7558_, v___f_7554_, v___x_7560_, v___x_7561_);
    v___x_7563_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_7563_, 0, v___x_7562_);
    v___x_7564_ = 0;
    v___x_7565_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(
        v___x_7560_,
        v___x_7564_,
        v___x_7563_,
        v___f_7559_,
    );
    return v___x_7565_;
}
pub unsafe fn l_Std_Async_BaseAsync_concurrently___redArg___lam__3___boxed(
    mut v_y_7566_: *mut LeanObject,
    mut v_prio_7567_: *mut LeanObject,
    mut v___f_7568_: *mut LeanObject,
    mut v_taskX_7569_: *mut LeanObject,
    mut v___y_7570_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7571_: *mut LeanObject = core::ptr::null_mut();
    v_res_7571_ = l_Std_Async_BaseAsync_concurrently___redArg___lam__3(
        v_y_7566_,
        v_prio_7567_,
        v___f_7568_,
        v_taskX_7569_,
    );
    return v_res_7571_;
}
pub unsafe fn l_Std_Async_BaseAsync_concurrently___redArg(
    mut v_x_7572_: *mut LeanObject,
    mut v_y_7573_: *mut LeanObject,
    mut v_prio_7574_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7581_: u8 = 0;
    let mut v___x_7582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7584_: u8 = 0;
    let mut v___x_7585_: *mut LeanObject = core::ptr::null_mut();
    v___x_7576_ = lean_alloc_closure(
        l_Std_Async_BaseAsync_toRawBaseIO___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___x_7576_, 0, lean_box(0));
    lean_closure_set(v___x_7576_, 1, v_x_7572_);
    lean_inc(v_prio_7574_);
    v___x_7577_ = lean_io_as_task(v___x_7576_, v_prio_7574_);
    v___f_7578_ = l_Std_Async_MaybeTask_joinTask___redArg___closed__0;
    v___f_7579_ = lean_alloc_closure(
        l_Std_Async_BaseAsync_concurrently___redArg___lam__3___boxed as *mut core::ffi::c_void,
        5,
        3,
    );
    lean_closure_set(v___f_7579_, 0, v_y_7573_);
    lean_closure_set(v___f_7579_, 1, v_prio_7574_);
    lean_closure_set(v___f_7579_, 2, v___f_7578_);
    v___x_7580_ = lean_unsigned_to_nat(0);
    v___x_7581_ = 1;
    v___x_7582_ = lean_task_bind(v___x_7577_, v___f_7578_, v___x_7580_, v___x_7581_);
    v___x_7583_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_7583_, 0, v___x_7582_);
    v___x_7584_ = 0;
    v___x_7585_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(
        v___x_7580_,
        v___x_7584_,
        v___x_7583_,
        v___f_7579_,
    );
    return v___x_7585_;
}
pub unsafe fn l_Std_Async_BaseAsync_concurrently___redArg___boxed(
    mut v_x_7586_: *mut LeanObject,
    mut v_y_7587_: *mut LeanObject,
    mut v_prio_7588_: *mut LeanObject,
    mut v_a_7589_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7590_: *mut LeanObject = core::ptr::null_mut();
    v_res_7590_ = l_Std_Async_BaseAsync_concurrently___redArg(v_x_7586_, v_y_7587_, v_prio_7588_);
    return v_res_7590_;
}
pub unsafe fn l_Std_Async_BaseAsync_concurrently(
    mut v_00_u03b1_7591_: *mut LeanObject,
    mut v_00_u03b2_7592_: *mut LeanObject,
    mut v_x_7593_: *mut LeanObject,
    mut v_y_7594_: *mut LeanObject,
    mut v_prio_7595_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7602_: u8 = 0;
    let mut v___x_7603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7605_: u8 = 0;
    let mut v___x_7606_: *mut LeanObject = core::ptr::null_mut();
    v___x_7597_ = lean_alloc_closure(
        l_Std_Async_BaseAsync_toRawBaseIO___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___x_7597_, 0, lean_box(0));
    lean_closure_set(v___x_7597_, 1, v_x_7593_);
    lean_inc(v_prio_7595_);
    v___x_7598_ = lean_io_as_task(v___x_7597_, v_prio_7595_);
    v___f_7599_ = l_Std_Async_MaybeTask_joinTask___redArg___closed__0;
    v___f_7600_ = lean_alloc_closure(
        l_Std_Async_BaseAsync_concurrently___redArg___lam__3___boxed as *mut core::ffi::c_void,
        5,
        3,
    );
    lean_closure_set(v___f_7600_, 0, v_y_7594_);
    lean_closure_set(v___f_7600_, 1, v_prio_7595_);
    lean_closure_set(v___f_7600_, 2, v___f_7599_);
    v___x_7601_ = lean_unsigned_to_nat(0);
    v___x_7602_ = 1;
    v___x_7603_ = lean_task_bind(v___x_7598_, v___f_7599_, v___x_7601_, v___x_7602_);
    v___x_7604_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_7604_, 0, v___x_7603_);
    v___x_7605_ = 0;
    v___x_7606_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(
        v___x_7601_,
        v___x_7605_,
        v___x_7604_,
        v___f_7600_,
    );
    return v___x_7606_;
}
pub unsafe fn l_Std_Async_BaseAsync_concurrently___boxed(
    mut v_00_u03b1_7607_: *mut LeanObject,
    mut v_00_u03b2_7608_: *mut LeanObject,
    mut v_x_7609_: *mut LeanObject,
    mut v_y_7610_: *mut LeanObject,
    mut v_prio_7611_: *mut LeanObject,
    mut v_a_7612_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7613_: *mut LeanObject = core::ptr::null_mut();
    v_res_7613_ = l_Std_Async_BaseAsync_concurrently(
        v_00_u03b1_7607_,
        v_00_u03b2_7608_,
        v_x_7609_,
        v_y_7610_,
        v_prio_7611_,
    );
    return v_res_7613_;
}
pub unsafe fn l_Std_Async_BaseAsync_race___redArg___lam__2(
    mut v_promise_7614_: *mut LeanObject,
    mut v_value_7615_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7617_: *mut LeanObject = core::ptr::null_mut();
    v___x_7617_ = lean_io_promise_resolve(v_value_7615_, v_promise_7614_);
    return v___x_7617_;
}
pub unsafe fn l_Std_Async_BaseAsync_race___redArg___lam__2___boxed(
    mut v_promise_7618_: *mut LeanObject,
    mut v_value_7619_: *mut LeanObject,
    mut v___y_7620_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7621_: *mut LeanObject = core::ptr::null_mut();
    v_res_7621_ = l_Std_Async_BaseAsync_race___redArg___lam__2(v_promise_7618_, v_value_7619_);
    lean_dec(v_promise_7618_);
    return v_res_7621_;
}
pub unsafe fn l_Std_Async_BaseAsync_race___redArg___lam__0(
    mut v_promise_7622_: *mut LeanObject,
    mut v_____r_7623_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7626_: *mut LeanObject = core::ptr::null_mut();
    v___x_7625_ = l_IO_Promise_result_x21___redArg(v_promise_7622_);
    v___x_7626_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_7626_, 0, v___x_7625_);
    return v___x_7626_;
}
pub unsafe fn l_Std_Async_BaseAsync_race___redArg___lam__0___boxed(
    mut v_promise_7627_: *mut LeanObject,
    mut v_____r_7628_: *mut LeanObject,
    mut v___y_7629_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7630_: *mut LeanObject = core::ptr::null_mut();
    v_res_7630_ = l_Std_Async_BaseAsync_race___redArg___lam__0(v_promise_7627_, v_____r_7628_);
    lean_dec(v_promise_7627_);
    return v_res_7630_;
}
pub unsafe fn l_Std_Async_BaseAsync_race___redArg___lam__1(
    mut v_task_u2082_7631_: *mut LeanObject,
    mut v___x_7632_: *mut LeanObject,
    mut v___x_7633_: *mut LeanObject,
    mut v___x_7634_: u8,
    mut v___f_7635_: *mut LeanObject,
    mut v_____r_7636_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7640_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___x_7633_);
    v___x_7638_ =
        l_BaseIO_chainTask___redArg(v_task_u2082_7631_, v___x_7632_, v___x_7633_, v___x_7634_);
    v___x_7639_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_7639_, 0, v___x_7638_);
    v___x_7640_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(
        v___x_7633_,
        v___x_7634_,
        v___x_7639_,
        v___f_7635_,
    );
    return v___x_7640_;
}
pub unsafe fn l_Std_Async_BaseAsync_race___redArg___lam__1___boxed(
    mut v_task_u2082_7641_: *mut LeanObject,
    mut v___x_7642_: *mut LeanObject,
    mut v___x_7643_: *mut LeanObject,
    mut v___x_7644_: *mut LeanObject,
    mut v___f_7645_: *mut LeanObject,
    mut v_____r_7646_: *mut LeanObject,
    mut v___y_7647_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_616__boxed_7648_: u8 = 0;
    let mut v_res_7649_: *mut LeanObject = core::ptr::null_mut();
    v___x_616__boxed_7648_ = (lean_unbox(v___x_7644_) as u8);
    v_res_7649_ = l_Std_Async_BaseAsync_race___redArg___lam__1(
        v_task_u2082_7641_,
        v___x_7642_,
        v___x_7643_,
        v___x_616__boxed_7648_,
        v___f_7645_,
        v_____r_7646_,
    );
    return v_res_7649_;
}
pub unsafe fn l_Std_Async_BaseAsync_race___redArg___lam__3(
    mut v___f_7650_: *mut LeanObject,
    mut v___f_7651_: *mut LeanObject,
    mut v_task_u2081_7652_: *mut LeanObject,
    mut v___f_7653_: *mut LeanObject,
    mut v_task_u2082_7654_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7659_: u8 = 0;
    let mut v___x_7660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7664_: *mut LeanObject = core::ptr::null_mut();
    v___x_7656_ = lean_alloc_closure(l_liftM as *mut core::ffi::c_void, 5, 4);
    lean_closure_set(v___x_7656_, 0, lean_box(0));
    lean_closure_set(v___x_7656_, 1, lean_box(0));
    lean_closure_set(v___x_7656_, 2, v___f_7650_);
    lean_closure_set(v___x_7656_, 3, lean_box(0));
    v___x_7657_ = lean_alloc_closure(l_Function_comp as *mut core::ffi::c_void, 6, 5);
    lean_closure_set(v___x_7657_, 0, lean_box(0));
    lean_closure_set(v___x_7657_, 1, lean_box(0));
    lean_closure_set(v___x_7657_, 2, lean_box(0));
    lean_closure_set(v___x_7657_, 3, v___x_7656_);
    lean_closure_set(v___x_7657_, 4, v___f_7651_);
    v___x_7658_ = lean_unsigned_to_nat(0);
    v___x_7659_ = 0;
    lean_inc_ref(v___x_7657_);
    v___x_7660_ =
        l_BaseIO_chainTask___redArg(v_task_u2081_7652_, v___x_7657_, v___x_7658_, v___x_7659_);
    v___x_7661_ = lean_box((v___x_7659_) as usize);
    v___f_7662_ = lean_alloc_closure(
        l_Std_Async_BaseAsync_race___redArg___lam__1___boxed as *mut core::ffi::c_void,
        7,
        5,
    );
    lean_closure_set(v___f_7662_, 0, v_task_u2082_7654_);
    lean_closure_set(v___f_7662_, 1, v___x_7657_);
    lean_closure_set(v___f_7662_, 2, v___x_7658_);
    lean_closure_set(v___f_7662_, 3, v___x_7661_);
    lean_closure_set(v___f_7662_, 4, v___f_7653_);
    v___x_7663_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_7663_, 0, v___x_7660_);
    v___x_7664_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(
        v___x_7658_,
        v___x_7659_,
        v___x_7663_,
        v___f_7662_,
    );
    return v___x_7664_;
}
pub unsafe fn l_Std_Async_BaseAsync_race___redArg___lam__3___boxed(
    mut v___f_7665_: *mut LeanObject,
    mut v___f_7666_: *mut LeanObject,
    mut v_task_u2081_7667_: *mut LeanObject,
    mut v___f_7668_: *mut LeanObject,
    mut v_task_u2082_7669_: *mut LeanObject,
    mut v___y_7670_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7671_: *mut LeanObject = core::ptr::null_mut();
    v_res_7671_ = l_Std_Async_BaseAsync_race___redArg___lam__3(
        v___f_7665_,
        v___f_7666_,
        v_task_u2081_7667_,
        v___f_7668_,
        v_task_u2082_7669_,
    );
    return v_res_7671_;
}
pub unsafe fn l_Std_Async_BaseAsync_race___redArg___lam__4(
    mut v_y_7672_: *mut LeanObject,
    mut v_prio_7673_: *mut LeanObject,
    mut v___f_7674_: *mut LeanObject,
    mut v___f_7675_: *mut LeanObject,
    mut v___f_7676_: *mut LeanObject,
    mut v___f_7677_: *mut LeanObject,
    mut v_task_u2081_7678_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7684_: u8 = 0;
    let mut v___x_7685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7687_: u8 = 0;
    let mut v___x_7688_: *mut LeanObject = core::ptr::null_mut();
    v___x_7680_ = lean_alloc_closure(
        l_Std_Async_BaseAsync_toRawBaseIO___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___x_7680_, 0, lean_box(0));
    lean_closure_set(v___x_7680_, 1, v_y_7672_);
    v___x_7681_ = lean_io_as_task(v___x_7680_, v_prio_7673_);
    v___f_7682_ = lean_alloc_closure(
        l_Std_Async_BaseAsync_race___redArg___lam__3___boxed as *mut core::ffi::c_void,
        6,
        4,
    );
    lean_closure_set(v___f_7682_, 0, v___f_7674_);
    lean_closure_set(v___f_7682_, 1, v___f_7675_);
    lean_closure_set(v___f_7682_, 2, v_task_u2081_7678_);
    lean_closure_set(v___f_7682_, 3, v___f_7676_);
    v___x_7683_ = lean_unsigned_to_nat(0);
    v___x_7684_ = 1;
    v___x_7685_ = lean_task_bind(v___x_7681_, v___f_7677_, v___x_7683_, v___x_7684_);
    v___x_7686_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_7686_, 0, v___x_7685_);
    v___x_7687_ = 0;
    v___x_7688_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(
        v___x_7683_,
        v___x_7687_,
        v___x_7686_,
        v___f_7682_,
    );
    return v___x_7688_;
}
pub unsafe fn l_Std_Async_BaseAsync_race___redArg___lam__4___boxed(
    mut v_y_7689_: *mut LeanObject,
    mut v_prio_7690_: *mut LeanObject,
    mut v___f_7691_: *mut LeanObject,
    mut v___f_7692_: *mut LeanObject,
    mut v___f_7693_: *mut LeanObject,
    mut v___f_7694_: *mut LeanObject,
    mut v_task_u2081_7695_: *mut LeanObject,
    mut v___y_7696_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7697_: *mut LeanObject = core::ptr::null_mut();
    v_res_7697_ = l_Std_Async_BaseAsync_race___redArg___lam__4(
        v_y_7689_,
        v_prio_7690_,
        v___f_7691_,
        v___f_7692_,
        v___f_7693_,
        v___f_7694_,
        v_task_u2081_7695_,
    );
    return v_res_7697_;
}
pub unsafe fn l_Std_Async_BaseAsync_race___redArg___lam__5(
    mut v_x_7698_: *mut LeanObject,
    mut v_prio_7699_: *mut LeanObject,
    mut v_y_7700_: *mut LeanObject,
    mut v___f_7701_: *mut LeanObject,
    mut v___f_7702_: *mut LeanObject,
    mut v___f_7703_: *mut LeanObject,
    mut v_promise_7704_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7712_: u8 = 0;
    let mut v___x_7713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7715_: u8 = 0;
    let mut v___x_7716_: *mut LeanObject = core::ptr::null_mut();
    v___x_7706_ = lean_alloc_closure(
        l_Std_Async_BaseAsync_toRawBaseIO___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___x_7706_, 0, lean_box(0));
    lean_closure_set(v___x_7706_, 1, v_x_7698_);
    lean_inc(v_prio_7699_);
    v___x_7707_ = lean_io_as_task(v___x_7706_, v_prio_7699_);
    lean_inc(v_promise_7704_);
    v___f_7708_ = lean_alloc_closure(
        l_Std_Async_BaseAsync_race___redArg___lam__2___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_7708_, 0, v_promise_7704_);
    v___f_7709_ = lean_alloc_closure(
        l_Std_Async_BaseAsync_race___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_7709_, 0, v_promise_7704_);
    v___f_7710_ = lean_alloc_closure(
        l_Std_Async_BaseAsync_race___redArg___lam__4___boxed as *mut core::ffi::c_void,
        8,
        6,
    );
    lean_closure_set(v___f_7710_, 0, v_y_7700_);
    lean_closure_set(v___f_7710_, 1, v_prio_7699_);
    lean_closure_set(v___f_7710_, 2, v___f_7701_);
    lean_closure_set(v___f_7710_, 3, v___f_7708_);
    lean_closure_set(v___f_7710_, 4, v___f_7709_);
    lean_closure_set(v___f_7710_, 5, v___f_7702_);
    v___x_7711_ = lean_unsigned_to_nat(0);
    v___x_7712_ = 1;
    v___x_7713_ = lean_task_bind(v___x_7707_, v___f_7703_, v___x_7711_, v___x_7712_);
    v___x_7714_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_7714_, 0, v___x_7713_);
    v___x_7715_ = 0;
    v___x_7716_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(
        v___x_7711_,
        v___x_7715_,
        v___x_7714_,
        v___f_7710_,
    );
    return v___x_7716_;
}
pub unsafe fn l_Std_Async_BaseAsync_race___redArg___lam__5___boxed(
    mut v_x_7717_: *mut LeanObject,
    mut v_prio_7718_: *mut LeanObject,
    mut v_y_7719_: *mut LeanObject,
    mut v___f_7720_: *mut LeanObject,
    mut v___f_7721_: *mut LeanObject,
    mut v___f_7722_: *mut LeanObject,
    mut v_promise_7723_: *mut LeanObject,
    mut v___y_7724_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7725_: *mut LeanObject = core::ptr::null_mut();
    v_res_7725_ = l_Std_Async_BaseAsync_race___redArg___lam__5(
        v_x_7717_,
        v_prio_7718_,
        v_y_7719_,
        v___f_7720_,
        v___f_7721_,
        v___f_7722_,
        v_promise_7723_,
    );
    return v_res_7725_;
}
pub unsafe fn l_Std_Async_BaseAsync_race___redArg(
    mut v_x_7727_: *mut LeanObject,
    mut v_y_7728_: *mut LeanObject,
    mut v_prio_7729_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7737_: u8 = 0;
    let mut v___x_7738_: *mut LeanObject = core::ptr::null_mut();
    v___x_7731_ = lean_io_promise_new();
    v___f_7732_ = l_Std_Async_MaybeTask_joinTask___redArg___closed__0;
    v___f_7733_ = l_Std_Async_BaseAsync_race___redArg___closed__0;
    v___f_7734_ = lean_alloc_closure(
        l_Std_Async_BaseAsync_race___redArg___lam__5___boxed as *mut core::ffi::c_void,
        8,
        6,
    );
    lean_closure_set(v___f_7734_, 0, v_x_7727_);
    lean_closure_set(v___f_7734_, 1, v_prio_7729_);
    lean_closure_set(v___f_7734_, 2, v_y_7728_);
    lean_closure_set(v___f_7734_, 3, v___f_7733_);
    lean_closure_set(v___f_7734_, 4, v___f_7732_);
    lean_closure_set(v___f_7734_, 5, v___f_7732_);
    v___x_7735_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_7735_, 0, v___x_7731_);
    v___x_7736_ = lean_unsigned_to_nat(0);
    v___x_7737_ = 0;
    v___x_7738_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(
        v___x_7736_,
        v___x_7737_,
        v___x_7735_,
        v___f_7734_,
    );
    return v___x_7738_;
}
pub unsafe fn l_Std_Async_BaseAsync_race___redArg___boxed(
    mut v_x_7739_: *mut LeanObject,
    mut v_y_7740_: *mut LeanObject,
    mut v_prio_7741_: *mut LeanObject,
    mut v_a_7742_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7743_: *mut LeanObject = core::ptr::null_mut();
    v_res_7743_ = l_Std_Async_BaseAsync_race___redArg(v_x_7739_, v_y_7740_, v_prio_7741_);
    return v_res_7743_;
}
pub unsafe fn l_Std_Async_BaseAsync_race(
    mut v_00_u03b1_7744_: *mut LeanObject,
    mut v_inst_7745_: *mut LeanObject,
    mut v_x_7746_: *mut LeanObject,
    mut v_y_7747_: *mut LeanObject,
    mut v_prio_7748_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7756_: u8 = 0;
    let mut v___x_7757_: *mut LeanObject = core::ptr::null_mut();
    v___x_7750_ = lean_io_promise_new();
    v___f_7751_ = l_Std_Async_MaybeTask_joinTask___redArg___closed__0;
    v___f_7752_ = l_Std_Async_BaseAsync_race___redArg___closed__0;
    v___f_7753_ = lean_alloc_closure(
        l_Std_Async_BaseAsync_race___redArg___lam__5___boxed as *mut core::ffi::c_void,
        8,
        6,
    );
    lean_closure_set(v___f_7753_, 0, v_x_7746_);
    lean_closure_set(v___f_7753_, 1, v_prio_7748_);
    lean_closure_set(v___f_7753_, 2, v_y_7747_);
    lean_closure_set(v___f_7753_, 3, v___f_7752_);
    lean_closure_set(v___f_7753_, 4, v___f_7751_);
    lean_closure_set(v___f_7753_, 5, v___f_7751_);
    v___x_7754_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_7754_, 0, v___x_7750_);
    v___x_7755_ = lean_unsigned_to_nat(0);
    v___x_7756_ = 0;
    v___x_7757_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(
        v___x_7755_,
        v___x_7756_,
        v___x_7754_,
        v___f_7753_,
    );
    return v___x_7757_;
}
pub unsafe fn l_Std_Async_BaseAsync_race___boxed(
    mut v_00_u03b1_7758_: *mut LeanObject,
    mut v_inst_7759_: *mut LeanObject,
    mut v_x_7760_: *mut LeanObject,
    mut v_y_7761_: *mut LeanObject,
    mut v_prio_7762_: *mut LeanObject,
    mut v_a_7763_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7764_: *mut LeanObject = core::ptr::null_mut();
    v_res_7764_ = l_Std_Async_BaseAsync_race(
        v_00_u03b1_7758_,
        v_inst_7759_,
        v_x_7760_,
        v_y_7761_,
        v_prio_7762_,
    );
    lean_dec(v_inst_7759_);
    return v_res_7764_;
}
pub unsafe fn l_Std_Async_BaseAsync_concurrentlyAll___redArg___lam__1(
    mut v_prio_7765_: *mut LeanObject,
    mut v___f_7766_: *mut LeanObject,
    mut v_x_7767_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7772_: u8 = 0;
    let mut v___x_7773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7774_: *mut LeanObject = core::ptr::null_mut();
    v___x_7769_ = lean_alloc_closure(
        l_Std_Async_BaseAsync_toRawBaseIO___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___x_7769_, 0, lean_box(0));
    lean_closure_set(v___x_7769_, 1, v_x_7767_);
    v___x_7770_ = lean_io_as_task(v___x_7769_, v_prio_7765_);
    v___x_7771_ = lean_unsigned_to_nat(0);
    v___x_7772_ = 1;
    v___x_7773_ = lean_task_bind(v___x_7770_, v___f_7766_, v___x_7771_, v___x_7772_);
    v___x_7774_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_7774_, 0, v___x_7773_);
    return v___x_7774_;
}
pub unsafe fn l_Std_Async_BaseAsync_concurrentlyAll___redArg___lam__1___boxed(
    mut v_prio_7775_: *mut LeanObject,
    mut v___f_7776_: *mut LeanObject,
    mut v_x_7777_: *mut LeanObject,
    mut v___y_7778_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7779_: *mut LeanObject = core::ptr::null_mut();
    v_res_7779_ = l_Std_Async_BaseAsync_concurrentlyAll___redArg___lam__1(
        v_prio_7775_,
        v___f_7776_,
        v_x_7777_,
    );
    return v_res_7779_;
}
pub unsafe fn l_Std_Async_BaseAsync_concurrentlyAll___redArg___lam__0(
    mut v___x_7781_: *mut LeanObject,
    mut v_tasks_7782_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_7785_: usize = 0;
    let mut v___x_7786_: usize = 0;
    let mut v___x_218__overap_7787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7788_: *mut LeanObject = core::ptr::null_mut();
    v___x_7784_ = l_Std_Async_BaseAsync_concurrentlyAll___redArg___lam__0___closed__0;
    v_sz_7785_ = lean_array_size(v_tasks_7782_);
    v___x_7786_ = 0usize;
    v___x_218__overap_7787_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
        lean_box(0),
        lean_box(0),
        lean_box(0),
        v___x_7781_,
        v___x_7784_,
        v_sz_7785_,
        v___x_7786_,
        v_tasks_7782_,
    );
    v___x_7788_ = lean_apply_1(v___x_218__overap_7787_, lean_box(0));
    return v___x_7788_;
}
pub unsafe fn l_Std_Async_BaseAsync_concurrentlyAll___redArg___lam__0___boxed(
    mut v___x_7789_: *mut LeanObject,
    mut v_tasks_7790_: *mut LeanObject,
    mut v___y_7791_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7792_: *mut LeanObject = core::ptr::null_mut();
    v_res_7792_ =
        l_Std_Async_BaseAsync_concurrentlyAll___redArg___lam__0(v___x_7789_, v_tasks_7790_);
    return v_res_7792_;
}
pub unsafe fn l_Std_Async_BaseAsync_concurrentlyAll___redArg(
    mut v_xs_7795_: *mut LeanObject,
    mut v_prio_7796_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_7798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_7801_: usize = 0;
    let mut v___x_7802_: usize = 0;
    let mut v___x_167__overap_7803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7807_: u8 = 0;
    let mut v___x_7808_: *mut LeanObject = core::ptr::null_mut();
    v___f_7798_ = l_Std_Async_MaybeTask_joinTask___redArg___closed__0;
    v___f_7799_ = lean_alloc_closure(
        l_Std_Async_BaseAsync_concurrentlyAll___redArg___lam__1___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_7799_, 0, v_prio_7796_);
    lean_closure_set(v___f_7799_, 1, v___f_7798_);
    v___x_7800_ = l_Std_Async_BaseAsync_instMonad;
    v_sz_7801_ = lean_array_size(v_xs_7795_);
    v___x_7802_ = 0usize;
    v___x_167__overap_7803_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
        lean_box(0),
        lean_box(0),
        lean_box(0),
        v___x_7800_,
        v___f_7799_,
        v_sz_7801_,
        v___x_7802_,
        v_xs_7795_,
    );
    v___x_7804_ = lean_apply_1(v___x_167__overap_7803_, lean_box(0));
    v___f_7805_ = l_Std_Async_BaseAsync_concurrentlyAll___redArg___closed__0;
    v___x_7806_ = lean_unsigned_to_nat(0);
    v___x_7807_ = 0;
    v___x_7808_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(
        v___x_7806_,
        v___x_7807_,
        v___x_7804_,
        v___f_7805_,
    );
    return v___x_7808_;
}
pub unsafe fn l_Std_Async_BaseAsync_concurrentlyAll___redArg___boxed(
    mut v_xs_7809_: *mut LeanObject,
    mut v_prio_7810_: *mut LeanObject,
    mut v_a_7811_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7812_: *mut LeanObject = core::ptr::null_mut();
    v_res_7812_ = l_Std_Async_BaseAsync_concurrentlyAll___redArg(v_xs_7809_, v_prio_7810_);
    return v_res_7812_;
}
pub unsafe fn l_Std_Async_BaseAsync_concurrentlyAll(
    mut v_00_u03b1_7813_: *mut LeanObject,
    mut v_xs_7814_: *mut LeanObject,
    mut v_prio_7815_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_7817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_7820_: usize = 0;
    let mut v___x_7821_: usize = 0;
    let mut v___x_188__overap_7822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7826_: u8 = 0;
    let mut v___x_7827_: *mut LeanObject = core::ptr::null_mut();
    v___f_7817_ = l_Std_Async_MaybeTask_joinTask___redArg___closed__0;
    v___f_7818_ = lean_alloc_closure(
        l_Std_Async_BaseAsync_concurrentlyAll___redArg___lam__1___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_7818_, 0, v_prio_7815_);
    lean_closure_set(v___f_7818_, 1, v___f_7817_);
    v___x_7819_ = l_Std_Async_BaseAsync_instMonad;
    v_sz_7820_ = lean_array_size(v_xs_7814_);
    v___x_7821_ = 0usize;
    v___x_188__overap_7822_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
        lean_box(0),
        lean_box(0),
        lean_box(0),
        v___x_7819_,
        v___f_7818_,
        v_sz_7820_,
        v___x_7821_,
        v_xs_7814_,
    );
    v___x_7823_ = lean_apply_1(v___x_188__overap_7822_, lean_box(0));
    v___f_7824_ = l_Std_Async_BaseAsync_concurrentlyAll___redArg___closed__0;
    v___x_7825_ = lean_unsigned_to_nat(0);
    v___x_7826_ = 0;
    v___x_7827_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(
        v___x_7825_,
        v___x_7826_,
        v___x_7823_,
        v___f_7824_,
    );
    return v___x_7827_;
}
pub unsafe fn l_Std_Async_BaseAsync_concurrentlyAll___boxed(
    mut v_00_u03b1_7828_: *mut LeanObject,
    mut v_xs_7829_: *mut LeanObject,
    mut v_prio_7830_: *mut LeanObject,
    mut v_a_7831_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7832_: *mut LeanObject = core::ptr::null_mut();
    v_res_7832_ = l_Std_Async_BaseAsync_concurrentlyAll(v_00_u03b1_7828_, v_xs_7829_, v_prio_7830_);
    return v_res_7832_;
}
pub unsafe fn l_Std_Async_BaseAsync_raceAll___redArg___lam__2(
    mut v___f_7833_: *mut LeanObject,
    mut v___f_7834_: *mut LeanObject,
    mut v_task_u2081_7835_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7840_: u8 = 0;
    let mut v___x_7841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7842_: *mut LeanObject = core::ptr::null_mut();
    v___x_7837_ = lean_alloc_closure(l_liftM as *mut core::ffi::c_void, 5, 4);
    lean_closure_set(v___x_7837_, 0, lean_box(0));
    lean_closure_set(v___x_7837_, 1, lean_box(0));
    lean_closure_set(v___x_7837_, 2, v___f_7833_);
    lean_closure_set(v___x_7837_, 3, lean_box(0));
    v___x_7838_ = lean_alloc_closure(l_Function_comp as *mut core::ffi::c_void, 6, 5);
    lean_closure_set(v___x_7838_, 0, lean_box(0));
    lean_closure_set(v___x_7838_, 1, lean_box(0));
    lean_closure_set(v___x_7838_, 2, lean_box(0));
    lean_closure_set(v___x_7838_, 3, v___x_7837_);
    lean_closure_set(v___x_7838_, 4, v___f_7834_);
    v___x_7839_ = lean_unsigned_to_nat(0);
    v___x_7840_ = 0;
    v___x_7841_ =
        l_BaseIO_chainTask___redArg(v_task_u2081_7835_, v___x_7838_, v___x_7839_, v___x_7840_);
    v___x_7842_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_7842_, 0, v___x_7841_);
    return v___x_7842_;
}
pub unsafe fn l_Std_Async_BaseAsync_raceAll___redArg___lam__2___boxed(
    mut v___f_7843_: *mut LeanObject,
    mut v___f_7844_: *mut LeanObject,
    mut v_task_u2081_7845_: *mut LeanObject,
    mut v___y_7846_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7847_: *mut LeanObject = core::ptr::null_mut();
    v_res_7847_ = l_Std_Async_BaseAsync_raceAll___redArg___lam__2(
        v___f_7843_,
        v___f_7844_,
        v_task_u2081_7845_,
    );
    return v_res_7847_;
}
pub unsafe fn l_Std_Async_BaseAsync_raceAll___redArg___lam__0(
    mut v_prio_7848_: *mut LeanObject,
    mut v___f_7849_: *mut LeanObject,
    mut v___f_7850_: *mut LeanObject,
    mut v_x_7851_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7856_: u8 = 0;
    let mut v___x_7857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7859_: u8 = 0;
    let mut v___x_7860_: *mut LeanObject = core::ptr::null_mut();
    v___x_7853_ = lean_alloc_closure(
        l_Std_Async_BaseAsync_toRawBaseIO___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___x_7853_, 0, lean_box(0));
    lean_closure_set(v___x_7853_, 1, v_x_7851_);
    v___x_7854_ = lean_io_as_task(v___x_7853_, v_prio_7848_);
    v___x_7855_ = lean_unsigned_to_nat(0);
    v___x_7856_ = 1;
    v___x_7857_ = lean_task_bind(v___x_7854_, v___f_7849_, v___x_7855_, v___x_7856_);
    v___x_7858_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_7858_, 0, v___x_7857_);
    v___x_7859_ = 0;
    v___x_7860_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(
        v___x_7855_,
        v___x_7859_,
        v___x_7858_,
        v___f_7850_,
    );
    return v___x_7860_;
}
pub unsafe fn l_Std_Async_BaseAsync_raceAll___redArg___lam__0___boxed(
    mut v_prio_7861_: *mut LeanObject,
    mut v___f_7862_: *mut LeanObject,
    mut v___f_7863_: *mut LeanObject,
    mut v_x_7864_: *mut LeanObject,
    mut v___y_7865_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7866_: *mut LeanObject = core::ptr::null_mut();
    v_res_7866_ = l_Std_Async_BaseAsync_raceAll___redArg___lam__0(
        v_prio_7861_,
        v___f_7862_,
        v___f_7863_,
        v_x_7864_,
    );
    return v_res_7866_;
}
pub unsafe fn l_Std_Async_BaseAsync_raceAll___redArg___lam__3(
    mut v___f_7867_: *mut LeanObject,
    mut v_prio_7868_: *mut LeanObject,
    mut v___f_7869_: *mut LeanObject,
    mut v_inst_7870_: *mut LeanObject,
    mut v_xs_7871_: *mut LeanObject,
    mut v_promise_7872_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_7874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7880_: u8 = 0;
    let mut v___x_7881_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_promise_7872_);
    v___f_7874_ = lean_alloc_closure(
        l_Std_Async_BaseAsync_race___redArg___lam__2___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_7874_, 0, v_promise_7872_);
    v___f_7875_ = lean_alloc_closure(
        l_Std_Async_BaseAsync_raceAll___redArg___lam__2___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_7875_, 0, v___f_7867_);
    lean_closure_set(v___f_7875_, 1, v___f_7874_);
    v___f_7876_ = lean_alloc_closure(
        l_Std_Async_BaseAsync_raceAll___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        3,
    );
    lean_closure_set(v___f_7876_, 0, v_prio_7868_);
    lean_closure_set(v___f_7876_, 1, v___f_7869_);
    lean_closure_set(v___f_7876_, 2, v___f_7875_);
    v___x_7877_ = lean_apply_3(v_inst_7870_, v_xs_7871_, v___f_7876_, lean_box(0));
    v___f_7878_ = lean_alloc_closure(
        l_Std_Async_BaseAsync_race___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_7878_, 0, v_promise_7872_);
    v___x_7879_ = lean_unsigned_to_nat(0);
    v___x_7880_ = 0;
    v___x_7881_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(
        v___x_7879_,
        v___x_7880_,
        v___x_7877_,
        v___f_7878_,
    );
    return v___x_7881_;
}
pub unsafe fn l_Std_Async_BaseAsync_raceAll___redArg___lam__3___boxed(
    mut v___f_7882_: *mut LeanObject,
    mut v_prio_7883_: *mut LeanObject,
    mut v___f_7884_: *mut LeanObject,
    mut v_inst_7885_: *mut LeanObject,
    mut v_xs_7886_: *mut LeanObject,
    mut v_promise_7887_: *mut LeanObject,
    mut v___y_7888_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7889_: *mut LeanObject = core::ptr::null_mut();
    v_res_7889_ = l_Std_Async_BaseAsync_raceAll___redArg___lam__3(
        v___f_7882_,
        v_prio_7883_,
        v___f_7884_,
        v_inst_7885_,
        v_xs_7886_,
        v_promise_7887_,
    );
    return v_res_7889_;
}
pub unsafe fn l_Std_Async_BaseAsync_raceAll___redArg(
    mut v_inst_7890_: *mut LeanObject,
    mut v_xs_7891_: *mut LeanObject,
    mut v_prio_7892_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7900_: u8 = 0;
    let mut v___x_7901_: *mut LeanObject = core::ptr::null_mut();
    v___x_7894_ = lean_io_promise_new();
    v___f_7895_ = l_Std_Async_MaybeTask_joinTask___redArg___closed__0;
    v___f_7896_ = l_Std_Async_BaseAsync_race___redArg___closed__0;
    v___f_7897_ = lean_alloc_closure(
        l_Std_Async_BaseAsync_raceAll___redArg___lam__3___boxed as *mut core::ffi::c_void,
        7,
        5,
    );
    lean_closure_set(v___f_7897_, 0, v___f_7896_);
    lean_closure_set(v___f_7897_, 1, v_prio_7892_);
    lean_closure_set(v___f_7897_, 2, v___f_7895_);
    lean_closure_set(v___f_7897_, 3, v_inst_7890_);
    lean_closure_set(v___f_7897_, 4, v_xs_7891_);
    v___x_7898_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_7898_, 0, v___x_7894_);
    v___x_7899_ = lean_unsigned_to_nat(0);
    v___x_7900_ = 0;
    v___x_7901_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(
        v___x_7899_,
        v___x_7900_,
        v___x_7898_,
        v___f_7897_,
    );
    return v___x_7901_;
}
pub unsafe fn l_Std_Async_BaseAsync_raceAll___redArg___boxed(
    mut v_inst_7902_: *mut LeanObject,
    mut v_xs_7903_: *mut LeanObject,
    mut v_prio_7904_: *mut LeanObject,
    mut v_a_7905_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7906_: *mut LeanObject = core::ptr::null_mut();
    v_res_7906_ = l_Std_Async_BaseAsync_raceAll___redArg(v_inst_7902_, v_xs_7903_, v_prio_7904_);
    return v_res_7906_;
}
pub unsafe fn l_Std_Async_BaseAsync_raceAll(
    mut v_00_u03b1_7907_: *mut LeanObject,
    mut v_c_7908_: *mut LeanObject,
    mut v_inst_7909_: *mut LeanObject,
    mut v_inst_7910_: *mut LeanObject,
    mut v_xs_7911_: *mut LeanObject,
    mut v_prio_7912_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7920_: u8 = 0;
    let mut v___x_7921_: *mut LeanObject = core::ptr::null_mut();
    v___x_7914_ = lean_io_promise_new();
    v___f_7915_ = l_Std_Async_MaybeTask_joinTask___redArg___closed__0;
    v___f_7916_ = l_Std_Async_BaseAsync_race___redArg___closed__0;
    v___f_7917_ = lean_alloc_closure(
        l_Std_Async_BaseAsync_raceAll___redArg___lam__3___boxed as *mut core::ffi::c_void,
        7,
        5,
    );
    lean_closure_set(v___f_7917_, 0, v___f_7916_);
    lean_closure_set(v___f_7917_, 1, v_prio_7912_);
    lean_closure_set(v___f_7917_, 2, v___f_7915_);
    lean_closure_set(v___f_7917_, 3, v_inst_7910_);
    lean_closure_set(v___f_7917_, 4, v_xs_7911_);
    v___x_7918_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_7918_, 0, v___x_7914_);
    v___x_7919_ = lean_unsigned_to_nat(0);
    v___x_7920_ = 0;
    v___x_7921_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(
        v___x_7919_,
        v___x_7920_,
        v___x_7918_,
        v___f_7917_,
    );
    return v___x_7921_;
}
pub unsafe fn l_Std_Async_BaseAsync_raceAll___boxed(
    mut v_00_u03b1_7922_: *mut LeanObject,
    mut v_c_7923_: *mut LeanObject,
    mut v_inst_7924_: *mut LeanObject,
    mut v_inst_7925_: *mut LeanObject,
    mut v_xs_7926_: *mut LeanObject,
    mut v_prio_7927_: *mut LeanObject,
    mut v_a_7928_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7929_: *mut LeanObject = core::ptr::null_mut();
    v_res_7929_ = l_Std_Async_BaseAsync_raceAll(
        v_00_u03b1_7922_,
        v_c_7923_,
        v_inst_7924_,
        v_inst_7925_,
        v_xs_7926_,
        v_prio_7927_,
    );
    lean_dec(v_inst_7924_);
    return v_res_7929_;
}
pub unsafe fn l_Std_Async_EAsync_toBaseIO___redArg(
    mut v_x_7930_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7932_: *mut LeanObject = core::ptr::null_mut();
    v___x_7932_ = lean_apply_1(v_x_7930_, lean_box(0));
    if lean_obj_tag(v___x_7932_) == 0 {
        let mut v_a_7933_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7934_: *mut LeanObject = core::ptr::null_mut();
        v_a_7933_ = lean_ctor_get(v___x_7932_, 0);
        lean_inc(v_a_7933_);
        lean_dec_ref_known(v___x_7932_, 1);
        v___x_7934_ = lean_task_pure(v_a_7933_);
        return v___x_7934_;
    } else {
        let mut v_a_7935_: *mut LeanObject = core::ptr::null_mut();
        v_a_7935_ = lean_ctor_get(v___x_7932_, 0);
        lean_inc_ref(v_a_7935_);
        lean_dec_ref_known(v___x_7932_, 1);
        return v_a_7935_;
    }
}
pub unsafe fn l_Std_Async_EAsync_toBaseIO___redArg___boxed(
    mut v_x_7936_: *mut LeanObject,
    mut v_a_7937_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7938_: *mut LeanObject = core::ptr::null_mut();
    v_res_7938_ = l_Std_Async_EAsync_toBaseIO___redArg(v_x_7936_);
    return v_res_7938_;
}
pub unsafe fn l_Std_Async_EAsync_toBaseIO(
    mut v_00_u03b5_7939_: *mut LeanObject,
    mut v_00_u03b1_7940_: *mut LeanObject,
    mut v_x_7941_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7943_: *mut LeanObject = core::ptr::null_mut();
    v___x_7943_ = lean_apply_1(v_x_7941_, lean_box(0));
    if lean_obj_tag(v___x_7943_) == 0 {
        let mut v_a_7944_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7945_: *mut LeanObject = core::ptr::null_mut();
        v_a_7944_ = lean_ctor_get(v___x_7943_, 0);
        lean_inc(v_a_7944_);
        lean_dec_ref_known(v___x_7943_, 1);
        v___x_7945_ = lean_task_pure(v_a_7944_);
        return v___x_7945_;
    } else {
        let mut v_a_7946_: *mut LeanObject = core::ptr::null_mut();
        v_a_7946_ = lean_ctor_get(v___x_7943_, 0);
        lean_inc_ref(v_a_7946_);
        lean_dec_ref_known(v___x_7943_, 1);
        return v_a_7946_;
    }
}
pub unsafe fn l_Std_Async_EAsync_toBaseIO___boxed(
    mut v_00_u03b5_7947_: *mut LeanObject,
    mut v_00_u03b1_7948_: *mut LeanObject,
    mut v_x_7949_: *mut LeanObject,
    mut v_a_7950_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7951_: *mut LeanObject = core::ptr::null_mut();
    v_res_7951_ = l_Std_Async_EAsync_toBaseIO(v_00_u03b5_7947_, v_00_u03b1_7948_, v_x_7949_);
    return v_res_7951_;
}
pub unsafe fn l_Std_Async_EAsync_ofTask___redArg(
    mut v_x_7952_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7954_: *mut LeanObject = core::ptr::null_mut();
    v___x_7954_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_7954_, 0, v_x_7952_);
    return v___x_7954_;
}
pub unsafe fn l_Std_Async_EAsync_ofTask___redArg___boxed(
    mut v_x_7955_: *mut LeanObject,
    mut v_a_7956_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7957_: *mut LeanObject = core::ptr::null_mut();
    v_res_7957_ = l_Std_Async_EAsync_ofTask___redArg(v_x_7955_);
    return v_res_7957_;
}
pub unsafe fn l_Std_Async_EAsync_ofTask(
    mut v_00_u03b5_7958_: *mut LeanObject,
    mut v_00_u03b1_7959_: *mut LeanObject,
    mut v_x_7960_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7962_: *mut LeanObject = core::ptr::null_mut();
    v___x_7962_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_7962_, 0, v_x_7960_);
    return v___x_7962_;
}
pub unsafe fn l_Std_Async_EAsync_ofTask___boxed(
    mut v_00_u03b5_7963_: *mut LeanObject,
    mut v_00_u03b1_7964_: *mut LeanObject,
    mut v_x_7965_: *mut LeanObject,
    mut v_a_7966_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7967_: *mut LeanObject = core::ptr::null_mut();
    v_res_7967_ = l_Std_Async_EAsync_ofTask(v_00_u03b5_7963_, v_00_u03b1_7964_, v_x_7965_);
    return v_res_7967_;
}
pub unsafe fn l_Std_Async_EAsync_toEIO___redArg(mut v_x_7968_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_7970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7974_: u8 = 0;
    let mut v___x_7975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7979_: u8 = 0;
    let mut v_a_7980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7983_: u8 = 0;
    let mut v___x_7985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7987_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7970_ = lean_apply_1(v_x_7968_, lean_box(0));
                if lean_obj_tag(v___x_7970_) == 0 {
                    v_a_7971_ = lean_ctor_get(v___x_7970_, 0);
                    v_isSharedCheck_7979_ = (!lean_is_exclusive(v___x_7970_)) as u8;
                    if v_isSharedCheck_7979_ == 0 {
                        v___x_7973_ = v___x_7970_;
                        v_isShared_7974_ = v_isSharedCheck_7979_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7971_);
                        lean_dec(v___x_7970_);
                        v___x_7973_ = lean_box(0);
                        v_isShared_7974_ = v_isSharedCheck_7979_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_7980_ = lean_ctor_get(v___x_7970_, 0);
                    v_isSharedCheck_7987_ = (!lean_is_exclusive(v___x_7970_)) as u8;
                    if v_isSharedCheck_7987_ == 0 {
                        v___x_7982_ = v___x_7970_;
                        v_isShared_7983_ = v_isSharedCheck_7987_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_7980_);
                        lean_dec(v___x_7970_);
                        v___x_7982_ = lean_box(0);
                        v_isShared_7983_ = v_isSharedCheck_7987_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7975_ = lean_task_pure(v_a_7971_);
                if v_isShared_7974_ == 0 {
                    lean_ctor_set(v___x_7973_, 0, v___x_7975_);
                    v___x_7977_ = v___x_7973_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7978_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7978_, 0, v___x_7975_);
                    v___x_7977_ = v_reuseFailAlloc_7978_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7977_;
            }
            3 => {
                if v_isShared_7983_ == 0 {
                    lean_ctor_set_tag(v___x_7982_, 0);
                    v___x_7985_ = v___x_7982_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7986_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7986_, 0, v_a_7980_);
                    v___x_7985_ = v_reuseFailAlloc_7986_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7985_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_EAsync_toEIO___redArg___boxed(
    mut v_x_7988_: *mut LeanObject,
    mut v_a_7989_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7990_: *mut LeanObject = core::ptr::null_mut();
    v_res_7990_ = l_Std_Async_EAsync_toEIO___redArg(v_x_7988_);
    return v_res_7990_;
}
pub unsafe fn l_Std_Async_EAsync_toEIO(
    mut v_00_u03b5_7991_: *mut LeanObject,
    mut v_00_u03b1_7992_: *mut LeanObject,
    mut v_x_7993_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7999_: u8 = 0;
    let mut v___x_8000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8004_: u8 = 0;
    let mut v_a_8005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8008_: u8 = 0;
    let mut v___x_8010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8012_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7995_ = lean_apply_1(v_x_7993_, lean_box(0));
                if lean_obj_tag(v___x_7995_) == 0 {
                    v_a_7996_ = lean_ctor_get(v___x_7995_, 0);
                    v_isSharedCheck_8004_ = (!lean_is_exclusive(v___x_7995_)) as u8;
                    if v_isSharedCheck_8004_ == 0 {
                        v___x_7998_ = v___x_7995_;
                        v_isShared_7999_ = v_isSharedCheck_8004_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7996_);
                        lean_dec(v___x_7995_);
                        v___x_7998_ = lean_box(0);
                        v_isShared_7999_ = v_isSharedCheck_8004_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_8005_ = lean_ctor_get(v___x_7995_, 0);
                    v_isSharedCheck_8012_ = (!lean_is_exclusive(v___x_7995_)) as u8;
                    if v_isSharedCheck_8012_ == 0 {
                        v___x_8007_ = v___x_7995_;
                        v_isShared_8008_ = v_isSharedCheck_8012_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_8005_);
                        lean_dec(v___x_7995_);
                        v___x_8007_ = lean_box(0);
                        v_isShared_8008_ = v_isSharedCheck_8012_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_8000_ = lean_task_pure(v_a_7996_);
                if v_isShared_7999_ == 0 {
                    lean_ctor_set(v___x_7998_, 0, v___x_8000_);
                    v___x_8002_ = v___x_7998_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8003_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8003_, 0, v___x_8000_);
                    v___x_8002_ = v_reuseFailAlloc_8003_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8002_;
            }
            3 => {
                if v_isShared_8008_ == 0 {
                    lean_ctor_set_tag(v___x_8007_, 0);
                    v___x_8010_ = v___x_8007_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8011_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8011_, 0, v_a_8005_);
                    v___x_8010_ = v_reuseFailAlloc_8011_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_8010_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_EAsync_toEIO___boxed(
    mut v_00_u03b5_8013_: *mut LeanObject,
    mut v_00_u03b1_8014_: *mut LeanObject,
    mut v_x_8015_: *mut LeanObject,
    mut v_a_8016_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8017_: *mut LeanObject = core::ptr::null_mut();
    v_res_8017_ = l_Std_Async_EAsync_toEIO(v_00_u03b5_8013_, v_00_u03b1_8014_, v_x_8015_);
    return v_res_8017_;
}
pub unsafe fn l_Std_Async_EAsync_ofETask___redArg(
    mut v_x_8018_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8020_: *mut LeanObject = core::ptr::null_mut();
    v___x_8020_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_8020_, 0, v_x_8018_);
    return v___x_8020_;
}
pub unsafe fn l_Std_Async_EAsync_ofETask___redArg___boxed(
    mut v_x_8021_: *mut LeanObject,
    mut v_a_8022_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8023_: *mut LeanObject = core::ptr::null_mut();
    v_res_8023_ = l_Std_Async_EAsync_ofETask___redArg(v_x_8021_);
    return v_res_8023_;
}
pub unsafe fn l_Std_Async_EAsync_ofETask(
    mut v_00_u03b5_8024_: *mut LeanObject,
    mut v_00_u03b1_8025_: *mut LeanObject,
    mut v_x_8026_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8028_: *mut LeanObject = core::ptr::null_mut();
    v___x_8028_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_8028_, 0, v_x_8026_);
    return v___x_8028_;
}
pub unsafe fn l_Std_Async_EAsync_ofETask___boxed(
    mut v_00_u03b5_8029_: *mut LeanObject,
    mut v_00_u03b1_8030_: *mut LeanObject,
    mut v_x_8031_: *mut LeanObject,
    mut v_a_8032_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8033_: *mut LeanObject = core::ptr::null_mut();
    v_res_8033_ = l_Std_Async_EAsync_ofETask(v_00_u03b5_8029_, v_00_u03b1_8030_, v_x_8031_);
    return v_res_8033_;
}
pub unsafe fn l_Std_Async_EAsync_pure___redArg(mut v_a_8034_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_8036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8037_: *mut LeanObject = core::ptr::null_mut();
    v___x_8036_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_8036_, 0, v_a_8034_);
    v___x_8037_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_8037_, 0, v___x_8036_);
    return v___x_8037_;
}
pub unsafe fn l_Std_Async_EAsync_pure___redArg___boxed(
    mut v_a_8038_: *mut LeanObject,
    mut v_a_8039_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8040_: *mut LeanObject = core::ptr::null_mut();
    v_res_8040_ = l_Std_Async_EAsync_pure___redArg(v_a_8038_);
    return v_res_8040_;
}
pub unsafe fn l_Std_Async_EAsync_pure(
    mut v_00_u03b1_8041_: *mut LeanObject,
    mut v_00_u03b5_8042_: *mut LeanObject,
    mut v_a_8043_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8046_: *mut LeanObject = core::ptr::null_mut();
    v___x_8045_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_8045_, 0, v_a_8043_);
    v___x_8046_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_8046_, 0, v___x_8045_);
    return v___x_8046_;
}
pub unsafe fn l_Std_Async_EAsync_pure___boxed(
    mut v_00_u03b1_8047_: *mut LeanObject,
    mut v_00_u03b5_8048_: *mut LeanObject,
    mut v_a_8049_: *mut LeanObject,
    mut v_a_8050_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8051_: *mut LeanObject = core::ptr::null_mut();
    v_res_8051_ = l_Std_Async_EAsync_pure(v_00_u03b1_8047_, v_00_u03b5_8048_, v_a_8049_);
    return v_res_8051_;
}
pub unsafe fn l_Std_Async_EAsync_map___redArg(
    mut v_f_8052_: *mut LeanObject,
    mut v_self_8053_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8063_: u8 = 0;
    let mut v___x_8065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8067_: u8 = 0;
    let mut v_a_8068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8071_: u8 = 0;
    let mut v___x_8072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8076_: u8 = 0;
    let mut v_a_8077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8080_: u8 = 0;
    let mut v___x_8081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8083_: u8 = 0;
    let mut v___x_8084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8088_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8055_ = lean_apply_1(v_self_8053_, lean_box(0));
                if lean_obj_tag(v___x_8055_) == 0 {
                    v_a_8059_ = lean_ctor_get(v___x_8055_, 0);
                    lean_inc(v_a_8059_);
                    lean_dec_ref_known(v___x_8055_, 1);
                    if lean_obj_tag(v_a_8059_) == 0 {
                        lean_dec(v_f_8052_);
                        v_a_8060_ = lean_ctor_get(v_a_8059_, 0);
                        v_isSharedCheck_8067_ = (!lean_is_exclusive(v_a_8059_)) as u8;
                        if v_isSharedCheck_8067_ == 0 {
                            v___x_8062_ = v_a_8059_;
                            v_isShared_8063_ = v_isSharedCheck_8067_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_8060_);
                            lean_dec(v_a_8059_);
                            v___x_8062_ = lean_box(0);
                            v_isShared_8063_ = v_isSharedCheck_8067_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_a_8068_ = lean_ctor_get(v_a_8059_, 0);
                        v_isSharedCheck_8076_ = (!lean_is_exclusive(v_a_8059_)) as u8;
                        if v_isSharedCheck_8076_ == 0 {
                            v___x_8070_ = v_a_8059_;
                            v_isShared_8071_ = v_isSharedCheck_8076_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_8068_);
                            lean_dec(v_a_8059_);
                            v___x_8070_ = lean_box(0);
                            v_isShared_8071_ = v_isSharedCheck_8076_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_a_8077_ = lean_ctor_get(v___x_8055_, 0);
                    v_isSharedCheck_8088_ = (!lean_is_exclusive(v___x_8055_)) as u8;
                    if v_isSharedCheck_8088_ == 0 {
                        v___x_8079_ = v___x_8055_;
                        v_isShared_8080_ = v_isSharedCheck_8088_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_8077_);
                        lean_dec(v___x_8055_);
                        v___x_8079_ = lean_box(0);
                        v_isShared_8080_ = v_isSharedCheck_8088_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v___x_8058_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_8058_, 0, v___y_8057_);
                return v___x_8058_;
            }
            2 => {
                if v_isShared_8063_ == 0 {
                    v___x_8065_ = v___x_8062_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_8066_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8066_, 0, v_a_8060_);
                    v___x_8065_ = v_reuseFailAlloc_8066_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___y_8057_ = v___x_8065_;
                state = 1;
                continue;
            }
            4 => {
                v___x_8072_ = lean_apply_1(v_f_8052_, v_a_8068_);
                if v_isShared_8071_ == 0 {
                    lean_ctor_set(v___x_8070_, 0, v___x_8072_);
                    v___x_8074_ = v___x_8070_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_8075_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8075_, 0, v___x_8072_);
                    v___x_8074_ = v_reuseFailAlloc_8075_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___y_8057_ = v___x_8074_;
                state = 1;
                continue;
            }
            6 => {
                v___x_8081_ = lean_alloc_closure(l_Except_map as *mut core::ffi::c_void, 5, 4);
                lean_closure_set(v___x_8081_, 0, lean_box(0));
                lean_closure_set(v___x_8081_, 1, lean_box(0));
                lean_closure_set(v___x_8081_, 2, lean_box(0));
                lean_closure_set(v___x_8081_, 3, v_f_8052_);
                v___x_8082_ = lean_unsigned_to_nat(0);
                v___x_8083_ = 0;
                v___x_8084_ = lean_task_map(v___x_8081_, v_a_8077_, v___x_8082_, v___x_8083_);
                if v_isShared_8080_ == 0 {
                    lean_ctor_set(v___x_8079_, 0, v___x_8084_);
                    v___x_8086_ = v___x_8079_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_8087_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8087_, 0, v___x_8084_);
                    v___x_8086_ = v_reuseFailAlloc_8087_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_8086_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_EAsync_map___redArg___boxed(
    mut v_f_8089_: *mut LeanObject,
    mut v_self_8090_: *mut LeanObject,
    mut v_a_8091_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8092_: *mut LeanObject = core::ptr::null_mut();
    v_res_8092_ = l_Std_Async_EAsync_map___redArg(v_f_8089_, v_self_8090_);
    return v_res_8092_;
}
pub unsafe fn l_Std_Async_EAsync_map(
    mut v_00_u03b1_8093_: *mut LeanObject,
    mut v_00_u03b2_8094_: *mut LeanObject,
    mut v_00_u03b5_8095_: *mut LeanObject,
    mut v_f_8096_: *mut LeanObject,
    mut v_self_8097_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8107_: u8 = 0;
    let mut v___x_8109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8111_: u8 = 0;
    let mut v_a_8112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8115_: u8 = 0;
    let mut v___x_8116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8120_: u8 = 0;
    let mut v_a_8121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8124_: u8 = 0;
    let mut v___x_8125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8127_: u8 = 0;
    let mut v___x_8128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8132_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8099_ = lean_apply_1(v_self_8097_, lean_box(0));
                if lean_obj_tag(v___x_8099_) == 0 {
                    v_a_8103_ = lean_ctor_get(v___x_8099_, 0);
                    lean_inc(v_a_8103_);
                    lean_dec_ref_known(v___x_8099_, 1);
                    if lean_obj_tag(v_a_8103_) == 0 {
                        lean_dec(v_f_8096_);
                        v_a_8104_ = lean_ctor_get(v_a_8103_, 0);
                        v_isSharedCheck_8111_ = (!lean_is_exclusive(v_a_8103_)) as u8;
                        if v_isSharedCheck_8111_ == 0 {
                            v___x_8106_ = v_a_8103_;
                            v_isShared_8107_ = v_isSharedCheck_8111_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_8104_);
                            lean_dec(v_a_8103_);
                            v___x_8106_ = lean_box(0);
                            v_isShared_8107_ = v_isSharedCheck_8111_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_a_8112_ = lean_ctor_get(v_a_8103_, 0);
                        v_isSharedCheck_8120_ = (!lean_is_exclusive(v_a_8103_)) as u8;
                        if v_isSharedCheck_8120_ == 0 {
                            v___x_8114_ = v_a_8103_;
                            v_isShared_8115_ = v_isSharedCheck_8120_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_8112_);
                            lean_dec(v_a_8103_);
                            v___x_8114_ = lean_box(0);
                            v_isShared_8115_ = v_isSharedCheck_8120_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_a_8121_ = lean_ctor_get(v___x_8099_, 0);
                    v_isSharedCheck_8132_ = (!lean_is_exclusive(v___x_8099_)) as u8;
                    if v_isSharedCheck_8132_ == 0 {
                        v___x_8123_ = v___x_8099_;
                        v_isShared_8124_ = v_isSharedCheck_8132_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_8121_);
                        lean_dec(v___x_8099_);
                        v___x_8123_ = lean_box(0);
                        v_isShared_8124_ = v_isSharedCheck_8132_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v___x_8102_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_8102_, 0, v___y_8101_);
                return v___x_8102_;
            }
            2 => {
                if v_isShared_8107_ == 0 {
                    v___x_8109_ = v___x_8106_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_8110_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8110_, 0, v_a_8104_);
                    v___x_8109_ = v_reuseFailAlloc_8110_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___y_8101_ = v___x_8109_;
                state = 1;
                continue;
            }
            4 => {
                v___x_8116_ = lean_apply_1(v_f_8096_, v_a_8112_);
                if v_isShared_8115_ == 0 {
                    lean_ctor_set(v___x_8114_, 0, v___x_8116_);
                    v___x_8118_ = v___x_8114_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_8119_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8119_, 0, v___x_8116_);
                    v___x_8118_ = v_reuseFailAlloc_8119_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___y_8101_ = v___x_8118_;
                state = 1;
                continue;
            }
            6 => {
                v___x_8125_ = lean_alloc_closure(l_Except_map as *mut core::ffi::c_void, 5, 4);
                lean_closure_set(v___x_8125_, 0, lean_box(0));
                lean_closure_set(v___x_8125_, 1, lean_box(0));
                lean_closure_set(v___x_8125_, 2, lean_box(0));
                lean_closure_set(v___x_8125_, 3, v_f_8096_);
                v___x_8126_ = lean_unsigned_to_nat(0);
                v___x_8127_ = 0;
                v___x_8128_ = lean_task_map(v___x_8125_, v_a_8121_, v___x_8126_, v___x_8127_);
                if v_isShared_8124_ == 0 {
                    lean_ctor_set(v___x_8123_, 0, v___x_8128_);
                    v___x_8130_ = v___x_8123_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_8131_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8131_, 0, v___x_8128_);
                    v___x_8130_ = v_reuseFailAlloc_8131_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_8130_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_EAsync_map___boxed(
    mut v_00_u03b1_8133_: *mut LeanObject,
    mut v_00_u03b2_8134_: *mut LeanObject,
    mut v_00_u03b5_8135_: *mut LeanObject,
    mut v_f_8136_: *mut LeanObject,
    mut v_self_8137_: *mut LeanObject,
    mut v_a_8138_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8139_: *mut LeanObject = core::ptr::null_mut();
    v_res_8139_ = l_Std_Async_EAsync_map(
        v_00_u03b1_8133_,
        v_00_u03b2_8134_,
        v_00_u03b5_8135_,
        v_f_8136_,
        v_self_8137_,
    );
    return v_res_8139_;
}
pub unsafe fn l_Std_Async_EAsync_bind___redArg___lam__0(
    mut v_f_8140_: *mut LeanObject,
    mut v_x_8141_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_8143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8146_: u8 = 0;
    let mut v___x_8148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8151_: u8 = 0;
    let mut v_a_8152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8153_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_8141_) == 0 {
                    lean_dec_ref(v_f_8140_);
                    v_a_8143_ = lean_ctor_get(v_x_8141_, 0);
                    v_isSharedCheck_8151_ = (!lean_is_exclusive(v_x_8141_)) as u8;
                    if v_isSharedCheck_8151_ == 0 {
                        v___x_8145_ = v_x_8141_;
                        v_isShared_8146_ = v_isSharedCheck_8151_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_8143_);
                        lean_dec(v_x_8141_);
                        v___x_8145_ = lean_box(0);
                        v_isShared_8146_ = v_isSharedCheck_8151_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_8152_ = lean_ctor_get(v_x_8141_, 0);
                    lean_inc(v_a_8152_);
                    lean_dec_ref_known(v_x_8141_, 1);
                    v___x_8153_ = lean_apply_2(v_f_8140_, v_a_8152_, lean_box(0));
                    return v___x_8153_;
                }
            }
            1 => {
                if v_isShared_8146_ == 0 {
                    v___x_8148_ = v___x_8145_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8150_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8150_, 0, v_a_8143_);
                    v___x_8148_ = v_reuseFailAlloc_8150_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_8149_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_8149_, 0, v___x_8148_);
                return v___x_8149_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_EAsync_bind___redArg___lam__0___boxed(
    mut v_f_8154_: *mut LeanObject,
    mut v_x_8155_: *mut LeanObject,
    mut v___y_8156_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8157_: *mut LeanObject = core::ptr::null_mut();
    v_res_8157_ = l_Std_Async_EAsync_bind___redArg___lam__0(v_f_8154_, v_x_8155_);
    return v_res_8157_;
}
pub unsafe fn l_Std_Async_EAsync_bind___redArg(
    mut v_self_8158_: *mut LeanObject,
    mut v_f_8159_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8164_: u8 = 0;
    let mut v___x_8165_: *mut LeanObject = core::ptr::null_mut();
    v___x_8161_ = lean_apply_1(v_self_8158_, lean_box(0));
    v___f_8162_ = lean_alloc_closure(
        l_Std_Async_EAsync_bind___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_8162_, 0, v_f_8159_);
    v___x_8163_ = lean_unsigned_to_nat(0);
    v___x_8164_ = 0;
    v___x_8165_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(
        v___x_8163_,
        v___x_8164_,
        v___x_8161_,
        v___f_8162_,
    );
    return v___x_8165_;
}
pub unsafe fn l_Std_Async_EAsync_bind___redArg___boxed(
    mut v_self_8166_: *mut LeanObject,
    mut v_f_8167_: *mut LeanObject,
    mut v_a_8168_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8169_: *mut LeanObject = core::ptr::null_mut();
    v_res_8169_ = l_Std_Async_EAsync_bind___redArg(v_self_8166_, v_f_8167_);
    return v_res_8169_;
}
pub unsafe fn l_Std_Async_EAsync_bind(
    mut v_00_u03b5_8170_: *mut LeanObject,
    mut v_00_u03b1_8171_: *mut LeanObject,
    mut v_00_u03b2_8172_: *mut LeanObject,
    mut v_self_8173_: *mut LeanObject,
    mut v_f_8174_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8179_: u8 = 0;
    let mut v___x_8180_: *mut LeanObject = core::ptr::null_mut();
    v___x_8176_ = lean_apply_1(v_self_8173_, lean_box(0));
    v___f_8177_ = lean_alloc_closure(
        l_Std_Async_EAsync_bind___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_8177_, 0, v_f_8174_);
    v___x_8178_ = lean_unsigned_to_nat(0);
    v___x_8179_ = 0;
    v___x_8180_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(
        v___x_8178_,
        v___x_8179_,
        v___x_8176_,
        v___f_8177_,
    );
    return v___x_8180_;
}
pub unsafe fn l_Std_Async_EAsync_bind___boxed(
    mut v_00_u03b5_8181_: *mut LeanObject,
    mut v_00_u03b1_8182_: *mut LeanObject,
    mut v_00_u03b2_8183_: *mut LeanObject,
    mut v_self_8184_: *mut LeanObject,
    mut v_f_8185_: *mut LeanObject,
    mut v_a_8186_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8187_: *mut LeanObject = core::ptr::null_mut();
    v_res_8187_ = l_Std_Async_EAsync_bind(
        v_00_u03b5_8181_,
        v_00_u03b1_8182_,
        v_00_u03b2_8183_,
        v_self_8184_,
        v_f_8185_,
    );
    return v_res_8187_;
}
pub unsafe fn l_Std_Async_EAsync_lift___redArg(mut v_x_8188_: *mut LeanObject) -> *mut LeanObject {
    let mut v_val_8191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8197_: u8 = 0;
    let mut v___x_8199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8201_: u8 = 0;
    let mut v_a_8202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8205_: u8 = 0;
    let mut v___x_8207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8209_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8193_ = lean_apply_1(v_x_8188_, lean_box(0));
                if lean_obj_tag(v___x_8193_) == 0 {
                    v_a_8194_ = lean_ctor_get(v___x_8193_, 0);
                    v_isSharedCheck_8201_ = (!lean_is_exclusive(v___x_8193_)) as u8;
                    if v_isSharedCheck_8201_ == 0 {
                        v___x_8196_ = v___x_8193_;
                        v_isShared_8197_ = v_isSharedCheck_8201_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_8194_);
                        lean_dec(v___x_8193_);
                        v___x_8196_ = lean_box(0);
                        v_isShared_8197_ = v_isSharedCheck_8201_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_8202_ = lean_ctor_get(v___x_8193_, 0);
                    v_isSharedCheck_8209_ = (!lean_is_exclusive(v___x_8193_)) as u8;
                    if v_isSharedCheck_8209_ == 0 {
                        v___x_8204_ = v___x_8193_;
                        v_isShared_8205_ = v_isSharedCheck_8209_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_8202_);
                        lean_dec(v___x_8193_);
                        v___x_8204_ = lean_box(0);
                        v_isShared_8205_ = v_isSharedCheck_8209_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_8192_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_8192_, 0, v_val_8191_);
                return v___x_8192_;
            }
            2 => {
                if v_isShared_8197_ == 0 {
                    lean_ctor_set_tag(v___x_8196_, 1);
                    v___x_8199_ = v___x_8196_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_8200_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8200_, 0, v_a_8194_);
                    v___x_8199_ = v_reuseFailAlloc_8200_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_val_8191_ = v___x_8199_;
                state = 1;
                continue;
            }
            4 => {
                if v_isShared_8205_ == 0 {
                    lean_ctor_set_tag(v___x_8204_, 0);
                    v___x_8207_ = v___x_8204_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_8208_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8208_, 0, v_a_8202_);
                    v___x_8207_ = v_reuseFailAlloc_8208_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_val_8191_ = v___x_8207_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_EAsync_lift___redArg___boxed(
    mut v_x_8210_: *mut LeanObject,
    mut v_a_8211_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8212_: *mut LeanObject = core::ptr::null_mut();
    v_res_8212_ = l_Std_Async_EAsync_lift___redArg(v_x_8210_);
    return v_res_8212_;
}
pub unsafe fn l_Std_Async_EAsync_lift(
    mut v_00_u03b5_8213_: *mut LeanObject,
    mut v_00_u03b1_8214_: *mut LeanObject,
    mut v_x_8215_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_val_8218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8224_: u8 = 0;
    let mut v___x_8226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8228_: u8 = 0;
    let mut v_a_8229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8232_: u8 = 0;
    let mut v___x_8234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8236_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8220_ = lean_apply_1(v_x_8215_, lean_box(0));
                if lean_obj_tag(v___x_8220_) == 0 {
                    v_a_8221_ = lean_ctor_get(v___x_8220_, 0);
                    v_isSharedCheck_8228_ = (!lean_is_exclusive(v___x_8220_)) as u8;
                    if v_isSharedCheck_8228_ == 0 {
                        v___x_8223_ = v___x_8220_;
                        v_isShared_8224_ = v_isSharedCheck_8228_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_8221_);
                        lean_dec(v___x_8220_);
                        v___x_8223_ = lean_box(0);
                        v_isShared_8224_ = v_isSharedCheck_8228_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_8229_ = lean_ctor_get(v___x_8220_, 0);
                    v_isSharedCheck_8236_ = (!lean_is_exclusive(v___x_8220_)) as u8;
                    if v_isSharedCheck_8236_ == 0 {
                        v___x_8231_ = v___x_8220_;
                        v_isShared_8232_ = v_isSharedCheck_8236_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_8229_);
                        lean_dec(v___x_8220_);
                        v___x_8231_ = lean_box(0);
                        v_isShared_8232_ = v_isSharedCheck_8236_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_8219_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_8219_, 0, v_val_8218_);
                return v___x_8219_;
            }
            2 => {
                if v_isShared_8224_ == 0 {
                    lean_ctor_set_tag(v___x_8223_, 1);
                    v___x_8226_ = v___x_8223_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_8227_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8227_, 0, v_a_8221_);
                    v___x_8226_ = v_reuseFailAlloc_8227_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_val_8218_ = v___x_8226_;
                state = 1;
                continue;
            }
            4 => {
                if v_isShared_8232_ == 0 {
                    lean_ctor_set_tag(v___x_8231_, 0);
                    v___x_8234_ = v___x_8231_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_8235_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8235_, 0, v_a_8229_);
                    v___x_8234_ = v_reuseFailAlloc_8235_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_val_8218_ = v___x_8234_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_EAsync_lift___boxed(
    mut v_00_u03b5_8237_: *mut LeanObject,
    mut v_00_u03b1_8238_: *mut LeanObject,
    mut v_x_8239_: *mut LeanObject,
    mut v_a_8240_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8241_: *mut LeanObject = core::ptr::null_mut();
    v_res_8241_ = l_Std_Async_EAsync_lift(v_00_u03b5_8237_, v_00_u03b1_8238_, v_x_8239_);
    return v_res_8241_;
}
pub unsafe fn l_Std_Async_EAsync_wait___redArg(
    mut v_self_8242_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_8246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8251_: u8 = 0;
    let mut v___x_8253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8255_: u8 = 0;
    let mut v_a_8256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8259_: u8 = 0;
    let mut v___x_8261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8263_: u8 = 0;
    let mut v_a_8264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8266_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8244_ = lean_apply_1(v_self_8242_, lean_box(0));
                if lean_obj_tag(v___x_8244_) == 0 {
                    v_a_8264_ = lean_ctor_get(v___x_8244_, 0);
                    lean_inc(v_a_8264_);
                    lean_dec_ref_known(v___x_8244_, 1);
                    v___x_8265_ = lean_task_pure(v_a_8264_);
                    v_val_8246_ = v___x_8265_;
                    state = 1;
                    continue;
                } else {
                    v_a_8266_ = lean_ctor_get(v___x_8244_, 0);
                    lean_inc_ref(v_a_8266_);
                    lean_dec_ref_known(v___x_8244_, 1);
                    v_val_8246_ = v_a_8266_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_8247_ = lean_task_get_own(v_val_8246_);
                if lean_obj_tag(v___x_8247_) == 0 {
                    v_a_8248_ = lean_ctor_get(v___x_8247_, 0);
                    v_isSharedCheck_8255_ = (!lean_is_exclusive(v___x_8247_)) as u8;
                    if v_isSharedCheck_8255_ == 0 {
                        v___x_8250_ = v___x_8247_;
                        v_isShared_8251_ = v_isSharedCheck_8255_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_8248_);
                        lean_dec(v___x_8247_);
                        v___x_8250_ = lean_box(0);
                        v_isShared_8251_ = v_isSharedCheck_8255_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_8256_ = lean_ctor_get(v___x_8247_, 0);
                    v_isSharedCheck_8263_ = (!lean_is_exclusive(v___x_8247_)) as u8;
                    if v_isSharedCheck_8263_ == 0 {
                        v___x_8258_ = v___x_8247_;
                        v_isShared_8259_ = v_isSharedCheck_8263_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_8256_);
                        lean_dec(v___x_8247_);
                        v___x_8258_ = lean_box(0);
                        v_isShared_8259_ = v_isSharedCheck_8263_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_8251_ == 0 {
                    lean_ctor_set_tag(v___x_8250_, 1);
                    v___x_8253_ = v___x_8250_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_8254_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8254_, 0, v_a_8248_);
                    v___x_8253_ = v_reuseFailAlloc_8254_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_8253_;
            }
            4 => {
                if v_isShared_8259_ == 0 {
                    lean_ctor_set_tag(v___x_8258_, 0);
                    v___x_8261_ = v___x_8258_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_8262_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8262_, 0, v_a_8256_);
                    v___x_8261_ = v_reuseFailAlloc_8262_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_8261_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_EAsync_wait___redArg___boxed(
    mut v_self_8267_: *mut LeanObject,
    mut v_a_8268_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8269_: *mut LeanObject = core::ptr::null_mut();
    v_res_8269_ = l_Std_Async_EAsync_wait___redArg(v_self_8267_);
    return v_res_8269_;
}
pub unsafe fn l_Std_Async_EAsync_wait(
    mut v_00_u03b5_8270_: *mut LeanObject,
    mut v_00_u03b1_8271_: *mut LeanObject,
    mut v_self_8272_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_val_8275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8280_: u8 = 0;
    let mut v___x_8282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8284_: u8 = 0;
    let mut v_a_8285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8288_: u8 = 0;
    let mut v___x_8290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8292_: u8 = 0;
    let mut v___x_8293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8296_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8293_ = lean_apply_1(v_self_8272_, lean_box(0));
                if lean_obj_tag(v___x_8293_) == 0 {
                    v_a_8294_ = lean_ctor_get(v___x_8293_, 0);
                    lean_inc(v_a_8294_);
                    lean_dec_ref_known(v___x_8293_, 1);
                    v___x_8295_ = lean_task_pure(v_a_8294_);
                    v_val_8275_ = v___x_8295_;
                    state = 1;
                    continue;
                } else {
                    v_a_8296_ = lean_ctor_get(v___x_8293_, 0);
                    lean_inc_ref(v_a_8296_);
                    lean_dec_ref_known(v___x_8293_, 1);
                    v_val_8275_ = v_a_8296_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_8276_ = lean_task_get_own(v_val_8275_);
                if lean_obj_tag(v___x_8276_) == 0 {
                    v_a_8277_ = lean_ctor_get(v___x_8276_, 0);
                    v_isSharedCheck_8284_ = (!lean_is_exclusive(v___x_8276_)) as u8;
                    if v_isSharedCheck_8284_ == 0 {
                        v___x_8279_ = v___x_8276_;
                        v_isShared_8280_ = v_isSharedCheck_8284_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_8277_);
                        lean_dec(v___x_8276_);
                        v___x_8279_ = lean_box(0);
                        v_isShared_8280_ = v_isSharedCheck_8284_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_8285_ = lean_ctor_get(v___x_8276_, 0);
                    v_isSharedCheck_8292_ = (!lean_is_exclusive(v___x_8276_)) as u8;
                    if v_isSharedCheck_8292_ == 0 {
                        v___x_8287_ = v___x_8276_;
                        v_isShared_8288_ = v_isSharedCheck_8292_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_8285_);
                        lean_dec(v___x_8276_);
                        v___x_8287_ = lean_box(0);
                        v_isShared_8288_ = v_isSharedCheck_8292_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_8280_ == 0 {
                    lean_ctor_set_tag(v___x_8279_, 1);
                    v___x_8282_ = v___x_8279_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_8283_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8283_, 0, v_a_8277_);
                    v___x_8282_ = v_reuseFailAlloc_8283_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_8282_;
            }
            4 => {
                if v_isShared_8288_ == 0 {
                    lean_ctor_set_tag(v___x_8287_, 0);
                    v___x_8290_ = v___x_8287_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_8291_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8291_, 0, v_a_8285_);
                    v___x_8290_ = v_reuseFailAlloc_8291_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_8290_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_EAsync_wait___boxed(
    mut v_00_u03b5_8297_: *mut LeanObject,
    mut v_00_u03b1_8298_: *mut LeanObject,
    mut v_self_8299_: *mut LeanObject,
    mut v_a_8300_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8301_: *mut LeanObject = core::ptr::null_mut();
    v_res_8301_ = l_Std_Async_EAsync_wait(v_00_u03b5_8297_, v_00_u03b1_8298_, v_self_8299_);
    return v_res_8301_;
}
pub unsafe fn l_Std_Async_EAsync_asTask___redArg___lam__0(
    mut v_x_8302_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_8302_) == 0 {
        let mut v_a_8303_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8304_: *mut LeanObject = core::ptr::null_mut();
        v_a_8303_ = lean_ctor_get(v_x_8302_, 0);
        lean_inc(v_a_8303_);
        lean_dec_ref_known(v_x_8302_, 1);
        v___x_8304_ = lean_task_pure(v_a_8303_);
        return v___x_8304_;
    } else {
        let mut v_a_8305_: *mut LeanObject = core::ptr::null_mut();
        v_a_8305_ = lean_ctor_get(v_x_8302_, 0);
        lean_inc_ref(v_a_8305_);
        lean_dec_ref_known(v_x_8302_, 1);
        return v_a_8305_;
    }
}
pub unsafe fn l_Std_Async_EAsync_asTask___redArg(
    mut v_x_8307_: *mut LeanObject,
    mut v_prio_8308_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8314_: u8 = 0;
    let mut v___x_8315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8316_: *mut LeanObject = core::ptr::null_mut();
    v___x_8310_ = lean_alloc_closure(
        l_Std_Async_BaseAsync_toRawBaseIO___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___x_8310_, 0, lean_box(0));
    lean_closure_set(v___x_8310_, 1, v_x_8307_);
    v___x_8311_ = lean_io_as_task(v___x_8310_, v_prio_8308_);
    v___f_8312_ = l_Std_Async_EAsync_asTask___redArg___closed__0;
    v___x_8313_ = lean_unsigned_to_nat(0);
    v___x_8314_ = 1;
    v___x_8315_ = lean_task_bind(v___x_8311_, v___f_8312_, v___x_8313_, v___x_8314_);
    v___x_8316_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_8316_, 0, v___x_8315_);
    return v___x_8316_;
}
pub unsafe fn l_Std_Async_EAsync_asTask___redArg___boxed(
    mut v_x_8317_: *mut LeanObject,
    mut v_prio_8318_: *mut LeanObject,
    mut v_a_8319_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8320_: *mut LeanObject = core::ptr::null_mut();
    v_res_8320_ = l_Std_Async_EAsync_asTask___redArg(v_x_8317_, v_prio_8318_);
    return v_res_8320_;
}
pub unsafe fn l_Std_Async_EAsync_asTask(
    mut v_00_u03b5_8321_: *mut LeanObject,
    mut v_00_u03b1_8322_: *mut LeanObject,
    mut v_x_8323_: *mut LeanObject,
    mut v_prio_8324_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8330_: u8 = 0;
    let mut v___x_8331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8332_: *mut LeanObject = core::ptr::null_mut();
    v___x_8326_ = lean_alloc_closure(
        l_Std_Async_BaseAsync_toRawBaseIO___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___x_8326_, 0, lean_box(0));
    lean_closure_set(v___x_8326_, 1, v_x_8323_);
    v___x_8327_ = lean_io_as_task(v___x_8326_, v_prio_8324_);
    v___f_8328_ = l_Std_Async_EAsync_asTask___redArg___closed__0;
    v___x_8329_ = lean_unsigned_to_nat(0);
    v___x_8330_ = 1;
    v___x_8331_ = lean_task_bind(v___x_8327_, v___f_8328_, v___x_8329_, v___x_8330_);
    v___x_8332_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_8332_, 0, v___x_8331_);
    return v___x_8332_;
}
pub unsafe fn l_Std_Async_EAsync_asTask___boxed(
    mut v_00_u03b5_8333_: *mut LeanObject,
    mut v_00_u03b1_8334_: *mut LeanObject,
    mut v_x_8335_: *mut LeanObject,
    mut v_prio_8336_: *mut LeanObject,
    mut v_a_8337_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8338_: *mut LeanObject = core::ptr::null_mut();
    v_res_8338_ =
        l_Std_Async_EAsync_asTask(v_00_u03b5_8333_, v_00_u03b1_8334_, v_x_8335_, v_prio_8336_);
    return v_res_8338_;
}
pub unsafe fn l_Std_Async_EAsync_block___redArg(
    mut v_x_8339_: *mut LeanObject,
    mut v_prio_8340_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8346_: u8 = 0;
    let mut v___x_8347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8352_: u8 = 0;
    let mut v___x_8354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8356_: u8 = 0;
    let mut v_a_8357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8360_: u8 = 0;
    let mut v___x_8362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8364_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8342_ = lean_alloc_closure(
                    l_Std_Async_BaseAsync_toRawBaseIO___boxed as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___x_8342_, 0, lean_box(0));
                lean_closure_set(v___x_8342_, 1, v_x_8339_);
                v___x_8343_ = lean_io_as_task(v___x_8342_, v_prio_8340_);
                v___f_8344_ = l_Std_Async_EAsync_asTask___redArg___closed__0;
                v___x_8345_ = lean_unsigned_to_nat(0);
                v___x_8346_ = 1;
                v___x_8347_ = lean_task_bind(v___x_8343_, v___f_8344_, v___x_8345_, v___x_8346_);
                v___x_8348_ = lean_task_get_own(v___x_8347_);
                if lean_obj_tag(v___x_8348_) == 0 {
                    v_a_8349_ = lean_ctor_get(v___x_8348_, 0);
                    v_isSharedCheck_8356_ = (!lean_is_exclusive(v___x_8348_)) as u8;
                    if v_isSharedCheck_8356_ == 0 {
                        v___x_8351_ = v___x_8348_;
                        v_isShared_8352_ = v_isSharedCheck_8356_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_8349_);
                        lean_dec(v___x_8348_);
                        v___x_8351_ = lean_box(0);
                        v_isShared_8352_ = v_isSharedCheck_8356_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_8357_ = lean_ctor_get(v___x_8348_, 0);
                    v_isSharedCheck_8364_ = (!lean_is_exclusive(v___x_8348_)) as u8;
                    if v_isSharedCheck_8364_ == 0 {
                        v___x_8359_ = v___x_8348_;
                        v_isShared_8360_ = v_isSharedCheck_8364_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_8357_);
                        lean_dec(v___x_8348_);
                        v___x_8359_ = lean_box(0);
                        v_isShared_8360_ = v_isSharedCheck_8364_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_8352_ == 0 {
                    lean_ctor_set_tag(v___x_8351_, 1);
                    v___x_8354_ = v___x_8351_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8355_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8355_, 0, v_a_8349_);
                    v___x_8354_ = v_reuseFailAlloc_8355_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8354_;
            }
            3 => {
                if v_isShared_8360_ == 0 {
                    lean_ctor_set_tag(v___x_8359_, 0);
                    v___x_8362_ = v___x_8359_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8363_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8363_, 0, v_a_8357_);
                    v___x_8362_ = v_reuseFailAlloc_8363_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_8362_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_EAsync_block___redArg___boxed(
    mut v_x_8365_: *mut LeanObject,
    mut v_prio_8366_: *mut LeanObject,
    mut v_a_8367_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8368_: *mut LeanObject = core::ptr::null_mut();
    v_res_8368_ = l_Std_Async_EAsync_block___redArg(v_x_8365_, v_prio_8366_);
    return v_res_8368_;
}
pub unsafe fn l_Std_Async_EAsync_block(
    mut v_00_u03b5_8369_: *mut LeanObject,
    mut v_00_u03b1_8370_: *mut LeanObject,
    mut v_x_8371_: *mut LeanObject,
    mut v_prio_8372_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8378_: u8 = 0;
    let mut v___x_8379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8384_: u8 = 0;
    let mut v___x_8386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8388_: u8 = 0;
    let mut v_a_8389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8392_: u8 = 0;
    let mut v___x_8394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8396_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8374_ = lean_alloc_closure(
                    l_Std_Async_BaseAsync_toRawBaseIO___boxed as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___x_8374_, 0, lean_box(0));
                lean_closure_set(v___x_8374_, 1, v_x_8371_);
                v___x_8375_ = lean_io_as_task(v___x_8374_, v_prio_8372_);
                v___f_8376_ = l_Std_Async_EAsync_asTask___redArg___closed__0;
                v___x_8377_ = lean_unsigned_to_nat(0);
                v___x_8378_ = 1;
                v___x_8379_ = lean_task_bind(v___x_8375_, v___f_8376_, v___x_8377_, v___x_8378_);
                v___x_8380_ = lean_task_get_own(v___x_8379_);
                if lean_obj_tag(v___x_8380_) == 0 {
                    v_a_8381_ = lean_ctor_get(v___x_8380_, 0);
                    v_isSharedCheck_8388_ = (!lean_is_exclusive(v___x_8380_)) as u8;
                    if v_isSharedCheck_8388_ == 0 {
                        v___x_8383_ = v___x_8380_;
                        v_isShared_8384_ = v_isSharedCheck_8388_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_8381_);
                        lean_dec(v___x_8380_);
                        v___x_8383_ = lean_box(0);
                        v_isShared_8384_ = v_isSharedCheck_8388_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_8389_ = lean_ctor_get(v___x_8380_, 0);
                    v_isSharedCheck_8396_ = (!lean_is_exclusive(v___x_8380_)) as u8;
                    if v_isSharedCheck_8396_ == 0 {
                        v___x_8391_ = v___x_8380_;
                        v_isShared_8392_ = v_isSharedCheck_8396_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_8389_);
                        lean_dec(v___x_8380_);
                        v___x_8391_ = lean_box(0);
                        v_isShared_8392_ = v_isSharedCheck_8396_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_8384_ == 0 {
                    lean_ctor_set_tag(v___x_8383_, 1);
                    v___x_8386_ = v___x_8383_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8387_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8387_, 0, v_a_8381_);
                    v___x_8386_ = v_reuseFailAlloc_8387_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8386_;
            }
            3 => {
                if v_isShared_8392_ == 0 {
                    lean_ctor_set_tag(v___x_8391_, 0);
                    v___x_8394_ = v___x_8391_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8395_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8395_, 0, v_a_8389_);
                    v___x_8394_ = v_reuseFailAlloc_8395_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_8394_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_EAsync_block___boxed(
    mut v_00_u03b5_8397_: *mut LeanObject,
    mut v_00_u03b1_8398_: *mut LeanObject,
    mut v_x_8399_: *mut LeanObject,
    mut v_prio_8400_: *mut LeanObject,
    mut v_a_8401_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8402_: *mut LeanObject = core::ptr::null_mut();
    v_res_8402_ =
        l_Std_Async_EAsync_block(v_00_u03b5_8397_, v_00_u03b1_8398_, v_x_8399_, v_prio_8400_);
    return v_res_8402_;
}
pub unsafe fn l_Std_Async_EAsync_throw___redArg(mut v_e_8403_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_8405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8406_: *mut LeanObject = core::ptr::null_mut();
    v___x_8405_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_8405_, 0, v_e_8403_);
    v___x_8406_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_8406_, 0, v___x_8405_);
    return v___x_8406_;
}
pub unsafe fn l_Std_Async_EAsync_throw___redArg___boxed(
    mut v_e_8407_: *mut LeanObject,
    mut v_a_8408_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8409_: *mut LeanObject = core::ptr::null_mut();
    v_res_8409_ = l_Std_Async_EAsync_throw___redArg(v_e_8407_);
    return v_res_8409_;
}
pub unsafe fn l_Std_Async_EAsync_throw(
    mut v_00_u03b5_8410_: *mut LeanObject,
    mut v_00_u03b1_8411_: *mut LeanObject,
    mut v_e_8412_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8415_: *mut LeanObject = core::ptr::null_mut();
    v___x_8414_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_8414_, 0, v_e_8412_);
    v___x_8415_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_8415_, 0, v___x_8414_);
    return v___x_8415_;
}
pub unsafe fn l_Std_Async_EAsync_throw___boxed(
    mut v_00_u03b5_8416_: *mut LeanObject,
    mut v_00_u03b1_8417_: *mut LeanObject,
    mut v_e_8418_: *mut LeanObject,
    mut v_a_8419_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8420_: *mut LeanObject = core::ptr::null_mut();
    v_res_8420_ = l_Std_Async_EAsync_throw(v_00_u03b5_8416_, v_00_u03b1_8417_, v_e_8418_);
    return v_res_8420_;
}
pub unsafe fn l_Std_Async_EAsync_tryCatch___redArg___lam__0(
    mut v_f_8421_: *mut LeanObject,
    mut v_x_8422_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_8422_) == 0 {
        let mut v_a_8424_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8425_: *mut LeanObject = core::ptr::null_mut();
        v_a_8424_ = lean_ctor_get(v_x_8422_, 0);
        lean_inc(v_a_8424_);
        lean_dec_ref_known(v_x_8422_, 1);
        v___x_8425_ = lean_apply_2(v_f_8421_, v_a_8424_, lean_box(0));
        return v___x_8425_;
    } else {
        let mut v___x_8426_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_f_8421_);
        v___x_8426_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_8426_, 0, v_x_8422_);
        return v___x_8426_;
    }
}
pub unsafe fn l_Std_Async_EAsync_tryCatch___redArg___lam__0___boxed(
    mut v_f_8427_: *mut LeanObject,
    mut v_x_8428_: *mut LeanObject,
    mut v___y_8429_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8430_: *mut LeanObject = core::ptr::null_mut();
    v_res_8430_ = l_Std_Async_EAsync_tryCatch___redArg___lam__0(v_f_8427_, v_x_8428_);
    return v_res_8430_;
}
pub unsafe fn l_Std_Async_EAsync_tryCatch___redArg(
    mut v_x_8431_: *mut LeanObject,
    mut v_f_8432_: *mut LeanObject,
    mut v_prio_8433_: *mut LeanObject,
    mut v_sync_8434_: u8,
) -> *mut LeanObject {
    let mut v___x_8436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8438_: *mut LeanObject = core::ptr::null_mut();
    v___x_8436_ = lean_apply_1(v_x_8431_, lean_box(0));
    v___f_8437_ = lean_alloc_closure(
        l_Std_Async_EAsync_tryCatch___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_8437_, 0, v_f_8432_);
    v___x_8438_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(
        v_prio_8433_,
        v_sync_8434_,
        v___x_8436_,
        v___f_8437_,
    );
    return v___x_8438_;
}
pub unsafe fn l_Std_Async_EAsync_tryCatch___redArg___boxed(
    mut v_x_8439_: *mut LeanObject,
    mut v_f_8440_: *mut LeanObject,
    mut v_prio_8441_: *mut LeanObject,
    mut v_sync_8442_: *mut LeanObject,
    mut v_a_8443_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sync_boxed_8444_: u8 = 0;
    let mut v_res_8445_: *mut LeanObject = core::ptr::null_mut();
    v_sync_boxed_8444_ = (lean_unbox(v_sync_8442_) as u8);
    v_res_8445_ = l_Std_Async_EAsync_tryCatch___redArg(
        v_x_8439_,
        v_f_8440_,
        v_prio_8441_,
        v_sync_boxed_8444_,
    );
    return v_res_8445_;
}
pub unsafe fn l_Std_Async_EAsync_tryCatch(
    mut v_00_u03b5_8446_: *mut LeanObject,
    mut v_00_u03b1_8447_: *mut LeanObject,
    mut v_x_8448_: *mut LeanObject,
    mut v_f_8449_: *mut LeanObject,
    mut v_prio_8450_: *mut LeanObject,
    mut v_sync_8451_: u8,
) -> *mut LeanObject {
    let mut v___x_8453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8455_: *mut LeanObject = core::ptr::null_mut();
    v___x_8453_ = lean_apply_1(v_x_8448_, lean_box(0));
    v___f_8454_ = lean_alloc_closure(
        l_Std_Async_EAsync_tryCatch___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_8454_, 0, v_f_8449_);
    v___x_8455_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(
        v_prio_8450_,
        v_sync_8451_,
        v___x_8453_,
        v___f_8454_,
    );
    return v___x_8455_;
}
pub unsafe fn l_Std_Async_EAsync_tryCatch___boxed(
    mut v_00_u03b5_8456_: *mut LeanObject,
    mut v_00_u03b1_8457_: *mut LeanObject,
    mut v_x_8458_: *mut LeanObject,
    mut v_f_8459_: *mut LeanObject,
    mut v_prio_8460_: *mut LeanObject,
    mut v_sync_8461_: *mut LeanObject,
    mut v_a_8462_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sync_boxed_8463_: u8 = 0;
    let mut v_res_8464_: *mut LeanObject = core::ptr::null_mut();
    v_sync_boxed_8463_ = (lean_unbox(v_sync_8461_) as u8);
    v_res_8464_ = l_Std_Async_EAsync_tryCatch(
        v_00_u03b5_8456_,
        v_00_u03b1_8457_,
        v_x_8458_,
        v_f_8459_,
        v_prio_8460_,
        v_sync_boxed_8463_,
    );
    return v_res_8464_;
}
pub unsafe fn l_Std_Async_EAsync_tryFinally_x27___redArg___lam__0(
    mut v_a_8465_: *mut LeanObject,
    mut v_____do__lift_8466_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_8468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8471_: u8 = 0;
    let mut v___x_8473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8476_: u8 = 0;
    let mut v___x_8478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8479_: u8 = 0;
    let mut v___x_8481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8484_: u8 = 0;
    let mut v_unused_8485_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_____do__lift_8466_) == 0 {
                    lean_dec(v_a_8465_);
                    v_a_8468_ = lean_ctor_get(v_____do__lift_8466_, 0);
                    v_isSharedCheck_8476_ = (!lean_is_exclusive(v_____do__lift_8466_)) as u8;
                    if v_isSharedCheck_8476_ == 0 {
                        v___x_8470_ = v_____do__lift_8466_;
                        v_isShared_8471_ = v_isSharedCheck_8476_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_8468_);
                        lean_dec(v_____do__lift_8466_);
                        v___x_8470_ = lean_box(0);
                        v_isShared_8471_ = v_isSharedCheck_8476_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_isSharedCheck_8484_ = (!lean_is_exclusive(v_____do__lift_8466_)) as u8;
                    if v_isSharedCheck_8484_ == 0 {
                        v_unused_8485_ = lean_ctor_get(v_____do__lift_8466_, 0);
                        lean_dec(v_unused_8485_);
                        v___x_8478_ = v_____do__lift_8466_;
                        v_isShared_8479_ = v_isSharedCheck_8484_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v_____do__lift_8466_);
                        v___x_8478_ = lean_box(0);
                        v_isShared_8479_ = v_isSharedCheck_8484_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_8471_ == 0 {
                    v___x_8473_ = v___x_8470_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8475_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8475_, 0, v_a_8468_);
                    v___x_8473_ = v_reuseFailAlloc_8475_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_8474_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_8474_, 0, v___x_8473_);
                return v___x_8474_;
            }
            3 => {
                if v_isShared_8479_ == 0 {
                    lean_ctor_set_tag(v___x_8478_, 0);
                    lean_ctor_set(v___x_8478_, 0, v_a_8465_);
                    v___x_8481_ = v___x_8478_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8483_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8483_, 0, v_a_8465_);
                    v___x_8481_ = v_reuseFailAlloc_8483_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_8482_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_8482_, 0, v___x_8481_);
                return v___x_8482_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_EAsync_tryFinally_x27___redArg___lam__0___boxed(
    mut v_a_8486_: *mut LeanObject,
    mut v_____do__lift_8487_: *mut LeanObject,
    mut v___y_8488_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8489_: *mut LeanObject = core::ptr::null_mut();
    v_res_8489_ =
        l_Std_Async_EAsync_tryFinally_x27___redArg___lam__0(v_a_8486_, v_____do__lift_8487_);
    return v_res_8489_;
}
pub unsafe fn l_Std_Async_EAsync_tryFinally_x27___redArg___lam__1(
    mut v_a_8490_: *mut LeanObject,
    mut v_____do__lift_8491_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_8493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8496_: u8 = 0;
    let mut v___x_8498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8501_: u8 = 0;
    let mut v_a_8502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8505_: u8 = 0;
    let mut v___x_8506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8511_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_____do__lift_8491_) == 0 {
                    lean_dec(v_a_8490_);
                    v_a_8493_ = lean_ctor_get(v_____do__lift_8491_, 0);
                    v_isSharedCheck_8501_ = (!lean_is_exclusive(v_____do__lift_8491_)) as u8;
                    if v_isSharedCheck_8501_ == 0 {
                        v___x_8495_ = v_____do__lift_8491_;
                        v_isShared_8496_ = v_isSharedCheck_8501_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_8493_);
                        lean_dec(v_____do__lift_8491_);
                        v___x_8495_ = lean_box(0);
                        v_isShared_8496_ = v_isSharedCheck_8501_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_8502_ = lean_ctor_get(v_____do__lift_8491_, 0);
                    v_isSharedCheck_8511_ = (!lean_is_exclusive(v_____do__lift_8491_)) as u8;
                    if v_isSharedCheck_8511_ == 0 {
                        v___x_8504_ = v_____do__lift_8491_;
                        v_isShared_8505_ = v_isSharedCheck_8511_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_8502_);
                        lean_dec(v_____do__lift_8491_);
                        v___x_8504_ = lean_box(0);
                        v_isShared_8505_ = v_isSharedCheck_8511_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_8496_ == 0 {
                    v___x_8498_ = v___x_8495_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8500_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8500_, 0, v_a_8493_);
                    v___x_8498_ = v_reuseFailAlloc_8500_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_8499_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_8499_, 0, v___x_8498_);
                return v___x_8499_;
            }
            3 => {
                v___x_8506_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_8506_, 0, v_a_8490_);
                lean_ctor_set(v___x_8506_, 1, v_a_8502_);
                if v_isShared_8505_ == 0 {
                    lean_ctor_set(v___x_8504_, 0, v___x_8506_);
                    v___x_8508_ = v___x_8504_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8510_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8510_, 0, v___x_8506_);
                    v___x_8508_ = v_reuseFailAlloc_8510_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_8509_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_8509_, 0, v___x_8508_);
                return v___x_8509_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_EAsync_tryFinally_x27___redArg___lam__1___boxed(
    mut v_a_8512_: *mut LeanObject,
    mut v_____do__lift_8513_: *mut LeanObject,
    mut v___y_8514_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8515_: *mut LeanObject = core::ptr::null_mut();
    v_res_8515_ =
        l_Std_Async_EAsync_tryFinally_x27___redArg___lam__1(v_a_8512_, v_____do__lift_8513_);
    return v_res_8515_;
}
pub unsafe fn l_Std_Async_EAsync_tryFinally_x27___redArg___lam__2(
    mut v_f_8516_: *mut LeanObject,
    mut v_x_8517_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_8519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8524_: u8 = 0;
    let mut v___x_8525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8529_: u8 = 0;
    let mut v___x_8531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8535_: u8 = 0;
    let mut v___x_8536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8538_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_8517_) == 0 {
                    v_a_8519_ = lean_ctor_get(v_x_8517_, 0);
                    lean_inc(v_a_8519_);
                    lean_dec_ref_known(v_x_8517_, 1);
                    v___x_8520_ = lean_box(0);
                    v___x_8521_ = lean_apply_2(v_f_8516_, v___x_8520_, lean_box(0));
                    v___f_8522_ = lean_alloc_closure(
                        l_Std_Async_EAsync_tryFinally_x27___redArg___lam__0___boxed
                            as *mut core::ffi::c_void,
                        3,
                        1,
                    );
                    lean_closure_set(v___f_8522_, 0, v_a_8519_);
                    v___x_8523_ = lean_unsigned_to_nat(0);
                    v___x_8524_ = 0;
                    v___x_8525_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_8523_, v___x_8524_, v___x_8521_, v___f_8522_);
                    return v___x_8525_;
                } else {
                    v_a_8526_ = lean_ctor_get(v_x_8517_, 0);
                    v_isSharedCheck_8538_ = (!lean_is_exclusive(v_x_8517_)) as u8;
                    if v_isSharedCheck_8538_ == 0 {
                        v___x_8528_ = v_x_8517_;
                        v_isShared_8529_ = v_isSharedCheck_8538_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_8526_);
                        lean_dec(v_x_8517_);
                        v___x_8528_ = lean_box(0);
                        v_isShared_8529_ = v_isSharedCheck_8538_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_a_8526_);
                if v_isShared_8529_ == 0 {
                    v___x_8531_ = v___x_8528_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8537_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8537_, 0, v_a_8526_);
                    v___x_8531_ = v_reuseFailAlloc_8537_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_8532_ = lean_apply_2(v_f_8516_, v___x_8531_, lean_box(0));
                v___f_8533_ = lean_alloc_closure(
                    l_Std_Async_EAsync_tryFinally_x27___redArg___lam__1___boxed
                        as *mut core::ffi::c_void,
                    3,
                    1,
                );
                lean_closure_set(v___f_8533_, 0, v_a_8526_);
                v___x_8534_ = lean_unsigned_to_nat(0);
                v___x_8535_ = 0;
                v___x_8536_ =
                    l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(
                        v___x_8534_,
                        v___x_8535_,
                        v___x_8532_,
                        v___f_8533_,
                    );
                return v___x_8536_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_EAsync_tryFinally_x27___redArg___lam__2___boxed(
    mut v_f_8539_: *mut LeanObject,
    mut v_x_8540_: *mut LeanObject,
    mut v___y_8541_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8542_: *mut LeanObject = core::ptr::null_mut();
    v_res_8542_ = l_Std_Async_EAsync_tryFinally_x27___redArg___lam__2(v_f_8539_, v_x_8540_);
    return v_res_8542_;
}
pub unsafe fn l_Std_Async_EAsync_tryFinally_x27___redArg(
    mut v_x_8543_: *mut LeanObject,
    mut v_f_8544_: *mut LeanObject,
    mut v_prio_8545_: *mut LeanObject,
    mut v_sync_8546_: u8,
) -> *mut LeanObject {
    let mut v___x_8548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8550_: *mut LeanObject = core::ptr::null_mut();
    v___x_8548_ = lean_apply_1(v_x_8543_, lean_box(0));
    v___f_8549_ = lean_alloc_closure(
        l_Std_Async_EAsync_tryFinally_x27___redArg___lam__2___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_8549_, 0, v_f_8544_);
    v___x_8550_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(
        v_prio_8545_,
        v_sync_8546_,
        v___x_8548_,
        v___f_8549_,
    );
    return v___x_8550_;
}
pub unsafe fn l_Std_Async_EAsync_tryFinally_x27___redArg___boxed(
    mut v_x_8551_: *mut LeanObject,
    mut v_f_8552_: *mut LeanObject,
    mut v_prio_8553_: *mut LeanObject,
    mut v_sync_8554_: *mut LeanObject,
    mut v_a_8555_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sync_boxed_8556_: u8 = 0;
    let mut v_res_8557_: *mut LeanObject = core::ptr::null_mut();
    v_sync_boxed_8556_ = (lean_unbox(v_sync_8554_) as u8);
    v_res_8557_ = l_Std_Async_EAsync_tryFinally_x27___redArg(
        v_x_8551_,
        v_f_8552_,
        v_prio_8553_,
        v_sync_boxed_8556_,
    );
    return v_res_8557_;
}
pub unsafe fn l_Std_Async_EAsync_tryFinally_x27(
    mut v_00_u03b5_8558_: *mut LeanObject,
    mut v_00_u03b1_8559_: *mut LeanObject,
    mut v_00_u03b2_8560_: *mut LeanObject,
    mut v_x_8561_: *mut LeanObject,
    mut v_f_8562_: *mut LeanObject,
    mut v_prio_8563_: *mut LeanObject,
    mut v_sync_8564_: u8,
) -> *mut LeanObject {
    let mut v___x_8566_: *mut LeanObject = core::ptr::null_mut();
    v___x_8566_ = l_Std_Async_EAsync_tryFinally_x27___redArg(
        v_x_8561_,
        v_f_8562_,
        v_prio_8563_,
        v_sync_8564_,
    );
    return v___x_8566_;
}
pub unsafe fn l_Std_Async_EAsync_tryFinally_x27___boxed(
    mut v_00_u03b5_8567_: *mut LeanObject,
    mut v_00_u03b1_8568_: *mut LeanObject,
    mut v_00_u03b2_8569_: *mut LeanObject,
    mut v_x_8570_: *mut LeanObject,
    mut v_f_8571_: *mut LeanObject,
    mut v_prio_8572_: *mut LeanObject,
    mut v_sync_8573_: *mut LeanObject,
    mut v_a_8574_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sync_boxed_8575_: u8 = 0;
    let mut v_res_8576_: *mut LeanObject = core::ptr::null_mut();
    v_sync_boxed_8575_ = (lean_unbox(v_sync_8573_) as u8);
    v_res_8576_ = l_Std_Async_EAsync_tryFinally_x27(
        v_00_u03b5_8567_,
        v_00_u03b1_8568_,
        v_00_u03b2_8569_,
        v_x_8570_,
        v_f_8571_,
        v_prio_8572_,
        v_sync_boxed_8575_,
    );
    return v_res_8576_;
}
pub unsafe fn l_Std_Async_EAsync_await___redArg(mut v_x_8577_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_8579_: *mut LeanObject = core::ptr::null_mut();
    v___x_8579_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_8579_, 0, v_x_8577_);
    return v___x_8579_;
}
pub unsafe fn l_Std_Async_EAsync_await___redArg___boxed(
    mut v_x_8580_: *mut LeanObject,
    mut v_a_8581_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8582_: *mut LeanObject = core::ptr::null_mut();
    v_res_8582_ = l_Std_Async_EAsync_await___redArg(v_x_8580_);
    return v_res_8582_;
}
pub unsafe fn l_Std_Async_EAsync_await(
    mut v_00_u03b5_8583_: *mut LeanObject,
    mut v_00_u03b1_8584_: *mut LeanObject,
    mut v_x_8585_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8587_: *mut LeanObject = core::ptr::null_mut();
    v___x_8587_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_8587_, 0, v_x_8585_);
    return v___x_8587_;
}
pub unsafe fn l_Std_Async_EAsync_await___boxed(
    mut v_00_u03b5_8588_: *mut LeanObject,
    mut v_00_u03b1_8589_: *mut LeanObject,
    mut v_x_8590_: *mut LeanObject,
    mut v_a_8591_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8592_: *mut LeanObject = core::ptr::null_mut();
    v_res_8592_ = l_Std_Async_EAsync_await(v_00_u03b5_8588_, v_00_u03b1_8589_, v_x_8590_);
    return v_res_8592_;
}
pub unsafe fn l_Std_Async_EAsync_async___redArg(
    mut v_self_8593_: *mut LeanObject,
    mut v_prio_8594_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8600_: u8 = 0;
    let mut v___x_8601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8603_: *mut LeanObject = core::ptr::null_mut();
    v___x_8596_ = lean_alloc_closure(
        l_Std_Async_BaseAsync_toRawBaseIO___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___x_8596_, 0, lean_box(0));
    lean_closure_set(v___x_8596_, 1, v_self_8593_);
    v___x_8597_ = lean_io_as_task(v___x_8596_, v_prio_8594_);
    v___f_8598_ = l_Std_Async_EAsync_asTask___redArg___closed__0;
    v___x_8599_ = lean_unsigned_to_nat(0);
    v___x_8600_ = 1;
    v___x_8601_ = lean_task_bind(v___x_8597_, v___f_8598_, v___x_8599_, v___x_8600_);
    v___x_8602_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_8602_, 0, v___x_8601_);
    v___x_8603_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_8603_, 0, v___x_8602_);
    return v___x_8603_;
}
pub unsafe fn l_Std_Async_EAsync_async___redArg___boxed(
    mut v_self_8604_: *mut LeanObject,
    mut v_prio_8605_: *mut LeanObject,
    mut v_a_8606_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8607_: *mut LeanObject = core::ptr::null_mut();
    v_res_8607_ = l_Std_Async_EAsync_async___redArg(v_self_8604_, v_prio_8605_);
    return v_res_8607_;
}
pub unsafe fn l_Std_Async_EAsync_async(
    mut v_00_u03b5_8608_: *mut LeanObject,
    mut v_00_u03b1_8609_: *mut LeanObject,
    mut v_self_8610_: *mut LeanObject,
    mut v_prio_8611_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8617_: u8 = 0;
    let mut v___x_8618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8620_: *mut LeanObject = core::ptr::null_mut();
    v___x_8613_ = lean_alloc_closure(
        l_Std_Async_BaseAsync_toRawBaseIO___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___x_8613_, 0, lean_box(0));
    lean_closure_set(v___x_8613_, 1, v_self_8610_);
    v___x_8614_ = lean_io_as_task(v___x_8613_, v_prio_8611_);
    v___f_8615_ = l_Std_Async_EAsync_asTask___redArg___closed__0;
    v___x_8616_ = lean_unsigned_to_nat(0);
    v___x_8617_ = 1;
    v___x_8618_ = lean_task_bind(v___x_8614_, v___f_8615_, v___x_8616_, v___x_8617_);
    v___x_8619_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_8619_, 0, v___x_8618_);
    v___x_8620_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_8620_, 0, v___x_8619_);
    return v___x_8620_;
}
pub unsafe fn l_Std_Async_EAsync_async___boxed(
    mut v_00_u03b5_8621_: *mut LeanObject,
    mut v_00_u03b1_8622_: *mut LeanObject,
    mut v_self_8623_: *mut LeanObject,
    mut v_prio_8624_: *mut LeanObject,
    mut v_a_8625_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8626_: *mut LeanObject = core::ptr::null_mut();
    v_res_8626_ = l_Std_Async_EAsync_async(
        v_00_u03b5_8621_,
        v_00_u03b1_8622_,
        v_self_8623_,
        v_prio_8624_,
    );
    return v_res_8626_;
}
pub unsafe fn l_Std_Async_EAsync_instFunctor___lam__0(
    mut v_00_u03b1_8627_: *mut LeanObject,
    mut v_00_u03b2_8628_: *mut LeanObject,
    mut v___y_8629_: *mut LeanObject,
    mut v___y_8630_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8640_: u8 = 0;
    let mut v___x_8642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8644_: u8 = 0;
    let mut v_a_8645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8648_: u8 = 0;
    let mut v___x_8649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8653_: u8 = 0;
    let mut v_a_8654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8657_: u8 = 0;
    let mut v___x_8658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8660_: u8 = 0;
    let mut v___x_8661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8665_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8632_ = lean_apply_1(v___y_8630_, lean_box(0));
                if lean_obj_tag(v___x_8632_) == 0 {
                    v_a_8636_ = lean_ctor_get(v___x_8632_, 0);
                    lean_inc(v_a_8636_);
                    lean_dec_ref_known(v___x_8632_, 1);
                    if lean_obj_tag(v_a_8636_) == 0 {
                        lean_dec(v___y_8629_);
                        v_a_8637_ = lean_ctor_get(v_a_8636_, 0);
                        v_isSharedCheck_8644_ = (!lean_is_exclusive(v_a_8636_)) as u8;
                        if v_isSharedCheck_8644_ == 0 {
                            v___x_8639_ = v_a_8636_;
                            v_isShared_8640_ = v_isSharedCheck_8644_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_8637_);
                            lean_dec(v_a_8636_);
                            v___x_8639_ = lean_box(0);
                            v_isShared_8640_ = v_isSharedCheck_8644_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_a_8645_ = lean_ctor_get(v_a_8636_, 0);
                        v_isSharedCheck_8653_ = (!lean_is_exclusive(v_a_8636_)) as u8;
                        if v_isSharedCheck_8653_ == 0 {
                            v___x_8647_ = v_a_8636_;
                            v_isShared_8648_ = v_isSharedCheck_8653_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_8645_);
                            lean_dec(v_a_8636_);
                            v___x_8647_ = lean_box(0);
                            v_isShared_8648_ = v_isSharedCheck_8653_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_a_8654_ = lean_ctor_get(v___x_8632_, 0);
                    v_isSharedCheck_8665_ = (!lean_is_exclusive(v___x_8632_)) as u8;
                    if v_isSharedCheck_8665_ == 0 {
                        v___x_8656_ = v___x_8632_;
                        v_isShared_8657_ = v_isSharedCheck_8665_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_8654_);
                        lean_dec(v___x_8632_);
                        v___x_8656_ = lean_box(0);
                        v_isShared_8657_ = v_isSharedCheck_8665_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v___x_8635_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_8635_, 0, v___y_8634_);
                return v___x_8635_;
            }
            2 => {
                if v_isShared_8640_ == 0 {
                    v___x_8642_ = v___x_8639_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_8643_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8643_, 0, v_a_8637_);
                    v___x_8642_ = v_reuseFailAlloc_8643_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___y_8634_ = v___x_8642_;
                state = 1;
                continue;
            }
            4 => {
                v___x_8649_ = lean_apply_1(v___y_8629_, v_a_8645_);
                if v_isShared_8648_ == 0 {
                    lean_ctor_set(v___x_8647_, 0, v___x_8649_);
                    v___x_8651_ = v___x_8647_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_8652_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8652_, 0, v___x_8649_);
                    v___x_8651_ = v_reuseFailAlloc_8652_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___y_8634_ = v___x_8651_;
                state = 1;
                continue;
            }
            6 => {
                v___x_8658_ = lean_alloc_closure(l_Except_map as *mut core::ffi::c_void, 5, 4);
                lean_closure_set(v___x_8658_, 0, lean_box(0));
                lean_closure_set(v___x_8658_, 1, lean_box(0));
                lean_closure_set(v___x_8658_, 2, lean_box(0));
                lean_closure_set(v___x_8658_, 3, v___y_8629_);
                v___x_8659_ = lean_unsigned_to_nat(0);
                v___x_8660_ = 0;
                v___x_8661_ = lean_task_map(v___x_8658_, v_a_8654_, v___x_8659_, v___x_8660_);
                if v_isShared_8657_ == 0 {
                    lean_ctor_set(v___x_8656_, 0, v___x_8661_);
                    v___x_8663_ = v___x_8656_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_8664_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8664_, 0, v___x_8661_);
                    v___x_8663_ = v_reuseFailAlloc_8664_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_8663_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_EAsync_instFunctor___lam__0___boxed(
    mut v_00_u03b1_8666_: *mut LeanObject,
    mut v_00_u03b2_8667_: *mut LeanObject,
    mut v___y_8668_: *mut LeanObject,
    mut v___y_8669_: *mut LeanObject,
    mut v___y_8670_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8671_: *mut LeanObject = core::ptr::null_mut();
    v_res_8671_ = l_Std_Async_EAsync_instFunctor___lam__0(
        v_00_u03b1_8666_,
        v_00_u03b2_8667_,
        v___y_8668_,
        v___y_8669_,
    );
    return v_res_8671_;
}
pub unsafe fn l_Std_Async_EAsync_instFunctor___lam__1(
    mut v___f_8672_: *mut LeanObject,
    mut v_00_u03b1_8673_: *mut LeanObject,
    mut v_00_u03b2_8674_: *mut LeanObject,
    mut v___y_8675_: *mut LeanObject,
    mut v___y_8676_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8679_: *mut LeanObject = core::ptr::null_mut();
    v___x_8678_ = lean_alloc_closure(l_Function_const___boxed as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___x_8678_, 0, lean_box(0));
    lean_closure_set(v___x_8678_, 1, lean_box(0));
    lean_closure_set(v___x_8678_, 2, v___y_8675_);
    v___x_8679_ = lean_apply_5(
        v___f_8672_,
        lean_box(0),
        lean_box(0),
        v___x_8678_,
        v___y_8676_,
        lean_box(0),
    );
    return v___x_8679_;
}
pub unsafe fn l_Std_Async_EAsync_instFunctor___lam__1___boxed(
    mut v___f_8680_: *mut LeanObject,
    mut v_00_u03b1_8681_: *mut LeanObject,
    mut v_00_u03b2_8682_: *mut LeanObject,
    mut v___y_8683_: *mut LeanObject,
    mut v___y_8684_: *mut LeanObject,
    mut v___y_8685_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8686_: *mut LeanObject = core::ptr::null_mut();
    v_res_8686_ = l_Std_Async_EAsync_instFunctor___lam__1(
        v___f_8680_,
        v_00_u03b1_8681_,
        v_00_u03b2_8682_,
        v___y_8683_,
        v___y_8684_,
    );
    return v_res_8686_;
}
pub unsafe fn l_Std_Async_EAsync_instFunctor(
    mut v_00_u03b5_8693_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8694_: *mut LeanObject = core::ptr::null_mut();
    v___x_8694_ = l_Std_Async_EAsync_instFunctor___closed__2;
    return v___x_8694_;
}
pub unsafe fn l_Std_Async_EAsync_instMonad___lam__0(
    mut v_00_u03b1_8695_: *mut LeanObject,
    mut v___y_8696_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8699_: *mut LeanObject = core::ptr::null_mut();
    v___x_8698_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_8698_, 0, v___y_8696_);
    v___x_8699_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_8699_, 0, v___x_8698_);
    return v___x_8699_;
}
pub unsafe fn l_Std_Async_EAsync_instMonad___lam__0___boxed(
    mut v_00_u03b1_8700_: *mut LeanObject,
    mut v___y_8701_: *mut LeanObject,
    mut v___y_8702_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8703_: *mut LeanObject = core::ptr::null_mut();
    v_res_8703_ = l_Std_Async_EAsync_instMonad___lam__0(v_00_u03b1_8700_, v___y_8701_);
    return v_res_8703_;
}
pub unsafe fn l_Std_Async_EAsync_instMonad___lam__1(
    mut v_x_8704_: *mut LeanObject,
    mut v_x_8705_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_8707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8710_: u8 = 0;
    let mut v___x_8712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8715_: u8 = 0;
    let mut v_a_8716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8726_: u8 = 0;
    let mut v___x_8728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8730_: u8 = 0;
    let mut v_a_8731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8734_: u8 = 0;
    let mut v___x_8735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8739_: u8 = 0;
    let mut v_a_8740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8743_: u8 = 0;
    let mut v___x_8744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8746_: u8 = 0;
    let mut v___x_8747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8751_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_8705_) == 0 {
                    lean_dec_ref(v_x_8704_);
                    v_a_8707_ = lean_ctor_get(v_x_8705_, 0);
                    v_isSharedCheck_8715_ = (!lean_is_exclusive(v_x_8705_)) as u8;
                    if v_isSharedCheck_8715_ == 0 {
                        v___x_8709_ = v_x_8705_;
                        v_isShared_8710_ = v_isSharedCheck_8715_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_8707_);
                        lean_dec(v_x_8705_);
                        v___x_8709_ = lean_box(0);
                        v_isShared_8710_ = v_isSharedCheck_8715_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_8716_ = lean_ctor_get(v_x_8705_, 0);
                    lean_inc(v_a_8716_);
                    lean_dec_ref_known(v_x_8705_, 1);
                    v___x_8717_ = lean_box(0);
                    v___x_8718_ = lean_apply_2(v_x_8704_, v___x_8717_, lean_box(0));
                    if lean_obj_tag(v___x_8718_) == 0 {
                        v_a_8722_ = lean_ctor_get(v___x_8718_, 0);
                        lean_inc(v_a_8722_);
                        lean_dec_ref_known(v___x_8718_, 1);
                        if lean_obj_tag(v_a_8722_) == 0 {
                            lean_dec(v_a_8716_);
                            v_a_8723_ = lean_ctor_get(v_a_8722_, 0);
                            v_isSharedCheck_8730_ = (!lean_is_exclusive(v_a_8722_)) as u8;
                            if v_isSharedCheck_8730_ == 0 {
                                v___x_8725_ = v_a_8722_;
                                v_isShared_8726_ = v_isSharedCheck_8730_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_a_8723_);
                                lean_dec(v_a_8722_);
                                v___x_8725_ = lean_box(0);
                                v_isShared_8726_ = v_isSharedCheck_8730_;
                                state = 4;
                                continue;
                            }
                        } else {
                            v_a_8731_ = lean_ctor_get(v_a_8722_, 0);
                            v_isSharedCheck_8739_ = (!lean_is_exclusive(v_a_8722_)) as u8;
                            if v_isSharedCheck_8739_ == 0 {
                                v___x_8733_ = v_a_8722_;
                                v_isShared_8734_ = v_isSharedCheck_8739_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_a_8731_);
                                lean_dec(v_a_8722_);
                                v___x_8733_ = lean_box(0);
                                v_isShared_8734_ = v_isSharedCheck_8739_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        v_a_8740_ = lean_ctor_get(v___x_8718_, 0);
                        v_isSharedCheck_8751_ = (!lean_is_exclusive(v___x_8718_)) as u8;
                        if v_isSharedCheck_8751_ == 0 {
                            v___x_8742_ = v___x_8718_;
                            v_isShared_8743_ = v_isSharedCheck_8751_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_8740_);
                            lean_dec(v___x_8718_);
                            v___x_8742_ = lean_box(0);
                            v_isShared_8743_ = v_isSharedCheck_8751_;
                            state = 8;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_8710_ == 0 {
                    v___x_8712_ = v___x_8709_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8714_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8714_, 0, v_a_8707_);
                    v___x_8712_ = v_reuseFailAlloc_8714_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_8713_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_8713_, 0, v___x_8712_);
                return v___x_8713_;
            }
            3 => {
                v___x_8721_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_8721_, 0, v___y_8720_);
                return v___x_8721_;
            }
            4 => {
                if v_isShared_8726_ == 0 {
                    v___x_8728_ = v___x_8725_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_8729_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8729_, 0, v_a_8723_);
                    v___x_8728_ = v_reuseFailAlloc_8729_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___y_8720_ = v___x_8728_;
                state = 3;
                continue;
            }
            6 => {
                v___x_8735_ = lean_apply_1(v_a_8716_, v_a_8731_);
                if v_isShared_8734_ == 0 {
                    lean_ctor_set(v___x_8733_, 0, v___x_8735_);
                    v___x_8737_ = v___x_8733_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_8738_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8738_, 0, v___x_8735_);
                    v___x_8737_ = v_reuseFailAlloc_8738_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_8720_ = v___x_8737_;
                state = 3;
                continue;
            }
            8 => {
                v___x_8744_ = lean_alloc_closure(l_Except_map as *mut core::ffi::c_void, 5, 4);
                lean_closure_set(v___x_8744_, 0, lean_box(0));
                lean_closure_set(v___x_8744_, 1, lean_box(0));
                lean_closure_set(v___x_8744_, 2, lean_box(0));
                lean_closure_set(v___x_8744_, 3, v_a_8716_);
                v___x_8745_ = lean_unsigned_to_nat(0);
                v___x_8746_ = 0;
                v___x_8747_ = lean_task_map(v___x_8744_, v_a_8740_, v___x_8745_, v___x_8746_);
                if v_isShared_8743_ == 0 {
                    lean_ctor_set(v___x_8742_, 0, v___x_8747_);
                    v___x_8749_ = v___x_8742_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_8750_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8750_, 0, v___x_8747_);
                    v___x_8749_ = v_reuseFailAlloc_8750_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_8749_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_EAsync_instMonad___lam__1___boxed(
    mut v_x_8752_: *mut LeanObject,
    mut v_x_8753_: *mut LeanObject,
    mut v___y_8754_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8755_: *mut LeanObject = core::ptr::null_mut();
    v_res_8755_ = l_Std_Async_EAsync_instMonad___lam__1(v_x_8752_, v_x_8753_);
    return v_res_8755_;
}
pub unsafe fn l_Std_Async_EAsync_instMonad___lam__2(
    mut v_00_u03b1_8756_: *mut LeanObject,
    mut v_00_u03b2_8757_: *mut LeanObject,
    mut v_f_8758_: *mut LeanObject,
    mut v_x_8759_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8764_: u8 = 0;
    let mut v___x_8765_: *mut LeanObject = core::ptr::null_mut();
    v___x_8761_ = lean_apply_1(v_f_8758_, lean_box(0));
    v___f_8762_ = lean_alloc_closure(
        l_Std_Async_EAsync_instMonad___lam__1___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_8762_, 0, v_x_8759_);
    v___x_8763_ = lean_unsigned_to_nat(0);
    v___x_8764_ = 0;
    v___x_8765_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(
        v___x_8763_,
        v___x_8764_,
        v___x_8761_,
        v___f_8762_,
    );
    return v___x_8765_;
}
pub unsafe fn l_Std_Async_EAsync_instMonad___lam__2___boxed(
    mut v_00_u03b1_8766_: *mut LeanObject,
    mut v_00_u03b2_8767_: *mut LeanObject,
    mut v_f_8768_: *mut LeanObject,
    mut v_x_8769_: *mut LeanObject,
    mut v___y_8770_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8771_: *mut LeanObject = core::ptr::null_mut();
    v_res_8771_ = l_Std_Async_EAsync_instMonad___lam__2(
        v_00_u03b1_8766_,
        v_00_u03b2_8767_,
        v_f_8768_,
        v_x_8769_,
    );
    return v_res_8771_;
}
pub unsafe fn l_Std_Async_EAsync_instMonad___lam__3(
    mut v___f_8772_: *mut LeanObject,
    mut v_a_8773_: *mut LeanObject,
    mut v_x_8774_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_8776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8779_: u8 = 0;
    let mut v___x_8781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8784_: u8 = 0;
    let mut v___x_8785_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_8774_) == 0 {
                    lean_dec(v_a_8773_);
                    lean_dec_ref(v___f_8772_);
                    v_a_8776_ = lean_ctor_get(v_x_8774_, 0);
                    v_isSharedCheck_8784_ = (!lean_is_exclusive(v_x_8774_)) as u8;
                    if v_isSharedCheck_8784_ == 0 {
                        v___x_8778_ = v_x_8774_;
                        v_isShared_8779_ = v_isSharedCheck_8784_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_8776_);
                        lean_dec(v_x_8774_);
                        v___x_8778_ = lean_box(0);
                        v_isShared_8779_ = v_isSharedCheck_8784_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v_x_8774_, 1);
                    v___x_8785_ = lean_apply_3(v___f_8772_, lean_box(0), v_a_8773_, lean_box(0));
                    return v___x_8785_;
                }
            }
            1 => {
                if v_isShared_8779_ == 0 {
                    v___x_8781_ = v___x_8778_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8783_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8783_, 0, v_a_8776_);
                    v___x_8781_ = v_reuseFailAlloc_8783_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_8782_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_8782_, 0, v___x_8781_);
                return v___x_8782_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_EAsync_instMonad___lam__3___boxed(
    mut v___f_8786_: *mut LeanObject,
    mut v_a_8787_: *mut LeanObject,
    mut v_x_8788_: *mut LeanObject,
    mut v___y_8789_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8790_: *mut LeanObject = core::ptr::null_mut();
    v_res_8790_ = l_Std_Async_EAsync_instMonad___lam__3(v___f_8786_, v_a_8787_, v_x_8788_);
    return v_res_8790_;
}
pub unsafe fn l_Std_Async_EAsync_instMonad___lam__4(
    mut v_y_8791_: *mut LeanObject,
    mut v___f_8792_: *mut LeanObject,
    mut v_x_8793_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_8793_) == 0 {
        let mut v___x_8795_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v___f_8792_);
        lean_dec_ref(v_y_8791_);
        v___x_8795_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_8795_, 0, v_x_8793_);
        return v___x_8795_;
    } else {
        let mut v_a_8796_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8797_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8798_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_8799_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8800_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8801_: u8 = 0;
        let mut v___x_8802_: *mut LeanObject = core::ptr::null_mut();
        v_a_8796_ = lean_ctor_get(v_x_8793_, 0);
        lean_inc(v_a_8796_);
        lean_dec_ref_known(v_x_8793_, 1);
        v___x_8797_ = lean_box(0);
        v___x_8798_ = lean_apply_2(v_y_8791_, v___x_8797_, lean_box(0));
        v___f_8799_ = lean_alloc_closure(
            l_Std_Async_EAsync_instMonad___lam__3___boxed as *mut core::ffi::c_void,
            4,
            2,
        );
        lean_closure_set(v___f_8799_, 0, v___f_8792_);
        lean_closure_set(v___f_8799_, 1, v_a_8796_);
        v___x_8800_ = lean_unsigned_to_nat(0);
        v___x_8801_ = 0;
        v___x_8802_ =
            l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(
                v___x_8800_,
                v___x_8801_,
                v___x_8798_,
                v___f_8799_,
            );
        return v___x_8802_;
    }
}
pub unsafe fn l_Std_Async_EAsync_instMonad___lam__4___boxed(
    mut v_y_8803_: *mut LeanObject,
    mut v___f_8804_: *mut LeanObject,
    mut v_x_8805_: *mut LeanObject,
    mut v___y_8806_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8807_: *mut LeanObject = core::ptr::null_mut();
    v_res_8807_ = l_Std_Async_EAsync_instMonad___lam__4(v_y_8803_, v___f_8804_, v_x_8805_);
    return v_res_8807_;
}
pub unsafe fn l_Std_Async_EAsync_instMonad___lam__5(
    mut v___f_8808_: *mut LeanObject,
    mut v_00_u03b1_8809_: *mut LeanObject,
    mut v_00_u03b2_8810_: *mut LeanObject,
    mut v_x_8811_: *mut LeanObject,
    mut v_y_8812_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8817_: u8 = 0;
    let mut v___x_8818_: *mut LeanObject = core::ptr::null_mut();
    v___x_8814_ = lean_apply_1(v_x_8811_, lean_box(0));
    v___f_8815_ = lean_alloc_closure(
        l_Std_Async_EAsync_instMonad___lam__4___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_8815_, 0, v_y_8812_);
    lean_closure_set(v___f_8815_, 1, v___f_8808_);
    v___x_8816_ = lean_unsigned_to_nat(0);
    v___x_8817_ = 0;
    v___x_8818_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(
        v___x_8816_,
        v___x_8817_,
        v___x_8814_,
        v___f_8815_,
    );
    return v___x_8818_;
}
pub unsafe fn l_Std_Async_EAsync_instMonad___lam__5___boxed(
    mut v___f_8819_: *mut LeanObject,
    mut v_00_u03b1_8820_: *mut LeanObject,
    mut v_00_u03b2_8821_: *mut LeanObject,
    mut v_x_8822_: *mut LeanObject,
    mut v_y_8823_: *mut LeanObject,
    mut v___y_8824_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8825_: *mut LeanObject = core::ptr::null_mut();
    v_res_8825_ = l_Std_Async_EAsync_instMonad___lam__5(
        v___f_8819_,
        v_00_u03b1_8820_,
        v_00_u03b2_8821_,
        v_x_8822_,
        v_y_8823_,
    );
    return v_res_8825_;
}
pub unsafe fn l_Std_Async_EAsync_instMonad___lam__6(
    mut v_y_8826_: *mut LeanObject,
    mut v_x_8827_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_8829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8832_: u8 = 0;
    let mut v___x_8834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8837_: u8 = 0;
    let mut v___x_8838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8839_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_8827_) == 0 {
                    lean_dec_ref(v_y_8826_);
                    v_a_8829_ = lean_ctor_get(v_x_8827_, 0);
                    v_isSharedCheck_8837_ = (!lean_is_exclusive(v_x_8827_)) as u8;
                    if v_isSharedCheck_8837_ == 0 {
                        v___x_8831_ = v_x_8827_;
                        v_isShared_8832_ = v_isSharedCheck_8837_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_8829_);
                        lean_dec(v_x_8827_);
                        v___x_8831_ = lean_box(0);
                        v_isShared_8832_ = v_isSharedCheck_8837_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v_x_8827_, 1);
                    v___x_8838_ = lean_box(0);
                    v___x_8839_ = lean_apply_2(v_y_8826_, v___x_8838_, lean_box(0));
                    return v___x_8839_;
                }
            }
            1 => {
                if v_isShared_8832_ == 0 {
                    v___x_8834_ = v___x_8831_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8836_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8836_, 0, v_a_8829_);
                    v___x_8834_ = v_reuseFailAlloc_8836_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_8835_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_8835_, 0, v___x_8834_);
                return v___x_8835_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_EAsync_instMonad___lam__6___boxed(
    mut v_y_8840_: *mut LeanObject,
    mut v_x_8841_: *mut LeanObject,
    mut v___y_8842_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8843_: *mut LeanObject = core::ptr::null_mut();
    v_res_8843_ = l_Std_Async_EAsync_instMonad___lam__6(v_y_8840_, v_x_8841_);
    return v_res_8843_;
}
pub unsafe fn l_Std_Async_EAsync_instMonad___lam__7(
    mut v_00_u03b1_8844_: *mut LeanObject,
    mut v_00_u03b2_8845_: *mut LeanObject,
    mut v_x_8846_: *mut LeanObject,
    mut v_y_8847_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8852_: u8 = 0;
    let mut v___x_8853_: *mut LeanObject = core::ptr::null_mut();
    v___x_8849_ = lean_apply_1(v_x_8846_, lean_box(0));
    v___f_8850_ = lean_alloc_closure(
        l_Std_Async_EAsync_instMonad___lam__6___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_8850_, 0, v_y_8847_);
    v___x_8851_ = lean_unsigned_to_nat(0);
    v___x_8852_ = 0;
    v___x_8853_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(
        v___x_8851_,
        v___x_8852_,
        v___x_8849_,
        v___f_8850_,
    );
    return v___x_8853_;
}
pub unsafe fn l_Std_Async_EAsync_instMonad___lam__7___boxed(
    mut v_00_u03b1_8854_: *mut LeanObject,
    mut v_00_u03b2_8855_: *mut LeanObject,
    mut v_x_8856_: *mut LeanObject,
    mut v_y_8857_: *mut LeanObject,
    mut v___y_8858_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8859_: *mut LeanObject = core::ptr::null_mut();
    v_res_8859_ = l_Std_Async_EAsync_instMonad___lam__7(
        v_00_u03b1_8854_,
        v_00_u03b2_8855_,
        v_x_8856_,
        v_y_8857_,
    );
    return v_res_8859_;
}
pub unsafe fn _init_l_Std_Async_EAsync_instMonad___closed__4() -> *mut LeanObject {
    let mut v___x_8865_: *mut LeanObject = core::ptr::null_mut();
    v___x_8865_ = l_Std_Async_EAsync_instFunctor(lean_box(0));
    return v___x_8865_;
}
pub unsafe fn _init_l_Std_Async_EAsync_instMonad___closed__5() -> *mut LeanObject {
    let mut v___f_8866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8871_: *mut LeanObject = core::ptr::null_mut();
    v___f_8866_ = l_Std_Async_EAsync_instMonad___closed__3;
    v___f_8867_ = l_Std_Async_EAsync_instMonad___closed__2;
    v___f_8868_ = l_Std_Async_EAsync_instMonad___closed__1;
    v___f_8869_ = l_Std_Async_EAsync_instMonad___closed__0;
    v___x_8870_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_EAsync_instMonad___closed__4),
        core::ptr::addr_of_mut!(l_Std_Async_EAsync_instMonad___closed__4_once),
        _init_l_Std_Async_EAsync_instMonad___closed__4,
    );
    v___x_8871_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_8871_, 0, v___x_8870_);
    lean_ctor_set(v___x_8871_, 1, v___f_8869_);
    lean_ctor_set(v___x_8871_, 2, v___f_8868_);
    lean_ctor_set(v___x_8871_, 3, v___f_8867_);
    lean_ctor_set(v___x_8871_, 4, v___f_8866_);
    return v___x_8871_;
}
pub unsafe fn _init_l_Std_Async_EAsync_instMonad___closed__7() -> *mut LeanObject {
    let mut v___x_8873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8875_: *mut LeanObject = core::ptr::null_mut();
    v___x_8873_ = l_Std_Async_EAsync_instMonad___closed__6;
    v___x_8874_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_EAsync_instMonad___closed__5),
        core::ptr::addr_of_mut!(l_Std_Async_EAsync_instMonad___closed__5_once),
        _init_l_Std_Async_EAsync_instMonad___closed__5,
    );
    v___x_8875_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_8875_, 0, v___x_8874_);
    lean_ctor_set(v___x_8875_, 1, v___x_8873_);
    return v___x_8875_;
}
pub unsafe fn l_Std_Async_EAsync_instMonad(
    mut v_00_u03b5_8876_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8877_: *mut LeanObject = core::ptr::null_mut();
    v___x_8877_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_EAsync_instMonad___closed__7),
        core::ptr::addr_of_mut!(l_Std_Async_EAsync_instMonad___closed__7_once),
        _init_l_Std_Async_EAsync_instMonad___closed__7,
    );
    return v___x_8877_;
}
pub unsafe fn l_Std_Async_EAsync_instMonadLiftEIO(
    mut v_00_u03b5_8879_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8880_: *mut LeanObject = core::ptr::null_mut();
    v___x_8880_ = l_Std_Async_EAsync_instMonadLiftEIO___closed__0;
    return v___x_8880_;
}
pub unsafe fn l_Std_Async_EAsync_instMonadExcept___lam__1(
    mut v_00_u03b1_8881_: *mut LeanObject,
    mut v_x_8882_: *mut LeanObject,
    mut v_f_8883_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8888_: u8 = 0;
    let mut v___x_8889_: *mut LeanObject = core::ptr::null_mut();
    v___x_8885_ = lean_apply_1(v_x_8882_, lean_box(0));
    v___f_8886_ = lean_alloc_closure(
        l_Std_Async_EAsync_tryCatch___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_8886_, 0, v_f_8883_);
    v___x_8887_ = lean_unsigned_to_nat(0);
    v___x_8888_ = 0;
    v___x_8889_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(
        v___x_8887_,
        v___x_8888_,
        v___x_8885_,
        v___f_8886_,
    );
    return v___x_8889_;
}
pub unsafe fn l_Std_Async_EAsync_instMonadExcept___lam__1___boxed(
    mut v_00_u03b1_8890_: *mut LeanObject,
    mut v_x_8891_: *mut LeanObject,
    mut v_f_8892_: *mut LeanObject,
    mut v___y_8893_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8894_: *mut LeanObject = core::ptr::null_mut();
    v_res_8894_ =
        l_Std_Async_EAsync_instMonadExcept___lam__1(v_00_u03b1_8890_, v_x_8891_, v_f_8892_);
    return v_res_8894_;
}
pub unsafe fn l_Std_Async_EAsync_instMonadExcept(
    mut v_00_u03b5_8900_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8901_: *mut LeanObject = core::ptr::null_mut();
    v___x_8901_ = l_Std_Async_EAsync_instMonadExcept___closed__2;
    return v___x_8901_;
}
pub unsafe fn l_Std_Async_EAsync_instMonadExceptOf(
    mut v_00_u03b5_8905_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8906_: *mut LeanObject = core::ptr::null_mut();
    v___x_8906_ = l_Std_Async_EAsync_instMonadExceptOf___closed__0;
    return v___x_8906_;
}
pub unsafe fn l_Std_Async_EAsync_instMonadFinally___lam__0(
    mut v_00_u03b1_8907_: *mut LeanObject,
    mut v_00_u03b2_8908_: *mut LeanObject,
    mut v_x_8909_: *mut LeanObject,
    mut v_f_8910_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8913_: u8 = 0;
    let mut v___x_8914_: *mut LeanObject = core::ptr::null_mut();
    v___x_8912_ = lean_unsigned_to_nat(0);
    v___x_8913_ = 0;
    v___x_8914_ =
        l_Std_Async_EAsync_tryFinally_x27___redArg(v_x_8909_, v_f_8910_, v___x_8912_, v___x_8913_);
    return v___x_8914_;
}
pub unsafe fn l_Std_Async_EAsync_instMonadFinally___lam__0___boxed(
    mut v_00_u03b1_8915_: *mut LeanObject,
    mut v_00_u03b2_8916_: *mut LeanObject,
    mut v_x_8917_: *mut LeanObject,
    mut v_f_8918_: *mut LeanObject,
    mut v___y_8919_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8920_: *mut LeanObject = core::ptr::null_mut();
    v_res_8920_ = l_Std_Async_EAsync_instMonadFinally___lam__0(
        v_00_u03b1_8915_,
        v_00_u03b2_8916_,
        v_x_8917_,
        v_f_8918_,
    );
    return v_res_8920_;
}
pub unsafe fn l_Std_Async_EAsync_instMonadFinally(
    mut v_00_u03b5_8922_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_8923_: *mut LeanObject = core::ptr::null_mut();
    v___f_8923_ = l_Std_Async_EAsync_instMonadFinally___closed__0;
    return v___f_8923_;
}
pub unsafe fn _init_l_Std_Async_EAsync_instOrElse___closed__0() -> *mut LeanObject {
    let mut v___x_8924_: *mut LeanObject = core::ptr::null_mut();
    v___x_8924_ = l_Std_Async_EAsync_instMonadExcept(lean_box(0));
    return v___x_8924_;
}
pub unsafe fn _init_l_Std_Async_EAsync_instOrElse___closed__1() -> *mut LeanObject {
    let mut v___x_8925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8926_: *mut LeanObject = core::ptr::null_mut();
    v___x_8925_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_EAsync_instOrElse___closed__0),
        core::ptr::addr_of_mut!(l_Std_Async_EAsync_instOrElse___closed__0_once),
        _init_l_Std_Async_EAsync_instOrElse___closed__0,
    );
    v___x_8926_ = lean_alloc_closure(l_MonadExcept_orElse as *mut core::ffi::c_void, 6, 4);
    lean_closure_set(v___x_8926_, 0, lean_box(0));
    lean_closure_set(v___x_8926_, 1, lean_box(0));
    lean_closure_set(v___x_8926_, 2, v___x_8925_);
    lean_closure_set(v___x_8926_, 3, lean_box(0));
    return v___x_8926_;
}
pub unsafe fn l_Std_Async_EAsync_instOrElse(
    mut v_00_u03b5_8927_: *mut LeanObject,
    mut v_00_u03b1_8928_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8929_: *mut LeanObject = core::ptr::null_mut();
    v___x_8929_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_EAsync_instOrElse___closed__1),
        core::ptr::addr_of_mut!(l_Std_Async_EAsync_instOrElse___closed__1_once),
        _init_l_Std_Async_EAsync_instOrElse___closed__1,
    );
    return v___x_8929_;
}
pub unsafe fn l_Std_Async_EAsync_instInhabited___redArg(
    mut v_inst_8930_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8933_: *mut LeanObject = core::ptr::null_mut();
    v___x_8931_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_8931_, 0, v_inst_8930_);
    v___x_8932_ = lean_alloc_closure(
        l_Std_Async_BaseAsync_pure___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___x_8932_, 0, lean_box(0));
    lean_closure_set(v___x_8932_, 1, v___x_8931_);
    v___x_8933_ = lean_alloc_closure(
        l_Std_Async_BaseAsync_mk___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___x_8933_, 0, lean_box(0));
    lean_closure_set(v___x_8933_, 1, v___x_8932_);
    return v___x_8933_;
}
pub unsafe fn l_Std_Async_EAsync_instInhabited(
    mut v_00_u03b5_8934_: *mut LeanObject,
    mut v_00_u03b1_8935_: *mut LeanObject,
    mut v_inst_8936_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8937_: *mut LeanObject = core::ptr::null_mut();
    v___x_8937_ = l_Std_Async_EAsync_instInhabited___redArg(v_inst_8936_);
    return v___x_8937_;
}
pub unsafe fn l_Std_Async_EAsync_instMonadAwaitETask___lam__0(
    mut v_00_u03b1_8938_: *mut LeanObject,
    mut v_t_8939_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8941_: *mut LeanObject = core::ptr::null_mut();
    v___x_8941_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_8941_, 0, v_t_8939_);
    return v___x_8941_;
}
pub unsafe fn l_Std_Async_EAsync_instMonadAwaitETask___lam__0___boxed(
    mut v_00_u03b1_8942_: *mut LeanObject,
    mut v_t_8943_: *mut LeanObject,
    mut v___y_8944_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8945_: *mut LeanObject = core::ptr::null_mut();
    v_res_8945_ = l_Std_Async_EAsync_instMonadAwaitETask___lam__0(v_00_u03b1_8942_, v_t_8943_);
    return v_res_8945_;
}
pub unsafe fn l_Std_Async_EAsync_instMonadAwaitETask(
    mut v_00_u03b5_8947_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_8948_: *mut LeanObject = core::ptr::null_mut();
    v___f_8948_ = l_Std_Async_EAsync_instMonadAwaitETask___closed__0;
    return v___f_8948_;
}
pub unsafe fn l_Std_Async_EAsync_instMonadAwaitTask___lam__1(
    mut v___f_8949_: *mut LeanObject,
    mut v_00_u03b1_8950_: *mut LeanObject,
    mut v_t_8951_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8954_: u8 = 0;
    let mut v___x_8955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8956_: *mut LeanObject = core::ptr::null_mut();
    v___x_8953_ = lean_unsigned_to_nat(0);
    v___x_8954_ = 0;
    v___x_8955_ = lean_task_map(v___f_8949_, v_t_8951_, v___x_8953_, v___x_8954_);
    v___x_8956_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_8956_, 0, v___x_8955_);
    return v___x_8956_;
}
pub unsafe fn l_Std_Async_EAsync_instMonadAwaitTask___lam__1___boxed(
    mut v___f_8957_: *mut LeanObject,
    mut v_00_u03b1_8958_: *mut LeanObject,
    mut v_t_8959_: *mut LeanObject,
    mut v___y_8960_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8961_: *mut LeanObject = core::ptr::null_mut();
    v_res_8961_ =
        l_Std_Async_EAsync_instMonadAwaitTask___lam__1(v___f_8957_, v_00_u03b1_8958_, v_t_8959_);
    return v_res_8961_;
}
pub unsafe fn l_Std_Async_EAsync_instMonadAwaitTask(
    mut v_00_u03b5_8964_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_8965_: *mut LeanObject = core::ptr::null_mut();
    v___f_8965_ = l_Std_Async_EAsync_instMonadAwaitTask___closed__0;
    return v___f_8965_;
}
pub unsafe fn l_Std_Async_EAsync_instMonadAwaitAsyncTaskError___lam__0(
    mut v_00_u03b1_8966_: *mut LeanObject,
    mut v_t_8967_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8969_: *mut LeanObject = core::ptr::null_mut();
    v___x_8969_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_8969_, 0, v_t_8967_);
    return v___x_8969_;
}
pub unsafe fn l_Std_Async_EAsync_instMonadAwaitAsyncTaskError___lam__0___boxed(
    mut v_00_u03b1_8970_: *mut LeanObject,
    mut v_t_8971_: *mut LeanObject,
    mut v___y_8972_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8973_: *mut LeanObject = core::ptr::null_mut();
    v_res_8973_ =
        l_Std_Async_EAsync_instMonadAwaitAsyncTaskError___lam__0(v_00_u03b1_8970_, v_t_8971_);
    return v_res_8973_;
}
pub unsafe fn l_Std_Async_EAsync_instMonadAwaitPromise___lam__1(
    mut v___f_8976_: *mut LeanObject,
    mut v_00_u03b1_8977_: *mut LeanObject,
    mut v_t_8978_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8982_: u8 = 0;
    let mut v___x_8983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8984_: *mut LeanObject = core::ptr::null_mut();
    v___x_8980_ = l_IO_Promise_result_x21___redArg(v_t_8978_);
    v___x_8981_ = lean_unsigned_to_nat(0);
    v___x_8982_ = 0;
    v___x_8983_ = lean_task_map(v___f_8976_, v___x_8980_, v___x_8981_, v___x_8982_);
    v___x_8984_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_8984_, 0, v___x_8983_);
    return v___x_8984_;
}
pub unsafe fn l_Std_Async_EAsync_instMonadAwaitPromise___lam__1___boxed(
    mut v___f_8985_: *mut LeanObject,
    mut v_00_u03b1_8986_: *mut LeanObject,
    mut v_t_8987_: *mut LeanObject,
    mut v___y_8988_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8989_: *mut LeanObject = core::ptr::null_mut();
    v_res_8989_ =
        l_Std_Async_EAsync_instMonadAwaitPromise___lam__1(v___f_8985_, v_00_u03b1_8986_, v_t_8987_);
    lean_dec(v_t_8987_);
    return v_res_8989_;
}
pub unsafe fn l_Std_Async_EAsync_instMonadAwaitPromise(
    mut v_00_u03b5_8992_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_8993_: *mut LeanObject = core::ptr::null_mut();
    v___f_8993_ = l_Std_Async_EAsync_instMonadAwaitPromise___closed__0;
    return v___f_8993_;
}
pub unsafe fn l_Std_Async_EAsync_instMonadAsyncETask___lam__1(
    mut v___f_8994_: *mut LeanObject,
    mut v_00_u03b1_8995_: *mut LeanObject,
    mut v_t_8996_: *mut LeanObject,
    mut v_prio_8997_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9002_: u8 = 0;
    let mut v___x_9003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9005_: *mut LeanObject = core::ptr::null_mut();
    v___x_8999_ = lean_alloc_closure(
        l_Std_Async_BaseAsync_toRawBaseIO___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___x_8999_, 0, lean_box(0));
    lean_closure_set(v___x_8999_, 1, v_t_8996_);
    v___x_9000_ = lean_io_as_task(v___x_8999_, v_prio_8997_);
    v___x_9001_ = lean_unsigned_to_nat(0);
    v___x_9002_ = 1;
    v___x_9003_ = lean_task_bind(v___x_9000_, v___f_8994_, v___x_9001_, v___x_9002_);
    v___x_9004_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_9004_, 0, v___x_9003_);
    v___x_9005_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_9005_, 0, v___x_9004_);
    return v___x_9005_;
}
pub unsafe fn l_Std_Async_EAsync_instMonadAsyncETask___lam__1___boxed(
    mut v___f_9006_: *mut LeanObject,
    mut v_00_u03b1_9007_: *mut LeanObject,
    mut v_t_9008_: *mut LeanObject,
    mut v_prio_9009_: *mut LeanObject,
    mut v___y_9010_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9011_: *mut LeanObject = core::ptr::null_mut();
    v_res_9011_ = l_Std_Async_EAsync_instMonadAsyncETask___lam__1(
        v___f_9006_,
        v_00_u03b1_9007_,
        v_t_9008_,
        v_prio_9009_,
    );
    return v_res_9011_;
}
pub unsafe fn l_Std_Async_EAsync_instMonadAsyncETask(
    mut v_00_u03b5_9014_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_9015_: *mut LeanObject = core::ptr::null_mut();
    v___f_9015_ = l_Std_Async_EAsync_instMonadAsyncETask___closed__0;
    return v___f_9015_;
}
pub unsafe fn l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___lam__0(
    mut v_x_9016_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_9016_) == 0 {
        let mut v_a_9017_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_9018_: *mut LeanObject = core::ptr::null_mut();
        v_a_9017_ = lean_ctor_get(v_x_9016_, 0);
        lean_inc(v_a_9017_);
        lean_dec_ref_known(v_x_9016_, 1);
        v___x_9018_ = lean_task_pure(v_a_9017_);
        return v___x_9018_;
    } else {
        let mut v_a_9019_: *mut LeanObject = core::ptr::null_mut();
        v_a_9019_ = lean_ctor_get(v_x_9016_, 0);
        lean_inc_ref(v_a_9019_);
        lean_dec_ref_known(v_x_9016_, 1);
        return v_a_9019_;
    }
}
pub unsafe fn l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___lam__1(
    mut v___f_9020_: *mut LeanObject,
    mut v_00_u03b1_9021_: *mut LeanObject,
    mut v_t_9022_: *mut LeanObject,
    mut v_prio_9023_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9028_: u8 = 0;
    let mut v___x_9029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9031_: *mut LeanObject = core::ptr::null_mut();
    v___x_9025_ = lean_alloc_closure(
        l_Std_Async_BaseAsync_toRawBaseIO___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___x_9025_, 0, lean_box(0));
    lean_closure_set(v___x_9025_, 1, v_t_9022_);
    v___x_9026_ = lean_io_as_task(v___x_9025_, v_prio_9023_);
    v___x_9027_ = lean_unsigned_to_nat(0);
    v___x_9028_ = 1;
    v___x_9029_ = lean_task_bind(v___x_9026_, v___f_9020_, v___x_9027_, v___x_9028_);
    v___x_9030_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_9030_, 0, v___x_9029_);
    v___x_9031_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_9031_, 0, v___x_9030_);
    return v___x_9031_;
}
pub unsafe fn l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___lam__1___boxed(
    mut v___f_9032_: *mut LeanObject,
    mut v_00_u03b1_9033_: *mut LeanObject,
    mut v_t_9034_: *mut LeanObject,
    mut v_prio_9035_: *mut LeanObject,
    mut v___y_9036_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9037_: *mut LeanObject = core::ptr::null_mut();
    v_res_9037_ = l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___lam__1(
        v___f_9032_,
        v_00_u03b1_9033_,
        v_t_9034_,
        v_prio_9035_,
    );
    return v_res_9037_;
}
pub unsafe fn l_Std_Async_EAsync_instMonadLiftBaseIO___lam__0(
    mut v_00_u03b1_9042_: *mut LeanObject,
    mut v_x_9043_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9047_: *mut LeanObject = core::ptr::null_mut();
    v___x_9045_ = lean_apply_1(v_x_9043_, lean_box(0));
    v___x_9046_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_9046_, 0, v___x_9045_);
    v___x_9047_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_9047_, 0, v___x_9046_);
    return v___x_9047_;
}
pub unsafe fn l_Std_Async_EAsync_instMonadLiftBaseIO___lam__0___boxed(
    mut v_00_u03b1_9048_: *mut LeanObject,
    mut v_x_9049_: *mut LeanObject,
    mut v___y_9050_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9051_: *mut LeanObject = core::ptr::null_mut();
    v_res_9051_ = l_Std_Async_EAsync_instMonadLiftBaseIO___lam__0(v_00_u03b1_9048_, v_x_9049_);
    return v_res_9051_;
}
pub unsafe fn l_Std_Async_EAsync_instMonadLiftBaseIO(
    mut v_00_u03b5_9053_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_9054_: *mut LeanObject = core::ptr::null_mut();
    v___f_9054_ = l_Std_Async_EAsync_instMonadLiftBaseIO___closed__0;
    return v___f_9054_;
}
pub unsafe fn l_Std_Async_EAsync_instMonadLiftEIO__1___lam__0(
    mut v_00_u03b1_9055_: *mut LeanObject,
    mut v_x_9056_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_val_9059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9065_: u8 = 0;
    let mut v___x_9067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9069_: u8 = 0;
    let mut v_a_9070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9073_: u8 = 0;
    let mut v___x_9075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9077_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_9061_ = lean_apply_1(v_x_9056_, lean_box(0));
                if lean_obj_tag(v___x_9061_) == 0 {
                    v_a_9062_ = lean_ctor_get(v___x_9061_, 0);
                    v_isSharedCheck_9069_ = (!lean_is_exclusive(v___x_9061_)) as u8;
                    if v_isSharedCheck_9069_ == 0 {
                        v___x_9064_ = v___x_9061_;
                        v_isShared_9065_ = v_isSharedCheck_9069_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_9062_);
                        lean_dec(v___x_9061_);
                        v___x_9064_ = lean_box(0);
                        v_isShared_9065_ = v_isSharedCheck_9069_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_9070_ = lean_ctor_get(v___x_9061_, 0);
                    v_isSharedCheck_9077_ = (!lean_is_exclusive(v___x_9061_)) as u8;
                    if v_isSharedCheck_9077_ == 0 {
                        v___x_9072_ = v___x_9061_;
                        v_isShared_9073_ = v_isSharedCheck_9077_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_9070_);
                        lean_dec(v___x_9061_);
                        v___x_9072_ = lean_box(0);
                        v_isShared_9073_ = v_isSharedCheck_9077_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_9060_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_9060_, 0, v_val_9059_);
                return v___x_9060_;
            }
            2 => {
                if v_isShared_9065_ == 0 {
                    lean_ctor_set_tag(v___x_9064_, 1);
                    v___x_9067_ = v___x_9064_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_9068_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9068_, 0, v_a_9062_);
                    v___x_9067_ = v_reuseFailAlloc_9068_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_val_9059_ = v___x_9067_;
                state = 1;
                continue;
            }
            4 => {
                if v_isShared_9073_ == 0 {
                    lean_ctor_set_tag(v___x_9072_, 0);
                    v___x_9075_ = v___x_9072_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_9076_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9076_, 0, v_a_9070_);
                    v___x_9075_ = v_reuseFailAlloc_9076_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_val_9059_ = v___x_9075_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_EAsync_instMonadLiftEIO__1___lam__0___boxed(
    mut v_00_u03b1_9078_: *mut LeanObject,
    mut v_x_9079_: *mut LeanObject,
    mut v___y_9080_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9081_: *mut LeanObject = core::ptr::null_mut();
    v_res_9081_ = l_Std_Async_EAsync_instMonadLiftEIO__1___lam__0(v_00_u03b1_9078_, v_x_9079_);
    return v_res_9081_;
}
pub unsafe fn l_Std_Async_EAsync_instMonadLiftEIO__1(
    mut v_00_u03b5_9083_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_9084_: *mut LeanObject = core::ptr::null_mut();
    v___f_9084_ = l_Std_Async_EAsync_instMonadLiftEIO__1___closed__0;
    return v___f_9084_;
}
pub unsafe fn l_Std_Async_EAsync_instMonadLiftBaseAsync___lam__1(
    mut v___f_9085_: *mut LeanObject,
    mut v_00_u03b1_9086_: *mut LeanObject,
    mut v_x_9087_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9093_: u8 = 0;
    let mut v___x_9094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9098_: u8 = 0;
    let mut v_a_9099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9102_: u8 = 0;
    let mut v___x_9103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9104_: u8 = 0;
    let mut v___x_9105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9109_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_9089_ = lean_apply_1(v_x_9087_, lean_box(0));
                if lean_obj_tag(v___x_9089_) == 0 {
                    lean_dec_ref(v___f_9085_);
                    v_a_9090_ = lean_ctor_get(v___x_9089_, 0);
                    v_isSharedCheck_9098_ = (!lean_is_exclusive(v___x_9089_)) as u8;
                    if v_isSharedCheck_9098_ == 0 {
                        v___x_9092_ = v___x_9089_;
                        v_isShared_9093_ = v_isSharedCheck_9098_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_9090_);
                        lean_dec(v___x_9089_);
                        v___x_9092_ = lean_box(0);
                        v_isShared_9093_ = v_isSharedCheck_9098_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_9099_ = lean_ctor_get(v___x_9089_, 0);
                    v_isSharedCheck_9109_ = (!lean_is_exclusive(v___x_9089_)) as u8;
                    if v_isSharedCheck_9109_ == 0 {
                        v___x_9101_ = v___x_9089_;
                        v_isShared_9102_ = v_isSharedCheck_9109_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_9099_);
                        lean_dec(v___x_9089_);
                        v___x_9101_ = lean_box(0);
                        v_isShared_9102_ = v_isSharedCheck_9109_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_9094_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_9094_, 0, v_a_9090_);
                if v_isShared_9093_ == 0 {
                    lean_ctor_set(v___x_9092_, 0, v___x_9094_);
                    v___x_9096_ = v___x_9092_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_9097_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9097_, 0, v___x_9094_);
                    v___x_9096_ = v_reuseFailAlloc_9097_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_9096_;
            }
            3 => {
                v___x_9103_ = lean_unsigned_to_nat(0);
                v___x_9104_ = 0;
                v___x_9105_ = lean_task_map(v___f_9085_, v_a_9099_, v___x_9103_, v___x_9104_);
                if v_isShared_9102_ == 0 {
                    lean_ctor_set(v___x_9101_, 0, v___x_9105_);
                    v___x_9107_ = v___x_9101_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_9108_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9108_, 0, v___x_9105_);
                    v___x_9107_ = v_reuseFailAlloc_9108_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_9107_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_EAsync_instMonadLiftBaseAsync___lam__1___boxed(
    mut v___f_9110_: *mut LeanObject,
    mut v_00_u03b1_9111_: *mut LeanObject,
    mut v_x_9112_: *mut LeanObject,
    mut v___y_9113_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9114_: *mut LeanObject = core::ptr::null_mut();
    v_res_9114_ = l_Std_Async_EAsync_instMonadLiftBaseAsync___lam__1(
        v___f_9110_,
        v_00_u03b1_9111_,
        v_x_9112_,
    );
    return v_res_9114_;
}
pub unsafe fn l_Std_Async_EAsync_instMonadLiftBaseAsync(
    mut v_00_u03b5_9117_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_9118_: *mut LeanObject = core::ptr::null_mut();
    v___f_9118_ = l_Std_Async_EAsync_instMonadLiftBaseAsync___closed__0;
    return v___f_9118_;
}
pub unsafe fn l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___redArg___lam__0___boxed(
    mut v_promise_9119_: *mut LeanObject,
    mut v_f_9120_: *mut LeanObject,
    mut v_prio_9121_: *mut LeanObject,
    mut v_x_9122_: *mut LeanObject,
    mut v___y_9123_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9124_: *mut LeanObject = core::ptr::null_mut();
    v_res_9124_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___redArg___lam__0(
        v_promise_9119_,
        v_f_9120_,
        v_prio_9121_,
        v_x_9122_,
    );
    return v_res_9124_;
}
pub unsafe fn l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___redArg(
    mut v_f_9125_: *mut LeanObject,
    mut v_prio_9126_: *mut LeanObject,
    mut v_promise_9127_: *mut LeanObject,
    mut v_b_9128_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9136_: u8 = 0;
    let mut v___x_9138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9141_: u8 = 0;
    let mut v_a_9142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9145_: u8 = 0;
    let mut v_a_9146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9153_: u8 = 0;
    let mut v_a_9154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9156_: u8 = 0;
    let mut v___x_9157_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_9130_ = lean_box(0);
                lean_inc_ref(v_f_9125_);
                v___x_9131_ = lean_apply_3(v_f_9125_, v___x_9130_, v_b_9128_, lean_box(0));
                if lean_obj_tag(v___x_9131_) == 0 {
                    v_a_9132_ = lean_ctor_get(v___x_9131_, 0);
                    lean_inc(v_a_9132_);
                    lean_dec_ref_known(v___x_9131_, 1);
                    if lean_obj_tag(v_a_9132_) == 0 {
                        lean_dec(v_prio_9126_);
                        lean_dec_ref(v_f_9125_);
                        v_a_9133_ = lean_ctor_get(v_a_9132_, 0);
                        v_isSharedCheck_9141_ = (!lean_is_exclusive(v_a_9132_)) as u8;
                        if v_isSharedCheck_9141_ == 0 {
                            v___x_9135_ = v_a_9132_;
                            v_isShared_9136_ = v_isSharedCheck_9141_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_9133_);
                            lean_dec(v_a_9132_);
                            v___x_9135_ = lean_box(0);
                            v_isShared_9136_ = v_isSharedCheck_9141_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_9142_ = lean_ctor_get(v_a_9132_, 0);
                        v_isSharedCheck_9153_ = (!lean_is_exclusive(v_a_9132_)) as u8;
                        if v_isSharedCheck_9153_ == 0 {
                            v___x_9144_ = v_a_9132_;
                            v_isShared_9145_ = v_isSharedCheck_9153_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_9142_);
                            lean_dec(v_a_9132_);
                            v___x_9144_ = lean_box(0);
                            v_isShared_9145_ = v_isSharedCheck_9153_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_9154_ = lean_ctor_get(v___x_9131_, 0);
                    lean_inc_ref(v_a_9154_);
                    lean_dec_ref_known(v___x_9131_, 1);
                    lean_inc(v_prio_9126_);
                    v___f_9155_ = lean_alloc_closure(l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___redArg___lam__0___boxed as *mut core::ffi::c_void, 5, 3);
                    lean_closure_set(v___f_9155_, 0, v_promise_9127_);
                    lean_closure_set(v___f_9155_, 1, v_f_9125_);
                    lean_closure_set(v___f_9155_, 2, v_prio_9126_);
                    v___x_9156_ = 0;
                    v___x_9157_ = l_BaseIO_chainTask___redArg(
                        v_a_9154_,
                        v___f_9155_,
                        v_prio_9126_,
                        v___x_9156_,
                    );
                    return v___x_9157_;
                }
            }
            1 => {
                if v_isShared_9136_ == 0 {
                    v___x_9138_ = v___x_9135_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_9140_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9140_, 0, v_a_9133_);
                    v___x_9138_ = v_reuseFailAlloc_9140_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_9139_ = lean_io_promise_resolve(v___x_9138_, v_promise_9127_);
                lean_dec(v_promise_9127_);
                return v___x_9139_;
            }
            3 => {
                if lean_obj_tag(v_a_9142_) == 0 {
                    lean_dec(v_prio_9126_);
                    lean_dec_ref(v_f_9125_);
                    v_a_9146_ = lean_ctor_get(v_a_9142_, 0);
                    lean_inc(v_a_9146_);
                    lean_dec_ref_known(v_a_9142_, 1);
                    if v_isShared_9145_ == 0 {
                        lean_ctor_set(v___x_9144_, 0, v_a_9146_);
                        v___x_9148_ = v___x_9144_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_9150_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_9150_, 0, v_a_9146_);
                        v___x_9148_ = v_reuseFailAlloc_9150_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_9144_);
                    v_a_9151_ = lean_ctor_get(v_a_9142_, 0);
                    lean_inc(v_a_9151_);
                    lean_dec_ref_known(v_a_9142_, 1);
                    v_b_9128_ = v_a_9151_;
                    state = 0;
                    continue;
                }
            }
            4 => {
                v___x_9149_ = lean_io_promise_resolve(v___x_9148_, v_promise_9127_);
                lean_dec(v_promise_9127_);
                return v___x_9149_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___redArg___lam__0(
    mut v_promise_9158_: *mut LeanObject,
    mut v_f_9159_: *mut LeanObject,
    mut v_prio_9160_: *mut LeanObject,
    mut v_x_9161_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_9163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9166_: u8 = 0;
    let mut v___x_9168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9171_: u8 = 0;
    let mut v_a_9172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9175_: u8 = 0;
    let mut v_a_9176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9183_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_9161_) == 0 {
                    lean_dec(v_prio_9160_);
                    lean_dec_ref(v_f_9159_);
                    v_a_9163_ = lean_ctor_get(v_x_9161_, 0);
                    v_isSharedCheck_9171_ = (!lean_is_exclusive(v_x_9161_)) as u8;
                    if v_isSharedCheck_9171_ == 0 {
                        v___x_9165_ = v_x_9161_;
                        v_isShared_9166_ = v_isSharedCheck_9171_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_9163_);
                        lean_dec(v_x_9161_);
                        v___x_9165_ = lean_box(0);
                        v_isShared_9166_ = v_isSharedCheck_9171_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_9172_ = lean_ctor_get(v_x_9161_, 0);
                    v_isSharedCheck_9183_ = (!lean_is_exclusive(v_x_9161_)) as u8;
                    if v_isSharedCheck_9183_ == 0 {
                        v___x_9174_ = v_x_9161_;
                        v_isShared_9175_ = v_isSharedCheck_9183_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_9172_);
                        lean_dec(v_x_9161_);
                        v___x_9174_ = lean_box(0);
                        v_isShared_9175_ = v_isSharedCheck_9183_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_9166_ == 0 {
                    v___x_9168_ = v___x_9165_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_9170_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9170_, 0, v_a_9163_);
                    v___x_9168_ = v_reuseFailAlloc_9170_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_9169_ = lean_io_promise_resolve(v___x_9168_, v_promise_9158_);
                lean_dec(v_promise_9158_);
                return v___x_9169_;
            }
            3 => {
                if lean_obj_tag(v_a_9172_) == 0 {
                    lean_dec(v_prio_9160_);
                    lean_dec_ref(v_f_9159_);
                    v_a_9176_ = lean_ctor_get(v_a_9172_, 0);
                    lean_inc(v_a_9176_);
                    lean_dec_ref_known(v_a_9172_, 1);
                    if v_isShared_9175_ == 0 {
                        lean_ctor_set(v___x_9174_, 0, v_a_9176_);
                        v___x_9178_ = v___x_9174_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_9180_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_9180_, 0, v_a_9176_);
                        v___x_9178_ = v_reuseFailAlloc_9180_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_9174_);
                    v_a_9181_ = lean_ctor_get(v_a_9172_, 0);
                    lean_inc(v_a_9181_);
                    lean_dec_ref_known(v_a_9172_, 1);
                    v___x_9182_ =
                        l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___redArg(
                            v_f_9159_,
                            v_prio_9160_,
                            v_promise_9158_,
                            v_a_9181_,
                        );
                    return v___x_9182_;
                }
            }
            4 => {
                v___x_9179_ = lean_io_promise_resolve(v___x_9178_, v_promise_9158_);
                lean_dec(v_promise_9158_);
                return v___x_9179_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___redArg___boxed(
    mut v_f_9184_: *mut LeanObject,
    mut v_prio_9185_: *mut LeanObject,
    mut v_promise_9186_: *mut LeanObject,
    mut v_b_9187_: *mut LeanObject,
    mut v_a_9188_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9189_: *mut LeanObject = core::ptr::null_mut();
    v_res_9189_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___redArg(
        v_f_9184_,
        v_prio_9185_,
        v_promise_9186_,
        v_b_9187_,
    );
    return v_res_9189_;
}
pub unsafe fn l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop(
    mut v_00_u03b5_9190_: *mut LeanObject,
    mut v_00_u03b2_9191_: *mut LeanObject,
    mut v_f_9192_: *mut LeanObject,
    mut v_prio_9193_: *mut LeanObject,
    mut v_promise_9194_: *mut LeanObject,
    mut v_b_9195_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9197_: *mut LeanObject = core::ptr::null_mut();
    v___x_9197_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___redArg(
        v_f_9192_,
        v_prio_9193_,
        v_promise_9194_,
        v_b_9195_,
    );
    return v___x_9197_;
}
pub unsafe fn l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___boxed(
    mut v_00_u03b5_9198_: *mut LeanObject,
    mut v_00_u03b2_9199_: *mut LeanObject,
    mut v_f_9200_: *mut LeanObject,
    mut v_prio_9201_: *mut LeanObject,
    mut v_promise_9202_: *mut LeanObject,
    mut v_b_9203_: *mut LeanObject,
    mut v_a_9204_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9205_: *mut LeanObject = core::ptr::null_mut();
    v_res_9205_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop(
        v_00_u03b5_9198_,
        v_00_u03b2_9199_,
        v_f_9200_,
        v_prio_9201_,
        v_promise_9202_,
        v_b_9203_,
    );
    return v_res_9205_;
}
pub unsafe fn l_Std_Async_EAsync_forIn___redArg___lam__0(
    mut v_a_9206_: *mut LeanObject,
    mut v_x_9207_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_9209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9212_: u8 = 0;
    let mut v___x_9214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9217_: u8 = 0;
    let mut v___x_9218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9219_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_9207_) == 0 {
                    v_a_9209_ = lean_ctor_get(v_x_9207_, 0);
                    v_isSharedCheck_9217_ = (!lean_is_exclusive(v_x_9207_)) as u8;
                    if v_isSharedCheck_9217_ == 0 {
                        v___x_9211_ = v_x_9207_;
                        v_isShared_9212_ = v_isSharedCheck_9217_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_9209_);
                        lean_dec(v_x_9207_);
                        v___x_9211_ = lean_box(0);
                        v_isShared_9212_ = v_isSharedCheck_9217_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v_x_9207_, 1);
                    v___x_9218_ = l_IO_Promise_result_x21___redArg(v_a_9206_);
                    v___x_9219_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_9219_, 0, v___x_9218_);
                    return v___x_9219_;
                }
            }
            1 => {
                if v_isShared_9212_ == 0 {
                    v___x_9214_ = v___x_9211_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_9216_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9216_, 0, v_a_9209_);
                    v___x_9214_ = v_reuseFailAlloc_9216_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_9215_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_9215_, 0, v___x_9214_);
                return v___x_9215_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_EAsync_forIn___redArg___lam__0___boxed(
    mut v_a_9220_: *mut LeanObject,
    mut v_x_9221_: *mut LeanObject,
    mut v___y_9222_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9223_: *mut LeanObject = core::ptr::null_mut();
    v_res_9223_ = l_Std_Async_EAsync_forIn___redArg___lam__0(v_a_9220_, v_x_9221_);
    lean_dec(v_a_9220_);
    return v_res_9223_;
}
pub unsafe fn l_Std_Async_EAsync_forIn___redArg___lam__1(
    mut v_f_9224_: *mut LeanObject,
    mut v_prio_9225_: *mut LeanObject,
    mut v_init_9226_: *mut LeanObject,
    mut v_x_9227_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_9229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9232_: u8 = 0;
    let mut v___x_9234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9237_: u8 = 0;
    let mut v_a_9238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9241_: u8 = 0;
    let mut v___x_9242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9248_: u8 = 0;
    let mut v___x_9249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9251_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_9227_) == 0 {
                    lean_dec(v_init_9226_);
                    lean_dec(v_prio_9225_);
                    lean_dec_ref(v_f_9224_);
                    v_a_9229_ = lean_ctor_get(v_x_9227_, 0);
                    v_isSharedCheck_9237_ = (!lean_is_exclusive(v_x_9227_)) as u8;
                    if v_isSharedCheck_9237_ == 0 {
                        v___x_9231_ = v_x_9227_;
                        v_isShared_9232_ = v_isSharedCheck_9237_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_9229_);
                        lean_dec(v_x_9227_);
                        v___x_9231_ = lean_box(0);
                        v_isShared_9232_ = v_isSharedCheck_9237_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_9238_ = lean_ctor_get(v_x_9227_, 0);
                    v_isSharedCheck_9251_ = (!lean_is_exclusive(v_x_9227_)) as u8;
                    if v_isSharedCheck_9251_ == 0 {
                        v___x_9240_ = v_x_9227_;
                        v_isShared_9241_ = v_isSharedCheck_9251_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_9238_);
                        lean_dec(v_x_9227_);
                        v___x_9240_ = lean_box(0);
                        v_isShared_9241_ = v_isSharedCheck_9251_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_9232_ == 0 {
                    v___x_9234_ = v___x_9231_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_9236_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9236_, 0, v_a_9229_);
                    v___x_9234_ = v_reuseFailAlloc_9236_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_9235_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_9235_, 0, v___x_9234_);
                return v___x_9235_;
            }
            3 => {
                lean_inc(v_a_9238_);
                v___x_9242_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___redArg(
                    v_f_9224_,
                    v_prio_9225_,
                    v_a_9238_,
                    v_init_9226_,
                );
                v___f_9243_ = lean_alloc_closure(
                    l_Std_Async_EAsync_forIn___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    3,
                    1,
                );
                lean_closure_set(v___f_9243_, 0, v_a_9238_);
                if v_isShared_9241_ == 0 {
                    lean_ctor_set(v___x_9240_, 0, v___x_9242_);
                    v___x_9245_ = v___x_9240_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_9250_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9250_, 0, v___x_9242_);
                    v___x_9245_ = v_reuseFailAlloc_9250_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_9246_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_9246_, 0, v___x_9245_);
                v___x_9247_ = lean_unsigned_to_nat(0);
                v___x_9248_ = 0;
                v___x_9249_ =
                    l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(
                        v___x_9247_,
                        v___x_9248_,
                        v___x_9246_,
                        v___f_9243_,
                    );
                return v___x_9249_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_EAsync_forIn___redArg___lam__1___boxed(
    mut v_f_9252_: *mut LeanObject,
    mut v_prio_9253_: *mut LeanObject,
    mut v_init_9254_: *mut LeanObject,
    mut v_x_9255_: *mut LeanObject,
    mut v___y_9256_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9257_: *mut LeanObject = core::ptr::null_mut();
    v_res_9257_ = l_Std_Async_EAsync_forIn___redArg___lam__1(
        v_f_9252_,
        v_prio_9253_,
        v_init_9254_,
        v_x_9255_,
    );
    return v_res_9257_;
}
pub unsafe fn l_Std_Async_EAsync_forIn___redArg(
    mut v_init_9258_: *mut LeanObject,
    mut v_f_9259_: *mut LeanObject,
    mut v_prio_9260_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9267_: u8 = 0;
    let mut v___x_9268_: *mut LeanObject = core::ptr::null_mut();
    v___x_9262_ = lean_io_promise_new();
    v___f_9263_ = lean_alloc_closure(
        l_Std_Async_EAsync_forIn___redArg___lam__1___boxed as *mut core::ffi::c_void,
        5,
        3,
    );
    lean_closure_set(v___f_9263_, 0, v_f_9259_);
    lean_closure_set(v___f_9263_, 1, v_prio_9260_);
    lean_closure_set(v___f_9263_, 2, v_init_9258_);
    v___x_9264_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_9264_, 0, v___x_9262_);
    v___x_9265_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_9265_, 0, v___x_9264_);
    v___x_9266_ = lean_unsigned_to_nat(0);
    v___x_9267_ = 0;
    v___x_9268_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(
        v___x_9266_,
        v___x_9267_,
        v___x_9265_,
        v___f_9263_,
    );
    return v___x_9268_;
}
pub unsafe fn l_Std_Async_EAsync_forIn___redArg___boxed(
    mut v_init_9269_: *mut LeanObject,
    mut v_f_9270_: *mut LeanObject,
    mut v_prio_9271_: *mut LeanObject,
    mut v_a_9272_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9273_: *mut LeanObject = core::ptr::null_mut();
    v_res_9273_ = l_Std_Async_EAsync_forIn___redArg(v_init_9269_, v_f_9270_, v_prio_9271_);
    return v_res_9273_;
}
pub unsafe fn l_Std_Async_EAsync_forIn(
    mut v_00_u03b5_9274_: *mut LeanObject,
    mut v_00_u03b2_9275_: *mut LeanObject,
    mut v_init_9276_: *mut LeanObject,
    mut v_f_9277_: *mut LeanObject,
    mut v_prio_9278_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9285_: u8 = 0;
    let mut v___x_9286_: *mut LeanObject = core::ptr::null_mut();
    v___x_9280_ = lean_io_promise_new();
    v___f_9281_ = lean_alloc_closure(
        l_Std_Async_EAsync_forIn___redArg___lam__1___boxed as *mut core::ffi::c_void,
        5,
        3,
    );
    lean_closure_set(v___f_9281_, 0, v_f_9277_);
    lean_closure_set(v___f_9281_, 1, v_prio_9278_);
    lean_closure_set(v___f_9281_, 2, v_init_9276_);
    v___x_9282_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_9282_, 0, v___x_9280_);
    v___x_9283_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_9283_, 0, v___x_9282_);
    v___x_9284_ = lean_unsigned_to_nat(0);
    v___x_9285_ = 0;
    v___x_9286_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(
        v___x_9284_,
        v___x_9285_,
        v___x_9283_,
        v___f_9281_,
    );
    return v___x_9286_;
}
pub unsafe fn l_Std_Async_EAsync_forIn___boxed(
    mut v_00_u03b5_9287_: *mut LeanObject,
    mut v_00_u03b2_9288_: *mut LeanObject,
    mut v_init_9289_: *mut LeanObject,
    mut v_f_9290_: *mut LeanObject,
    mut v_prio_9291_: *mut LeanObject,
    mut v_a_9292_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9293_: *mut LeanObject = core::ptr::null_mut();
    v_res_9293_ = l_Std_Async_EAsync_forIn(
        v_00_u03b5_9287_,
        v_00_u03b2_9288_,
        v_init_9289_,
        v_f_9290_,
        v_prio_9291_,
    );
    return v_res_9293_;
}
pub unsafe fn l_Std_Async_EAsync_instForInLoopUnit___lam__1(
    mut v_f_9294_: *mut LeanObject,
    mut v___x_9295_: *mut LeanObject,
    mut v_init_9296_: *mut LeanObject,
    mut v_x_9297_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_9299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9302_: u8 = 0;
    let mut v___x_9304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9307_: u8 = 0;
    let mut v_a_9308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9311_: u8 = 0;
    let mut v___x_9312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9317_: u8 = 0;
    let mut v___x_9318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9320_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_9297_) == 0 {
                    lean_dec(v_init_9296_);
                    lean_dec(v___x_9295_);
                    lean_dec_ref(v_f_9294_);
                    v_a_9299_ = lean_ctor_get(v_x_9297_, 0);
                    v_isSharedCheck_9307_ = (!lean_is_exclusive(v_x_9297_)) as u8;
                    if v_isSharedCheck_9307_ == 0 {
                        v___x_9301_ = v_x_9297_;
                        v_isShared_9302_ = v_isSharedCheck_9307_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_9299_);
                        lean_dec(v_x_9297_);
                        v___x_9301_ = lean_box(0);
                        v_isShared_9302_ = v_isSharedCheck_9307_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_9308_ = lean_ctor_get(v_x_9297_, 0);
                    v_isSharedCheck_9320_ = (!lean_is_exclusive(v_x_9297_)) as u8;
                    if v_isSharedCheck_9320_ == 0 {
                        v___x_9310_ = v_x_9297_;
                        v_isShared_9311_ = v_isSharedCheck_9320_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_9308_);
                        lean_dec(v_x_9297_);
                        v___x_9310_ = lean_box(0);
                        v_isShared_9311_ = v_isSharedCheck_9320_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_9302_ == 0 {
                    v___x_9304_ = v___x_9301_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_9306_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9306_, 0, v_a_9299_);
                    v___x_9304_ = v_reuseFailAlloc_9306_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_9305_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_9305_, 0, v___x_9304_);
                return v___x_9305_;
            }
            3 => {
                lean_inc(v_a_9308_);
                lean_inc(v___x_9295_);
                v___x_9312_ = l___private_Std_Async_Basic_0__Std_Async_EAsync_forIn_loop___redArg(
                    v_f_9294_,
                    v___x_9295_,
                    v_a_9308_,
                    v_init_9296_,
                );
                v___f_9313_ = lean_alloc_closure(
                    l_Std_Async_EAsync_forIn___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    3,
                    1,
                );
                lean_closure_set(v___f_9313_, 0, v_a_9308_);
                if v_isShared_9311_ == 0 {
                    lean_ctor_set(v___x_9310_, 0, v___x_9312_);
                    v___x_9315_ = v___x_9310_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_9319_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9319_, 0, v___x_9312_);
                    v___x_9315_ = v_reuseFailAlloc_9319_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_9316_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_9316_, 0, v___x_9315_);
                v___x_9317_ = 0;
                v___x_9318_ =
                    l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(
                        v___x_9295_,
                        v___x_9317_,
                        v___x_9316_,
                        v___f_9313_,
                    );
                return v___x_9318_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_EAsync_instForInLoopUnit___lam__1___boxed(
    mut v_f_9321_: *mut LeanObject,
    mut v___x_9322_: *mut LeanObject,
    mut v_init_9323_: *mut LeanObject,
    mut v_x_9324_: *mut LeanObject,
    mut v___y_9325_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9326_: *mut LeanObject = core::ptr::null_mut();
    v_res_9326_ = l_Std_Async_EAsync_instForInLoopUnit___lam__1(
        v_f_9321_,
        v___x_9322_,
        v_init_9323_,
        v_x_9324_,
    );
    return v_res_9326_;
}
pub unsafe fn l_Std_Async_EAsync_instForInLoopUnit___lam__0(
    mut v_00_u03b2_9327_: *mut LeanObject,
    mut v_x_9328_: *mut LeanObject,
    mut v_init_9329_: *mut LeanObject,
    mut v_f_9330_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9337_: u8 = 0;
    let mut v___x_9338_: *mut LeanObject = core::ptr::null_mut();
    v___x_9332_ = lean_io_promise_new();
    v___x_9333_ = lean_unsigned_to_nat(0);
    v___f_9334_ = lean_alloc_closure(
        l_Std_Async_EAsync_instForInLoopUnit___lam__1___boxed as *mut core::ffi::c_void,
        5,
        3,
    );
    lean_closure_set(v___f_9334_, 0, v_f_9330_);
    lean_closure_set(v___f_9334_, 1, v___x_9333_);
    lean_closure_set(v___f_9334_, 2, v_init_9329_);
    v___x_9335_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_9335_, 0, v___x_9332_);
    v___x_9336_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_9336_, 0, v___x_9335_);
    v___x_9337_ = 0;
    v___x_9338_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(
        v___x_9333_,
        v___x_9337_,
        v___x_9336_,
        v___f_9334_,
    );
    return v___x_9338_;
}
pub unsafe fn l_Std_Async_EAsync_instForInLoopUnit___lam__0___boxed(
    mut v_00_u03b2_9339_: *mut LeanObject,
    mut v_x_9340_: *mut LeanObject,
    mut v_init_9341_: *mut LeanObject,
    mut v_f_9342_: *mut LeanObject,
    mut v___y_9343_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9344_: *mut LeanObject = core::ptr::null_mut();
    v_res_9344_ = l_Std_Async_EAsync_instForInLoopUnit___lam__0(
        v_00_u03b2_9339_,
        v_x_9340_,
        v_init_9341_,
        v_f_9342_,
    );
    return v_res_9344_;
}
pub unsafe fn l_Std_Async_EAsync_instForInLoopUnit(
    mut v_00_u03b5_9346_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_9347_: *mut LeanObject = core::ptr::null_mut();
    v___f_9347_ = l_Std_Async_EAsync_instForInLoopUnit___closed__0;
    return v___f_9347_;
}
pub unsafe fn l_Std_Async_EAsync_ofExcept___redArg(
    mut v_except_9348_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9350_: *mut LeanObject = core::ptr::null_mut();
    v___x_9350_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_9350_, 0, v_except_9348_);
    return v___x_9350_;
}
pub unsafe fn l_Std_Async_EAsync_ofExcept___redArg___boxed(
    mut v_except_9351_: *mut LeanObject,
    mut v_a_9352_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9353_: *mut LeanObject = core::ptr::null_mut();
    v_res_9353_ = l_Std_Async_EAsync_ofExcept___redArg(v_except_9351_);
    return v_res_9353_;
}
pub unsafe fn l_Std_Async_EAsync_ofExcept(
    mut v_00_u03b5_9354_: *mut LeanObject,
    mut v_00_u03b1_9355_: *mut LeanObject,
    mut v_except_9356_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9358_: *mut LeanObject = core::ptr::null_mut();
    v___x_9358_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_9358_, 0, v_except_9356_);
    return v___x_9358_;
}
pub unsafe fn l_Std_Async_EAsync_ofExcept___boxed(
    mut v_00_u03b5_9359_: *mut LeanObject,
    mut v_00_u03b1_9360_: *mut LeanObject,
    mut v_except_9361_: *mut LeanObject,
    mut v_a_9362_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9363_: *mut LeanObject = core::ptr::null_mut();
    v_res_9363_ = l_Std_Async_EAsync_ofExcept(v_00_u03b5_9359_, v_00_u03b1_9360_, v_except_9361_);
    return v_res_9363_;
}
pub unsafe fn l_Std_Async_EAsync_concurrently___redArg___lam__1(
    mut v_a_9364_: *mut LeanObject,
    mut v_x_9365_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_9367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9370_: u8 = 0;
    let mut v___x_9372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9375_: u8 = 0;
    let mut v_a_9376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9379_: u8 = 0;
    let mut v___x_9380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9385_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_9365_) == 0 {
                    lean_dec(v_a_9364_);
                    v_a_9367_ = lean_ctor_get(v_x_9365_, 0);
                    v_isSharedCheck_9375_ = (!lean_is_exclusive(v_x_9365_)) as u8;
                    if v_isSharedCheck_9375_ == 0 {
                        v___x_9369_ = v_x_9365_;
                        v_isShared_9370_ = v_isSharedCheck_9375_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_9367_);
                        lean_dec(v_x_9365_);
                        v___x_9369_ = lean_box(0);
                        v_isShared_9370_ = v_isSharedCheck_9375_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_9376_ = lean_ctor_get(v_x_9365_, 0);
                    v_isSharedCheck_9385_ = (!lean_is_exclusive(v_x_9365_)) as u8;
                    if v_isSharedCheck_9385_ == 0 {
                        v___x_9378_ = v_x_9365_;
                        v_isShared_9379_ = v_isSharedCheck_9385_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_9376_);
                        lean_dec(v_x_9365_);
                        v___x_9378_ = lean_box(0);
                        v_isShared_9379_ = v_isSharedCheck_9385_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_9370_ == 0 {
                    v___x_9372_ = v___x_9369_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_9374_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9374_, 0, v_a_9367_);
                    v___x_9372_ = v_reuseFailAlloc_9374_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_9373_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_9373_, 0, v___x_9372_);
                return v___x_9373_;
            }
            3 => {
                v___x_9380_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_9380_, 0, v_a_9364_);
                lean_ctor_set(v___x_9380_, 1, v_a_9376_);
                if v_isShared_9379_ == 0 {
                    lean_ctor_set(v___x_9378_, 0, v___x_9380_);
                    v___x_9382_ = v___x_9378_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_9384_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9384_, 0, v___x_9380_);
                    v___x_9382_ = v_reuseFailAlloc_9384_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_9383_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_9383_, 0, v___x_9382_);
                return v___x_9383_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_EAsync_concurrently___redArg___lam__1___boxed(
    mut v_a_9386_: *mut LeanObject,
    mut v_x_9387_: *mut LeanObject,
    mut v___y_9388_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9389_: *mut LeanObject = core::ptr::null_mut();
    v_res_9389_ = l_Std_Async_EAsync_concurrently___redArg___lam__1(v_a_9386_, v_x_9387_);
    return v_res_9389_;
}
pub unsafe fn l_Std_Async_EAsync_concurrently___redArg___lam__0(
    mut v_a_9390_: *mut LeanObject,
    mut v_x_9391_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_9393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9396_: u8 = 0;
    let mut v___x_9398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9401_: u8 = 0;
    let mut v_a_9402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9406_: u8 = 0;
    let mut v___x_9407_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_9391_) == 0 {
                    lean_dec_ref(v_a_9390_);
                    v_a_9393_ = lean_ctor_get(v_x_9391_, 0);
                    v_isSharedCheck_9401_ = (!lean_is_exclusive(v_x_9391_)) as u8;
                    if v_isSharedCheck_9401_ == 0 {
                        v___x_9395_ = v_x_9391_;
                        v_isShared_9396_ = v_isSharedCheck_9401_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_9393_);
                        lean_dec(v_x_9391_);
                        v___x_9395_ = lean_box(0);
                        v_isShared_9396_ = v_isSharedCheck_9401_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_9402_ = lean_ctor_get(v_x_9391_, 0);
                    lean_inc(v_a_9402_);
                    lean_dec_ref_known(v_x_9391_, 1);
                    v___f_9403_ = lean_alloc_closure(
                        l_Std_Async_EAsync_concurrently___redArg___lam__1___boxed
                            as *mut core::ffi::c_void,
                        3,
                        1,
                    );
                    lean_closure_set(v___f_9403_, 0, v_a_9402_);
                    v___x_9404_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_9404_, 0, v_a_9390_);
                    v___x_9405_ = lean_unsigned_to_nat(0);
                    v___x_9406_ = 0;
                    v___x_9407_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_9405_, v___x_9406_, v___x_9404_, v___f_9403_);
                    return v___x_9407_;
                }
            }
            1 => {
                if v_isShared_9396_ == 0 {
                    v___x_9398_ = v___x_9395_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_9400_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9400_, 0, v_a_9393_);
                    v___x_9398_ = v_reuseFailAlloc_9400_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_9399_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_9399_, 0, v___x_9398_);
                return v___x_9399_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_EAsync_concurrently___redArg___lam__0___boxed(
    mut v_a_9408_: *mut LeanObject,
    mut v_x_9409_: *mut LeanObject,
    mut v___y_9410_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9411_: *mut LeanObject = core::ptr::null_mut();
    v_res_9411_ = l_Std_Async_EAsync_concurrently___redArg___lam__0(v_a_9408_, v_x_9409_);
    return v_res_9411_;
}
pub unsafe fn l_Std_Async_EAsync_concurrently___redArg___lam__2(
    mut v_a_9412_: *mut LeanObject,
    mut v_x_9413_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_9415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9418_: u8 = 0;
    let mut v___x_9420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9423_: u8 = 0;
    let mut v_a_9424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9428_: u8 = 0;
    let mut v___x_9429_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_9413_) == 0 {
                    lean_dec_ref(v_a_9412_);
                    v_a_9415_ = lean_ctor_get(v_x_9413_, 0);
                    v_isSharedCheck_9423_ = (!lean_is_exclusive(v_x_9413_)) as u8;
                    if v_isSharedCheck_9423_ == 0 {
                        v___x_9417_ = v_x_9413_;
                        v_isShared_9418_ = v_isSharedCheck_9423_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_9415_);
                        lean_dec(v_x_9413_);
                        v___x_9417_ = lean_box(0);
                        v_isShared_9418_ = v_isSharedCheck_9423_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_9424_ = lean_ctor_get(v_x_9413_, 0);
                    lean_inc(v_a_9424_);
                    lean_dec_ref_known(v_x_9413_, 1);
                    v___f_9425_ = lean_alloc_closure(
                        l_Std_Async_EAsync_concurrently___redArg___lam__0___boxed
                            as *mut core::ffi::c_void,
                        3,
                        1,
                    );
                    lean_closure_set(v___f_9425_, 0, v_a_9424_);
                    v___x_9426_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_9426_, 0, v_a_9412_);
                    v___x_9427_ = lean_unsigned_to_nat(0);
                    v___x_9428_ = 0;
                    v___x_9429_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_9427_, v___x_9428_, v___x_9426_, v___f_9425_);
                    return v___x_9429_;
                }
            }
            1 => {
                if v_isShared_9418_ == 0 {
                    v___x_9420_ = v___x_9417_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_9422_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9422_, 0, v_a_9415_);
                    v___x_9420_ = v_reuseFailAlloc_9422_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_9421_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_9421_, 0, v___x_9420_);
                return v___x_9421_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_EAsync_concurrently___redArg___lam__2___boxed(
    mut v_a_9430_: *mut LeanObject,
    mut v_x_9431_: *mut LeanObject,
    mut v___y_9432_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9433_: *mut LeanObject = core::ptr::null_mut();
    v_res_9433_ = l_Std_Async_EAsync_concurrently___redArg___lam__2(v_a_9430_, v_x_9431_);
    return v_res_9433_;
}
pub unsafe fn l_Std_Async_EAsync_concurrently___redArg___lam__3(
    mut v_y_9434_: *mut LeanObject,
    mut v_prio_9435_: *mut LeanObject,
    mut v___f_9436_: *mut LeanObject,
    mut v_x_9437_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_9439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9442_: u8 = 0;
    let mut v___x_9444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9447_: u8 = 0;
    let mut v_a_9448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9451_: u8 = 0;
    let mut v___x_9452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9456_: u8 = 0;
    let mut v___x_9457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9461_: u8 = 0;
    let mut v___x_9462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9464_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_9437_) == 0 {
                    lean_dec_ref(v___f_9436_);
                    lean_dec(v_prio_9435_);
                    lean_dec_ref(v_y_9434_);
                    v_a_9439_ = lean_ctor_get(v_x_9437_, 0);
                    v_isSharedCheck_9447_ = (!lean_is_exclusive(v_x_9437_)) as u8;
                    if v_isSharedCheck_9447_ == 0 {
                        v___x_9441_ = v_x_9437_;
                        v_isShared_9442_ = v_isSharedCheck_9447_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_9439_);
                        lean_dec(v_x_9437_);
                        v___x_9441_ = lean_box(0);
                        v_isShared_9442_ = v_isSharedCheck_9447_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_9448_ = lean_ctor_get(v_x_9437_, 0);
                    v_isSharedCheck_9464_ = (!lean_is_exclusive(v_x_9437_)) as u8;
                    if v_isSharedCheck_9464_ == 0 {
                        v___x_9450_ = v_x_9437_;
                        v_isShared_9451_ = v_isSharedCheck_9464_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_9448_);
                        lean_dec(v_x_9437_);
                        v___x_9450_ = lean_box(0);
                        v_isShared_9451_ = v_isSharedCheck_9464_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_9442_ == 0 {
                    v___x_9444_ = v___x_9441_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_9446_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9446_, 0, v_a_9439_);
                    v___x_9444_ = v_reuseFailAlloc_9446_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_9445_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_9445_, 0, v___x_9444_);
                return v___x_9445_;
            }
            3 => {
                v___x_9452_ = lean_alloc_closure(
                    l_Std_Async_BaseAsync_toRawBaseIO___boxed as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___x_9452_, 0, lean_box(0));
                lean_closure_set(v___x_9452_, 1, v_y_9434_);
                v___x_9453_ = lean_io_as_task(v___x_9452_, v_prio_9435_);
                v___f_9454_ = lean_alloc_closure(
                    l_Std_Async_EAsync_concurrently___redArg___lam__2___boxed
                        as *mut core::ffi::c_void,
                    3,
                    1,
                );
                lean_closure_set(v___f_9454_, 0, v_a_9448_);
                v___x_9455_ = lean_unsigned_to_nat(0);
                v___x_9456_ = 1;
                v___x_9457_ = lean_task_bind(v___x_9453_, v___f_9436_, v___x_9455_, v___x_9456_);
                if v_isShared_9451_ == 0 {
                    lean_ctor_set(v___x_9450_, 0, v___x_9457_);
                    v___x_9459_ = v___x_9450_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_9463_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9463_, 0, v___x_9457_);
                    v___x_9459_ = v_reuseFailAlloc_9463_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_9460_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_9460_, 0, v___x_9459_);
                v___x_9461_ = 0;
                v___x_9462_ =
                    l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(
                        v___x_9455_,
                        v___x_9461_,
                        v___x_9460_,
                        v___f_9454_,
                    );
                return v___x_9462_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_EAsync_concurrently___redArg___lam__3___boxed(
    mut v_y_9465_: *mut LeanObject,
    mut v_prio_9466_: *mut LeanObject,
    mut v___f_9467_: *mut LeanObject,
    mut v_x_9468_: *mut LeanObject,
    mut v___y_9469_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9470_: *mut LeanObject = core::ptr::null_mut();
    v_res_9470_ = l_Std_Async_EAsync_concurrently___redArg___lam__3(
        v_y_9465_,
        v_prio_9466_,
        v___f_9467_,
        v_x_9468_,
    );
    return v_res_9470_;
}
pub unsafe fn l_Std_Async_EAsync_concurrently___redArg(
    mut v_x_9471_: *mut LeanObject,
    mut v_y_9472_: *mut LeanObject,
    mut v_prio_9473_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9480_: u8 = 0;
    let mut v___x_9481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9484_: u8 = 0;
    let mut v___x_9485_: *mut LeanObject = core::ptr::null_mut();
    v___x_9475_ = lean_alloc_closure(
        l_Std_Async_BaseAsync_toRawBaseIO___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___x_9475_, 0, lean_box(0));
    lean_closure_set(v___x_9475_, 1, v_x_9471_);
    lean_inc(v_prio_9473_);
    v___x_9476_ = lean_io_as_task(v___x_9475_, v_prio_9473_);
    v___f_9477_ = l_Std_Async_EAsync_asTask___redArg___closed__0;
    v___f_9478_ = lean_alloc_closure(
        l_Std_Async_EAsync_concurrently___redArg___lam__3___boxed as *mut core::ffi::c_void,
        5,
        3,
    );
    lean_closure_set(v___f_9478_, 0, v_y_9472_);
    lean_closure_set(v___f_9478_, 1, v_prio_9473_);
    lean_closure_set(v___f_9478_, 2, v___f_9477_);
    v___x_9479_ = lean_unsigned_to_nat(0);
    v___x_9480_ = 1;
    v___x_9481_ = lean_task_bind(v___x_9476_, v___f_9477_, v___x_9479_, v___x_9480_);
    v___x_9482_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_9482_, 0, v___x_9481_);
    v___x_9483_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_9483_, 0, v___x_9482_);
    v___x_9484_ = 0;
    v___x_9485_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(
        v___x_9479_,
        v___x_9484_,
        v___x_9483_,
        v___f_9478_,
    );
    return v___x_9485_;
}
pub unsafe fn l_Std_Async_EAsync_concurrently___redArg___boxed(
    mut v_x_9486_: *mut LeanObject,
    mut v_y_9487_: *mut LeanObject,
    mut v_prio_9488_: *mut LeanObject,
    mut v_a_9489_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9490_: *mut LeanObject = core::ptr::null_mut();
    v_res_9490_ = l_Std_Async_EAsync_concurrently___redArg(v_x_9486_, v_y_9487_, v_prio_9488_);
    return v_res_9490_;
}
pub unsafe fn l_Std_Async_EAsync_concurrently(
    mut v_00_u03b5_9491_: *mut LeanObject,
    mut v_00_u03b1_9492_: *mut LeanObject,
    mut v_00_u03b2_9493_: *mut LeanObject,
    mut v_x_9494_: *mut LeanObject,
    mut v_y_9495_: *mut LeanObject,
    mut v_prio_9496_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9503_: u8 = 0;
    let mut v___x_9504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9507_: u8 = 0;
    let mut v___x_9508_: *mut LeanObject = core::ptr::null_mut();
    v___x_9498_ = lean_alloc_closure(
        l_Std_Async_BaseAsync_toRawBaseIO___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___x_9498_, 0, lean_box(0));
    lean_closure_set(v___x_9498_, 1, v_x_9494_);
    lean_inc(v_prio_9496_);
    v___x_9499_ = lean_io_as_task(v___x_9498_, v_prio_9496_);
    v___f_9500_ = l_Std_Async_EAsync_asTask___redArg___closed__0;
    v___f_9501_ = lean_alloc_closure(
        l_Std_Async_EAsync_concurrently___redArg___lam__3___boxed as *mut core::ffi::c_void,
        5,
        3,
    );
    lean_closure_set(v___f_9501_, 0, v_y_9495_);
    lean_closure_set(v___f_9501_, 1, v_prio_9496_);
    lean_closure_set(v___f_9501_, 2, v___f_9500_);
    v___x_9502_ = lean_unsigned_to_nat(0);
    v___x_9503_ = 1;
    v___x_9504_ = lean_task_bind(v___x_9499_, v___f_9500_, v___x_9502_, v___x_9503_);
    v___x_9505_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_9505_, 0, v___x_9504_);
    v___x_9506_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_9506_, 0, v___x_9505_);
    v___x_9507_ = 0;
    v___x_9508_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(
        v___x_9502_,
        v___x_9507_,
        v___x_9506_,
        v___f_9501_,
    );
    return v___x_9508_;
}
pub unsafe fn l_Std_Async_EAsync_concurrently___boxed(
    mut v_00_u03b5_9509_: *mut LeanObject,
    mut v_00_u03b1_9510_: *mut LeanObject,
    mut v_00_u03b2_9511_: *mut LeanObject,
    mut v_x_9512_: *mut LeanObject,
    mut v_y_9513_: *mut LeanObject,
    mut v_prio_9514_: *mut LeanObject,
    mut v_a_9515_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9516_: *mut LeanObject = core::ptr::null_mut();
    v_res_9516_ = l_Std_Async_EAsync_concurrently(
        v_00_u03b5_9509_,
        v_00_u03b1_9510_,
        v_00_u03b2_9511_,
        v_x_9512_,
        v_y_9513_,
        v_prio_9514_,
    );
    return v_res_9516_;
}
pub unsafe fn l_Std_Async_EAsync_race___redArg___lam__1(
    mut v_x_9517_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_9519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9522_: u8 = 0;
    let mut v___x_9524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9527_: u8 = 0;
    let mut v_a_9528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9529_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_9517_) == 0 {
                    v_a_9519_ = lean_ctor_get(v_x_9517_, 0);
                    v_isSharedCheck_9527_ = (!lean_is_exclusive(v_x_9517_)) as u8;
                    if v_isSharedCheck_9527_ == 0 {
                        v___x_9521_ = v_x_9517_;
                        v_isShared_9522_ = v_isSharedCheck_9527_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_9519_);
                        lean_dec(v_x_9517_);
                        v___x_9521_ = lean_box(0);
                        v_isShared_9522_ = v_isSharedCheck_9527_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_9528_ = lean_ctor_get(v_x_9517_, 0);
                    lean_inc(v_a_9528_);
                    lean_dec_ref_known(v_x_9517_, 1);
                    v___x_9529_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_9529_, 0, v_a_9528_);
                    return v___x_9529_;
                }
            }
            1 => {
                if v_isShared_9522_ == 0 {
                    v___x_9524_ = v___x_9521_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_9526_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9526_, 0, v_a_9519_);
                    v___x_9524_ = v_reuseFailAlloc_9526_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_9525_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_9525_, 0, v___x_9524_);
                return v___x_9525_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_EAsync_race___redArg___lam__1___boxed(
    mut v_x_9530_: *mut LeanObject,
    mut v___y_9531_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9532_: *mut LeanObject = core::ptr::null_mut();
    v_res_9532_ = l_Std_Async_EAsync_race___redArg___lam__1(v_x_9530_);
    return v_res_9532_;
}
pub unsafe fn l_Std_Async_EAsync_race___redArg___lam__0(
    mut v_a_9533_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9534_: *mut LeanObject = core::ptr::null_mut();
    v___x_9534_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_9534_, 0, v_a_9533_);
    return v___x_9534_;
}
pub unsafe fn l_Std_Async_EAsync_race___redArg___lam__3(
    mut v_a_9535_: *mut LeanObject,
    mut v_value_9536_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9538_: *mut LeanObject = core::ptr::null_mut();
    v___x_9538_ = lean_io_promise_resolve(v_value_9536_, v_a_9535_);
    return v___x_9538_;
}
pub unsafe fn l_Std_Async_EAsync_race___redArg___lam__3___boxed(
    mut v_a_9539_: *mut LeanObject,
    mut v_value_9540_: *mut LeanObject,
    mut v___y_9541_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9542_: *mut LeanObject = core::ptr::null_mut();
    v_res_9542_ = l_Std_Async_EAsync_race___redArg___lam__3(v_a_9539_, v_value_9540_);
    lean_dec(v_a_9539_);
    return v_res_9542_;
}
pub unsafe fn l_Std_Async_EAsync_race___redArg___lam__2(
    mut v_a_9543_: *mut LeanObject,
    mut v___f_9544_: *mut LeanObject,
    mut v___f_9545_: *mut LeanObject,
    mut v_x_9546_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_9548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9551_: u8 = 0;
    let mut v___x_9553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9556_: u8 = 0;
    let mut v___x_9557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9559_: u8 = 0;
    let mut v___x_9560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9562_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_9546_) == 0 {
                    lean_dec_ref(v___f_9545_);
                    lean_dec_ref(v___f_9544_);
                    v_a_9548_ = lean_ctor_get(v_x_9546_, 0);
                    v_isSharedCheck_9556_ = (!lean_is_exclusive(v_x_9546_)) as u8;
                    if v_isSharedCheck_9556_ == 0 {
                        v___x_9550_ = v_x_9546_;
                        v_isShared_9551_ = v_isSharedCheck_9556_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_9548_);
                        lean_dec(v_x_9546_);
                        v___x_9550_ = lean_box(0);
                        v_isShared_9551_ = v_isSharedCheck_9556_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v_x_9546_, 1);
                    v___x_9557_ = l_IO_Promise_result_x21___redArg(v_a_9543_);
                    v___x_9558_ = lean_unsigned_to_nat(0);
                    v___x_9559_ = 0;
                    v___x_9560_ = lean_task_map(v___f_9544_, v___x_9557_, v___x_9558_, v___x_9559_);
                    v___x_9561_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_9561_, 0, v___x_9560_);
                    v___x_9562_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_9558_, v___x_9559_, v___x_9561_, v___f_9545_);
                    return v___x_9562_;
                }
            }
            1 => {
                if v_isShared_9551_ == 0 {
                    v___x_9553_ = v___x_9550_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_9555_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9555_, 0, v_a_9548_);
                    v___x_9553_ = v_reuseFailAlloc_9555_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_9554_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_9554_, 0, v___x_9553_);
                return v___x_9554_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_EAsync_race___redArg___lam__2___boxed(
    mut v_a_9563_: *mut LeanObject,
    mut v___f_9564_: *mut LeanObject,
    mut v___f_9565_: *mut LeanObject,
    mut v_x_9566_: *mut LeanObject,
    mut v___y_9567_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9568_: *mut LeanObject = core::ptr::null_mut();
    v_res_9568_ =
        l_Std_Async_EAsync_race___redArg___lam__2(v_a_9563_, v___f_9564_, v___f_9565_, v_x_9566_);
    lean_dec(v_a_9563_);
    return v_res_9568_;
}
pub unsafe fn l_Std_Async_EAsync_race___redArg___lam__4(
    mut v_a_9569_: *mut LeanObject,
    mut v___x_9570_: *mut LeanObject,
    mut v___x_9571_: *mut LeanObject,
    mut v___x_9572_: u8,
    mut v___f_9573_: *mut LeanObject,
    mut v_x_9574_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_9576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9579_: u8 = 0;
    let mut v___x_9581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9584_: u8 = 0;
    let mut v___x_9586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9587_: u8 = 0;
    let mut v___x_9588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9594_: u8 = 0;
    let mut v_unused_9595_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_9574_) == 0 {
                    lean_dec_ref(v___f_9573_);
                    lean_dec(v___x_9571_);
                    lean_dec_ref(v___x_9570_);
                    lean_dec_ref(v_a_9569_);
                    v_a_9576_ = lean_ctor_get(v_x_9574_, 0);
                    v_isSharedCheck_9584_ = (!lean_is_exclusive(v_x_9574_)) as u8;
                    if v_isSharedCheck_9584_ == 0 {
                        v___x_9578_ = v_x_9574_;
                        v_isShared_9579_ = v_isSharedCheck_9584_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_9576_);
                        lean_dec(v_x_9574_);
                        v___x_9578_ = lean_box(0);
                        v_isShared_9579_ = v_isSharedCheck_9584_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_isSharedCheck_9594_ = (!lean_is_exclusive(v_x_9574_)) as u8;
                    if v_isSharedCheck_9594_ == 0 {
                        v_unused_9595_ = lean_ctor_get(v_x_9574_, 0);
                        lean_dec(v_unused_9595_);
                        v___x_9586_ = v_x_9574_;
                        v_isShared_9587_ = v_isSharedCheck_9594_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v_x_9574_);
                        v___x_9586_ = lean_box(0);
                        v_isShared_9587_ = v_isSharedCheck_9594_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_9579_ == 0 {
                    v___x_9581_ = v___x_9578_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_9583_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9583_, 0, v_a_9576_);
                    v___x_9581_ = v_reuseFailAlloc_9583_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_9582_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_9582_, 0, v___x_9581_);
                return v___x_9582_;
            }
            3 => {
                lean_inc(v___x_9571_);
                v___x_9588_ =
                    l_BaseIO_chainTask___redArg(v_a_9569_, v___x_9570_, v___x_9571_, v___x_9572_);
                if v_isShared_9587_ == 0 {
                    lean_ctor_set(v___x_9586_, 0, v___x_9588_);
                    v___x_9590_ = v___x_9586_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_9593_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9593_, 0, v___x_9588_);
                    v___x_9590_ = v_reuseFailAlloc_9593_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_9591_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_9591_, 0, v___x_9590_);
                v___x_9592_ =
                    l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(
                        v___x_9571_,
                        v___x_9572_,
                        v___x_9591_,
                        v___f_9573_,
                    );
                return v___x_9592_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_EAsync_race___redArg___lam__4___boxed(
    mut v_a_9596_: *mut LeanObject,
    mut v___x_9597_: *mut LeanObject,
    mut v___x_9598_: *mut LeanObject,
    mut v___x_9599_: *mut LeanObject,
    mut v___f_9600_: *mut LeanObject,
    mut v_x_9601_: *mut LeanObject,
    mut v___y_9602_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1425__boxed_9603_: u8 = 0;
    let mut v_res_9604_: *mut LeanObject = core::ptr::null_mut();
    v___x_1425__boxed_9603_ = (lean_unbox(v___x_9599_) as u8);
    v_res_9604_ = l_Std_Async_EAsync_race___redArg___lam__4(
        v_a_9596_,
        v___x_9597_,
        v___x_9598_,
        v___x_1425__boxed_9603_,
        v___f_9600_,
        v_x_9601_,
    );
    return v_res_9604_;
}
pub unsafe fn l_Std_Async_EAsync_race___redArg___lam__5(
    mut v___f_9605_: *mut LeanObject,
    mut v___f_9606_: *mut LeanObject,
    mut v_a_9607_: *mut LeanObject,
    mut v___f_9608_: *mut LeanObject,
    mut v_x_9609_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_9611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9614_: u8 = 0;
    let mut v___x_9616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9619_: u8 = 0;
    let mut v_a_9620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9623_: u8 = 0;
    let mut v___x_9624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9627_: u8 = 0;
    let mut v___x_9628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9636_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_9609_) == 0 {
                    lean_dec_ref(v___f_9608_);
                    lean_dec_ref(v_a_9607_);
                    lean_dec_ref(v___f_9606_);
                    lean_dec(v___f_9605_);
                    v_a_9611_ = lean_ctor_get(v_x_9609_, 0);
                    v_isSharedCheck_9619_ = (!lean_is_exclusive(v_x_9609_)) as u8;
                    if v_isSharedCheck_9619_ == 0 {
                        v___x_9613_ = v_x_9609_;
                        v_isShared_9614_ = v_isSharedCheck_9619_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_9611_);
                        lean_dec(v_x_9609_);
                        v___x_9613_ = lean_box(0);
                        v_isShared_9614_ = v_isSharedCheck_9619_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_9620_ = lean_ctor_get(v_x_9609_, 0);
                    v_isSharedCheck_9636_ = (!lean_is_exclusive(v_x_9609_)) as u8;
                    if v_isSharedCheck_9636_ == 0 {
                        v___x_9622_ = v_x_9609_;
                        v_isShared_9623_ = v_isSharedCheck_9636_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_9620_);
                        lean_dec(v_x_9609_);
                        v___x_9622_ = lean_box(0);
                        v_isShared_9623_ = v_isSharedCheck_9636_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_9614_ == 0 {
                    v___x_9616_ = v___x_9613_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_9618_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9618_, 0, v_a_9611_);
                    v___x_9616_ = v_reuseFailAlloc_9618_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_9617_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_9617_, 0, v___x_9616_);
                return v___x_9617_;
            }
            3 => {
                v___x_9624_ = lean_alloc_closure(l_liftM as *mut core::ffi::c_void, 5, 4);
                lean_closure_set(v___x_9624_, 0, lean_box(0));
                lean_closure_set(v___x_9624_, 1, lean_box(0));
                lean_closure_set(v___x_9624_, 2, v___f_9605_);
                lean_closure_set(v___x_9624_, 3, lean_box(0));
                v___x_9625_ = lean_alloc_closure(l_Function_comp as *mut core::ffi::c_void, 6, 5);
                lean_closure_set(v___x_9625_, 0, lean_box(0));
                lean_closure_set(v___x_9625_, 1, lean_box(0));
                lean_closure_set(v___x_9625_, 2, lean_box(0));
                lean_closure_set(v___x_9625_, 3, v___x_9624_);
                lean_closure_set(v___x_9625_, 4, v___f_9606_);
                v___x_9626_ = lean_unsigned_to_nat(0);
                v___x_9627_ = 0;
                lean_inc_ref(v___x_9625_);
                v___x_9628_ =
                    l_BaseIO_chainTask___redArg(v_a_9607_, v___x_9625_, v___x_9626_, v___x_9627_);
                v___x_9629_ = lean_box((v___x_9627_) as usize);
                v___f_9630_ = lean_alloc_closure(
                    l_Std_Async_EAsync_race___redArg___lam__4___boxed as *mut core::ffi::c_void,
                    7,
                    5,
                );
                lean_closure_set(v___f_9630_, 0, v_a_9620_);
                lean_closure_set(v___f_9630_, 1, v___x_9625_);
                lean_closure_set(v___f_9630_, 2, v___x_9626_);
                lean_closure_set(v___f_9630_, 3, v___x_9629_);
                lean_closure_set(v___f_9630_, 4, v___f_9608_);
                if v_isShared_9623_ == 0 {
                    lean_ctor_set(v___x_9622_, 0, v___x_9628_);
                    v___x_9632_ = v___x_9622_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_9635_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9635_, 0, v___x_9628_);
                    v___x_9632_ = v_reuseFailAlloc_9635_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_9633_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_9633_, 0, v___x_9632_);
                v___x_9634_ =
                    l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(
                        v___x_9626_,
                        v___x_9627_,
                        v___x_9633_,
                        v___f_9630_,
                    );
                return v___x_9634_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_EAsync_race___redArg___lam__5___boxed(
    mut v___f_9637_: *mut LeanObject,
    mut v___f_9638_: *mut LeanObject,
    mut v_a_9639_: *mut LeanObject,
    mut v___f_9640_: *mut LeanObject,
    mut v_x_9641_: *mut LeanObject,
    mut v___y_9642_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9643_: *mut LeanObject = core::ptr::null_mut();
    v_res_9643_ = l_Std_Async_EAsync_race___redArg___lam__5(
        v___f_9637_,
        v___f_9638_,
        v_a_9639_,
        v___f_9640_,
        v_x_9641_,
    );
    return v_res_9643_;
}
pub unsafe fn l_Std_Async_EAsync_race___redArg___lam__6(
    mut v_y_9644_: *mut LeanObject,
    mut v_prio_9645_: *mut LeanObject,
    mut v___f_9646_: *mut LeanObject,
    mut v___f_9647_: *mut LeanObject,
    mut v___f_9648_: *mut LeanObject,
    mut v___f_9649_: *mut LeanObject,
    mut v_x_9650_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_9652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9655_: u8 = 0;
    let mut v___x_9657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9660_: u8 = 0;
    let mut v_a_9661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9664_: u8 = 0;
    let mut v___x_9665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9669_: u8 = 0;
    let mut v___x_9670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9674_: u8 = 0;
    let mut v___x_9675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9677_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_9650_) == 0 {
                    lean_dec_ref(v___f_9649_);
                    lean_dec_ref(v___f_9648_);
                    lean_dec_ref(v___f_9647_);
                    lean_dec(v___f_9646_);
                    lean_dec(v_prio_9645_);
                    lean_dec_ref(v_y_9644_);
                    v_a_9652_ = lean_ctor_get(v_x_9650_, 0);
                    v_isSharedCheck_9660_ = (!lean_is_exclusive(v_x_9650_)) as u8;
                    if v_isSharedCheck_9660_ == 0 {
                        v___x_9654_ = v_x_9650_;
                        v_isShared_9655_ = v_isSharedCheck_9660_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_9652_);
                        lean_dec(v_x_9650_);
                        v___x_9654_ = lean_box(0);
                        v_isShared_9655_ = v_isSharedCheck_9660_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_9661_ = lean_ctor_get(v_x_9650_, 0);
                    v_isSharedCheck_9677_ = (!lean_is_exclusive(v_x_9650_)) as u8;
                    if v_isSharedCheck_9677_ == 0 {
                        v___x_9663_ = v_x_9650_;
                        v_isShared_9664_ = v_isSharedCheck_9677_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_9661_);
                        lean_dec(v_x_9650_);
                        v___x_9663_ = lean_box(0);
                        v_isShared_9664_ = v_isSharedCheck_9677_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_9655_ == 0 {
                    v___x_9657_ = v___x_9654_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_9659_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9659_, 0, v_a_9652_);
                    v___x_9657_ = v_reuseFailAlloc_9659_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_9658_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_9658_, 0, v___x_9657_);
                return v___x_9658_;
            }
            3 => {
                v___x_9665_ = lean_alloc_closure(
                    l_Std_Async_BaseAsync_toRawBaseIO___boxed as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___x_9665_, 0, lean_box(0));
                lean_closure_set(v___x_9665_, 1, v_y_9644_);
                v___x_9666_ = lean_io_as_task(v___x_9665_, v_prio_9645_);
                v___f_9667_ = lean_alloc_closure(
                    l_Std_Async_EAsync_race___redArg___lam__5___boxed as *mut core::ffi::c_void,
                    6,
                    4,
                );
                lean_closure_set(v___f_9667_, 0, v___f_9646_);
                lean_closure_set(v___f_9667_, 1, v___f_9647_);
                lean_closure_set(v___f_9667_, 2, v_a_9661_);
                lean_closure_set(v___f_9667_, 3, v___f_9648_);
                v___x_9668_ = lean_unsigned_to_nat(0);
                v___x_9669_ = 1;
                v___x_9670_ = lean_task_bind(v___x_9666_, v___f_9649_, v___x_9668_, v___x_9669_);
                if v_isShared_9664_ == 0 {
                    lean_ctor_set(v___x_9663_, 0, v___x_9670_);
                    v___x_9672_ = v___x_9663_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_9676_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9676_, 0, v___x_9670_);
                    v___x_9672_ = v_reuseFailAlloc_9676_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_9673_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_9673_, 0, v___x_9672_);
                v___x_9674_ = 0;
                v___x_9675_ =
                    l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(
                        v___x_9668_,
                        v___x_9674_,
                        v___x_9673_,
                        v___f_9667_,
                    );
                return v___x_9675_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_EAsync_race___redArg___lam__6___boxed(
    mut v_y_9678_: *mut LeanObject,
    mut v_prio_9679_: *mut LeanObject,
    mut v___f_9680_: *mut LeanObject,
    mut v___f_9681_: *mut LeanObject,
    mut v___f_9682_: *mut LeanObject,
    mut v___f_9683_: *mut LeanObject,
    mut v_x_9684_: *mut LeanObject,
    mut v___y_9685_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9686_: *mut LeanObject = core::ptr::null_mut();
    v_res_9686_ = l_Std_Async_EAsync_race___redArg___lam__6(
        v_y_9678_,
        v_prio_9679_,
        v___f_9680_,
        v___f_9681_,
        v___f_9682_,
        v___f_9683_,
        v_x_9684_,
    );
    return v_res_9686_;
}
pub unsafe fn l_Std_Async_EAsync_race___redArg___lam__7(
    mut v_x_9687_: *mut LeanObject,
    mut v_prio_9688_: *mut LeanObject,
    mut v___f_9689_: *mut LeanObject,
    mut v___f_9690_: *mut LeanObject,
    mut v_y_9691_: *mut LeanObject,
    mut v___f_9692_: *mut LeanObject,
    mut v___f_9693_: *mut LeanObject,
    mut v___f_9694_: *mut LeanObject,
    mut v_x_9695_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_9697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9700_: u8 = 0;
    let mut v___x_9702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9705_: u8 = 0;
    let mut v_a_9706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9709_: u8 = 0;
    let mut v___x_9710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9716_: u8 = 0;
    let mut v___x_9717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9721_: u8 = 0;
    let mut v___x_9722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9724_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_9695_) == 0 {
                    lean_dec_ref(v___f_9694_);
                    lean_dec_ref(v___f_9693_);
                    lean_dec(v___f_9692_);
                    lean_dec_ref(v_y_9691_);
                    lean_dec_ref(v___f_9690_);
                    lean_dec_ref(v___f_9689_);
                    lean_dec(v_prio_9688_);
                    lean_dec_ref(v_x_9687_);
                    v_a_9697_ = lean_ctor_get(v_x_9695_, 0);
                    v_isSharedCheck_9705_ = (!lean_is_exclusive(v_x_9695_)) as u8;
                    if v_isSharedCheck_9705_ == 0 {
                        v___x_9699_ = v_x_9695_;
                        v_isShared_9700_ = v_isSharedCheck_9705_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_9697_);
                        lean_dec(v_x_9695_);
                        v___x_9699_ = lean_box(0);
                        v_isShared_9700_ = v_isSharedCheck_9705_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_9706_ = lean_ctor_get(v_x_9695_, 0);
                    v_isSharedCheck_9724_ = (!lean_is_exclusive(v_x_9695_)) as u8;
                    if v_isSharedCheck_9724_ == 0 {
                        v___x_9708_ = v_x_9695_;
                        v_isShared_9709_ = v_isSharedCheck_9724_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_9706_);
                        lean_dec(v_x_9695_);
                        v___x_9708_ = lean_box(0);
                        v_isShared_9709_ = v_isSharedCheck_9724_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_9700_ == 0 {
                    v___x_9702_ = v___x_9699_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_9704_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9704_, 0, v_a_9697_);
                    v___x_9702_ = v_reuseFailAlloc_9704_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_9703_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_9703_, 0, v___x_9702_);
                return v___x_9703_;
            }
            3 => {
                v___x_9710_ = lean_alloc_closure(
                    l_Std_Async_BaseAsync_toRawBaseIO___boxed as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___x_9710_, 0, lean_box(0));
                lean_closure_set(v___x_9710_, 1, v_x_9687_);
                lean_inc(v_prio_9688_);
                v___x_9711_ = lean_io_as_task(v___x_9710_, v_prio_9688_);
                lean_inc(v_a_9706_);
                v___f_9712_ = lean_alloc_closure(
                    l_Std_Async_EAsync_race___redArg___lam__3___boxed as *mut core::ffi::c_void,
                    3,
                    1,
                );
                lean_closure_set(v___f_9712_, 0, v_a_9706_);
                v___f_9713_ = lean_alloc_closure(
                    l_Std_Async_EAsync_race___redArg___lam__2___boxed as *mut core::ffi::c_void,
                    5,
                    3,
                );
                lean_closure_set(v___f_9713_, 0, v_a_9706_);
                lean_closure_set(v___f_9713_, 1, v___f_9689_);
                lean_closure_set(v___f_9713_, 2, v___f_9690_);
                v___f_9714_ = lean_alloc_closure(
                    l_Std_Async_EAsync_race___redArg___lam__6___boxed as *mut core::ffi::c_void,
                    8,
                    6,
                );
                lean_closure_set(v___f_9714_, 0, v_y_9691_);
                lean_closure_set(v___f_9714_, 1, v_prio_9688_);
                lean_closure_set(v___f_9714_, 2, v___f_9692_);
                lean_closure_set(v___f_9714_, 3, v___f_9712_);
                lean_closure_set(v___f_9714_, 4, v___f_9713_);
                lean_closure_set(v___f_9714_, 5, v___f_9693_);
                v___x_9715_ = lean_unsigned_to_nat(0);
                v___x_9716_ = 1;
                v___x_9717_ = lean_task_bind(v___x_9711_, v___f_9694_, v___x_9715_, v___x_9716_);
                if v_isShared_9709_ == 0 {
                    lean_ctor_set(v___x_9708_, 0, v___x_9717_);
                    v___x_9719_ = v___x_9708_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_9723_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9723_, 0, v___x_9717_);
                    v___x_9719_ = v_reuseFailAlloc_9723_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_9720_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_9720_, 0, v___x_9719_);
                v___x_9721_ = 0;
                v___x_9722_ =
                    l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(
                        v___x_9715_,
                        v___x_9721_,
                        v___x_9720_,
                        v___f_9714_,
                    );
                return v___x_9722_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_EAsync_race___redArg___lam__7___boxed(
    mut v_x_9725_: *mut LeanObject,
    mut v_prio_9726_: *mut LeanObject,
    mut v___f_9727_: *mut LeanObject,
    mut v___f_9728_: *mut LeanObject,
    mut v_y_9729_: *mut LeanObject,
    mut v___f_9730_: *mut LeanObject,
    mut v___f_9731_: *mut LeanObject,
    mut v___f_9732_: *mut LeanObject,
    mut v_x_9733_: *mut LeanObject,
    mut v___y_9734_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9735_: *mut LeanObject = core::ptr::null_mut();
    v_res_9735_ = l_Std_Async_EAsync_race___redArg___lam__7(
        v_x_9725_,
        v_prio_9726_,
        v___f_9727_,
        v___f_9728_,
        v_y_9729_,
        v___f_9730_,
        v___f_9731_,
        v___f_9732_,
        v_x_9733_,
    );
    return v_res_9735_;
}
pub unsafe fn l_Std_Async_EAsync_race___redArg(
    mut v_x_9738_: *mut LeanObject,
    mut v_y_9739_: *mut LeanObject,
    mut v_prio_9740_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9751_: u8 = 0;
    let mut v___x_9752_: *mut LeanObject = core::ptr::null_mut();
    v___x_9742_ = lean_io_promise_new();
    v___f_9743_ = l_Std_Async_EAsync_asTask___redArg___closed__0;
    v___f_9744_ = l_Std_Async_EAsync_race___redArg___closed__0;
    v___f_9745_ = l_Std_Async_EAsync_race___redArg___closed__1;
    v___f_9746_ = l_Std_Async_BaseAsync_race___redArg___closed__0;
    v___f_9747_ = lean_alloc_closure(
        l_Std_Async_EAsync_race___redArg___lam__7___boxed as *mut core::ffi::c_void,
        10,
        8,
    );
    lean_closure_set(v___f_9747_, 0, v_x_9738_);
    lean_closure_set(v___f_9747_, 1, v_prio_9740_);
    lean_closure_set(v___f_9747_, 2, v___f_9745_);
    lean_closure_set(v___f_9747_, 3, v___f_9744_);
    lean_closure_set(v___f_9747_, 4, v_y_9739_);
    lean_closure_set(v___f_9747_, 5, v___f_9746_);
    lean_closure_set(v___f_9747_, 6, v___f_9743_);
    lean_closure_set(v___f_9747_, 7, v___f_9743_);
    v___x_9748_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_9748_, 0, v___x_9742_);
    v___x_9749_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_9749_, 0, v___x_9748_);
    v___x_9750_ = lean_unsigned_to_nat(0);
    v___x_9751_ = 0;
    v___x_9752_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(
        v___x_9750_,
        v___x_9751_,
        v___x_9749_,
        v___f_9747_,
    );
    return v___x_9752_;
}
pub unsafe fn l_Std_Async_EAsync_race___redArg___boxed(
    mut v_x_9753_: *mut LeanObject,
    mut v_y_9754_: *mut LeanObject,
    mut v_prio_9755_: *mut LeanObject,
    mut v_a_9756_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9757_: *mut LeanObject = core::ptr::null_mut();
    v_res_9757_ = l_Std_Async_EAsync_race___redArg(v_x_9753_, v_y_9754_, v_prio_9755_);
    return v_res_9757_;
}
pub unsafe fn l_Std_Async_EAsync_race(
    mut v_00_u03b1_9758_: *mut LeanObject,
    mut v_00_u03b5_9759_: *mut LeanObject,
    mut v_inst_9760_: *mut LeanObject,
    mut v_x_9761_: *mut LeanObject,
    mut v_y_9762_: *mut LeanObject,
    mut v_prio_9763_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9774_: u8 = 0;
    let mut v___x_9775_: *mut LeanObject = core::ptr::null_mut();
    v___x_9765_ = lean_io_promise_new();
    v___f_9766_ = l_Std_Async_EAsync_asTask___redArg___closed__0;
    v___f_9767_ = l_Std_Async_EAsync_race___redArg___closed__0;
    v___f_9768_ = l_Std_Async_EAsync_race___redArg___closed__1;
    v___f_9769_ = l_Std_Async_BaseAsync_race___redArg___closed__0;
    v___f_9770_ = lean_alloc_closure(
        l_Std_Async_EAsync_race___redArg___lam__7___boxed as *mut core::ffi::c_void,
        10,
        8,
    );
    lean_closure_set(v___f_9770_, 0, v_x_9761_);
    lean_closure_set(v___f_9770_, 1, v_prio_9763_);
    lean_closure_set(v___f_9770_, 2, v___f_9768_);
    lean_closure_set(v___f_9770_, 3, v___f_9767_);
    lean_closure_set(v___f_9770_, 4, v_y_9762_);
    lean_closure_set(v___f_9770_, 5, v___f_9769_);
    lean_closure_set(v___f_9770_, 6, v___f_9766_);
    lean_closure_set(v___f_9770_, 7, v___f_9766_);
    v___x_9771_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_9771_, 0, v___x_9765_);
    v___x_9772_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_9772_, 0, v___x_9771_);
    v___x_9773_ = lean_unsigned_to_nat(0);
    v___x_9774_ = 0;
    v___x_9775_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(
        v___x_9773_,
        v___x_9774_,
        v___x_9772_,
        v___f_9770_,
    );
    return v___x_9775_;
}
pub unsafe fn l_Std_Async_EAsync_race___boxed(
    mut v_00_u03b1_9776_: *mut LeanObject,
    mut v_00_u03b5_9777_: *mut LeanObject,
    mut v_inst_9778_: *mut LeanObject,
    mut v_x_9779_: *mut LeanObject,
    mut v_y_9780_: *mut LeanObject,
    mut v_prio_9781_: *mut LeanObject,
    mut v_a_9782_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9783_: *mut LeanObject = core::ptr::null_mut();
    v_res_9783_ = l_Std_Async_EAsync_race(
        v_00_u03b1_9776_,
        v_00_u03b5_9777_,
        v_inst_9778_,
        v_x_9779_,
        v_y_9780_,
        v_prio_9781_,
    );
    lean_dec(v_inst_9778_);
    return v_res_9783_;
}
pub unsafe fn l_Std_Async_EAsync_concurrentlyAll___redArg___lam__1(
    mut v_prio_9784_: *mut LeanObject,
    mut v___f_9785_: *mut LeanObject,
    mut v_x_9786_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9791_: u8 = 0;
    let mut v___x_9792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9794_: *mut LeanObject = core::ptr::null_mut();
    v___x_9788_ = lean_alloc_closure(
        l_Std_Async_BaseAsync_toRawBaseIO___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___x_9788_, 0, lean_box(0));
    lean_closure_set(v___x_9788_, 1, v_x_9786_);
    v___x_9789_ = lean_io_as_task(v___x_9788_, v_prio_9784_);
    v___x_9790_ = lean_unsigned_to_nat(0);
    v___x_9791_ = 1;
    v___x_9792_ = lean_task_bind(v___x_9789_, v___f_9785_, v___x_9790_, v___x_9791_);
    v___x_9793_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_9793_, 0, v___x_9792_);
    v___x_9794_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_9794_, 0, v___x_9793_);
    return v___x_9794_;
}
pub unsafe fn l_Std_Async_EAsync_concurrentlyAll___redArg___lam__1___boxed(
    mut v_prio_9795_: *mut LeanObject,
    mut v___f_9796_: *mut LeanObject,
    mut v_x_9797_: *mut LeanObject,
    mut v___y_9798_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9799_: *mut LeanObject = core::ptr::null_mut();
    v_res_9799_ =
        l_Std_Async_EAsync_concurrentlyAll___redArg___lam__1(v_prio_9795_, v___f_9796_, v_x_9797_);
    return v_res_9799_;
}
pub unsafe fn l_Std_Async_EAsync_concurrentlyAll___redArg___lam__0(
    mut v___y_9800_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9802_: *mut LeanObject = core::ptr::null_mut();
    v___x_9802_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_9802_, 0, v___y_9800_);
    return v___x_9802_;
}
pub unsafe fn l_Std_Async_EAsync_concurrentlyAll___redArg___lam__0___boxed(
    mut v___y_9803_: *mut LeanObject,
    mut v___y_9804_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9805_: *mut LeanObject = core::ptr::null_mut();
    v_res_9805_ = l_Std_Async_EAsync_concurrentlyAll___redArg___lam__0(v___y_9803_);
    return v_res_9805_;
}
pub unsafe fn l_Std_Async_EAsync_concurrentlyAll___redArg___lam__2(
    mut v___x_9806_: *mut LeanObject,
    mut v___f_9807_: *mut LeanObject,
    mut v_x_9808_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_9810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9813_: u8 = 0;
    let mut v___x_9815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9818_: u8 = 0;
    let mut v_a_9819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_9820_: usize = 0;
    let mut v___x_9821_: usize = 0;
    let mut v___x_290__overap_9822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9823_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_9808_) == 0 {
                    lean_dec_ref(v___f_9807_);
                    lean_dec_ref(v___x_9806_);
                    v_a_9810_ = lean_ctor_get(v_x_9808_, 0);
                    v_isSharedCheck_9818_ = (!lean_is_exclusive(v_x_9808_)) as u8;
                    if v_isSharedCheck_9818_ == 0 {
                        v___x_9812_ = v_x_9808_;
                        v_isShared_9813_ = v_isSharedCheck_9818_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_9810_);
                        lean_dec(v_x_9808_);
                        v___x_9812_ = lean_box(0);
                        v_isShared_9813_ = v_isSharedCheck_9818_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_9819_ = lean_ctor_get(v_x_9808_, 0);
                    lean_inc(v_a_9819_);
                    lean_dec_ref_known(v_x_9808_, 1);
                    v_sz_9820_ = lean_array_size(v_a_9819_);
                    v___x_9821_ = 0usize;
                    v___x_290__overap_9822_ =
                        l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                            lean_box(0),
                            lean_box(0),
                            lean_box(0),
                            v___x_9806_,
                            v___f_9807_,
                            v_sz_9820_,
                            v___x_9821_,
                            v_a_9819_,
                        );
                    v___x_9823_ = lean_apply_1(v___x_290__overap_9822_, lean_box(0));
                    return v___x_9823_;
                }
            }
            1 => {
                if v_isShared_9813_ == 0 {
                    v___x_9815_ = v___x_9812_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_9817_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9817_, 0, v_a_9810_);
                    v___x_9815_ = v_reuseFailAlloc_9817_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_9816_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_9816_, 0, v___x_9815_);
                return v___x_9816_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_EAsync_concurrentlyAll___redArg___lam__2___boxed(
    mut v___x_9824_: *mut LeanObject,
    mut v___f_9825_: *mut LeanObject,
    mut v_x_9826_: *mut LeanObject,
    mut v___y_9827_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9828_: *mut LeanObject = core::ptr::null_mut();
    v_res_9828_ =
        l_Std_Async_EAsync_concurrentlyAll___redArg___lam__2(v___x_9824_, v___f_9825_, v_x_9826_);
    return v_res_9828_;
}
pub unsafe fn _init_l_Std_Async_EAsync_concurrentlyAll___redArg___closed__0() -> *mut LeanObject {
    let mut v___x_9829_: *mut LeanObject = core::ptr::null_mut();
    v___x_9829_ = l_Std_Async_EAsync_instMonad(lean_box(0));
    return v___x_9829_;
}
pub unsafe fn _init_l_Std_Async_EAsync_concurrentlyAll___redArg___closed__2() -> *mut LeanObject {
    let mut v___f_9831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9833_: *mut LeanObject = core::ptr::null_mut();
    v___f_9831_ = l_Std_Async_EAsync_concurrentlyAll___redArg___closed__1;
    v___x_9832_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_EAsync_concurrentlyAll___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Std_Async_EAsync_concurrentlyAll___redArg___closed__0_once),
        _init_l_Std_Async_EAsync_concurrentlyAll___redArg___closed__0,
    );
    v___f_9833_ = lean_alloc_closure(
        l_Std_Async_EAsync_concurrentlyAll___redArg___lam__2___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_9833_, 0, v___x_9832_);
    lean_closure_set(v___f_9833_, 1, v___f_9831_);
    return v___f_9833_;
}
pub unsafe fn l_Std_Async_EAsync_concurrentlyAll___redArg(
    mut v_xs_9834_: *mut LeanObject,
    mut v_prio_9835_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_9837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_9840_: usize = 0;
    let mut v___x_9841_: usize = 0;
    let mut v___x_217__overap_9842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9846_: u8 = 0;
    let mut v___x_9847_: *mut LeanObject = core::ptr::null_mut();
    v___f_9837_ = l_Std_Async_EAsync_asTask___redArg___closed__0;
    v___f_9838_ = lean_alloc_closure(
        l_Std_Async_EAsync_concurrentlyAll___redArg___lam__1___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_9838_, 0, v_prio_9835_);
    lean_closure_set(v___f_9838_, 1, v___f_9837_);
    v___x_9839_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_EAsync_concurrentlyAll___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Std_Async_EAsync_concurrentlyAll___redArg___closed__0_once),
        _init_l_Std_Async_EAsync_concurrentlyAll___redArg___closed__0,
    );
    v_sz_9840_ = lean_array_size(v_xs_9834_);
    v___x_9841_ = 0usize;
    v___x_217__overap_9842_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
        lean_box(0),
        lean_box(0),
        lean_box(0),
        v___x_9839_,
        v___f_9838_,
        v_sz_9840_,
        v___x_9841_,
        v_xs_9834_,
    );
    v___x_9843_ = lean_apply_1(v___x_217__overap_9842_, lean_box(0));
    v___f_9844_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_EAsync_concurrentlyAll___redArg___closed__2),
        core::ptr::addr_of_mut!(l_Std_Async_EAsync_concurrentlyAll___redArg___closed__2_once),
        _init_l_Std_Async_EAsync_concurrentlyAll___redArg___closed__2,
    );
    v___x_9845_ = lean_unsigned_to_nat(0);
    v___x_9846_ = 0;
    v___x_9847_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(
        v___x_9845_,
        v___x_9846_,
        v___x_9843_,
        v___f_9844_,
    );
    return v___x_9847_;
}
pub unsafe fn l_Std_Async_EAsync_concurrentlyAll___redArg___boxed(
    mut v_xs_9848_: *mut LeanObject,
    mut v_prio_9849_: *mut LeanObject,
    mut v_a_9850_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9851_: *mut LeanObject = core::ptr::null_mut();
    v_res_9851_ = l_Std_Async_EAsync_concurrentlyAll___redArg(v_xs_9848_, v_prio_9849_);
    return v_res_9851_;
}
pub unsafe fn l_Std_Async_EAsync_concurrentlyAll(
    mut v_00_u03b5_9852_: *mut LeanObject,
    mut v_00_u03b1_9853_: *mut LeanObject,
    mut v_xs_9854_: *mut LeanObject,
    mut v_prio_9855_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_9857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_9860_: usize = 0;
    let mut v___x_9861_: usize = 0;
    let mut v___x_239__overap_9862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9866_: u8 = 0;
    let mut v___x_9867_: *mut LeanObject = core::ptr::null_mut();
    v___f_9857_ = l_Std_Async_EAsync_asTask___redArg___closed__0;
    v___f_9858_ = lean_alloc_closure(
        l_Std_Async_EAsync_concurrentlyAll___redArg___lam__1___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_9858_, 0, v_prio_9855_);
    lean_closure_set(v___f_9858_, 1, v___f_9857_);
    v___x_9859_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_EAsync_concurrentlyAll___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Std_Async_EAsync_concurrentlyAll___redArg___closed__0_once),
        _init_l_Std_Async_EAsync_concurrentlyAll___redArg___closed__0,
    );
    v_sz_9860_ = lean_array_size(v_xs_9854_);
    v___x_9861_ = 0usize;
    v___x_239__overap_9862_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
        lean_box(0),
        lean_box(0),
        lean_box(0),
        v___x_9859_,
        v___f_9858_,
        v_sz_9860_,
        v___x_9861_,
        v_xs_9854_,
    );
    v___x_9863_ = lean_apply_1(v___x_239__overap_9862_, lean_box(0));
    v___f_9864_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_EAsync_concurrentlyAll___redArg___closed__2),
        core::ptr::addr_of_mut!(l_Std_Async_EAsync_concurrentlyAll___redArg___closed__2_once),
        _init_l_Std_Async_EAsync_concurrentlyAll___redArg___closed__2,
    );
    v___x_9865_ = lean_unsigned_to_nat(0);
    v___x_9866_ = 0;
    v___x_9867_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(
        v___x_9865_,
        v___x_9866_,
        v___x_9863_,
        v___f_9864_,
    );
    return v___x_9867_;
}
pub unsafe fn l_Std_Async_EAsync_concurrentlyAll___boxed(
    mut v_00_u03b5_9868_: *mut LeanObject,
    mut v_00_u03b1_9869_: *mut LeanObject,
    mut v_xs_9870_: *mut LeanObject,
    mut v_prio_9871_: *mut LeanObject,
    mut v_a_9872_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9873_: *mut LeanObject = core::ptr::null_mut();
    v_res_9873_ = l_Std_Async_EAsync_concurrentlyAll(
        v_00_u03b5_9868_,
        v_00_u03b1_9869_,
        v_xs_9870_,
        v_prio_9871_,
    );
    return v_res_9873_;
}
pub unsafe fn l_Std_Async_EAsync_raceAll___redArg___lam__4(
    mut v___f_9874_: *mut LeanObject,
    mut v___f_9875_: *mut LeanObject,
    mut v_x_9876_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_9878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9881_: u8 = 0;
    let mut v___x_9883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9886_: u8 = 0;
    let mut v_a_9887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9890_: u8 = 0;
    let mut v___x_9891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9894_: u8 = 0;
    let mut v___x_9895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9900_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_9876_) == 0 {
                    lean_dec_ref(v___f_9875_);
                    lean_dec(v___f_9874_);
                    v_a_9878_ = lean_ctor_get(v_x_9876_, 0);
                    v_isSharedCheck_9886_ = (!lean_is_exclusive(v_x_9876_)) as u8;
                    if v_isSharedCheck_9886_ == 0 {
                        v___x_9880_ = v_x_9876_;
                        v_isShared_9881_ = v_isSharedCheck_9886_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_9878_);
                        lean_dec(v_x_9876_);
                        v___x_9880_ = lean_box(0);
                        v_isShared_9881_ = v_isSharedCheck_9886_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_9887_ = lean_ctor_get(v_x_9876_, 0);
                    v_isSharedCheck_9900_ = (!lean_is_exclusive(v_x_9876_)) as u8;
                    if v_isSharedCheck_9900_ == 0 {
                        v___x_9889_ = v_x_9876_;
                        v_isShared_9890_ = v_isSharedCheck_9900_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_9887_);
                        lean_dec(v_x_9876_);
                        v___x_9889_ = lean_box(0);
                        v_isShared_9890_ = v_isSharedCheck_9900_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_9881_ == 0 {
                    v___x_9883_ = v___x_9880_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_9885_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9885_, 0, v_a_9878_);
                    v___x_9883_ = v_reuseFailAlloc_9885_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_9884_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_9884_, 0, v___x_9883_);
                return v___x_9884_;
            }
            3 => {
                v___x_9891_ = lean_alloc_closure(l_liftM as *mut core::ffi::c_void, 5, 4);
                lean_closure_set(v___x_9891_, 0, lean_box(0));
                lean_closure_set(v___x_9891_, 1, lean_box(0));
                lean_closure_set(v___x_9891_, 2, v___f_9874_);
                lean_closure_set(v___x_9891_, 3, lean_box(0));
                v___x_9892_ = lean_alloc_closure(l_Function_comp as *mut core::ffi::c_void, 6, 5);
                lean_closure_set(v___x_9892_, 0, lean_box(0));
                lean_closure_set(v___x_9892_, 1, lean_box(0));
                lean_closure_set(v___x_9892_, 2, lean_box(0));
                lean_closure_set(v___x_9892_, 3, v___x_9891_);
                lean_closure_set(v___x_9892_, 4, v___f_9875_);
                v___x_9893_ = lean_unsigned_to_nat(0);
                v___x_9894_ = 0;
                v___x_9895_ =
                    l_BaseIO_chainTask___redArg(v_a_9887_, v___x_9892_, v___x_9893_, v___x_9894_);
                if v_isShared_9890_ == 0 {
                    lean_ctor_set(v___x_9889_, 0, v___x_9895_);
                    v___x_9897_ = v___x_9889_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_9899_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9899_, 0, v___x_9895_);
                    v___x_9897_ = v_reuseFailAlloc_9899_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_9898_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_9898_, 0, v___x_9897_);
                return v___x_9898_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_EAsync_raceAll___redArg___lam__4___boxed(
    mut v___f_9901_: *mut LeanObject,
    mut v___f_9902_: *mut LeanObject,
    mut v_x_9903_: *mut LeanObject,
    mut v___y_9904_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9905_: *mut LeanObject = core::ptr::null_mut();
    v_res_9905_ = l_Std_Async_EAsync_raceAll___redArg___lam__4(v___f_9901_, v___f_9902_, v_x_9903_);
    return v_res_9905_;
}
pub unsafe fn l_Std_Async_EAsync_raceAll___redArg___lam__0(
    mut v_prio_9906_: *mut LeanObject,
    mut v___f_9907_: *mut LeanObject,
    mut v___f_9908_: *mut LeanObject,
    mut v_x_9909_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9914_: u8 = 0;
    let mut v___x_9915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9918_: u8 = 0;
    let mut v___x_9919_: *mut LeanObject = core::ptr::null_mut();
    v___x_9911_ = lean_alloc_closure(
        l_Std_Async_BaseAsync_toRawBaseIO___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___x_9911_, 0, lean_box(0));
    lean_closure_set(v___x_9911_, 1, v_x_9909_);
    v___x_9912_ = lean_io_as_task(v___x_9911_, v_prio_9906_);
    v___x_9913_ = lean_unsigned_to_nat(0);
    v___x_9914_ = 1;
    v___x_9915_ = lean_task_bind(v___x_9912_, v___f_9907_, v___x_9913_, v___x_9914_);
    v___x_9916_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_9916_, 0, v___x_9915_);
    v___x_9917_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_9917_, 0, v___x_9916_);
    v___x_9918_ = 0;
    v___x_9919_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(
        v___x_9913_,
        v___x_9918_,
        v___x_9917_,
        v___f_9908_,
    );
    return v___x_9919_;
}
pub unsafe fn l_Std_Async_EAsync_raceAll___redArg___lam__0___boxed(
    mut v_prio_9920_: *mut LeanObject,
    mut v___f_9921_: *mut LeanObject,
    mut v___f_9922_: *mut LeanObject,
    mut v_x_9923_: *mut LeanObject,
    mut v___y_9924_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9925_: *mut LeanObject = core::ptr::null_mut();
    v_res_9925_ = l_Std_Async_EAsync_raceAll___redArg___lam__0(
        v_prio_9920_,
        v___f_9921_,
        v___f_9922_,
        v_x_9923_,
    );
    return v_res_9925_;
}
pub unsafe fn l_Std_Async_EAsync_raceAll___redArg___lam__2(
    mut v___f_9926_: *mut LeanObject,
    mut v_prio_9927_: *mut LeanObject,
    mut v___f_9928_: *mut LeanObject,
    mut v_inst_9929_: *mut LeanObject,
    mut v_xs_9930_: *mut LeanObject,
    mut v___f_9931_: *mut LeanObject,
    mut v___f_9932_: *mut LeanObject,
    mut v_x_9933_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_9935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9938_: u8 = 0;
    let mut v___x_9940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9943_: u8 = 0;
    let mut v_a_9944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9951_: u8 = 0;
    let mut v___x_9952_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_9933_) == 0 {
                    lean_dec_ref(v___f_9932_);
                    lean_dec_ref(v___f_9931_);
                    lean_dec(v_xs_9930_);
                    lean_dec_ref(v_inst_9929_);
                    lean_dec_ref(v___f_9928_);
                    lean_dec(v_prio_9927_);
                    lean_dec(v___f_9926_);
                    v_a_9935_ = lean_ctor_get(v_x_9933_, 0);
                    v_isSharedCheck_9943_ = (!lean_is_exclusive(v_x_9933_)) as u8;
                    if v_isSharedCheck_9943_ == 0 {
                        v___x_9937_ = v_x_9933_;
                        v_isShared_9938_ = v_isSharedCheck_9943_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_9935_);
                        lean_dec(v_x_9933_);
                        v___x_9937_ = lean_box(0);
                        v_isShared_9938_ = v_isSharedCheck_9943_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_9944_ = lean_ctor_get(v_x_9933_, 0);
                    lean_inc_n(v_a_9944_, 2);
                    lean_dec_ref_known(v_x_9933_, 1);
                    v___f_9945_ = lean_alloc_closure(
                        l_Std_Async_EAsync_race___redArg___lam__3___boxed as *mut core::ffi::c_void,
                        3,
                        1,
                    );
                    lean_closure_set(v___f_9945_, 0, v_a_9944_);
                    v___f_9946_ = lean_alloc_closure(
                        l_Std_Async_EAsync_raceAll___redArg___lam__4___boxed
                            as *mut core::ffi::c_void,
                        4,
                        2,
                    );
                    lean_closure_set(v___f_9946_, 0, v___f_9926_);
                    lean_closure_set(v___f_9946_, 1, v___f_9945_);
                    v___f_9947_ = lean_alloc_closure(
                        l_Std_Async_EAsync_raceAll___redArg___lam__0___boxed
                            as *mut core::ffi::c_void,
                        5,
                        3,
                    );
                    lean_closure_set(v___f_9947_, 0, v_prio_9927_);
                    lean_closure_set(v___f_9947_, 1, v___f_9928_);
                    lean_closure_set(v___f_9947_, 2, v___f_9946_);
                    v___x_9948_ = lean_apply_3(v_inst_9929_, v_xs_9930_, v___f_9947_, lean_box(0));
                    v___f_9949_ = lean_alloc_closure(
                        l_Std_Async_EAsync_race___redArg___lam__2___boxed as *mut core::ffi::c_void,
                        5,
                        3,
                    );
                    lean_closure_set(v___f_9949_, 0, v_a_9944_);
                    lean_closure_set(v___f_9949_, 1, v___f_9931_);
                    lean_closure_set(v___f_9949_, 2, v___f_9932_);
                    v___x_9950_ = lean_unsigned_to_nat(0);
                    v___x_9951_ = 0;
                    v___x_9952_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_9950_, v___x_9951_, v___x_9948_, v___f_9949_);
                    return v___x_9952_;
                }
            }
            1 => {
                if v_isShared_9938_ == 0 {
                    v___x_9940_ = v___x_9937_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_9942_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9942_, 0, v_a_9935_);
                    v___x_9940_ = v_reuseFailAlloc_9942_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_9941_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_9941_, 0, v___x_9940_);
                return v___x_9941_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_EAsync_raceAll___redArg___lam__2___boxed(
    mut v___f_9953_: *mut LeanObject,
    mut v_prio_9954_: *mut LeanObject,
    mut v___f_9955_: *mut LeanObject,
    mut v_inst_9956_: *mut LeanObject,
    mut v_xs_9957_: *mut LeanObject,
    mut v___f_9958_: *mut LeanObject,
    mut v___f_9959_: *mut LeanObject,
    mut v_x_9960_: *mut LeanObject,
    mut v___y_9961_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9962_: *mut LeanObject = core::ptr::null_mut();
    v_res_9962_ = l_Std_Async_EAsync_raceAll___redArg___lam__2(
        v___f_9953_,
        v_prio_9954_,
        v___f_9955_,
        v_inst_9956_,
        v_xs_9957_,
        v___f_9958_,
        v___f_9959_,
        v_x_9960_,
    );
    return v_res_9962_;
}
pub unsafe fn l_Std_Async_EAsync_raceAll___redArg(
    mut v_inst_9963_: *mut LeanObject,
    mut v_xs_9964_: *mut LeanObject,
    mut v_prio_9965_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9976_: u8 = 0;
    let mut v___x_9977_: *mut LeanObject = core::ptr::null_mut();
    v___x_9967_ = lean_io_promise_new();
    v___f_9968_ = l_Std_Async_EAsync_race___redArg___closed__1;
    v___f_9969_ = l_Std_Async_EAsync_race___redArg___closed__0;
    v___f_9970_ = l_Std_Async_EAsync_asTask___redArg___closed__0;
    v___f_9971_ = l_Std_Async_BaseAsync_race___redArg___closed__0;
    v___f_9972_ = lean_alloc_closure(
        l_Std_Async_EAsync_raceAll___redArg___lam__2___boxed as *mut core::ffi::c_void,
        9,
        7,
    );
    lean_closure_set(v___f_9972_, 0, v___f_9971_);
    lean_closure_set(v___f_9972_, 1, v_prio_9965_);
    lean_closure_set(v___f_9972_, 2, v___f_9970_);
    lean_closure_set(v___f_9972_, 3, v_inst_9963_);
    lean_closure_set(v___f_9972_, 4, v_xs_9964_);
    lean_closure_set(v___f_9972_, 5, v___f_9968_);
    lean_closure_set(v___f_9972_, 6, v___f_9969_);
    v___x_9973_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_9973_, 0, v___x_9967_);
    v___x_9974_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_9974_, 0, v___x_9973_);
    v___x_9975_ = lean_unsigned_to_nat(0);
    v___x_9976_ = 0;
    v___x_9977_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(
        v___x_9975_,
        v___x_9976_,
        v___x_9974_,
        v___f_9972_,
    );
    return v___x_9977_;
}
pub unsafe fn l_Std_Async_EAsync_raceAll___redArg___boxed(
    mut v_inst_9978_: *mut LeanObject,
    mut v_xs_9979_: *mut LeanObject,
    mut v_prio_9980_: *mut LeanObject,
    mut v_a_9981_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9982_: *mut LeanObject = core::ptr::null_mut();
    v_res_9982_ = l_Std_Async_EAsync_raceAll___redArg(v_inst_9978_, v_xs_9979_, v_prio_9980_);
    return v_res_9982_;
}
pub unsafe fn l_Std_Async_EAsync_raceAll(
    mut v_00_u03b1_9983_: *mut LeanObject,
    mut v_00_u03b5_9984_: *mut LeanObject,
    mut v_c_9985_: *mut LeanObject,
    mut v_inst_9986_: *mut LeanObject,
    mut v_inst_9987_: *mut LeanObject,
    mut v_xs_9988_: *mut LeanObject,
    mut v_prio_9989_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10000_: u8 = 0;
    let mut v___x_10001_: *mut LeanObject = core::ptr::null_mut();
    v___x_9991_ = lean_io_promise_new();
    v___f_9992_ = l_Std_Async_EAsync_race___redArg___closed__1;
    v___f_9993_ = l_Std_Async_EAsync_race___redArg___closed__0;
    v___f_9994_ = l_Std_Async_EAsync_asTask___redArg___closed__0;
    v___f_9995_ = l_Std_Async_BaseAsync_race___redArg___closed__0;
    v___f_9996_ = lean_alloc_closure(
        l_Std_Async_EAsync_raceAll___redArg___lam__2___boxed as *mut core::ffi::c_void,
        9,
        7,
    );
    lean_closure_set(v___f_9996_, 0, v___f_9995_);
    lean_closure_set(v___f_9996_, 1, v_prio_9989_);
    lean_closure_set(v___f_9996_, 2, v___f_9994_);
    lean_closure_set(v___f_9996_, 3, v_inst_9987_);
    lean_closure_set(v___f_9996_, 4, v_xs_9988_);
    lean_closure_set(v___f_9996_, 5, v___f_9992_);
    lean_closure_set(v___f_9996_, 6, v___f_9993_);
    v___x_9997_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_9997_, 0, v___x_9991_);
    v___x_9998_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_9998_, 0, v___x_9997_);
    v___x_9999_ = lean_unsigned_to_nat(0);
    v___x_10000_ = 0;
    v___x_10001_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(
        v___x_9999_,
        v___x_10000_,
        v___x_9998_,
        v___f_9996_,
    );
    return v___x_10001_;
}
pub unsafe fn l_Std_Async_EAsync_raceAll___boxed(
    mut v_00_u03b1_10002_: *mut LeanObject,
    mut v_00_u03b5_10003_: *mut LeanObject,
    mut v_c_10004_: *mut LeanObject,
    mut v_inst_10005_: *mut LeanObject,
    mut v_inst_10006_: *mut LeanObject,
    mut v_xs_10007_: *mut LeanObject,
    mut v_prio_10008_: *mut LeanObject,
    mut v_a_10009_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10010_: *mut LeanObject = core::ptr::null_mut();
    v_res_10010_ = l_Std_Async_EAsync_raceAll(
        v_00_u03b1_10002_,
        v_00_u03b5_10003_,
        v_c_10004_,
        v_inst_10005_,
        v_inst_10006_,
        v_xs_10007_,
        v_prio_10008_,
    );
    lean_dec(v_inst_10005_);
    return v_res_10010_;
}
pub unsafe fn l_Std_Async_Async_toIO___redArg(mut v_x_10011_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_10013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_10014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10017_: u8 = 0;
    let mut v___x_10018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10022_: u8 = 0;
    let mut v_a_10023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10026_: u8 = 0;
    let mut v___x_10028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10030_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_10013_ = lean_apply_1(v_x_10011_, lean_box(0));
                if lean_obj_tag(v___x_10013_) == 0 {
                    v_a_10014_ = lean_ctor_get(v___x_10013_, 0);
                    v_isSharedCheck_10022_ = (!lean_is_exclusive(v___x_10013_)) as u8;
                    if v_isSharedCheck_10022_ == 0 {
                        v___x_10016_ = v___x_10013_;
                        v_isShared_10017_ = v_isSharedCheck_10022_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_10014_);
                        lean_dec(v___x_10013_);
                        v___x_10016_ = lean_box(0);
                        v_isShared_10017_ = v_isSharedCheck_10022_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_10023_ = lean_ctor_get(v___x_10013_, 0);
                    v_isSharedCheck_10030_ = (!lean_is_exclusive(v___x_10013_)) as u8;
                    if v_isSharedCheck_10030_ == 0 {
                        v___x_10025_ = v___x_10013_;
                        v_isShared_10026_ = v_isSharedCheck_10030_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_10023_);
                        lean_dec(v___x_10013_);
                        v___x_10025_ = lean_box(0);
                        v_isShared_10026_ = v_isSharedCheck_10030_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_10018_ = lean_task_pure(v_a_10014_);
                if v_isShared_10017_ == 0 {
                    lean_ctor_set(v___x_10016_, 0, v___x_10018_);
                    v___x_10020_ = v___x_10016_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_10021_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10021_, 0, v___x_10018_);
                    v___x_10020_ = v_reuseFailAlloc_10021_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_10020_;
            }
            3 => {
                if v_isShared_10026_ == 0 {
                    lean_ctor_set_tag(v___x_10025_, 0);
                    v___x_10028_ = v___x_10025_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_10029_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10029_, 0, v_a_10023_);
                    v___x_10028_ = v_reuseFailAlloc_10029_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_10028_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Async_toIO___redArg___boxed(
    mut v_x_10031_: *mut LeanObject,
    mut v_a_10032_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10033_: *mut LeanObject = core::ptr::null_mut();
    v_res_10033_ = l_Std_Async_Async_toIO___redArg(v_x_10031_);
    return v_res_10033_;
}
pub unsafe fn l_Std_Async_Async_toIO(
    mut v_00_u03b1_10034_: *mut LeanObject,
    mut v_x_10035_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_10038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10041_: u8 = 0;
    let mut v___x_10042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10046_: u8 = 0;
    let mut v_a_10047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10050_: u8 = 0;
    let mut v___x_10052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10054_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_10037_ = lean_apply_1(v_x_10035_, lean_box(0));
                if lean_obj_tag(v___x_10037_) == 0 {
                    v_a_10038_ = lean_ctor_get(v___x_10037_, 0);
                    v_isSharedCheck_10046_ = (!lean_is_exclusive(v___x_10037_)) as u8;
                    if v_isSharedCheck_10046_ == 0 {
                        v___x_10040_ = v___x_10037_;
                        v_isShared_10041_ = v_isSharedCheck_10046_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_10038_);
                        lean_dec(v___x_10037_);
                        v___x_10040_ = lean_box(0);
                        v_isShared_10041_ = v_isSharedCheck_10046_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_10047_ = lean_ctor_get(v___x_10037_, 0);
                    v_isSharedCheck_10054_ = (!lean_is_exclusive(v___x_10037_)) as u8;
                    if v_isSharedCheck_10054_ == 0 {
                        v___x_10049_ = v___x_10037_;
                        v_isShared_10050_ = v_isSharedCheck_10054_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_10047_);
                        lean_dec(v___x_10037_);
                        v___x_10049_ = lean_box(0);
                        v_isShared_10050_ = v_isSharedCheck_10054_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_10042_ = lean_task_pure(v_a_10038_);
                if v_isShared_10041_ == 0 {
                    lean_ctor_set(v___x_10040_, 0, v___x_10042_);
                    v___x_10044_ = v___x_10040_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_10045_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10045_, 0, v___x_10042_);
                    v___x_10044_ = v_reuseFailAlloc_10045_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_10044_;
            }
            3 => {
                if v_isShared_10050_ == 0 {
                    lean_ctor_set_tag(v___x_10049_, 0);
                    v___x_10052_ = v___x_10049_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_10053_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10053_, 0, v_a_10047_);
                    v___x_10052_ = v_reuseFailAlloc_10053_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_10052_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Async_toIO___boxed(
    mut v_00_u03b1_10055_: *mut LeanObject,
    mut v_x_10056_: *mut LeanObject,
    mut v_a_10057_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10058_: *mut LeanObject = core::ptr::null_mut();
    v_res_10058_ = l_Std_Async_Async_toIO(v_00_u03b1_10055_, v_x_10056_);
    return v_res_10058_;
}
pub unsafe fn l_Std_Async_Async_block___redArg(
    mut v_x_10059_: *mut LeanObject,
    mut v_prio_10060_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_10064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10066_: u8 = 0;
    let mut v___x_10067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_10069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10072_: u8 = 0;
    let mut v___x_10074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10076_: u8 = 0;
    let mut v_a_10077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10080_: u8 = 0;
    let mut v___x_10082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10084_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_10062_ = lean_alloc_closure(
                    l_Std_Async_BaseAsync_toRawBaseIO___boxed as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___x_10062_, 0, lean_box(0));
                lean_closure_set(v___x_10062_, 1, v_x_10059_);
                v___x_10063_ = lean_io_as_task(v___x_10062_, v_prio_10060_);
                v___f_10064_ = l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___closed__0;
                v___x_10065_ = lean_unsigned_to_nat(0);
                v___x_10066_ = 1;
                v___x_10067_ =
                    lean_task_bind(v___x_10063_, v___f_10064_, v___x_10065_, v___x_10066_);
                v___x_10068_ = lean_task_get_own(v___x_10067_);
                if lean_obj_tag(v___x_10068_) == 0 {
                    v_a_10069_ = lean_ctor_get(v___x_10068_, 0);
                    v_isSharedCheck_10076_ = (!lean_is_exclusive(v___x_10068_)) as u8;
                    if v_isSharedCheck_10076_ == 0 {
                        v___x_10071_ = v___x_10068_;
                        v_isShared_10072_ = v_isSharedCheck_10076_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_10069_);
                        lean_dec(v___x_10068_);
                        v___x_10071_ = lean_box(0);
                        v_isShared_10072_ = v_isSharedCheck_10076_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_10077_ = lean_ctor_get(v___x_10068_, 0);
                    v_isSharedCheck_10084_ = (!lean_is_exclusive(v___x_10068_)) as u8;
                    if v_isSharedCheck_10084_ == 0 {
                        v___x_10079_ = v___x_10068_;
                        v_isShared_10080_ = v_isSharedCheck_10084_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_10077_);
                        lean_dec(v___x_10068_);
                        v___x_10079_ = lean_box(0);
                        v_isShared_10080_ = v_isSharedCheck_10084_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_10072_ == 0 {
                    lean_ctor_set_tag(v___x_10071_, 1);
                    v___x_10074_ = v___x_10071_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_10075_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10075_, 0, v_a_10069_);
                    v___x_10074_ = v_reuseFailAlloc_10075_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_10074_;
            }
            3 => {
                if v_isShared_10080_ == 0 {
                    lean_ctor_set_tag(v___x_10079_, 0);
                    v___x_10082_ = v___x_10079_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_10083_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10083_, 0, v_a_10077_);
                    v___x_10082_ = v_reuseFailAlloc_10083_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_10082_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Async_block___redArg___boxed(
    mut v_x_10085_: *mut LeanObject,
    mut v_prio_10086_: *mut LeanObject,
    mut v_a_10087_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10088_: *mut LeanObject = core::ptr::null_mut();
    v_res_10088_ = l_Std_Async_Async_block___redArg(v_x_10085_, v_prio_10086_);
    return v_res_10088_;
}
pub unsafe fn l_Std_Async_Async_block(
    mut v_00_u03b1_10089_: *mut LeanObject,
    mut v_x_10090_: *mut LeanObject,
    mut v_prio_10091_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_10095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10097_: u8 = 0;
    let mut v___x_10098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_10100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10103_: u8 = 0;
    let mut v___x_10105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10107_: u8 = 0;
    let mut v_a_10108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10111_: u8 = 0;
    let mut v___x_10113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10115_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_10093_ = lean_alloc_closure(
                    l_Std_Async_BaseAsync_toRawBaseIO___boxed as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___x_10093_, 0, lean_box(0));
                lean_closure_set(v___x_10093_, 1, v_x_10090_);
                v___x_10094_ = lean_io_as_task(v___x_10093_, v_prio_10091_);
                v___f_10095_ = l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___closed__0;
                v___x_10096_ = lean_unsigned_to_nat(0);
                v___x_10097_ = 1;
                v___x_10098_ =
                    lean_task_bind(v___x_10094_, v___f_10095_, v___x_10096_, v___x_10097_);
                v___x_10099_ = lean_task_get_own(v___x_10098_);
                if lean_obj_tag(v___x_10099_) == 0 {
                    v_a_10100_ = lean_ctor_get(v___x_10099_, 0);
                    v_isSharedCheck_10107_ = (!lean_is_exclusive(v___x_10099_)) as u8;
                    if v_isSharedCheck_10107_ == 0 {
                        v___x_10102_ = v___x_10099_;
                        v_isShared_10103_ = v_isSharedCheck_10107_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_10100_);
                        lean_dec(v___x_10099_);
                        v___x_10102_ = lean_box(0);
                        v_isShared_10103_ = v_isSharedCheck_10107_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_10108_ = lean_ctor_get(v___x_10099_, 0);
                    v_isSharedCheck_10115_ = (!lean_is_exclusive(v___x_10099_)) as u8;
                    if v_isSharedCheck_10115_ == 0 {
                        v___x_10110_ = v___x_10099_;
                        v_isShared_10111_ = v_isSharedCheck_10115_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_10108_);
                        lean_dec(v___x_10099_);
                        v___x_10110_ = lean_box(0);
                        v_isShared_10111_ = v_isSharedCheck_10115_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_10103_ == 0 {
                    lean_ctor_set_tag(v___x_10102_, 1);
                    v___x_10105_ = v___x_10102_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_10106_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10106_, 0, v_a_10100_);
                    v___x_10105_ = v_reuseFailAlloc_10106_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_10105_;
            }
            3 => {
                if v_isShared_10111_ == 0 {
                    lean_ctor_set_tag(v___x_10110_, 0);
                    v___x_10113_ = v___x_10110_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_10114_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10114_, 0, v_a_10108_);
                    v___x_10113_ = v_reuseFailAlloc_10114_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_10113_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Async_block___boxed(
    mut v_00_u03b1_10116_: *mut LeanObject,
    mut v_x_10117_: *mut LeanObject,
    mut v_prio_10118_: *mut LeanObject,
    mut v_a_10119_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10120_: *mut LeanObject = core::ptr::null_mut();
    v_res_10120_ = l_Std_Async_Async_block(v_00_u03b1_10116_, v_x_10117_, v_prio_10118_);
    return v_res_10120_;
}
pub unsafe fn l_Std_Async_Async_ofPromise___redArg___lam__1(
    mut v___f_10121_: *mut LeanObject,
    mut v_x_10122_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_10124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10127_: u8 = 0;
    let mut v___x_10129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10132_: u8 = 0;
    let mut v_a_10133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_10134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10137_: u8 = 0;
    let mut v___x_10139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10142_: u8 = 0;
    let mut v_a_10143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10146_: u8 = 0;
    let mut v___x_10147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10148_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_10122_) == 0 {
                    lean_dec_ref(v___f_10121_);
                    v_a_10124_ = lean_ctor_get(v_x_10122_, 0);
                    v_isSharedCheck_10132_ = (!lean_is_exclusive(v_x_10122_)) as u8;
                    if v_isSharedCheck_10132_ == 0 {
                        v___x_10126_ = v_x_10122_;
                        v_isShared_10127_ = v_isSharedCheck_10132_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_10124_);
                        lean_dec(v_x_10122_);
                        v___x_10126_ = lean_box(0);
                        v_isShared_10127_ = v_isSharedCheck_10132_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_10133_ = lean_ctor_get(v_x_10122_, 0);
                    lean_inc(v_a_10133_);
                    lean_dec_ref_known(v_x_10122_, 1);
                    if lean_obj_tag(v_a_10133_) == 0 {
                        lean_dec_ref(v___f_10121_);
                        v_a_10134_ = lean_ctor_get(v_a_10133_, 0);
                        v_isSharedCheck_10142_ = (!lean_is_exclusive(v_a_10133_)) as u8;
                        if v_isSharedCheck_10142_ == 0 {
                            v___x_10136_ = v_a_10133_;
                            v_isShared_10137_ = v_isSharedCheck_10142_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_10134_);
                            lean_dec(v_a_10133_);
                            v___x_10136_ = lean_box(0);
                            v_isShared_10137_ = v_isSharedCheck_10142_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_10143_ = lean_ctor_get(v_a_10133_, 0);
                        lean_inc(v_a_10143_);
                        lean_dec_ref_known(v_a_10133_, 1);
                        v___x_10144_ = lean_io_promise_result_opt(v_a_10143_);
                        lean_dec(v_a_10143_);
                        v___x_10145_ = lean_unsigned_to_nat(0);
                        v___x_10146_ = 0;
                        v___x_10147_ =
                            lean_task_map(v___f_10121_, v___x_10144_, v___x_10145_, v___x_10146_);
                        v___x_10148_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_10148_, 0, v___x_10147_);
                        return v___x_10148_;
                    }
                }
            }
            1 => {
                if v_isShared_10127_ == 0 {
                    v___x_10129_ = v___x_10126_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_10131_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10131_, 0, v_a_10124_);
                    v___x_10129_ = v_reuseFailAlloc_10131_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_10130_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_10130_, 0, v___x_10129_);
                return v___x_10130_;
            }
            3 => {
                if v_isShared_10137_ == 0 {
                    v___x_10139_ = v___x_10136_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_10141_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10141_, 0, v_a_10134_);
                    v___x_10139_ = v_reuseFailAlloc_10141_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_10140_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_10140_, 0, v___x_10139_);
                return v___x_10140_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Async_ofPromise___redArg___lam__1___boxed(
    mut v___f_10149_: *mut LeanObject,
    mut v_x_10150_: *mut LeanObject,
    mut v___y_10151_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10152_: *mut LeanObject = core::ptr::null_mut();
    v_res_10152_ = l_Std_Async_Async_ofPromise___redArg___lam__1(v___f_10149_, v_x_10150_);
    return v_res_10152_;
}
pub unsafe fn l_Std_Async_Async_ofPromise___redArg(
    mut v_task_10153_: *mut LeanObject,
    mut v_error_10154_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_10156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_10157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_10159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10163_: u8 = 0;
    let mut v___x_10164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_10166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10169_: u8 = 0;
    let mut v___x_10171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10173_: u8 = 0;
    let mut v_a_10174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10177_: u8 = 0;
    let mut v___x_10179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10181_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_10156_ = lean_alloc_closure(
                    l_Std_Async_AsyncTask_ofPromise___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_10156_, 0, v_error_10154_);
                v___f_10157_ = lean_alloc_closure(
                    l_Std_Async_Async_ofPromise___redArg___lam__1___boxed as *mut core::ffi::c_void,
                    3,
                    1,
                );
                lean_closure_set(v___f_10157_, 0, v___f_10156_);
                v___x_10165_ = lean_apply_1(v_task_10153_, lean_box(0));
                if lean_obj_tag(v___x_10165_) == 0 {
                    v_a_10166_ = lean_ctor_get(v___x_10165_, 0);
                    v_isSharedCheck_10173_ = (!lean_is_exclusive(v___x_10165_)) as u8;
                    if v_isSharedCheck_10173_ == 0 {
                        v___x_10168_ = v___x_10165_;
                        v_isShared_10169_ = v_isSharedCheck_10173_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_10166_);
                        lean_dec(v___x_10165_);
                        v___x_10168_ = lean_box(0);
                        v_isShared_10169_ = v_isSharedCheck_10173_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_10174_ = lean_ctor_get(v___x_10165_, 0);
                    v_isSharedCheck_10181_ = (!lean_is_exclusive(v___x_10165_)) as u8;
                    if v_isSharedCheck_10181_ == 0 {
                        v___x_10176_ = v___x_10165_;
                        v_isShared_10177_ = v_isSharedCheck_10181_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_10174_);
                        lean_dec(v___x_10165_);
                        v___x_10176_ = lean_box(0);
                        v_isShared_10177_ = v_isSharedCheck_10181_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_10160_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_10160_, 0, v_val_10159_);
                v___x_10161_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_10161_, 0, v___x_10160_);
                v___x_10162_ = lean_unsigned_to_nat(0);
                v___x_10163_ = 0;
                v___x_10164_ =
                    l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(
                        v___x_10162_,
                        v___x_10163_,
                        v___x_10161_,
                        v___f_10157_,
                    );
                return v___x_10164_;
            }
            2 => {
                if v_isShared_10169_ == 0 {
                    lean_ctor_set_tag(v___x_10168_, 1);
                    v___x_10171_ = v___x_10168_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_10172_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10172_, 0, v_a_10166_);
                    v___x_10171_ = v_reuseFailAlloc_10172_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_val_10159_ = v___x_10171_;
                state = 1;
                continue;
            }
            4 => {
                if v_isShared_10177_ == 0 {
                    lean_ctor_set_tag(v___x_10176_, 0);
                    v___x_10179_ = v___x_10176_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_10180_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10180_, 0, v_a_10174_);
                    v___x_10179_ = v_reuseFailAlloc_10180_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_val_10159_ = v___x_10179_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Async_ofPromise___redArg___boxed(
    mut v_task_10182_: *mut LeanObject,
    mut v_error_10183_: *mut LeanObject,
    mut v_a_10184_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10185_: *mut LeanObject = core::ptr::null_mut();
    v_res_10185_ = l_Std_Async_Async_ofPromise___redArg(v_task_10182_, v_error_10183_);
    return v_res_10185_;
}
pub unsafe fn l_Std_Async_Async_ofPromise(
    mut v_00_u03b1_10186_: *mut LeanObject,
    mut v_task_10187_: *mut LeanObject,
    mut v_error_10188_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_10190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_10191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_10193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10197_: u8 = 0;
    let mut v___x_10198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_10200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10203_: u8 = 0;
    let mut v___x_10205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10207_: u8 = 0;
    let mut v_a_10208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10211_: u8 = 0;
    let mut v___x_10213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10215_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_10190_ = lean_alloc_closure(
                    l_Std_Async_AsyncTask_ofPromise___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_10190_, 0, v_error_10188_);
                v___f_10191_ = lean_alloc_closure(
                    l_Std_Async_Async_ofPromise___redArg___lam__1___boxed as *mut core::ffi::c_void,
                    3,
                    1,
                );
                lean_closure_set(v___f_10191_, 0, v___f_10190_);
                v___x_10199_ = lean_apply_1(v_task_10187_, lean_box(0));
                if lean_obj_tag(v___x_10199_) == 0 {
                    v_a_10200_ = lean_ctor_get(v___x_10199_, 0);
                    v_isSharedCheck_10207_ = (!lean_is_exclusive(v___x_10199_)) as u8;
                    if v_isSharedCheck_10207_ == 0 {
                        v___x_10202_ = v___x_10199_;
                        v_isShared_10203_ = v_isSharedCheck_10207_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_10200_);
                        lean_dec(v___x_10199_);
                        v___x_10202_ = lean_box(0);
                        v_isShared_10203_ = v_isSharedCheck_10207_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_10208_ = lean_ctor_get(v___x_10199_, 0);
                    v_isSharedCheck_10215_ = (!lean_is_exclusive(v___x_10199_)) as u8;
                    if v_isSharedCheck_10215_ == 0 {
                        v___x_10210_ = v___x_10199_;
                        v_isShared_10211_ = v_isSharedCheck_10215_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_10208_);
                        lean_dec(v___x_10199_);
                        v___x_10210_ = lean_box(0);
                        v_isShared_10211_ = v_isSharedCheck_10215_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_10194_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_10194_, 0, v_val_10193_);
                v___x_10195_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_10195_, 0, v___x_10194_);
                v___x_10196_ = lean_unsigned_to_nat(0);
                v___x_10197_ = 0;
                v___x_10198_ =
                    l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(
                        v___x_10196_,
                        v___x_10197_,
                        v___x_10195_,
                        v___f_10191_,
                    );
                return v___x_10198_;
            }
            2 => {
                if v_isShared_10203_ == 0 {
                    lean_ctor_set_tag(v___x_10202_, 1);
                    v___x_10205_ = v___x_10202_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_10206_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10206_, 0, v_a_10200_);
                    v___x_10205_ = v_reuseFailAlloc_10206_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_val_10193_ = v___x_10205_;
                state = 1;
                continue;
            }
            4 => {
                if v_isShared_10211_ == 0 {
                    lean_ctor_set_tag(v___x_10210_, 0);
                    v___x_10213_ = v___x_10210_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_10214_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10214_, 0, v_a_10208_);
                    v___x_10213_ = v_reuseFailAlloc_10214_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_val_10193_ = v___x_10213_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Async_ofPromise___boxed(
    mut v_00_u03b1_10216_: *mut LeanObject,
    mut v_task_10217_: *mut LeanObject,
    mut v_error_10218_: *mut LeanObject,
    mut v_a_10219_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10220_: *mut LeanObject = core::ptr::null_mut();
    v_res_10220_ = l_Std_Async_Async_ofPromise(v_00_u03b1_10216_, v_task_10217_, v_error_10218_);
    return v_res_10220_;
}
pub unsafe fn l_Std_Async_Async_ofAsyncTask___redArg(
    mut v_task_10221_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10223_: *mut LeanObject = core::ptr::null_mut();
    v___x_10223_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_10223_, 0, v_task_10221_);
    return v___x_10223_;
}
pub unsafe fn l_Std_Async_Async_ofAsyncTask___redArg___boxed(
    mut v_task_10224_: *mut LeanObject,
    mut v_a_10225_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10226_: *mut LeanObject = core::ptr::null_mut();
    v_res_10226_ = l_Std_Async_Async_ofAsyncTask___redArg(v_task_10224_);
    return v_res_10226_;
}
pub unsafe fn l_Std_Async_Async_ofAsyncTask(
    mut v_00_u03b1_10227_: *mut LeanObject,
    mut v_task_10228_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10230_: *mut LeanObject = core::ptr::null_mut();
    v___x_10230_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_10230_, 0, v_task_10228_);
    return v___x_10230_;
}
pub unsafe fn l_Std_Async_Async_ofAsyncTask___boxed(
    mut v_00_u03b1_10231_: *mut LeanObject,
    mut v_task_10232_: *mut LeanObject,
    mut v_a_10233_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10234_: *mut LeanObject = core::ptr::null_mut();
    v_res_10234_ = l_Std_Async_Async_ofAsyncTask(v_00_u03b1_10231_, v_task_10232_);
    return v_res_10234_;
}
pub unsafe fn l_Std_Async_Async_ofIOTask___redArg___lam__0(
    mut v_a_10235_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10236_: *mut LeanObject = core::ptr::null_mut();
    v___x_10236_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_10236_, 0, v_a_10235_);
    return v___x_10236_;
}
pub unsafe fn l_Std_Async_Async_ofIOTask___redArg___lam__1(
    mut v___f_10237_: *mut LeanObject,
    mut v_x_10238_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_10240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10243_: u8 = 0;
    let mut v___x_10245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10248_: u8 = 0;
    let mut v_a_10249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_10250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10253_: u8 = 0;
    let mut v___x_10255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10258_: u8 = 0;
    let mut v_a_10259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10261_: u8 = 0;
    let mut v___x_10262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10263_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_10238_) == 0 {
                    lean_dec_ref(v___f_10237_);
                    v_a_10240_ = lean_ctor_get(v_x_10238_, 0);
                    v_isSharedCheck_10248_ = (!lean_is_exclusive(v_x_10238_)) as u8;
                    if v_isSharedCheck_10248_ == 0 {
                        v___x_10242_ = v_x_10238_;
                        v_isShared_10243_ = v_isSharedCheck_10248_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_10240_);
                        lean_dec(v_x_10238_);
                        v___x_10242_ = lean_box(0);
                        v_isShared_10243_ = v_isSharedCheck_10248_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_10249_ = lean_ctor_get(v_x_10238_, 0);
                    lean_inc(v_a_10249_);
                    lean_dec_ref_known(v_x_10238_, 1);
                    if lean_obj_tag(v_a_10249_) == 0 {
                        lean_dec_ref(v___f_10237_);
                        v_a_10250_ = lean_ctor_get(v_a_10249_, 0);
                        v_isSharedCheck_10258_ = (!lean_is_exclusive(v_a_10249_)) as u8;
                        if v_isSharedCheck_10258_ == 0 {
                            v___x_10252_ = v_a_10249_;
                            v_isShared_10253_ = v_isSharedCheck_10258_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_10250_);
                            lean_dec(v_a_10249_);
                            v___x_10252_ = lean_box(0);
                            v_isShared_10253_ = v_isSharedCheck_10258_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_10259_ = lean_ctor_get(v_a_10249_, 0);
                        lean_inc(v_a_10259_);
                        lean_dec_ref_known(v_a_10249_, 1);
                        v___x_10260_ = lean_unsigned_to_nat(0);
                        v___x_10261_ = 0;
                        v___x_10262_ =
                            lean_task_map(v___f_10237_, v_a_10259_, v___x_10260_, v___x_10261_);
                        v___x_10263_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_10263_, 0, v___x_10262_);
                        return v___x_10263_;
                    }
                }
            }
            1 => {
                if v_isShared_10243_ == 0 {
                    v___x_10245_ = v___x_10242_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_10247_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10247_, 0, v_a_10240_);
                    v___x_10245_ = v_reuseFailAlloc_10247_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_10246_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_10246_, 0, v___x_10245_);
                return v___x_10246_;
            }
            3 => {
                if v_isShared_10253_ == 0 {
                    v___x_10255_ = v___x_10252_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_10257_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10257_, 0, v_a_10250_);
                    v___x_10255_ = v_reuseFailAlloc_10257_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_10256_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_10256_, 0, v___x_10255_);
                return v___x_10256_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Async_ofIOTask___redArg___lam__1___boxed(
    mut v___f_10264_: *mut LeanObject,
    mut v_x_10265_: *mut LeanObject,
    mut v___y_10266_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10267_: *mut LeanObject = core::ptr::null_mut();
    v_res_10267_ = l_Std_Async_Async_ofIOTask___redArg___lam__1(v___f_10264_, v_x_10265_);
    return v_res_10267_;
}
pub unsafe fn l_Std_Async_Async_ofIOTask___redArg(
    mut v_task_10271_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_10273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_10275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10279_: u8 = 0;
    let mut v___x_10280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_10282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10285_: u8 = 0;
    let mut v___x_10287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10289_: u8 = 0;
    let mut v_a_10290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10293_: u8 = 0;
    let mut v___x_10295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10297_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_10273_ = l_Std_Async_Async_ofIOTask___redArg___closed__1;
                v___x_10281_ = lean_apply_1(v_task_10271_, lean_box(0));
                if lean_obj_tag(v___x_10281_) == 0 {
                    v_a_10282_ = lean_ctor_get(v___x_10281_, 0);
                    v_isSharedCheck_10289_ = (!lean_is_exclusive(v___x_10281_)) as u8;
                    if v_isSharedCheck_10289_ == 0 {
                        v___x_10284_ = v___x_10281_;
                        v_isShared_10285_ = v_isSharedCheck_10289_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_10282_);
                        lean_dec(v___x_10281_);
                        v___x_10284_ = lean_box(0);
                        v_isShared_10285_ = v_isSharedCheck_10289_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_10290_ = lean_ctor_get(v___x_10281_, 0);
                    v_isSharedCheck_10297_ = (!lean_is_exclusive(v___x_10281_)) as u8;
                    if v_isSharedCheck_10297_ == 0 {
                        v___x_10292_ = v___x_10281_;
                        v_isShared_10293_ = v_isSharedCheck_10297_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_10290_);
                        lean_dec(v___x_10281_);
                        v___x_10292_ = lean_box(0);
                        v_isShared_10293_ = v_isSharedCheck_10297_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_10276_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_10276_, 0, v_val_10275_);
                v___x_10277_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_10277_, 0, v___x_10276_);
                v___x_10278_ = lean_unsigned_to_nat(0);
                v___x_10279_ = 0;
                v___x_10280_ =
                    l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(
                        v___x_10278_,
                        v___x_10279_,
                        v___x_10277_,
                        v___f_10273_,
                    );
                return v___x_10280_;
            }
            2 => {
                if v_isShared_10285_ == 0 {
                    lean_ctor_set_tag(v___x_10284_, 1);
                    v___x_10287_ = v___x_10284_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_10288_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10288_, 0, v_a_10282_);
                    v___x_10287_ = v_reuseFailAlloc_10288_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_val_10275_ = v___x_10287_;
                state = 1;
                continue;
            }
            4 => {
                if v_isShared_10293_ == 0 {
                    lean_ctor_set_tag(v___x_10292_, 0);
                    v___x_10295_ = v___x_10292_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_10296_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10296_, 0, v_a_10290_);
                    v___x_10295_ = v_reuseFailAlloc_10296_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_val_10275_ = v___x_10295_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Async_ofIOTask___redArg___boxed(
    mut v_task_10298_: *mut LeanObject,
    mut v_a_10299_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10300_: *mut LeanObject = core::ptr::null_mut();
    v_res_10300_ = l_Std_Async_Async_ofIOTask___redArg(v_task_10298_);
    return v_res_10300_;
}
pub unsafe fn l_Std_Async_Async_ofIOTask(
    mut v_00_u03b1_10301_: *mut LeanObject,
    mut v_task_10302_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_10304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_10306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10310_: u8 = 0;
    let mut v___x_10311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_10313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10316_: u8 = 0;
    let mut v___x_10318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10320_: u8 = 0;
    let mut v_a_10321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10324_: u8 = 0;
    let mut v___x_10326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10328_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_10304_ = l_Std_Async_Async_ofIOTask___redArg___closed__1;
                v___x_10312_ = lean_apply_1(v_task_10302_, lean_box(0));
                if lean_obj_tag(v___x_10312_) == 0 {
                    v_a_10313_ = lean_ctor_get(v___x_10312_, 0);
                    v_isSharedCheck_10320_ = (!lean_is_exclusive(v___x_10312_)) as u8;
                    if v_isSharedCheck_10320_ == 0 {
                        v___x_10315_ = v___x_10312_;
                        v_isShared_10316_ = v_isSharedCheck_10320_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_10313_);
                        lean_dec(v___x_10312_);
                        v___x_10315_ = lean_box(0);
                        v_isShared_10316_ = v_isSharedCheck_10320_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_10321_ = lean_ctor_get(v___x_10312_, 0);
                    v_isSharedCheck_10328_ = (!lean_is_exclusive(v___x_10312_)) as u8;
                    if v_isSharedCheck_10328_ == 0 {
                        v___x_10323_ = v___x_10312_;
                        v_isShared_10324_ = v_isSharedCheck_10328_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_10321_);
                        lean_dec(v___x_10312_);
                        v___x_10323_ = lean_box(0);
                        v_isShared_10324_ = v_isSharedCheck_10328_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_10307_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_10307_, 0, v_val_10306_);
                v___x_10308_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_10308_, 0, v___x_10307_);
                v___x_10309_ = lean_unsigned_to_nat(0);
                v___x_10310_ = 0;
                v___x_10311_ =
                    l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(
                        v___x_10309_,
                        v___x_10310_,
                        v___x_10308_,
                        v___f_10304_,
                    );
                return v___x_10311_;
            }
            2 => {
                if v_isShared_10316_ == 0 {
                    lean_ctor_set_tag(v___x_10315_, 1);
                    v___x_10318_ = v___x_10315_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_10319_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10319_, 0, v_a_10313_);
                    v___x_10318_ = v_reuseFailAlloc_10319_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_val_10306_ = v___x_10318_;
                state = 1;
                continue;
            }
            4 => {
                if v_isShared_10324_ == 0 {
                    lean_ctor_set_tag(v___x_10323_, 0);
                    v___x_10326_ = v___x_10323_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_10327_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10327_, 0, v_a_10321_);
                    v___x_10326_ = v_reuseFailAlloc_10327_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_val_10306_ = v___x_10326_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Async_ofIOTask___boxed(
    mut v_00_u03b1_10329_: *mut LeanObject,
    mut v_task_10330_: *mut LeanObject,
    mut v_a_10331_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10332_: *mut LeanObject = core::ptr::null_mut();
    v_res_10332_ = l_Std_Async_Async_ofIOTask(v_00_u03b1_10329_, v_task_10330_);
    return v_res_10332_;
}
pub unsafe fn l_Std_Async_Async_ofExcept___redArg(
    mut v_except_10333_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10335_: *mut LeanObject = core::ptr::null_mut();
    v___x_10335_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_10335_, 0, v_except_10333_);
    return v___x_10335_;
}
pub unsafe fn l_Std_Async_Async_ofExcept___redArg___boxed(
    mut v_except_10336_: *mut LeanObject,
    mut v_a_10337_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10338_: *mut LeanObject = core::ptr::null_mut();
    v_res_10338_ = l_Std_Async_Async_ofExcept___redArg(v_except_10336_);
    return v_res_10338_;
}
pub unsafe fn l_Std_Async_Async_ofExcept(
    mut v_00_u03b1_10339_: *mut LeanObject,
    mut v_except_10340_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10342_: *mut LeanObject = core::ptr::null_mut();
    v___x_10342_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_10342_, 0, v_except_10340_);
    return v___x_10342_;
}
pub unsafe fn l_Std_Async_Async_ofExcept___boxed(
    mut v_00_u03b1_10343_: *mut LeanObject,
    mut v_except_10344_: *mut LeanObject,
    mut v_a_10345_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10346_: *mut LeanObject = core::ptr::null_mut();
    v_res_10346_ = l_Std_Async_Async_ofExcept(v_00_u03b1_10343_, v_except_10344_);
    return v_res_10346_;
}
pub unsafe fn l_Std_Async_Async_ofTask___redArg(
    mut v_task_10347_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_10349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10351_: u8 = 0;
    let mut v___x_10352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10353_: *mut LeanObject = core::ptr::null_mut();
    v___f_10349_ = l_Std_Async_Async_ofIOTask___redArg___closed__0;
    v___x_10350_ = lean_unsigned_to_nat(0);
    v___x_10351_ = 0;
    v___x_10352_ = lean_task_map(v___f_10349_, v_task_10347_, v___x_10350_, v___x_10351_);
    v___x_10353_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_10353_, 0, v___x_10352_);
    return v___x_10353_;
}
pub unsafe fn l_Std_Async_Async_ofTask___redArg___boxed(
    mut v_task_10354_: *mut LeanObject,
    mut v_a_10355_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10356_: *mut LeanObject = core::ptr::null_mut();
    v_res_10356_ = l_Std_Async_Async_ofTask___redArg(v_task_10354_);
    return v_res_10356_;
}
pub unsafe fn l_Std_Async_Async_ofTask(
    mut v_00_u03b1_10357_: *mut LeanObject,
    mut v_task_10358_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_10360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10362_: u8 = 0;
    let mut v___x_10363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10364_: *mut LeanObject = core::ptr::null_mut();
    v___f_10360_ = l_Std_Async_Async_ofIOTask___redArg___closed__0;
    v___x_10361_ = lean_unsigned_to_nat(0);
    v___x_10362_ = 0;
    v___x_10363_ = lean_task_map(v___f_10360_, v_task_10358_, v___x_10361_, v___x_10362_);
    v___x_10364_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_10364_, 0, v___x_10363_);
    return v___x_10364_;
}
pub unsafe fn l_Std_Async_Async_ofTask___boxed(
    mut v_00_u03b1_10365_: *mut LeanObject,
    mut v_task_10366_: *mut LeanObject,
    mut v_a_10367_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10368_: *mut LeanObject = core::ptr::null_mut();
    v_res_10368_ = l_Std_Async_Async_ofTask(v_00_u03b1_10365_, v_task_10366_);
    return v_res_10368_;
}
pub unsafe fn l_Std_Async_Async_ofPurePromise___redArg(
    mut v_task_10369_: *mut LeanObject,
    mut v_error_10370_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_10373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10376_: u8 = 0;
    let mut v___f_10377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10380_: u8 = 0;
    let mut v___x_10381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10385_: u8 = 0;
    let mut v_a_10386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10389_: u8 = 0;
    let mut v___x_10391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10394_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_10372_ = lean_apply_1(v_task_10369_, lean_box(0));
                if lean_obj_tag(v___x_10372_) == 0 {
                    v_a_10373_ = lean_ctor_get(v___x_10372_, 0);
                    v_isSharedCheck_10385_ = (!lean_is_exclusive(v___x_10372_)) as u8;
                    if v_isSharedCheck_10385_ == 0 {
                        v___x_10375_ = v___x_10372_;
                        v_isShared_10376_ = v_isSharedCheck_10385_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_10373_);
                        lean_dec(v___x_10372_);
                        v___x_10375_ = lean_box(0);
                        v_isShared_10376_ = v_isSharedCheck_10385_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_error_10370_);
                    v_a_10386_ = lean_ctor_get(v___x_10372_, 0);
                    v_isSharedCheck_10394_ = (!lean_is_exclusive(v___x_10372_)) as u8;
                    if v_isSharedCheck_10394_ == 0 {
                        v___x_10388_ = v___x_10372_;
                        v_isShared_10389_ = v_isSharedCheck_10394_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_10386_);
                        lean_dec(v___x_10372_);
                        v___x_10388_ = lean_box(0);
                        v_isShared_10389_ = v_isSharedCheck_10394_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___f_10377_ = lean_alloc_closure(
                    l_Std_Async_AsyncTask_ofPurePromise___redArg___lam__0 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_10377_, 0, v_error_10370_);
                v___x_10378_ = lean_io_promise_result_opt(v_a_10373_);
                lean_dec(v_a_10373_);
                v___x_10379_ = lean_unsigned_to_nat(0);
                v___x_10380_ = 0;
                v___x_10381_ =
                    lean_task_map(v___f_10377_, v___x_10378_, v___x_10379_, v___x_10380_);
                if v_isShared_10376_ == 0 {
                    lean_ctor_set_tag(v___x_10375_, 1);
                    lean_ctor_set(v___x_10375_, 0, v___x_10381_);
                    v___x_10383_ = v___x_10375_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_10384_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10384_, 0, v___x_10381_);
                    v___x_10383_ = v_reuseFailAlloc_10384_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_10383_;
            }
            3 => {
                if v_isShared_10389_ == 0 {
                    lean_ctor_set_tag(v___x_10388_, 0);
                    v___x_10391_ = v___x_10388_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_10393_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10393_, 0, v_a_10386_);
                    v___x_10391_ = v_reuseFailAlloc_10393_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_10392_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_10392_, 0, v___x_10391_);
                return v___x_10392_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Async_ofPurePromise___redArg___boxed(
    mut v_task_10395_: *mut LeanObject,
    mut v_error_10396_: *mut LeanObject,
    mut v_a_10397_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10398_: *mut LeanObject = core::ptr::null_mut();
    v_res_10398_ = l_Std_Async_Async_ofPurePromise___redArg(v_task_10395_, v_error_10396_);
    return v_res_10398_;
}
pub unsafe fn l_Std_Async_Async_ofPurePromise(
    mut v_00_u03b1_10399_: *mut LeanObject,
    mut v_task_10400_: *mut LeanObject,
    mut v_error_10401_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_10404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10407_: u8 = 0;
    let mut v___f_10408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10411_: u8 = 0;
    let mut v___x_10412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10416_: u8 = 0;
    let mut v_a_10417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10420_: u8 = 0;
    let mut v___x_10422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10425_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_10403_ = lean_apply_1(v_task_10400_, lean_box(0));
                if lean_obj_tag(v___x_10403_) == 0 {
                    v_a_10404_ = lean_ctor_get(v___x_10403_, 0);
                    v_isSharedCheck_10416_ = (!lean_is_exclusive(v___x_10403_)) as u8;
                    if v_isSharedCheck_10416_ == 0 {
                        v___x_10406_ = v___x_10403_;
                        v_isShared_10407_ = v_isSharedCheck_10416_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_10404_);
                        lean_dec(v___x_10403_);
                        v___x_10406_ = lean_box(0);
                        v_isShared_10407_ = v_isSharedCheck_10416_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_error_10401_);
                    v_a_10417_ = lean_ctor_get(v___x_10403_, 0);
                    v_isSharedCheck_10425_ = (!lean_is_exclusive(v___x_10403_)) as u8;
                    if v_isSharedCheck_10425_ == 0 {
                        v___x_10419_ = v___x_10403_;
                        v_isShared_10420_ = v_isSharedCheck_10425_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_10417_);
                        lean_dec(v___x_10403_);
                        v___x_10419_ = lean_box(0);
                        v_isShared_10420_ = v_isSharedCheck_10425_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___f_10408_ = lean_alloc_closure(
                    l_Std_Async_AsyncTask_ofPurePromise___redArg___lam__0 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_10408_, 0, v_error_10401_);
                v___x_10409_ = lean_io_promise_result_opt(v_a_10404_);
                lean_dec(v_a_10404_);
                v___x_10410_ = lean_unsigned_to_nat(0);
                v___x_10411_ = 0;
                v___x_10412_ =
                    lean_task_map(v___f_10408_, v___x_10409_, v___x_10410_, v___x_10411_);
                if v_isShared_10407_ == 0 {
                    lean_ctor_set_tag(v___x_10406_, 1);
                    lean_ctor_set(v___x_10406_, 0, v___x_10412_);
                    v___x_10414_ = v___x_10406_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_10415_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10415_, 0, v___x_10412_);
                    v___x_10414_ = v_reuseFailAlloc_10415_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_10414_;
            }
            3 => {
                if v_isShared_10420_ == 0 {
                    lean_ctor_set_tag(v___x_10419_, 0);
                    v___x_10422_ = v___x_10419_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_10424_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10424_, 0, v_a_10417_);
                    v___x_10422_ = v_reuseFailAlloc_10424_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_10423_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_10423_, 0, v___x_10422_);
                return v___x_10423_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Async_ofPurePromise___boxed(
    mut v_00_u03b1_10426_: *mut LeanObject,
    mut v_task_10427_: *mut LeanObject,
    mut v_error_10428_: *mut LeanObject,
    mut v_a_10429_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10430_: *mut LeanObject = core::ptr::null_mut();
    v_res_10430_ =
        l_Std_Async_Async_ofPurePromise(v_00_u03b1_10426_, v_task_10427_, v_error_10428_);
    return v_res_10430_;
}
pub unsafe fn l_Std_Async_Async_instMonadAwaitAsyncTask___aux__1___redArg(
    mut v_t_10432_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10434_: *mut LeanObject = core::ptr::null_mut();
    v___x_10434_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_10434_, 0, v_t_10432_);
    return v___x_10434_;
}
pub unsafe fn l_Std_Async_Async_instMonadAwaitAsyncTask___aux__1___redArg___boxed(
    mut v_t_10435_: *mut LeanObject,
    mut v_a_10436_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10437_: *mut LeanObject = core::ptr::null_mut();
    v_res_10437_ = l_Std_Async_Async_instMonadAwaitAsyncTask___aux__1___redArg(v_t_10435_);
    return v_res_10437_;
}
pub unsafe fn l_Std_Async_Async_instMonadAwaitAsyncTask___aux__1(
    mut v_00_u03b1_10438_: *mut LeanObject,
    mut v_t_10439_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10441_: *mut LeanObject = core::ptr::null_mut();
    v___x_10441_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_10441_, 0, v_t_10439_);
    return v___x_10441_;
}
pub unsafe fn l_Std_Async_Async_instMonadAwaitAsyncTask___aux__1___boxed(
    mut v_00_u03b1_10442_: *mut LeanObject,
    mut v_t_10443_: *mut LeanObject,
    mut v_a_10444_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10445_: *mut LeanObject = core::ptr::null_mut();
    v_res_10445_ =
        l_Std_Async_Async_instMonadAwaitAsyncTask___aux__1(v_00_u03b1_10442_, v_t_10443_);
    return v_res_10445_;
}
pub unsafe fn l_Std_Async_Async_instMonadAwaitPromise___aux__1___redArg(
    mut v_t_10448_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_10450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10453_: u8 = 0;
    let mut v___x_10454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10455_: *mut LeanObject = core::ptr::null_mut();
    v___f_10450_ = l_Std_Async_Async_ofIOTask___redArg___closed__0;
    v___x_10451_ = l_IO_Promise_result_x21___redArg(v_t_10448_);
    v___x_10452_ = lean_unsigned_to_nat(0);
    v___x_10453_ = 0;
    v___x_10454_ = lean_task_map(v___f_10450_, v___x_10451_, v___x_10452_, v___x_10453_);
    v___x_10455_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_10455_, 0, v___x_10454_);
    return v___x_10455_;
}
pub unsafe fn l_Std_Async_Async_instMonadAwaitPromise___aux__1___redArg___boxed(
    mut v_t_10456_: *mut LeanObject,
    mut v_a_10457_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10458_: *mut LeanObject = core::ptr::null_mut();
    v_res_10458_ = l_Std_Async_Async_instMonadAwaitPromise___aux__1___redArg(v_t_10456_);
    lean_dec(v_t_10456_);
    return v_res_10458_;
}
pub unsafe fn l_Std_Async_Async_instMonadAwaitPromise___aux__1(
    mut v_00_u03b1_10459_: *mut LeanObject,
    mut v_t_10460_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_10462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10465_: u8 = 0;
    let mut v___x_10466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10467_: *mut LeanObject = core::ptr::null_mut();
    v___f_10462_ = l_Std_Async_Async_ofIOTask___redArg___closed__0;
    v___x_10463_ = l_IO_Promise_result_x21___redArg(v_t_10460_);
    v___x_10464_ = lean_unsigned_to_nat(0);
    v___x_10465_ = 0;
    v___x_10466_ = lean_task_map(v___f_10462_, v___x_10463_, v___x_10464_, v___x_10465_);
    v___x_10467_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_10467_, 0, v___x_10466_);
    return v___x_10467_;
}
pub unsafe fn l_Std_Async_Async_instMonadAwaitPromise___aux__1___boxed(
    mut v_00_u03b1_10468_: *mut LeanObject,
    mut v_t_10469_: *mut LeanObject,
    mut v_a_10470_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10471_: *mut LeanObject = core::ptr::null_mut();
    v_res_10471_ = l_Std_Async_Async_instMonadAwaitPromise___aux__1(v_00_u03b1_10468_, v_t_10469_);
    lean_dec(v_t_10469_);
    return v_res_10471_;
}
pub unsafe fn l_Std_Async_Async_concurrently___redArg___lam__1(
    mut v_a_10474_: *mut LeanObject,
    mut v_x_10475_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_10477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10480_: u8 = 0;
    let mut v___x_10482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10485_: u8 = 0;
    let mut v_a_10486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10489_: u8 = 0;
    let mut v___x_10490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10495_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_10475_) == 0 {
                    lean_dec(v_a_10474_);
                    v_a_10477_ = lean_ctor_get(v_x_10475_, 0);
                    v_isSharedCheck_10485_ = (!lean_is_exclusive(v_x_10475_)) as u8;
                    if v_isSharedCheck_10485_ == 0 {
                        v___x_10479_ = v_x_10475_;
                        v_isShared_10480_ = v_isSharedCheck_10485_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_10477_);
                        lean_dec(v_x_10475_);
                        v___x_10479_ = lean_box(0);
                        v_isShared_10480_ = v_isSharedCheck_10485_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_10486_ = lean_ctor_get(v_x_10475_, 0);
                    v_isSharedCheck_10495_ = (!lean_is_exclusive(v_x_10475_)) as u8;
                    if v_isSharedCheck_10495_ == 0 {
                        v___x_10488_ = v_x_10475_;
                        v_isShared_10489_ = v_isSharedCheck_10495_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_10486_);
                        lean_dec(v_x_10475_);
                        v___x_10488_ = lean_box(0);
                        v_isShared_10489_ = v_isSharedCheck_10495_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_10480_ == 0 {
                    v___x_10482_ = v___x_10479_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_10484_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10484_, 0, v_a_10477_);
                    v___x_10482_ = v_reuseFailAlloc_10484_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_10483_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_10483_, 0, v___x_10482_);
                return v___x_10483_;
            }
            3 => {
                v___x_10490_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_10490_, 0, v_a_10474_);
                lean_ctor_set(v___x_10490_, 1, v_a_10486_);
                if v_isShared_10489_ == 0 {
                    lean_ctor_set(v___x_10488_, 0, v___x_10490_);
                    v___x_10492_ = v___x_10488_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_10494_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10494_, 0, v___x_10490_);
                    v___x_10492_ = v_reuseFailAlloc_10494_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_10493_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_10493_, 0, v___x_10492_);
                return v___x_10493_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Async_concurrently___redArg___lam__1___boxed(
    mut v_a_10496_: *mut LeanObject,
    mut v_x_10497_: *mut LeanObject,
    mut v___y_10498_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10499_: *mut LeanObject = core::ptr::null_mut();
    v_res_10499_ = l_Std_Async_Async_concurrently___redArg___lam__1(v_a_10496_, v_x_10497_);
    return v_res_10499_;
}
pub unsafe fn l_Std_Async_Async_concurrently___redArg___lam__0(
    mut v_a_10500_: *mut LeanObject,
    mut v_x_10501_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_10503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10506_: u8 = 0;
    let mut v___x_10508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10511_: u8 = 0;
    let mut v_a_10512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_10513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10516_: u8 = 0;
    let mut v___x_10517_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_10501_) == 0 {
                    lean_dec_ref(v_a_10500_);
                    v_a_10503_ = lean_ctor_get(v_x_10501_, 0);
                    v_isSharedCheck_10511_ = (!lean_is_exclusive(v_x_10501_)) as u8;
                    if v_isSharedCheck_10511_ == 0 {
                        v___x_10505_ = v_x_10501_;
                        v_isShared_10506_ = v_isSharedCheck_10511_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_10503_);
                        lean_dec(v_x_10501_);
                        v___x_10505_ = lean_box(0);
                        v_isShared_10506_ = v_isSharedCheck_10511_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_10512_ = lean_ctor_get(v_x_10501_, 0);
                    lean_inc(v_a_10512_);
                    lean_dec_ref_known(v_x_10501_, 1);
                    v___f_10513_ = lean_alloc_closure(
                        l_Std_Async_Async_concurrently___redArg___lam__1___boxed
                            as *mut core::ffi::c_void,
                        3,
                        1,
                    );
                    lean_closure_set(v___f_10513_, 0, v_a_10512_);
                    v___x_10514_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_10514_, 0, v_a_10500_);
                    v___x_10515_ = lean_unsigned_to_nat(0);
                    v___x_10516_ = 0;
                    v___x_10517_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_10515_, v___x_10516_, v___x_10514_, v___f_10513_);
                    return v___x_10517_;
                }
            }
            1 => {
                if v_isShared_10506_ == 0 {
                    v___x_10508_ = v___x_10505_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_10510_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10510_, 0, v_a_10503_);
                    v___x_10508_ = v_reuseFailAlloc_10510_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_10509_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_10509_, 0, v___x_10508_);
                return v___x_10509_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Async_concurrently___redArg___lam__0___boxed(
    mut v_a_10518_: *mut LeanObject,
    mut v_x_10519_: *mut LeanObject,
    mut v___y_10520_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10521_: *mut LeanObject = core::ptr::null_mut();
    v_res_10521_ = l_Std_Async_Async_concurrently___redArg___lam__0(v_a_10518_, v_x_10519_);
    return v_res_10521_;
}
pub unsafe fn l_Std_Async_Async_concurrently___redArg___lam__2(
    mut v_a_10522_: *mut LeanObject,
    mut v_x_10523_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_10525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10528_: u8 = 0;
    let mut v___x_10530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10533_: u8 = 0;
    let mut v_a_10534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_10535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10538_: u8 = 0;
    let mut v___x_10539_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_10523_) == 0 {
                    lean_dec_ref(v_a_10522_);
                    v_a_10525_ = lean_ctor_get(v_x_10523_, 0);
                    v_isSharedCheck_10533_ = (!lean_is_exclusive(v_x_10523_)) as u8;
                    if v_isSharedCheck_10533_ == 0 {
                        v___x_10527_ = v_x_10523_;
                        v_isShared_10528_ = v_isSharedCheck_10533_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_10525_);
                        lean_dec(v_x_10523_);
                        v___x_10527_ = lean_box(0);
                        v_isShared_10528_ = v_isSharedCheck_10533_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_10534_ = lean_ctor_get(v_x_10523_, 0);
                    lean_inc(v_a_10534_);
                    lean_dec_ref_known(v_x_10523_, 1);
                    v___f_10535_ = lean_alloc_closure(
                        l_Std_Async_Async_concurrently___redArg___lam__0___boxed
                            as *mut core::ffi::c_void,
                        3,
                        1,
                    );
                    lean_closure_set(v___f_10535_, 0, v_a_10534_);
                    v___x_10536_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_10536_, 0, v_a_10522_);
                    v___x_10537_ = lean_unsigned_to_nat(0);
                    v___x_10538_ = 0;
                    v___x_10539_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_10537_, v___x_10538_, v___x_10536_, v___f_10535_);
                    return v___x_10539_;
                }
            }
            1 => {
                if v_isShared_10528_ == 0 {
                    v___x_10530_ = v___x_10527_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_10532_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10532_, 0, v_a_10525_);
                    v___x_10530_ = v_reuseFailAlloc_10532_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_10531_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_10531_, 0, v___x_10530_);
                return v___x_10531_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Async_concurrently___redArg___lam__2___boxed(
    mut v_a_10540_: *mut LeanObject,
    mut v_x_10541_: *mut LeanObject,
    mut v___y_10542_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10543_: *mut LeanObject = core::ptr::null_mut();
    v_res_10543_ = l_Std_Async_Async_concurrently___redArg___lam__2(v_a_10540_, v_x_10541_);
    return v_res_10543_;
}
pub unsafe fn l_Std_Async_Async_concurrently___redArg___lam__3(
    mut v_y_10544_: *mut LeanObject,
    mut v_prio_10545_: *mut LeanObject,
    mut v___f_10546_: *mut LeanObject,
    mut v_x_10547_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_10549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10552_: u8 = 0;
    let mut v___x_10554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10557_: u8 = 0;
    let mut v_a_10558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10561_: u8 = 0;
    let mut v___x_10562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_10564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10566_: u8 = 0;
    let mut v___x_10567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10571_: u8 = 0;
    let mut v___x_10572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10574_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_10547_) == 0 {
                    lean_dec_ref(v___f_10546_);
                    lean_dec(v_prio_10545_);
                    lean_dec_ref(v_y_10544_);
                    v_a_10549_ = lean_ctor_get(v_x_10547_, 0);
                    v_isSharedCheck_10557_ = (!lean_is_exclusive(v_x_10547_)) as u8;
                    if v_isSharedCheck_10557_ == 0 {
                        v___x_10551_ = v_x_10547_;
                        v_isShared_10552_ = v_isSharedCheck_10557_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_10549_);
                        lean_dec(v_x_10547_);
                        v___x_10551_ = lean_box(0);
                        v_isShared_10552_ = v_isSharedCheck_10557_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_10558_ = lean_ctor_get(v_x_10547_, 0);
                    v_isSharedCheck_10574_ = (!lean_is_exclusive(v_x_10547_)) as u8;
                    if v_isSharedCheck_10574_ == 0 {
                        v___x_10560_ = v_x_10547_;
                        v_isShared_10561_ = v_isSharedCheck_10574_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_10558_);
                        lean_dec(v_x_10547_);
                        v___x_10560_ = lean_box(0);
                        v_isShared_10561_ = v_isSharedCheck_10574_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_10552_ == 0 {
                    v___x_10554_ = v___x_10551_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_10556_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10556_, 0, v_a_10549_);
                    v___x_10554_ = v_reuseFailAlloc_10556_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_10555_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_10555_, 0, v___x_10554_);
                return v___x_10555_;
            }
            3 => {
                v___x_10562_ = lean_alloc_closure(
                    l_Std_Async_BaseAsync_toRawBaseIO___boxed as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___x_10562_, 0, lean_box(0));
                lean_closure_set(v___x_10562_, 1, v_y_10544_);
                v___x_10563_ = lean_io_as_task(v___x_10562_, v_prio_10545_);
                v___f_10564_ = lean_alloc_closure(
                    l_Std_Async_Async_concurrently___redArg___lam__2___boxed
                        as *mut core::ffi::c_void,
                    3,
                    1,
                );
                lean_closure_set(v___f_10564_, 0, v_a_10558_);
                v___x_10565_ = lean_unsigned_to_nat(0);
                v___x_10566_ = 1;
                v___x_10567_ =
                    lean_task_bind(v___x_10563_, v___f_10546_, v___x_10565_, v___x_10566_);
                if v_isShared_10561_ == 0 {
                    lean_ctor_set(v___x_10560_, 0, v___x_10567_);
                    v___x_10569_ = v___x_10560_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_10573_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10573_, 0, v___x_10567_);
                    v___x_10569_ = v_reuseFailAlloc_10573_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_10570_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_10570_, 0, v___x_10569_);
                v___x_10571_ = 0;
                v___x_10572_ =
                    l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(
                        v___x_10565_,
                        v___x_10571_,
                        v___x_10570_,
                        v___f_10564_,
                    );
                return v___x_10572_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Async_concurrently___redArg___lam__3___boxed(
    mut v_y_10575_: *mut LeanObject,
    mut v_prio_10576_: *mut LeanObject,
    mut v___f_10577_: *mut LeanObject,
    mut v_x_10578_: *mut LeanObject,
    mut v___y_10579_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10580_: *mut LeanObject = core::ptr::null_mut();
    v_res_10580_ = l_Std_Async_Async_concurrently___redArg___lam__3(
        v_y_10575_,
        v_prio_10576_,
        v___f_10577_,
        v_x_10578_,
    );
    return v_res_10580_;
}
pub unsafe fn l_Std_Async_Async_concurrently___redArg(
    mut v_x_10581_: *mut LeanObject,
    mut v_y_10582_: *mut LeanObject,
    mut v_prio_10583_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_10587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_10588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10590_: u8 = 0;
    let mut v___x_10591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10594_: u8 = 0;
    let mut v___x_10595_: *mut LeanObject = core::ptr::null_mut();
    v___x_10585_ = lean_alloc_closure(
        l_Std_Async_BaseAsync_toRawBaseIO___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___x_10585_, 0, lean_box(0));
    lean_closure_set(v___x_10585_, 1, v_x_10581_);
    lean_inc(v_prio_10583_);
    v___x_10586_ = lean_io_as_task(v___x_10585_, v_prio_10583_);
    v___f_10587_ = l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___closed__0;
    v___f_10588_ = lean_alloc_closure(
        l_Std_Async_Async_concurrently___redArg___lam__3___boxed as *mut core::ffi::c_void,
        5,
        3,
    );
    lean_closure_set(v___f_10588_, 0, v_y_10582_);
    lean_closure_set(v___f_10588_, 1, v_prio_10583_);
    lean_closure_set(v___f_10588_, 2, v___f_10587_);
    v___x_10589_ = lean_unsigned_to_nat(0);
    v___x_10590_ = 1;
    v___x_10591_ = lean_task_bind(v___x_10586_, v___f_10587_, v___x_10589_, v___x_10590_);
    v___x_10592_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_10592_, 0, v___x_10591_);
    v___x_10593_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_10593_, 0, v___x_10592_);
    v___x_10594_ = 0;
    v___x_10595_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(
        v___x_10589_,
        v___x_10594_,
        v___x_10593_,
        v___f_10588_,
    );
    return v___x_10595_;
}
pub unsafe fn l_Std_Async_Async_concurrently___redArg___boxed(
    mut v_x_10596_: *mut LeanObject,
    mut v_y_10597_: *mut LeanObject,
    mut v_prio_10598_: *mut LeanObject,
    mut v_a_10599_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10600_: *mut LeanObject = core::ptr::null_mut();
    v_res_10600_ = l_Std_Async_Async_concurrently___redArg(v_x_10596_, v_y_10597_, v_prio_10598_);
    return v_res_10600_;
}
pub unsafe fn l_Std_Async_Async_concurrently(
    mut v_00_u03b1_10601_: *mut LeanObject,
    mut v_00_u03b2_10602_: *mut LeanObject,
    mut v_x_10603_: *mut LeanObject,
    mut v_y_10604_: *mut LeanObject,
    mut v_prio_10605_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_10609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_10610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10612_: u8 = 0;
    let mut v___x_10613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10616_: u8 = 0;
    let mut v___x_10617_: *mut LeanObject = core::ptr::null_mut();
    v___x_10607_ = lean_alloc_closure(
        l_Std_Async_BaseAsync_toRawBaseIO___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___x_10607_, 0, lean_box(0));
    lean_closure_set(v___x_10607_, 1, v_x_10603_);
    lean_inc(v_prio_10605_);
    v___x_10608_ = lean_io_as_task(v___x_10607_, v_prio_10605_);
    v___f_10609_ = l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___closed__0;
    v___f_10610_ = lean_alloc_closure(
        l_Std_Async_Async_concurrently___redArg___lam__3___boxed as *mut core::ffi::c_void,
        5,
        3,
    );
    lean_closure_set(v___f_10610_, 0, v_y_10604_);
    lean_closure_set(v___f_10610_, 1, v_prio_10605_);
    lean_closure_set(v___f_10610_, 2, v___f_10609_);
    v___x_10611_ = lean_unsigned_to_nat(0);
    v___x_10612_ = 1;
    v___x_10613_ = lean_task_bind(v___x_10608_, v___f_10609_, v___x_10611_, v___x_10612_);
    v___x_10614_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_10614_, 0, v___x_10613_);
    v___x_10615_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_10615_, 0, v___x_10614_);
    v___x_10616_ = 0;
    v___x_10617_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(
        v___x_10611_,
        v___x_10616_,
        v___x_10615_,
        v___f_10610_,
    );
    return v___x_10617_;
}
pub unsafe fn l_Std_Async_Async_concurrently___boxed(
    mut v_00_u03b1_10618_: *mut LeanObject,
    mut v_00_u03b2_10619_: *mut LeanObject,
    mut v_x_10620_: *mut LeanObject,
    mut v_y_10621_: *mut LeanObject,
    mut v_prio_10622_: *mut LeanObject,
    mut v_a_10623_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10624_: *mut LeanObject = core::ptr::null_mut();
    v_res_10624_ = l_Std_Async_Async_concurrently(
        v_00_u03b1_10618_,
        v_00_u03b2_10619_,
        v_x_10620_,
        v_y_10621_,
        v_prio_10622_,
    );
    return v_res_10624_;
}
pub unsafe fn l_Std_Async_Async_race___redArg___lam__1(
    mut v_x_10625_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_10627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10630_: u8 = 0;
    let mut v___x_10632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10635_: u8 = 0;
    let mut v_a_10636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10637_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_10625_) == 0 {
                    v_a_10627_ = lean_ctor_get(v_x_10625_, 0);
                    v_isSharedCheck_10635_ = (!lean_is_exclusive(v_x_10625_)) as u8;
                    if v_isSharedCheck_10635_ == 0 {
                        v___x_10629_ = v_x_10625_;
                        v_isShared_10630_ = v_isSharedCheck_10635_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_10627_);
                        lean_dec(v_x_10625_);
                        v___x_10629_ = lean_box(0);
                        v_isShared_10630_ = v_isSharedCheck_10635_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_10636_ = lean_ctor_get(v_x_10625_, 0);
                    lean_inc(v_a_10636_);
                    lean_dec_ref_known(v_x_10625_, 1);
                    v___x_10637_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_10637_, 0, v_a_10636_);
                    return v___x_10637_;
                }
            }
            1 => {
                if v_isShared_10630_ == 0 {
                    v___x_10632_ = v___x_10629_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_10634_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10634_, 0, v_a_10627_);
                    v___x_10632_ = v_reuseFailAlloc_10634_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_10633_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_10633_, 0, v___x_10632_);
                return v___x_10633_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Async_race___redArg___lam__1___boxed(
    mut v_x_10638_: *mut LeanObject,
    mut v___y_10639_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10640_: *mut LeanObject = core::ptr::null_mut();
    v_res_10640_ = l_Std_Async_Async_race___redArg___lam__1(v_x_10638_);
    return v_res_10640_;
}
pub unsafe fn l_Std_Async_Async_race___redArg___lam__0(
    mut v_a_10641_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10642_: *mut LeanObject = core::ptr::null_mut();
    v___x_10642_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_10642_, 0, v_a_10641_);
    return v___x_10642_;
}
pub unsafe fn l_Std_Async_Async_race___redArg___lam__3(
    mut v_a_10643_: *mut LeanObject,
    mut v_value_10644_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10646_: *mut LeanObject = core::ptr::null_mut();
    v___x_10646_ = lean_io_promise_resolve(v_value_10644_, v_a_10643_);
    return v___x_10646_;
}
pub unsafe fn l_Std_Async_Async_race___redArg___lam__3___boxed(
    mut v_a_10647_: *mut LeanObject,
    mut v_value_10648_: *mut LeanObject,
    mut v___y_10649_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10650_: *mut LeanObject = core::ptr::null_mut();
    v_res_10650_ = l_Std_Async_Async_race___redArg___lam__3(v_a_10647_, v_value_10648_);
    lean_dec(v_a_10647_);
    return v_res_10650_;
}
pub unsafe fn l_Std_Async_Async_race___redArg___lam__2(
    mut v_a_10651_: *mut LeanObject,
    mut v___f_10652_: *mut LeanObject,
    mut v___f_10653_: *mut LeanObject,
    mut v_x_10654_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_10656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10659_: u8 = 0;
    let mut v___x_10661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10664_: u8 = 0;
    let mut v___x_10665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10667_: u8 = 0;
    let mut v___x_10668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10670_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_10654_) == 0 {
                    lean_dec_ref(v___f_10653_);
                    lean_dec_ref(v___f_10652_);
                    v_a_10656_ = lean_ctor_get(v_x_10654_, 0);
                    v_isSharedCheck_10664_ = (!lean_is_exclusive(v_x_10654_)) as u8;
                    if v_isSharedCheck_10664_ == 0 {
                        v___x_10658_ = v_x_10654_;
                        v_isShared_10659_ = v_isSharedCheck_10664_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_10656_);
                        lean_dec(v_x_10654_);
                        v___x_10658_ = lean_box(0);
                        v_isShared_10659_ = v_isSharedCheck_10664_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v_x_10654_, 1);
                    v___x_10665_ = l_IO_Promise_result_x21___redArg(v_a_10651_);
                    v___x_10666_ = lean_unsigned_to_nat(0);
                    v___x_10667_ = 0;
                    v___x_10668_ =
                        lean_task_map(v___f_10652_, v___x_10665_, v___x_10666_, v___x_10667_);
                    v___x_10669_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_10669_, 0, v___x_10668_);
                    v___x_10670_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_10666_, v___x_10667_, v___x_10669_, v___f_10653_);
                    return v___x_10670_;
                }
            }
            1 => {
                if v_isShared_10659_ == 0 {
                    v___x_10661_ = v___x_10658_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_10663_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10663_, 0, v_a_10656_);
                    v___x_10661_ = v_reuseFailAlloc_10663_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_10662_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_10662_, 0, v___x_10661_);
                return v___x_10662_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Async_race___redArg___lam__2___boxed(
    mut v_a_10671_: *mut LeanObject,
    mut v___f_10672_: *mut LeanObject,
    mut v___f_10673_: *mut LeanObject,
    mut v_x_10674_: *mut LeanObject,
    mut v___y_10675_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10676_: *mut LeanObject = core::ptr::null_mut();
    v_res_10676_ = l_Std_Async_Async_race___redArg___lam__2(
        v_a_10671_,
        v___f_10672_,
        v___f_10673_,
        v_x_10674_,
    );
    lean_dec(v_a_10671_);
    return v_res_10676_;
}
pub unsafe fn l_Std_Async_Async_race___redArg___lam__4(
    mut v_a_10677_: *mut LeanObject,
    mut v___x_10678_: *mut LeanObject,
    mut v___x_10679_: *mut LeanObject,
    mut v___x_10680_: u8,
    mut v___f_10681_: *mut LeanObject,
    mut v_x_10682_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_10684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10687_: u8 = 0;
    let mut v___x_10689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10692_: u8 = 0;
    let mut v___x_10694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10695_: u8 = 0;
    let mut v___x_10696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10702_: u8 = 0;
    let mut v_unused_10703_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_10682_) == 0 {
                    lean_dec_ref(v___f_10681_);
                    lean_dec(v___x_10679_);
                    lean_dec_ref(v___x_10678_);
                    lean_dec_ref(v_a_10677_);
                    v_a_10684_ = lean_ctor_get(v_x_10682_, 0);
                    v_isSharedCheck_10692_ = (!lean_is_exclusive(v_x_10682_)) as u8;
                    if v_isSharedCheck_10692_ == 0 {
                        v___x_10686_ = v_x_10682_;
                        v_isShared_10687_ = v_isSharedCheck_10692_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_10684_);
                        lean_dec(v_x_10682_);
                        v___x_10686_ = lean_box(0);
                        v_isShared_10687_ = v_isSharedCheck_10692_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_isSharedCheck_10702_ = (!lean_is_exclusive(v_x_10682_)) as u8;
                    if v_isSharedCheck_10702_ == 0 {
                        v_unused_10703_ = lean_ctor_get(v_x_10682_, 0);
                        lean_dec(v_unused_10703_);
                        v___x_10694_ = v_x_10682_;
                        v_isShared_10695_ = v_isSharedCheck_10702_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v_x_10682_);
                        v___x_10694_ = lean_box(0);
                        v_isShared_10695_ = v_isSharedCheck_10702_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_10687_ == 0 {
                    v___x_10689_ = v___x_10686_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_10691_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10691_, 0, v_a_10684_);
                    v___x_10689_ = v_reuseFailAlloc_10691_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_10690_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_10690_, 0, v___x_10689_);
                return v___x_10690_;
            }
            3 => {
                lean_inc(v___x_10679_);
                v___x_10696_ = l_BaseIO_chainTask___redArg(
                    v_a_10677_,
                    v___x_10678_,
                    v___x_10679_,
                    v___x_10680_,
                );
                if v_isShared_10695_ == 0 {
                    lean_ctor_set(v___x_10694_, 0, v___x_10696_);
                    v___x_10698_ = v___x_10694_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_10701_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10701_, 0, v___x_10696_);
                    v___x_10698_ = v_reuseFailAlloc_10701_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_10699_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_10699_, 0, v___x_10698_);
                v___x_10700_ =
                    l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(
                        v___x_10679_,
                        v___x_10680_,
                        v___x_10699_,
                        v___f_10681_,
                    );
                return v___x_10700_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Async_race___redArg___lam__4___boxed(
    mut v_a_10704_: *mut LeanObject,
    mut v___x_10705_: *mut LeanObject,
    mut v___x_10706_: *mut LeanObject,
    mut v___x_10707_: *mut LeanObject,
    mut v___f_10708_: *mut LeanObject,
    mut v_x_10709_: *mut LeanObject,
    mut v___y_10710_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1405__boxed_10711_: u8 = 0;
    let mut v_res_10712_: *mut LeanObject = core::ptr::null_mut();
    v___x_1405__boxed_10711_ = (lean_unbox(v___x_10707_) as u8);
    v_res_10712_ = l_Std_Async_Async_race___redArg___lam__4(
        v_a_10704_,
        v___x_10705_,
        v___x_10706_,
        v___x_1405__boxed_10711_,
        v___f_10708_,
        v_x_10709_,
    );
    return v_res_10712_;
}
pub unsafe fn l_Std_Async_Async_race___redArg___lam__5(
    mut v___f_10713_: *mut LeanObject,
    mut v___f_10714_: *mut LeanObject,
    mut v_a_10715_: *mut LeanObject,
    mut v___f_10716_: *mut LeanObject,
    mut v_x_10717_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_10719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10722_: u8 = 0;
    let mut v___x_10724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10727_: u8 = 0;
    let mut v_a_10728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10731_: u8 = 0;
    let mut v___x_10732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10735_: u8 = 0;
    let mut v___x_10736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_10738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10744_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_10717_) == 0 {
                    lean_dec_ref(v___f_10716_);
                    lean_dec_ref(v_a_10715_);
                    lean_dec_ref(v___f_10714_);
                    lean_dec(v___f_10713_);
                    v_a_10719_ = lean_ctor_get(v_x_10717_, 0);
                    v_isSharedCheck_10727_ = (!lean_is_exclusive(v_x_10717_)) as u8;
                    if v_isSharedCheck_10727_ == 0 {
                        v___x_10721_ = v_x_10717_;
                        v_isShared_10722_ = v_isSharedCheck_10727_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_10719_);
                        lean_dec(v_x_10717_);
                        v___x_10721_ = lean_box(0);
                        v_isShared_10722_ = v_isSharedCheck_10727_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_10728_ = lean_ctor_get(v_x_10717_, 0);
                    v_isSharedCheck_10744_ = (!lean_is_exclusive(v_x_10717_)) as u8;
                    if v_isSharedCheck_10744_ == 0 {
                        v___x_10730_ = v_x_10717_;
                        v_isShared_10731_ = v_isSharedCheck_10744_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_10728_);
                        lean_dec(v_x_10717_);
                        v___x_10730_ = lean_box(0);
                        v_isShared_10731_ = v_isSharedCheck_10744_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_10722_ == 0 {
                    v___x_10724_ = v___x_10721_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_10726_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10726_, 0, v_a_10719_);
                    v___x_10724_ = v_reuseFailAlloc_10726_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_10725_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_10725_, 0, v___x_10724_);
                return v___x_10725_;
            }
            3 => {
                v___x_10732_ = lean_alloc_closure(l_liftM as *mut core::ffi::c_void, 5, 4);
                lean_closure_set(v___x_10732_, 0, lean_box(0));
                lean_closure_set(v___x_10732_, 1, lean_box(0));
                lean_closure_set(v___x_10732_, 2, v___f_10713_);
                lean_closure_set(v___x_10732_, 3, lean_box(0));
                v___x_10733_ = lean_alloc_closure(l_Function_comp as *mut core::ffi::c_void, 6, 5);
                lean_closure_set(v___x_10733_, 0, lean_box(0));
                lean_closure_set(v___x_10733_, 1, lean_box(0));
                lean_closure_set(v___x_10733_, 2, lean_box(0));
                lean_closure_set(v___x_10733_, 3, v___x_10732_);
                lean_closure_set(v___x_10733_, 4, v___f_10714_);
                v___x_10734_ = lean_unsigned_to_nat(0);
                v___x_10735_ = 0;
                lean_inc_ref(v___x_10733_);
                v___x_10736_ = l_BaseIO_chainTask___redArg(
                    v_a_10715_,
                    v___x_10733_,
                    v___x_10734_,
                    v___x_10735_,
                );
                v___x_10737_ = lean_box((v___x_10735_) as usize);
                v___f_10738_ = lean_alloc_closure(
                    l_Std_Async_Async_race___redArg___lam__4___boxed as *mut core::ffi::c_void,
                    7,
                    5,
                );
                lean_closure_set(v___f_10738_, 0, v_a_10728_);
                lean_closure_set(v___f_10738_, 1, v___x_10733_);
                lean_closure_set(v___f_10738_, 2, v___x_10734_);
                lean_closure_set(v___f_10738_, 3, v___x_10737_);
                lean_closure_set(v___f_10738_, 4, v___f_10716_);
                if v_isShared_10731_ == 0 {
                    lean_ctor_set(v___x_10730_, 0, v___x_10736_);
                    v___x_10740_ = v___x_10730_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_10743_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10743_, 0, v___x_10736_);
                    v___x_10740_ = v_reuseFailAlloc_10743_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_10741_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_10741_, 0, v___x_10740_);
                v___x_10742_ =
                    l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(
                        v___x_10734_,
                        v___x_10735_,
                        v___x_10741_,
                        v___f_10738_,
                    );
                return v___x_10742_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Async_race___redArg___lam__5___boxed(
    mut v___f_10745_: *mut LeanObject,
    mut v___f_10746_: *mut LeanObject,
    mut v_a_10747_: *mut LeanObject,
    mut v___f_10748_: *mut LeanObject,
    mut v_x_10749_: *mut LeanObject,
    mut v___y_10750_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10751_: *mut LeanObject = core::ptr::null_mut();
    v_res_10751_ = l_Std_Async_Async_race___redArg___lam__5(
        v___f_10745_,
        v___f_10746_,
        v_a_10747_,
        v___f_10748_,
        v_x_10749_,
    );
    return v_res_10751_;
}
pub unsafe fn l_Std_Async_Async_race___redArg___lam__6(
    mut v_y_10752_: *mut LeanObject,
    mut v_prio_10753_: *mut LeanObject,
    mut v___f_10754_: *mut LeanObject,
    mut v___f_10755_: *mut LeanObject,
    mut v___f_10756_: *mut LeanObject,
    mut v___f_10757_: *mut LeanObject,
    mut v_x_10758_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_10760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10763_: u8 = 0;
    let mut v___x_10765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10768_: u8 = 0;
    let mut v_a_10769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10772_: u8 = 0;
    let mut v___x_10773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_10775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10777_: u8 = 0;
    let mut v___x_10778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10782_: u8 = 0;
    let mut v___x_10783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10785_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_10758_) == 0 {
                    lean_dec_ref(v___f_10757_);
                    lean_dec_ref(v___f_10756_);
                    lean_dec_ref(v___f_10755_);
                    lean_dec(v___f_10754_);
                    lean_dec(v_prio_10753_);
                    lean_dec_ref(v_y_10752_);
                    v_a_10760_ = lean_ctor_get(v_x_10758_, 0);
                    v_isSharedCheck_10768_ = (!lean_is_exclusive(v_x_10758_)) as u8;
                    if v_isSharedCheck_10768_ == 0 {
                        v___x_10762_ = v_x_10758_;
                        v_isShared_10763_ = v_isSharedCheck_10768_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_10760_);
                        lean_dec(v_x_10758_);
                        v___x_10762_ = lean_box(0);
                        v_isShared_10763_ = v_isSharedCheck_10768_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_10769_ = lean_ctor_get(v_x_10758_, 0);
                    v_isSharedCheck_10785_ = (!lean_is_exclusive(v_x_10758_)) as u8;
                    if v_isSharedCheck_10785_ == 0 {
                        v___x_10771_ = v_x_10758_;
                        v_isShared_10772_ = v_isSharedCheck_10785_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_10769_);
                        lean_dec(v_x_10758_);
                        v___x_10771_ = lean_box(0);
                        v_isShared_10772_ = v_isSharedCheck_10785_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_10763_ == 0 {
                    v___x_10765_ = v___x_10762_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_10767_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10767_, 0, v_a_10760_);
                    v___x_10765_ = v_reuseFailAlloc_10767_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_10766_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_10766_, 0, v___x_10765_);
                return v___x_10766_;
            }
            3 => {
                v___x_10773_ = lean_alloc_closure(
                    l_Std_Async_BaseAsync_toRawBaseIO___boxed as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___x_10773_, 0, lean_box(0));
                lean_closure_set(v___x_10773_, 1, v_y_10752_);
                v___x_10774_ = lean_io_as_task(v___x_10773_, v_prio_10753_);
                v___f_10775_ = lean_alloc_closure(
                    l_Std_Async_Async_race___redArg___lam__5___boxed as *mut core::ffi::c_void,
                    6,
                    4,
                );
                lean_closure_set(v___f_10775_, 0, v___f_10754_);
                lean_closure_set(v___f_10775_, 1, v___f_10755_);
                lean_closure_set(v___f_10775_, 2, v_a_10769_);
                lean_closure_set(v___f_10775_, 3, v___f_10756_);
                v___x_10776_ = lean_unsigned_to_nat(0);
                v___x_10777_ = 1;
                v___x_10778_ =
                    lean_task_bind(v___x_10774_, v___f_10757_, v___x_10776_, v___x_10777_);
                if v_isShared_10772_ == 0 {
                    lean_ctor_set(v___x_10771_, 0, v___x_10778_);
                    v___x_10780_ = v___x_10771_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_10784_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10784_, 0, v___x_10778_);
                    v___x_10780_ = v_reuseFailAlloc_10784_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_10781_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_10781_, 0, v___x_10780_);
                v___x_10782_ = 0;
                v___x_10783_ =
                    l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(
                        v___x_10776_,
                        v___x_10782_,
                        v___x_10781_,
                        v___f_10775_,
                    );
                return v___x_10783_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Async_race___redArg___lam__6___boxed(
    mut v_y_10786_: *mut LeanObject,
    mut v_prio_10787_: *mut LeanObject,
    mut v___f_10788_: *mut LeanObject,
    mut v___f_10789_: *mut LeanObject,
    mut v___f_10790_: *mut LeanObject,
    mut v___f_10791_: *mut LeanObject,
    mut v_x_10792_: *mut LeanObject,
    mut v___y_10793_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10794_: *mut LeanObject = core::ptr::null_mut();
    v_res_10794_ = l_Std_Async_Async_race___redArg___lam__6(
        v_y_10786_,
        v_prio_10787_,
        v___f_10788_,
        v___f_10789_,
        v___f_10790_,
        v___f_10791_,
        v_x_10792_,
    );
    return v_res_10794_;
}
pub unsafe fn l_Std_Async_Async_race___redArg___lam__7(
    mut v_x_10795_: *mut LeanObject,
    mut v_prio_10796_: *mut LeanObject,
    mut v___f_10797_: *mut LeanObject,
    mut v___f_10798_: *mut LeanObject,
    mut v_y_10799_: *mut LeanObject,
    mut v___f_10800_: *mut LeanObject,
    mut v___f_10801_: *mut LeanObject,
    mut v___f_10802_: *mut LeanObject,
    mut v_x_10803_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_10805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10808_: u8 = 0;
    let mut v___x_10810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10813_: u8 = 0;
    let mut v_a_10814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10817_: u8 = 0;
    let mut v___x_10818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_10820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_10821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_10822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10824_: u8 = 0;
    let mut v___x_10825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10829_: u8 = 0;
    let mut v___x_10830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10832_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_10803_) == 0 {
                    lean_dec_ref(v___f_10802_);
                    lean_dec_ref(v___f_10801_);
                    lean_dec(v___f_10800_);
                    lean_dec_ref(v_y_10799_);
                    lean_dec_ref(v___f_10798_);
                    lean_dec_ref(v___f_10797_);
                    lean_dec(v_prio_10796_);
                    lean_dec_ref(v_x_10795_);
                    v_a_10805_ = lean_ctor_get(v_x_10803_, 0);
                    v_isSharedCheck_10813_ = (!lean_is_exclusive(v_x_10803_)) as u8;
                    if v_isSharedCheck_10813_ == 0 {
                        v___x_10807_ = v_x_10803_;
                        v_isShared_10808_ = v_isSharedCheck_10813_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_10805_);
                        lean_dec(v_x_10803_);
                        v___x_10807_ = lean_box(0);
                        v_isShared_10808_ = v_isSharedCheck_10813_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_10814_ = lean_ctor_get(v_x_10803_, 0);
                    v_isSharedCheck_10832_ = (!lean_is_exclusive(v_x_10803_)) as u8;
                    if v_isSharedCheck_10832_ == 0 {
                        v___x_10816_ = v_x_10803_;
                        v_isShared_10817_ = v_isSharedCheck_10832_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_10814_);
                        lean_dec(v_x_10803_);
                        v___x_10816_ = lean_box(0);
                        v_isShared_10817_ = v_isSharedCheck_10832_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_10808_ == 0 {
                    v___x_10810_ = v___x_10807_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_10812_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10812_, 0, v_a_10805_);
                    v___x_10810_ = v_reuseFailAlloc_10812_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_10811_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_10811_, 0, v___x_10810_);
                return v___x_10811_;
            }
            3 => {
                v___x_10818_ = lean_alloc_closure(
                    l_Std_Async_BaseAsync_toRawBaseIO___boxed as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___x_10818_, 0, lean_box(0));
                lean_closure_set(v___x_10818_, 1, v_x_10795_);
                lean_inc(v_prio_10796_);
                v___x_10819_ = lean_io_as_task(v___x_10818_, v_prio_10796_);
                lean_inc(v_a_10814_);
                v___f_10820_ = lean_alloc_closure(
                    l_Std_Async_Async_race___redArg___lam__3___boxed as *mut core::ffi::c_void,
                    3,
                    1,
                );
                lean_closure_set(v___f_10820_, 0, v_a_10814_);
                v___f_10821_ = lean_alloc_closure(
                    l_Std_Async_Async_race___redArg___lam__2___boxed as *mut core::ffi::c_void,
                    5,
                    3,
                );
                lean_closure_set(v___f_10821_, 0, v_a_10814_);
                lean_closure_set(v___f_10821_, 1, v___f_10797_);
                lean_closure_set(v___f_10821_, 2, v___f_10798_);
                v___f_10822_ = lean_alloc_closure(
                    l_Std_Async_Async_race___redArg___lam__6___boxed as *mut core::ffi::c_void,
                    8,
                    6,
                );
                lean_closure_set(v___f_10822_, 0, v_y_10799_);
                lean_closure_set(v___f_10822_, 1, v_prio_10796_);
                lean_closure_set(v___f_10822_, 2, v___f_10800_);
                lean_closure_set(v___f_10822_, 3, v___f_10820_);
                lean_closure_set(v___f_10822_, 4, v___f_10821_);
                lean_closure_set(v___f_10822_, 5, v___f_10801_);
                v___x_10823_ = lean_unsigned_to_nat(0);
                v___x_10824_ = 1;
                v___x_10825_ =
                    lean_task_bind(v___x_10819_, v___f_10802_, v___x_10823_, v___x_10824_);
                if v_isShared_10817_ == 0 {
                    lean_ctor_set(v___x_10816_, 0, v___x_10825_);
                    v___x_10827_ = v___x_10816_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_10831_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10831_, 0, v___x_10825_);
                    v___x_10827_ = v_reuseFailAlloc_10831_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_10828_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_10828_, 0, v___x_10827_);
                v___x_10829_ = 0;
                v___x_10830_ =
                    l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(
                        v___x_10823_,
                        v___x_10829_,
                        v___x_10828_,
                        v___f_10822_,
                    );
                return v___x_10830_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Async_race___redArg___lam__7___boxed(
    mut v_x_10833_: *mut LeanObject,
    mut v_prio_10834_: *mut LeanObject,
    mut v___f_10835_: *mut LeanObject,
    mut v___f_10836_: *mut LeanObject,
    mut v_y_10837_: *mut LeanObject,
    mut v___f_10838_: *mut LeanObject,
    mut v___f_10839_: *mut LeanObject,
    mut v___f_10840_: *mut LeanObject,
    mut v_x_10841_: *mut LeanObject,
    mut v___y_10842_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10843_: *mut LeanObject = core::ptr::null_mut();
    v_res_10843_ = l_Std_Async_Async_race___redArg___lam__7(
        v_x_10833_,
        v_prio_10834_,
        v___f_10835_,
        v___f_10836_,
        v_y_10837_,
        v___f_10838_,
        v___f_10839_,
        v___f_10840_,
        v_x_10841_,
    );
    return v_res_10843_;
}
pub unsafe fn l_Std_Async_Async_race___redArg(
    mut v_x_10846_: *mut LeanObject,
    mut v_y_10847_: *mut LeanObject,
    mut v_prio_10848_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_10851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_10852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_10853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_10854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_10855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10859_: u8 = 0;
    let mut v___x_10860_: *mut LeanObject = core::ptr::null_mut();
    v___x_10850_ = lean_io_promise_new();
    v___f_10851_ = l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___closed__0;
    v___f_10852_ = l_Std_Async_Async_race___redArg___closed__0;
    v___f_10853_ = l_Std_Async_Async_race___redArg___closed__1;
    v___f_10854_ = l_Std_Async_BaseAsync_race___redArg___closed__0;
    v___f_10855_ = lean_alloc_closure(
        l_Std_Async_Async_race___redArg___lam__7___boxed as *mut core::ffi::c_void,
        10,
        8,
    );
    lean_closure_set(v___f_10855_, 0, v_x_10846_);
    lean_closure_set(v___f_10855_, 1, v_prio_10848_);
    lean_closure_set(v___f_10855_, 2, v___f_10853_);
    lean_closure_set(v___f_10855_, 3, v___f_10852_);
    lean_closure_set(v___f_10855_, 4, v_y_10847_);
    lean_closure_set(v___f_10855_, 5, v___f_10854_);
    lean_closure_set(v___f_10855_, 6, v___f_10851_);
    lean_closure_set(v___f_10855_, 7, v___f_10851_);
    v___x_10856_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_10856_, 0, v___x_10850_);
    v___x_10857_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_10857_, 0, v___x_10856_);
    v___x_10858_ = lean_unsigned_to_nat(0);
    v___x_10859_ = 0;
    v___x_10860_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(
        v___x_10858_,
        v___x_10859_,
        v___x_10857_,
        v___f_10855_,
    );
    return v___x_10860_;
}
pub unsafe fn l_Std_Async_Async_race___redArg___boxed(
    mut v_x_10861_: *mut LeanObject,
    mut v_y_10862_: *mut LeanObject,
    mut v_prio_10863_: *mut LeanObject,
    mut v_a_10864_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10865_: *mut LeanObject = core::ptr::null_mut();
    v_res_10865_ = l_Std_Async_Async_race___redArg(v_x_10861_, v_y_10862_, v_prio_10863_);
    return v_res_10865_;
}
pub unsafe fn l_Std_Async_Async_race(
    mut v_00_u03b1_10866_: *mut LeanObject,
    mut v_inst_10867_: *mut LeanObject,
    mut v_x_10868_: *mut LeanObject,
    mut v_y_10869_: *mut LeanObject,
    mut v_prio_10870_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_10873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_10874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_10875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_10876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_10877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10881_: u8 = 0;
    let mut v___x_10882_: *mut LeanObject = core::ptr::null_mut();
    v___x_10872_ = lean_io_promise_new();
    v___f_10873_ = l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___closed__0;
    v___f_10874_ = l_Std_Async_Async_race___redArg___closed__0;
    v___f_10875_ = l_Std_Async_Async_race___redArg___closed__1;
    v___f_10876_ = l_Std_Async_BaseAsync_race___redArg___closed__0;
    v___f_10877_ = lean_alloc_closure(
        l_Std_Async_Async_race___redArg___lam__7___boxed as *mut core::ffi::c_void,
        10,
        8,
    );
    lean_closure_set(v___f_10877_, 0, v_x_10868_);
    lean_closure_set(v___f_10877_, 1, v_prio_10870_);
    lean_closure_set(v___f_10877_, 2, v___f_10875_);
    lean_closure_set(v___f_10877_, 3, v___f_10874_);
    lean_closure_set(v___f_10877_, 4, v_y_10869_);
    lean_closure_set(v___f_10877_, 5, v___f_10876_);
    lean_closure_set(v___f_10877_, 6, v___f_10873_);
    lean_closure_set(v___f_10877_, 7, v___f_10873_);
    v___x_10878_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_10878_, 0, v___x_10872_);
    v___x_10879_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_10879_, 0, v___x_10878_);
    v___x_10880_ = lean_unsigned_to_nat(0);
    v___x_10881_ = 0;
    v___x_10882_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(
        v___x_10880_,
        v___x_10881_,
        v___x_10879_,
        v___f_10877_,
    );
    return v___x_10882_;
}
pub unsafe fn l_Std_Async_Async_race___boxed(
    mut v_00_u03b1_10883_: *mut LeanObject,
    mut v_inst_10884_: *mut LeanObject,
    mut v_x_10885_: *mut LeanObject,
    mut v_y_10886_: *mut LeanObject,
    mut v_prio_10887_: *mut LeanObject,
    mut v_a_10888_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10889_: *mut LeanObject = core::ptr::null_mut();
    v_res_10889_ = l_Std_Async_Async_race(
        v_00_u03b1_10883_,
        v_inst_10884_,
        v_x_10885_,
        v_y_10886_,
        v_prio_10887_,
    );
    lean_dec(v_inst_10884_);
    return v_res_10889_;
}
pub unsafe fn l_Std_Async_Async_concurrentlyAll___redArg___lam__1(
    mut v_prio_10890_: *mut LeanObject,
    mut v___f_10891_: *mut LeanObject,
    mut v_x_10892_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10897_: u8 = 0;
    let mut v___x_10898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10900_: *mut LeanObject = core::ptr::null_mut();
    v___x_10894_ = lean_alloc_closure(
        l_Std_Async_BaseAsync_toRawBaseIO___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___x_10894_, 0, lean_box(0));
    lean_closure_set(v___x_10894_, 1, v_x_10892_);
    v___x_10895_ = lean_io_as_task(v___x_10894_, v_prio_10890_);
    v___x_10896_ = lean_unsigned_to_nat(0);
    v___x_10897_ = 1;
    v___x_10898_ = lean_task_bind(v___x_10895_, v___f_10891_, v___x_10896_, v___x_10897_);
    v___x_10899_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_10899_, 0, v___x_10898_);
    v___x_10900_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_10900_, 0, v___x_10899_);
    return v___x_10900_;
}
pub unsafe fn l_Std_Async_Async_concurrentlyAll___redArg___lam__1___boxed(
    mut v_prio_10901_: *mut LeanObject,
    mut v___f_10902_: *mut LeanObject,
    mut v_x_10903_: *mut LeanObject,
    mut v___y_10904_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10905_: *mut LeanObject = core::ptr::null_mut();
    v_res_10905_ = l_Std_Async_Async_concurrentlyAll___redArg___lam__1(
        v_prio_10901_,
        v___f_10902_,
        v_x_10903_,
    );
    return v_res_10905_;
}
pub unsafe fn l_Std_Async_Async_concurrentlyAll___redArg___lam__0(
    mut v___x_10907_: *mut LeanObject,
    mut v_x_10908_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_10910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10913_: u8 = 0;
    let mut v___x_10915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10918_: u8 = 0;
    let mut v_a_10919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_10921_: usize = 0;
    let mut v___x_10922_: usize = 0;
    let mut v___x_269__overap_10923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10924_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_10908_) == 0 {
                    lean_dec_ref(v___x_10907_);
                    v_a_10910_ = lean_ctor_get(v_x_10908_, 0);
                    v_isSharedCheck_10918_ = (!lean_is_exclusive(v_x_10908_)) as u8;
                    if v_isSharedCheck_10918_ == 0 {
                        v___x_10912_ = v_x_10908_;
                        v_isShared_10913_ = v_isSharedCheck_10918_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_10910_);
                        lean_dec(v_x_10908_);
                        v___x_10912_ = lean_box(0);
                        v_isShared_10913_ = v_isSharedCheck_10918_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_10919_ = lean_ctor_get(v_x_10908_, 0);
                    lean_inc(v_a_10919_);
                    lean_dec_ref_known(v_x_10908_, 1);
                    v___x_10920_ = l_Std_Async_Async_concurrentlyAll___redArg___lam__0___closed__0;
                    v_sz_10921_ = lean_array_size(v_a_10919_);
                    v___x_10922_ = 0usize;
                    v___x_269__overap_10923_ =
                        l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                            lean_box(0),
                            lean_box(0),
                            lean_box(0),
                            v___x_10907_,
                            v___x_10920_,
                            v_sz_10921_,
                            v___x_10922_,
                            v_a_10919_,
                        );
                    v___x_10924_ = lean_apply_1(v___x_269__overap_10923_, lean_box(0));
                    return v___x_10924_;
                }
            }
            1 => {
                if v_isShared_10913_ == 0 {
                    v___x_10915_ = v___x_10912_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_10917_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10917_, 0, v_a_10910_);
                    v___x_10915_ = v_reuseFailAlloc_10917_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_10916_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_10916_, 0, v___x_10915_);
                return v___x_10916_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Async_concurrentlyAll___redArg___lam__0___boxed(
    mut v___x_10925_: *mut LeanObject,
    mut v_x_10926_: *mut LeanObject,
    mut v___y_10927_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10928_: *mut LeanObject = core::ptr::null_mut();
    v_res_10928_ = l_Std_Async_Async_concurrentlyAll___redArg___lam__0(v___x_10925_, v_x_10926_);
    return v_res_10928_;
}
pub unsafe fn _init_l_Std_Async_Async_concurrentlyAll___redArg___closed__0() -> *mut LeanObject {
    let mut v___x_10929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_10930_: *mut LeanObject = core::ptr::null_mut();
    v___x_10929_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_EAsync_concurrentlyAll___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Std_Async_EAsync_concurrentlyAll___redArg___closed__0_once),
        _init_l_Std_Async_EAsync_concurrentlyAll___redArg___closed__0,
    );
    v___f_10930_ = lean_alloc_closure(
        l_Std_Async_Async_concurrentlyAll___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_10930_, 0, v___x_10929_);
    return v___f_10930_;
}
pub unsafe fn l_Std_Async_Async_concurrentlyAll___redArg(
    mut v_xs_10931_: *mut LeanObject,
    mut v_prio_10932_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_10934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_10935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_10937_: usize = 0;
    let mut v___x_10938_: usize = 0;
    let mut v___x_204__overap_10939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_10941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10943_: u8 = 0;
    let mut v___x_10944_: *mut LeanObject = core::ptr::null_mut();
    v___f_10934_ = l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___closed__0;
    v___f_10935_ = lean_alloc_closure(
        l_Std_Async_Async_concurrentlyAll___redArg___lam__1___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_10935_, 0, v_prio_10932_);
    lean_closure_set(v___f_10935_, 1, v___f_10934_);
    v___x_10936_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_EAsync_concurrentlyAll___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Std_Async_EAsync_concurrentlyAll___redArg___closed__0_once),
        _init_l_Std_Async_EAsync_concurrentlyAll___redArg___closed__0,
    );
    v_sz_10937_ = lean_array_size(v_xs_10931_);
    v___x_10938_ = 0usize;
    v___x_204__overap_10939_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
        lean_box(0),
        lean_box(0),
        lean_box(0),
        v___x_10936_,
        v___f_10935_,
        v_sz_10937_,
        v___x_10938_,
        v_xs_10931_,
    );
    v___x_10940_ = lean_apply_1(v___x_204__overap_10939_, lean_box(0));
    v___f_10941_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_Async_concurrentlyAll___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Std_Async_Async_concurrentlyAll___redArg___closed__0_once),
        _init_l_Std_Async_Async_concurrentlyAll___redArg___closed__0,
    );
    v___x_10942_ = lean_unsigned_to_nat(0);
    v___x_10943_ = 0;
    v___x_10944_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(
        v___x_10942_,
        v___x_10943_,
        v___x_10940_,
        v___f_10941_,
    );
    return v___x_10944_;
}
pub unsafe fn l_Std_Async_Async_concurrentlyAll___redArg___boxed(
    mut v_xs_10945_: *mut LeanObject,
    mut v_prio_10946_: *mut LeanObject,
    mut v_a_10947_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10948_: *mut LeanObject = core::ptr::null_mut();
    v_res_10948_ = l_Std_Async_Async_concurrentlyAll___redArg(v_xs_10945_, v_prio_10946_);
    return v_res_10948_;
}
pub unsafe fn l_Std_Async_Async_concurrentlyAll(
    mut v_00_u03b1_10949_: *mut LeanObject,
    mut v_xs_10950_: *mut LeanObject,
    mut v_prio_10951_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_10953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_10954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_10956_: usize = 0;
    let mut v___x_10957_: usize = 0;
    let mut v___x_226__overap_10958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_10960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10962_: u8 = 0;
    let mut v___x_10963_: *mut LeanObject = core::ptr::null_mut();
    v___f_10953_ = l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___closed__0;
    v___f_10954_ = lean_alloc_closure(
        l_Std_Async_Async_concurrentlyAll___redArg___lam__1___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_10954_, 0, v_prio_10951_);
    lean_closure_set(v___f_10954_, 1, v___f_10953_);
    v___x_10955_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_EAsync_concurrentlyAll___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Std_Async_EAsync_concurrentlyAll___redArg___closed__0_once),
        _init_l_Std_Async_EAsync_concurrentlyAll___redArg___closed__0,
    );
    v_sz_10956_ = lean_array_size(v_xs_10950_);
    v___x_10957_ = 0usize;
    v___x_226__overap_10958_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
        lean_box(0),
        lean_box(0),
        lean_box(0),
        v___x_10955_,
        v___f_10954_,
        v_sz_10956_,
        v___x_10957_,
        v_xs_10950_,
    );
    v___x_10959_ = lean_apply_1(v___x_226__overap_10958_, lean_box(0));
    v___f_10960_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_Async_concurrentlyAll___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Std_Async_Async_concurrentlyAll___redArg___closed__0_once),
        _init_l_Std_Async_Async_concurrentlyAll___redArg___closed__0,
    );
    v___x_10961_ = lean_unsigned_to_nat(0);
    v___x_10962_ = 0;
    v___x_10963_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(
        v___x_10961_,
        v___x_10962_,
        v___x_10959_,
        v___f_10960_,
    );
    return v___x_10963_;
}
pub unsafe fn l_Std_Async_Async_concurrentlyAll___boxed(
    mut v_00_u03b1_10964_: *mut LeanObject,
    mut v_xs_10965_: *mut LeanObject,
    mut v_prio_10966_: *mut LeanObject,
    mut v_a_10967_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10968_: *mut LeanObject = core::ptr::null_mut();
    v_res_10968_ = l_Std_Async_Async_concurrentlyAll(v_00_u03b1_10964_, v_xs_10965_, v_prio_10966_);
    return v_res_10968_;
}
pub unsafe fn l_Std_Async_Async_raceAll___redArg___lam__4(
    mut v___f_10969_: *mut LeanObject,
    mut v___f_10970_: *mut LeanObject,
    mut v_x_10971_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_10973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10976_: u8 = 0;
    let mut v___x_10978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10981_: u8 = 0;
    let mut v_a_10982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10985_: u8 = 0;
    let mut v___x_10986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10989_: u8 = 0;
    let mut v___x_10990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10995_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_10971_) == 0 {
                    lean_dec_ref(v___f_10970_);
                    lean_dec(v___f_10969_);
                    v_a_10973_ = lean_ctor_get(v_x_10971_, 0);
                    v_isSharedCheck_10981_ = (!lean_is_exclusive(v_x_10971_)) as u8;
                    if v_isSharedCheck_10981_ == 0 {
                        v___x_10975_ = v_x_10971_;
                        v_isShared_10976_ = v_isSharedCheck_10981_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_10973_);
                        lean_dec(v_x_10971_);
                        v___x_10975_ = lean_box(0);
                        v_isShared_10976_ = v_isSharedCheck_10981_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_10982_ = lean_ctor_get(v_x_10971_, 0);
                    v_isSharedCheck_10995_ = (!lean_is_exclusive(v_x_10971_)) as u8;
                    if v_isSharedCheck_10995_ == 0 {
                        v___x_10984_ = v_x_10971_;
                        v_isShared_10985_ = v_isSharedCheck_10995_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_10982_);
                        lean_dec(v_x_10971_);
                        v___x_10984_ = lean_box(0);
                        v_isShared_10985_ = v_isSharedCheck_10995_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_10976_ == 0 {
                    v___x_10978_ = v___x_10975_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_10980_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10980_, 0, v_a_10973_);
                    v___x_10978_ = v_reuseFailAlloc_10980_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_10979_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_10979_, 0, v___x_10978_);
                return v___x_10979_;
            }
            3 => {
                v___x_10986_ = lean_alloc_closure(l_liftM as *mut core::ffi::c_void, 5, 4);
                lean_closure_set(v___x_10986_, 0, lean_box(0));
                lean_closure_set(v___x_10986_, 1, lean_box(0));
                lean_closure_set(v___x_10986_, 2, v___f_10969_);
                lean_closure_set(v___x_10986_, 3, lean_box(0));
                v___x_10987_ = lean_alloc_closure(l_Function_comp as *mut core::ffi::c_void, 6, 5);
                lean_closure_set(v___x_10987_, 0, lean_box(0));
                lean_closure_set(v___x_10987_, 1, lean_box(0));
                lean_closure_set(v___x_10987_, 2, lean_box(0));
                lean_closure_set(v___x_10987_, 3, v___x_10986_);
                lean_closure_set(v___x_10987_, 4, v___f_10970_);
                v___x_10988_ = lean_unsigned_to_nat(0);
                v___x_10989_ = 0;
                v___x_10990_ = l_BaseIO_chainTask___redArg(
                    v_a_10982_,
                    v___x_10987_,
                    v___x_10988_,
                    v___x_10989_,
                );
                if v_isShared_10985_ == 0 {
                    lean_ctor_set(v___x_10984_, 0, v___x_10990_);
                    v___x_10992_ = v___x_10984_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_10994_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10994_, 0, v___x_10990_);
                    v___x_10992_ = v_reuseFailAlloc_10994_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_10993_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_10993_, 0, v___x_10992_);
                return v___x_10993_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Async_raceAll___redArg___lam__4___boxed(
    mut v___f_10996_: *mut LeanObject,
    mut v___f_10997_: *mut LeanObject,
    mut v_x_10998_: *mut LeanObject,
    mut v___y_10999_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_11000_: *mut LeanObject = core::ptr::null_mut();
    v_res_11000_ =
        l_Std_Async_Async_raceAll___redArg___lam__4(v___f_10996_, v___f_10997_, v_x_10998_);
    return v_res_11000_;
}
pub unsafe fn l_Std_Async_Async_raceAll___redArg___lam__0(
    mut v_prio_11001_: *mut LeanObject,
    mut v___f_11002_: *mut LeanObject,
    mut v___f_11003_: *mut LeanObject,
    mut v_x_11004_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_11006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_11007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_11008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_11009_: u8 = 0;
    let mut v___x_11010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_11011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_11012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_11013_: u8 = 0;
    let mut v___x_11014_: *mut LeanObject = core::ptr::null_mut();
    v___x_11006_ = lean_alloc_closure(
        l_Std_Async_BaseAsync_toRawBaseIO___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___x_11006_, 0, lean_box(0));
    lean_closure_set(v___x_11006_, 1, v_x_11004_);
    v___x_11007_ = lean_io_as_task(v___x_11006_, v_prio_11001_);
    v___x_11008_ = lean_unsigned_to_nat(0);
    v___x_11009_ = 1;
    v___x_11010_ = lean_task_bind(v___x_11007_, v___f_11002_, v___x_11008_, v___x_11009_);
    v___x_11011_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_11011_, 0, v___x_11010_);
    v___x_11012_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_11012_, 0, v___x_11011_);
    v___x_11013_ = 0;
    v___x_11014_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(
        v___x_11008_,
        v___x_11013_,
        v___x_11012_,
        v___f_11003_,
    );
    return v___x_11014_;
}
pub unsafe fn l_Std_Async_Async_raceAll___redArg___lam__0___boxed(
    mut v_prio_11015_: *mut LeanObject,
    mut v___f_11016_: *mut LeanObject,
    mut v___f_11017_: *mut LeanObject,
    mut v_x_11018_: *mut LeanObject,
    mut v___y_11019_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_11020_: *mut LeanObject = core::ptr::null_mut();
    v_res_11020_ = l_Std_Async_Async_raceAll___redArg___lam__0(
        v_prio_11015_,
        v___f_11016_,
        v___f_11017_,
        v_x_11018_,
    );
    return v_res_11020_;
}
pub unsafe fn l_Std_Async_Async_raceAll___redArg___lam__2(
    mut v___f_11021_: *mut LeanObject,
    mut v_prio_11022_: *mut LeanObject,
    mut v___f_11023_: *mut LeanObject,
    mut v_inst_11024_: *mut LeanObject,
    mut v_xs_11025_: *mut LeanObject,
    mut v___f_11026_: *mut LeanObject,
    mut v___f_11027_: *mut LeanObject,
    mut v_x_11028_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_11030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_11032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_11033_: u8 = 0;
    let mut v___x_11035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_11036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_11037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_11038_: u8 = 0;
    let mut v_a_11039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_11040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_11041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_11042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_11043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_11044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_11045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_11046_: u8 = 0;
    let mut v___x_11047_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_11028_) == 0 {
                    lean_dec_ref(v___f_11027_);
                    lean_dec_ref(v___f_11026_);
                    lean_dec(v_xs_11025_);
                    lean_dec_ref(v_inst_11024_);
                    lean_dec_ref(v___f_11023_);
                    lean_dec(v_prio_11022_);
                    lean_dec(v___f_11021_);
                    v_a_11030_ = lean_ctor_get(v_x_11028_, 0);
                    v_isSharedCheck_11038_ = (!lean_is_exclusive(v_x_11028_)) as u8;
                    if v_isSharedCheck_11038_ == 0 {
                        v___x_11032_ = v_x_11028_;
                        v_isShared_11033_ = v_isSharedCheck_11038_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_11030_);
                        lean_dec(v_x_11028_);
                        v___x_11032_ = lean_box(0);
                        v_isShared_11033_ = v_isSharedCheck_11038_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_11039_ = lean_ctor_get(v_x_11028_, 0);
                    lean_inc_n(v_a_11039_, 2);
                    lean_dec_ref_known(v_x_11028_, 1);
                    v___f_11040_ = lean_alloc_closure(
                        l_Std_Async_Async_race___redArg___lam__3___boxed as *mut core::ffi::c_void,
                        3,
                        1,
                    );
                    lean_closure_set(v___f_11040_, 0, v_a_11039_);
                    v___f_11041_ = lean_alloc_closure(
                        l_Std_Async_Async_raceAll___redArg___lam__4___boxed
                            as *mut core::ffi::c_void,
                        4,
                        2,
                    );
                    lean_closure_set(v___f_11041_, 0, v___f_11021_);
                    lean_closure_set(v___f_11041_, 1, v___f_11040_);
                    v___f_11042_ = lean_alloc_closure(
                        l_Std_Async_Async_raceAll___redArg___lam__0___boxed
                            as *mut core::ffi::c_void,
                        5,
                        3,
                    );
                    lean_closure_set(v___f_11042_, 0, v_prio_11022_);
                    lean_closure_set(v___f_11042_, 1, v___f_11023_);
                    lean_closure_set(v___f_11042_, 2, v___f_11041_);
                    v___x_11043_ =
                        lean_apply_3(v_inst_11024_, v_xs_11025_, v___f_11042_, lean_box(0));
                    v___f_11044_ = lean_alloc_closure(
                        l_Std_Async_Async_race___redArg___lam__2___boxed as *mut core::ffi::c_void,
                        5,
                        3,
                    );
                    lean_closure_set(v___f_11044_, 0, v_a_11039_);
                    lean_closure_set(v___f_11044_, 1, v___f_11026_);
                    lean_closure_set(v___f_11044_, 2, v___f_11027_);
                    v___x_11045_ = lean_unsigned_to_nat(0);
                    v___x_11046_ = 0;
                    v___x_11047_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(v___x_11045_, v___x_11046_, v___x_11043_, v___f_11044_);
                    return v___x_11047_;
                }
            }
            1 => {
                if v_isShared_11033_ == 0 {
                    v___x_11035_ = v___x_11032_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_11037_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_11037_, 0, v_a_11030_);
                    v___x_11035_ = v_reuseFailAlloc_11037_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_11036_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_11036_, 0, v___x_11035_);
                return v___x_11036_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Async_raceAll___redArg___lam__2___boxed(
    mut v___f_11048_: *mut LeanObject,
    mut v_prio_11049_: *mut LeanObject,
    mut v___f_11050_: *mut LeanObject,
    mut v_inst_11051_: *mut LeanObject,
    mut v_xs_11052_: *mut LeanObject,
    mut v___f_11053_: *mut LeanObject,
    mut v___f_11054_: *mut LeanObject,
    mut v_x_11055_: *mut LeanObject,
    mut v___y_11056_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_11057_: *mut LeanObject = core::ptr::null_mut();
    v_res_11057_ = l_Std_Async_Async_raceAll___redArg___lam__2(
        v___f_11048_,
        v_prio_11049_,
        v___f_11050_,
        v_inst_11051_,
        v_xs_11052_,
        v___f_11053_,
        v___f_11054_,
        v_x_11055_,
    );
    return v_res_11057_;
}
pub unsafe fn l_Std_Async_Async_raceAll___redArg(
    mut v_inst_11058_: *mut LeanObject,
    mut v_xs_11059_: *mut LeanObject,
    mut v_prio_11060_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_11062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_11063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_11064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_11065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_11066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_11067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_11068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_11069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_11070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_11071_: u8 = 0;
    let mut v___x_11072_: *mut LeanObject = core::ptr::null_mut();
    v___x_11062_ = lean_io_promise_new();
    v___f_11063_ = l_Std_Async_Async_race___redArg___closed__1;
    v___f_11064_ = l_Std_Async_Async_race___redArg___closed__0;
    v___f_11065_ = l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___closed__0;
    v___f_11066_ = l_Std_Async_BaseAsync_race___redArg___closed__0;
    v___f_11067_ = lean_alloc_closure(
        l_Std_Async_Async_raceAll___redArg___lam__2___boxed as *mut core::ffi::c_void,
        9,
        7,
    );
    lean_closure_set(v___f_11067_, 0, v___f_11066_);
    lean_closure_set(v___f_11067_, 1, v_prio_11060_);
    lean_closure_set(v___f_11067_, 2, v___f_11065_);
    lean_closure_set(v___f_11067_, 3, v_inst_11058_);
    lean_closure_set(v___f_11067_, 4, v_xs_11059_);
    lean_closure_set(v___f_11067_, 5, v___f_11063_);
    lean_closure_set(v___f_11067_, 6, v___f_11064_);
    v___x_11068_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_11068_, 0, v___x_11062_);
    v___x_11069_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_11069_, 0, v___x_11068_);
    v___x_11070_ = lean_unsigned_to_nat(0);
    v___x_11071_ = 0;
    v___x_11072_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(
        v___x_11070_,
        v___x_11071_,
        v___x_11069_,
        v___f_11067_,
    );
    return v___x_11072_;
}
pub unsafe fn l_Std_Async_Async_raceAll___redArg___boxed(
    mut v_inst_11073_: *mut LeanObject,
    mut v_xs_11074_: *mut LeanObject,
    mut v_prio_11075_: *mut LeanObject,
    mut v_a_11076_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_11077_: *mut LeanObject = core::ptr::null_mut();
    v_res_11077_ = l_Std_Async_Async_raceAll___redArg(v_inst_11073_, v_xs_11074_, v_prio_11075_);
    return v_res_11077_;
}
pub unsafe fn l_Std_Async_Async_raceAll(
    mut v_c_11078_: *mut LeanObject,
    mut v_00_u03b1_11079_: *mut LeanObject,
    mut v_inst_11080_: *mut LeanObject,
    mut v_xs_11081_: *mut LeanObject,
    mut v_prio_11082_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_11084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_11085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_11086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_11087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_11088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_11089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_11090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_11091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_11092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_11093_: u8 = 0;
    let mut v___x_11094_: *mut LeanObject = core::ptr::null_mut();
    v___x_11084_ = lean_io_promise_new();
    v___f_11085_ = l_Std_Async_Async_race___redArg___closed__1;
    v___f_11086_ = l_Std_Async_Async_race___redArg___closed__0;
    v___f_11087_ = l_Std_Async_EAsync_instMonadAsyncAsyncTaskError___closed__0;
    v___f_11088_ = l_Std_Async_BaseAsync_race___redArg___closed__0;
    v___f_11089_ = lean_alloc_closure(
        l_Std_Async_Async_raceAll___redArg___lam__2___boxed as *mut core::ffi::c_void,
        9,
        7,
    );
    lean_closure_set(v___f_11089_, 0, v___f_11088_);
    lean_closure_set(v___f_11089_, 1, v_prio_11082_);
    lean_closure_set(v___f_11089_, 2, v___f_11087_);
    lean_closure_set(v___f_11089_, 3, v_inst_11080_);
    lean_closure_set(v___f_11089_, 4, v_xs_11081_);
    lean_closure_set(v___f_11089_, 5, v___f_11085_);
    lean_closure_set(v___f_11089_, 6, v___f_11086_);
    v___x_11090_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_11090_, 0, v___x_11084_);
    v___x_11091_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_11091_, 0, v___x_11090_);
    v___x_11092_ = lean_unsigned_to_nat(0);
    v___x_11093_ = 0;
    v___x_11094_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask___redArg(
        v___x_11092_,
        v___x_11093_,
        v___x_11091_,
        v___f_11089_,
    );
    return v___x_11094_;
}
pub unsafe fn l_Std_Async_Async_raceAll___boxed(
    mut v_c_11095_: *mut LeanObject,
    mut v_00_u03b1_11096_: *mut LeanObject,
    mut v_inst_11097_: *mut LeanObject,
    mut v_xs_11098_: *mut LeanObject,
    mut v_prio_11099_: *mut LeanObject,
    mut v_a_11100_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_11101_: *mut LeanObject = core::ptr::null_mut();
    v_res_11101_ = l_Std_Async_Async_raceAll(
        v_c_11095_,
        v_00_u03b1_11096_,
        v_inst_11097_,
        v_xs_11098_,
        v_prio_11099_,
    );
    return v_res_11101_;
}
pub unsafe fn l_Std_Async_background___redArg(
    mut v_inst_11102_: *mut LeanObject,
    mut v_inst_11103_: *mut LeanObject,
    mut v_action_11104_: *mut LeanObject,
    mut v_prio_11105_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_11106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_11107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mapConst_11108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_11109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_11110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_11111_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_11106_ = lean_ctor_get(v_inst_11102_, 0);
    lean_inc_ref(v_toApplicative_11106_);
    lean_dec_ref(v_inst_11102_);
    v_toFunctor_11107_ = lean_ctor_get(v_toApplicative_11106_, 0);
    lean_inc_ref(v_toFunctor_11107_);
    lean_dec_ref(v_toApplicative_11106_);
    v_mapConst_11108_ = lean_ctor_get(v_toFunctor_11107_, 1);
    lean_inc(v_mapConst_11108_);
    lean_dec_ref(v_toFunctor_11107_);
    v___x_11109_ = lean_apply_3(v_inst_11103_, lean_box(0), v_action_11104_, v_prio_11105_);
    v___x_11110_ = lean_box(0);
    v___x_11111_ = lean_apply_4(
        v_mapConst_11108_,
        lean_box(0),
        lean_box(0),
        v___x_11110_,
        v___x_11109_,
    );
    return v___x_11111_;
}
pub unsafe fn l_Std_Async_background(
    mut v_m_11112_: *mut LeanObject,
    mut v_t_11113_: *mut LeanObject,
    mut v_00_u03b1_11114_: *mut LeanObject,
    mut v_inst_11115_: *mut LeanObject,
    mut v_inst_11116_: *mut LeanObject,
    mut v_action_11117_: *mut LeanObject,
    mut v_prio_11118_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_11119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_11120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mapConst_11121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_11122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_11123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_11124_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_11119_ = lean_ctor_get(v_inst_11115_, 0);
    lean_inc_ref(v_toApplicative_11119_);
    lean_dec_ref(v_inst_11115_);
    v_toFunctor_11120_ = lean_ctor_get(v_toApplicative_11119_, 0);
    lean_inc_ref(v_toFunctor_11120_);
    lean_dec_ref(v_toApplicative_11119_);
    v_mapConst_11121_ = lean_ctor_get(v_toFunctor_11120_, 1);
    lean_inc(v_mapConst_11121_);
    lean_dec_ref(v_toFunctor_11120_);
    v___x_11122_ = lean_apply_3(v_inst_11116_, lean_box(0), v_action_11117_, v_prio_11118_);
    v___x_11123_ = lean_box(0);
    v___x_11124_ = lean_apply_4(
        v_mapConst_11121_,
        lean_box(0),
        lean_box(0),
        v___x_11123_,
        v___x_11122_,
    );
    return v___x_11124_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Async_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_System_Promise(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_While(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Async_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Async_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_System_Promise(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_While(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Async_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Async_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Async_Basic(builtin);
}
