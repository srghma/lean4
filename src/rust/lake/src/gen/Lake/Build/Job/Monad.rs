// Lean compiler output
// Module: Lake.Build.Job.Monad
// Imports: Lake.Build.Fetch
use crate::r#gen::Init::Control::StateRef::{
    l_StateRefT_x27_instMonad___redArg, l_StateRefT_x27_lift___boxed,
};
use crate::r#gen::Init::Data::Array::Basic::l_Array_shrink___redArg;
use crate::r#gen::Init::Data::Nat::Fold::l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop;
use crate::r#gen::Init::Data::String::Slice::{l_String_Slice_toString, l_String_Slice_trimAscii};
use crate::r#gen::Init::Prelude::{
    l_ByteArray_empty, l_ReaderT_instMonad___redArg, l_ReaderT_instMonadLift___lam__0___boxed,
    l_instMonadStateOfOfMonadLift___redArg___lam__0,
    l_instMonadStateOfOfMonadLift___redArg___lam__1,
};
use crate::r#gen::Init::System::IO::{
    l_IO_FS_Stream_ofBuffer, l_instMonadBaseIO, l_instMonadBaseIO___aux__5___boxed,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lake::Build::Data::l_Lake_instDataKindUnit;
use crate::r#gen::Lake::Build::Fetch::{
    initialize_Lake_Build_Fetch, runtime_initialize_Lake_Build_Fetch,
};
use crate::r#gen::Lake::Build::Job::Basic::{l_Lake_JobAction_merge, l_Lake_JobState_merge};
use crate::r#gen::Lake::Build::Trace::{l_Lake_BuildTrace_mix, l_Lake_BuildTrace_nil};
use crate::r#gen::Lake::Util::EStateT::{
    l_Lake_EStateT_instFunctor___redArg, l_Lake_EStateT_instMonad___redArg___lam__1,
    l_Lake_EStateT_instMonad___redArg___lam__3, l_Lake_EStateT_instMonad___redArg___lam__5,
    l_Lake_EStateT_instMonad___redArg___lam__9, l_Lake_EStateT_instMonadStateOfOfPure___redArg,
    l_Lake_EStateT_instPure___redArg___lam__0,
};
use crate::r#gen::Lake::Util::EquipT::{
    l_Lake_EquipT_instMonad___redArg, l_Lake_EquipT_lift___boxed,
};
use crate::r#gen::Lake::Util::Log::l_Lake_pushLogEntry;
use crate::ffi::{lean_task_bind, lean_task_map, lean_task_pure};
use crate::ffi::{
    lean_array_uget, lean_array_uget_borrowed, lean_mk_array,
};
use crate::ffi::lean_array_fset;
use crate::ffi::lean_string_validate_utf8;
use crate::ffi::lean_string_append;
use crate::ffi::{
    lean_usize_add, lean_usize_of_nat, lean_usize_sub,
};
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_get_size, lean_array_mk, lean_array_push,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_panic_fn_borrowed, lean_string_from_utf8_unchecked,
    lean_string_utf8_byte_size, lean_usize_dec_eq,
};
use crate::ffi::{
    lean_get_set_stderr, lean_get_set_stdout, lean_io_as_task, lean_io_bind_task, lean_io_map_task,
    lean_io_wait,
};
use crate::ffi::{lean_st_mk_ref, lean_st_ref_get};
pub static l_Lake_instMonadStateOfJobStateJobM___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_instMonadBaseIO___aux__5___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instMonadStateOfJobStateJobM___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadStateOfJobStateJobM___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_instMonadStateOfJobStateJobM___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instMonadStateOfJobStateJobM___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instMonadStateOfJobStateJobM___closed__2_value: crate::leanh::LeanClosureObject<
    2,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_EquipT_lift___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 2,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_instMonadStateOfJobStateJobM___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadStateOfJobStateJobM___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instMonadStateOfJobStateJobM___closed__3_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_ReaderT_instMonadLift___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instMonadStateOfJobStateJobM___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadStateOfJobStateJobM___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instMonadStateOfJobStateJobM___closed__4_value: crate::leanh::LeanClosureObject<
    3,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_StateRefT_x27_lift___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 3,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_instMonadStateOfJobStateJobM___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadStateOfJobStateJobM___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instMonadStateOfJobStateJobM: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instMonadStateOfLogJobM___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instMonadStateOfLogJobM___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instMonadStateOfLogJobM___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadStateOfLogJobM___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instMonadStateOfLogJobM___closed__1_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instMonadStateOfLogJobM___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 8,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instMonadStateOfLogJobM___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadStateOfLogJobM___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instMonadStateOfLogJobM___closed__2_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instMonadStateOfLogJobM___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 9,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instMonadStateOfLogJobM___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadStateOfLogJobM___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instMonadStateOfLogJobM___closed__3_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instMonadStateOfLogJobM___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_instMonadStateOfLogJobM___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_instMonadStateOfLogJobM___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instMonadStateOfLogJobM___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadStateOfLogJobM___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instMonadStateOfLogJobM: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadStateOfLogJobM___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instMonadLogJobM___closed__0_value: crate::leanh::LeanClosureObject<2> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_pushLogEntry as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 2,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_instMonadStateOfLogJobM___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instMonadLogJobM___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadLogJobM___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instMonadLogJobM: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadLogJobM___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_instMonadErrorJobM___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instMonadErrorJobM___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 9,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instMonadErrorJobM___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadErrorJobM___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instMonadErrorJobM: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadErrorJobM___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instAlternativeJobM___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instAlternativeJobM___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 8,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instAlternativeJobM___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instAlternativeJobM___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instAlternativeJobM___closed__1_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instAlternativeJobM___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 10,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instAlternativeJobM___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instAlternativeJobM___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instAlternativeJobM: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_instMonadLiftLogIOJobM___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instMonadLiftLogIOJobM___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 9,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instMonadLiftLogIOJobM___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadLiftLogIOJobM___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instMonadLiftLogIOJobM: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadLiftLogIOJobM___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_takeTrace___redArg___closed__0_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [60, 110, 105, 108, 62, 0],
    };
static mut l_Lake_takeTrace___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_takeTrace___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_takeTrace___redArg___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_takeTrace___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instMonadLiftSpawnMJobM___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_JobM_runSpawnM___boxed as *const core::ffi::c_void,
        m_arity: 9,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instMonadLiftSpawnMJobM___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadLiftSpawnMJobM___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instMonadLiftSpawnMJobM: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadLiftSpawnMJobM___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instMonadLiftJobMFetchM___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_FetchM_runJobM___boxed as *const core::ffi::c_void,
        m_arity: 9,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instMonadLiftJobMFetchM___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadLiftJobMFetchM___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instMonadLiftJobMFetchM: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadLiftJobMFetchM___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instMonadLiftFetchMJobM___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_JobM_runFetchM___boxed as *const core::ffi::c_void,
        m_arity: 9,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instMonadLiftFetchMJobM___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadLiftFetchMJobM___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instMonadLiftFetchMJobM: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadLiftFetchMJobM___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lake_Job_sync_spec__0___closed__0_value:
    crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 1,
    m_capacity: 1,
    m_length: 0,
    m_data: [0],
};
static mut l_panic___at___00Lake_Job_sync_spec__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_panic___at___00Lake_Job_sync_spec__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_Job_sync___redArg___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Job_sync___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_Job_sync___redArg___closed__1_value: crate::leanh::LeanArrayObject<0> =
    crate::leanh::LeanArrayObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lake_Job_sync___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Job_sync___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_Job_sync___redArg___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Job_sync___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_Job_sync___redArg___closed__3_value: crate::leanh::LeanStringObject<16> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 16,
        m_capacity: 16,
        m_length: 15,
        m_data: [
            115, 116, 100, 111, 117, 116, 47, 115, 116, 100, 101, 114, 114, 58, 10, 0,
        ],
    };
static mut l_Lake_Job_sync___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Job_sync___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Job_sync___redArg___closed__4_value: crate::leanh::LeanStringObject<23> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 23,
        m_capacity: 23,
        m_length: 22,
        m_data: [
            73, 110, 105, 116, 46, 68, 97, 116, 97, 46, 83, 116, 114, 105, 110, 103, 46, 66, 97,
            115, 105, 99, 0,
        ],
    };
static mut l_Lake_Job_sync___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Job_sync___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Job_sync___redArg___closed__5_value: crate::leanh::LeanStringObject<17> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 17,
        m_capacity: 17,
        m_length: 16,
        m_data: [
            83, 116, 114, 105, 110, 103, 46, 102, 114, 111, 109, 85, 84, 70, 56, 33, 0,
        ],
    };
static mut l_Lake_Job_sync___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Job_sync___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Job_sync___redArg___closed__6_value: crate::leanh::LeanStringObject<21> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 21,
        m_capacity: 21,
        m_length: 20,
        m_data: [
            105, 110, 118, 97, 108, 105, 100, 32, 85, 84, 70, 45, 56, 32, 115, 116, 114, 105, 110,
            103, 0,
        ],
    };
static mut l_Lake_Job_sync___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Job_sync___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_Job_sync___redArg___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Job_sync___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lake_JobM_ofFn___redArg(
    mut v_f_3124_: *mut crate::leanh::LeanObject,
    mut v_a_3125_: *mut crate::leanh::LeanObject,
    mut v_a_3126_: *mut crate::leanh::LeanObject,
    mut v_a_3127_: *mut crate::leanh::LeanObject,
    mut v_a_3128_: *mut crate::leanh::LeanObject,
    mut v_a_3129_: *mut crate::leanh::LeanObject,
    mut v_a_3130_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_a_3129_);
    crate::leanh::lean_inc(v_a_3128_);
    crate::leanh::lean_inc(v_a_3127_);
    crate::leanh::lean_inc(v_a_3126_);
    v___x_3132_ = crate::leanh::lean_apply_7(
        v_f_3124_,
        v_a_3125_,
        v_a_3126_,
        v_a_3127_,
        v_a_3128_,
        v_a_3129_,
        v_a_3130_,
        crate::leanh::lean_box(0),
    );
    return v___x_3132_;
}
pub unsafe fn l_Lake_JobM_ofFn___redArg___boxed(
    mut v_f_3133_: *mut crate::leanh::LeanObject,
    mut v_a_3134_: *mut crate::leanh::LeanObject,
    mut v_a_3135_: *mut crate::leanh::LeanObject,
    mut v_a_3136_: *mut crate::leanh::LeanObject,
    mut v_a_3137_: *mut crate::leanh::LeanObject,
    mut v_a_3138_: *mut crate::leanh::LeanObject,
    mut v_a_3139_: *mut crate::leanh::LeanObject,
    mut v_a_3140_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3141_ = l_Lake_JobM_ofFn___redArg(
        v_f_3133_, v_a_3134_, v_a_3135_, v_a_3136_, v_a_3137_, v_a_3138_, v_a_3139_,
    );
    crate::leanh::lean_dec_ref(v_a_3138_);
    crate::leanh::lean_dec(v_a_3137_);
    crate::leanh::lean_dec(v_a_3136_);
    crate::leanh::lean_dec(v_a_3135_);
    return v_res_3141_;
}
pub unsafe fn l_Lake_JobM_ofFn(
    mut v_00_u03b1_3142_: *mut crate::leanh::LeanObject,
    mut v_f_3143_: *mut crate::leanh::LeanObject,
    mut v_a_3144_: *mut crate::leanh::LeanObject,
    mut v_a_3145_: *mut crate::leanh::LeanObject,
    mut v_a_3146_: *mut crate::leanh::LeanObject,
    mut v_a_3147_: *mut crate::leanh::LeanObject,
    mut v_a_3148_: *mut crate::leanh::LeanObject,
    mut v_a_3149_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_a_3148_);
    crate::leanh::lean_inc(v_a_3147_);
    crate::leanh::lean_inc(v_a_3146_);
    crate::leanh::lean_inc(v_a_3145_);
    v___x_3151_ = crate::leanh::lean_apply_7(
        v_f_3143_,
        v_a_3144_,
        v_a_3145_,
        v_a_3146_,
        v_a_3147_,
        v_a_3148_,
        v_a_3149_,
        crate::leanh::lean_box(0),
    );
    return v___x_3151_;
}
pub unsafe fn l_Lake_JobM_ofFn___boxed(
    mut v_00_u03b1_3152_: *mut crate::leanh::LeanObject,
    mut v_f_3153_: *mut crate::leanh::LeanObject,
    mut v_a_3154_: *mut crate::leanh::LeanObject,
    mut v_a_3155_: *mut crate::leanh::LeanObject,
    mut v_a_3156_: *mut crate::leanh::LeanObject,
    mut v_a_3157_: *mut crate::leanh::LeanObject,
    mut v_a_3158_: *mut crate::leanh::LeanObject,
    mut v_a_3159_: *mut crate::leanh::LeanObject,
    mut v_a_3160_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3161_ = l_Lake_JobM_ofFn(
        v_00_u03b1_3152_,
        v_f_3153_,
        v_a_3154_,
        v_a_3155_,
        v_a_3156_,
        v_a_3157_,
        v_a_3158_,
        v_a_3159_,
    );
    crate::leanh::lean_dec_ref(v_a_3158_);
    crate::leanh::lean_dec(v_a_3157_);
    crate::leanh::lean_dec(v_a_3156_);
    crate::leanh::lean_dec(v_a_3155_);
    return v_res_3161_;
}
pub unsafe fn l_Lake_JobM_toFn___redArg(
    mut v_self_3162_: *mut crate::leanh::LeanObject,
    mut v_fetch_3163_: *mut crate::leanh::LeanObject,
    mut v_pkg_x3f_3164_: *mut crate::leanh::LeanObject,
    mut v_stack_3165_: *mut crate::leanh::LeanObject,
    mut v_store_3166_: *mut crate::leanh::LeanObject,
    mut v_ctx_3167_: *mut crate::leanh::LeanObject,
    mut v_s_3168_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3170_ = crate::leanh::lean_apply_7(
        v_self_3162_,
        v_fetch_3163_,
        v_pkg_x3f_3164_,
        v_stack_3165_,
        v_store_3166_,
        v_ctx_3167_,
        v_s_3168_,
        crate::leanh::lean_box(0),
    );
    return v___x_3170_;
}
pub unsafe fn l_Lake_JobM_toFn___redArg___boxed(
    mut v_self_3171_: *mut crate::leanh::LeanObject,
    mut v_fetch_3172_: *mut crate::leanh::LeanObject,
    mut v_pkg_x3f_3173_: *mut crate::leanh::LeanObject,
    mut v_stack_3174_: *mut crate::leanh::LeanObject,
    mut v_store_3175_: *mut crate::leanh::LeanObject,
    mut v_ctx_3176_: *mut crate::leanh::LeanObject,
    mut v_s_3177_: *mut crate::leanh::LeanObject,
    mut v_a_3178_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3179_ = l_Lake_JobM_toFn___redArg(
        v_self_3171_,
        v_fetch_3172_,
        v_pkg_x3f_3173_,
        v_stack_3174_,
        v_store_3175_,
        v_ctx_3176_,
        v_s_3177_,
    );
    return v_res_3179_;
}
pub unsafe fn l_Lake_JobM_toFn(
    mut v_00_u03b1_3180_: *mut crate::leanh::LeanObject,
    mut v_self_3181_: *mut crate::leanh::LeanObject,
    mut v_fetch_3182_: *mut crate::leanh::LeanObject,
    mut v_pkg_x3f_3183_: *mut crate::leanh::LeanObject,
    mut v_stack_3184_: *mut crate::leanh::LeanObject,
    mut v_store_3185_: *mut crate::leanh::LeanObject,
    mut v_ctx_3186_: *mut crate::leanh::LeanObject,
    mut v_s_3187_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3189_ = crate::leanh::lean_apply_7(
        v_self_3181_,
        v_fetch_3182_,
        v_pkg_x3f_3183_,
        v_stack_3184_,
        v_store_3185_,
        v_ctx_3186_,
        v_s_3187_,
        crate::leanh::lean_box(0),
    );
    return v___x_3189_;
}
pub unsafe fn l_Lake_JobM_toFn___boxed(
    mut v_00_u03b1_3190_: *mut crate::leanh::LeanObject,
    mut v_self_3191_: *mut crate::leanh::LeanObject,
    mut v_fetch_3192_: *mut crate::leanh::LeanObject,
    mut v_pkg_x3f_3193_: *mut crate::leanh::LeanObject,
    mut v_stack_3194_: *mut crate::leanh::LeanObject,
    mut v_store_3195_: *mut crate::leanh::LeanObject,
    mut v_ctx_3196_: *mut crate::leanh::LeanObject,
    mut v_s_3197_: *mut crate::leanh::LeanObject,
    mut v_a_3198_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3199_ = l_Lake_JobM_toFn(
        v_00_u03b1_3190_,
        v_self_3191_,
        v_fetch_3192_,
        v_pkg_x3f_3193_,
        v_stack_3194_,
        v_store_3195_,
        v_ctx_3196_,
        v_s_3197_,
    );
    return v_res_3199_;
}
pub unsafe fn _init_l_Lake_instMonadStateOfJobStateJobM___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3201_ = l_Lake_instMonadStateOfJobStateJobM___closed__0;
    v___x_3202_ = l_Lake_EStateT_instMonadStateOfOfPure___redArg(v___x_3201_);
    return v___x_3202_;
}
pub unsafe fn _init_l_Lake_instMonadStateOfJobStateJobM() -> *mut crate::leanh::LeanObject {
    let mut v___x_3206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_get_3207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_set_3208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyGet_3209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3206_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instMonadStateOfJobStateJobM___closed__1),
        core::ptr::addr_of_mut!(l_Lake_instMonadStateOfJobStateJobM___closed__1_once),
        _init_l_Lake_instMonadStateOfJobStateJobM___closed__1,
    );
    v_get_3207_ = crate::leanh::lean_ctor_get(v___x_3206_, 0);
    v_set_3208_ = crate::leanh::lean_ctor_get(v___x_3206_, 1);
    v_modifyGet_3209_ = crate::leanh::lean_ctor_get(v___x_3206_, 2);
    v___x_3210_ = l_Lake_instMonadStateOfJobStateJobM___closed__2;
    v___f_3211_ = l_Lake_instMonadStateOfJobStateJobM___closed__3;
    v___x_3212_ = l_Lake_instMonadStateOfJobStateJobM___closed__4;
    crate::leanh::lean_inc(v_set_3208_);
    v___f_3213_ = crate::leanh::lean_alloc_closure(
        l_instMonadStateOfOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3213_, 0, v_set_3208_);
    crate::leanh::lean_closure_set(v___f_3213_, 1, v___f_3211_);
    crate::leanh::lean_inc(v_modifyGet_3209_);
    v___f_3214_ = crate::leanh::lean_alloc_closure(
        l_instMonadStateOfOfMonadLift___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3214_, 0, v_modifyGet_3209_);
    crate::leanh::lean_closure_set(v___f_3214_, 1, v___f_3211_);
    crate::leanh::lean_inc(v_get_3207_);
    v___x_3215_ = crate::leanh::lean_alloc_closure(
        l_ReaderT_instMonadLift___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___x_3215_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3215_, 1, v_get_3207_);
    v___f_3216_ = crate::leanh::lean_alloc_closure(
        l_instMonadStateOfOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3216_, 0, v___f_3213_);
    crate::leanh::lean_closure_set(v___f_3216_, 1, v___x_3212_);
    v___f_3217_ = crate::leanh::lean_alloc_closure(
        l_instMonadStateOfOfMonadLift___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3217_, 0, v___f_3214_);
    crate::leanh::lean_closure_set(v___f_3217_, 1, v___x_3212_);
    v___x_3218_ = crate::leanh::lean_alloc_closure(
        l_StateRefT_x27_lift___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___x_3218_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3218_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3218_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3218_, 3, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3218_, 4, v___x_3215_);
    v___f_3219_ = crate::leanh::lean_alloc_closure(
        l_instMonadStateOfOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3219_, 0, v___f_3216_);
    crate::leanh::lean_closure_set(v___f_3219_, 1, v___f_3211_);
    v___f_3220_ = crate::leanh::lean_alloc_closure(
        l_instMonadStateOfOfMonadLift___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3220_, 0, v___f_3217_);
    crate::leanh::lean_closure_set(v___f_3220_, 1, v___f_3211_);
    v___x_3221_ = crate::leanh::lean_alloc_closure(
        l_ReaderT_instMonadLift___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___x_3221_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3221_, 1, v___x_3218_);
    v___f_3222_ = crate::leanh::lean_alloc_closure(
        l_instMonadStateOfOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3222_, 0, v___f_3219_);
    crate::leanh::lean_closure_set(v___f_3222_, 1, v___f_3211_);
    v___f_3223_ = crate::leanh::lean_alloc_closure(
        l_instMonadStateOfOfMonadLift___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3223_, 0, v___f_3220_);
    crate::leanh::lean_closure_set(v___f_3223_, 1, v___f_3211_);
    v___x_3224_ = crate::leanh::lean_alloc_closure(
        l_ReaderT_instMonadLift___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___x_3224_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3224_, 1, v___x_3221_);
    v___f_3225_ = crate::leanh::lean_alloc_closure(
        l_instMonadStateOfOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3225_, 0, v___f_3222_);
    crate::leanh::lean_closure_set(v___f_3225_, 1, v___x_3210_);
    v___f_3226_ = crate::leanh::lean_alloc_closure(
        l_instMonadStateOfOfMonadLift___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3226_, 0, v___f_3223_);
    crate::leanh::lean_closure_set(v___f_3226_, 1, v___x_3210_);
    v___x_3227_ = crate::leanh::lean_alloc_closure(
        l_Lake_EquipT_lift___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___x_3227_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3227_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3227_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3227_, 3, v___x_3224_);
    v___x_3228_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3228_, 0, v___x_3227_);
    crate::leanh::lean_ctor_set(v___x_3228_, 1, v___f_3225_);
    crate::leanh::lean_ctor_set(v___x_3228_, 2, v___f_3226_);
    return v___x_3228_;
}
pub unsafe fn l_Lake_instMonadStateOfLogJobM___lam__0(
    mut v___y_3229_: *mut crate::leanh::LeanObject,
    mut v___y_3230_: *mut crate::leanh::LeanObject,
    mut v___y_3231_: *mut crate::leanh::LeanObject,
    mut v___y_3232_: *mut crate::leanh::LeanObject,
    mut v___y_3233_: *mut crate::leanh::LeanObject,
    mut v___y_3234_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_log_3236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_log_3236_ = crate::leanh::lean_ctor_get(v___y_3234_, 0);
    crate::leanh::lean_inc_ref(v_log_3236_);
    v___x_3237_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3237_, 0, v_log_3236_);
    crate::leanh::lean_ctor_set(v___x_3237_, 1, v___y_3234_);
    return v___x_3237_;
}
pub unsafe fn l_Lake_instMonadStateOfLogJobM___lam__0___boxed(
    mut v___y_3238_: *mut crate::leanh::LeanObject,
    mut v___y_3239_: *mut crate::leanh::LeanObject,
    mut v___y_3240_: *mut crate::leanh::LeanObject,
    mut v___y_3241_: *mut crate::leanh::LeanObject,
    mut v___y_3242_: *mut crate::leanh::LeanObject,
    mut v___y_3243_: *mut crate::leanh::LeanObject,
    mut v___y_3244_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3245_ = l_Lake_instMonadStateOfLogJobM___lam__0(
        v___y_3238_,
        v___y_3239_,
        v___y_3240_,
        v___y_3241_,
        v___y_3242_,
        v___y_3243_,
    );
    crate::leanh::lean_dec_ref(v___y_3242_);
    crate::leanh::lean_dec(v___y_3241_);
    crate::leanh::lean_dec(v___y_3240_);
    crate::leanh::lean_dec(v___y_3239_);
    crate::leanh::lean_dec_ref(v___y_3238_);
    return v_res_3245_;
}
pub unsafe fn l_Lake_instMonadStateOfLogJobM___lam__1(
    mut v_log_3246_: *mut crate::leanh::LeanObject,
    mut v___y_3247_: *mut crate::leanh::LeanObject,
    mut v___y_3248_: *mut crate::leanh::LeanObject,
    mut v___y_3249_: *mut crate::leanh::LeanObject,
    mut v___y_3250_: *mut crate::leanh::LeanObject,
    mut v___y_3251_: *mut crate::leanh::LeanObject,
    mut v___y_3252_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_action_3254_: u8 = 0;
    let mut v_wantsRebuild_3255_: u8 = 0;
    let mut v_trace_3256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildTime_3257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3260_: u8 = 0;
    let mut v___x_3261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3266_: u8 = 0;
    let mut v_unused_3267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_action_3254_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_3252_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_wantsRebuild_3255_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_3252_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                );
                v_trace_3256_ = crate::leanh::lean_ctor_get(v___y_3252_, 1);
                v_buildTime_3257_ = crate::leanh::lean_ctor_get(v___y_3252_, 2);
                v_isSharedCheck_3266_ = (!crate::leanh::lean_is_exclusive(v___y_3252_)) as u8;
                if v_isSharedCheck_3266_ == 0 {
                    v_unused_3267_ = crate::leanh::lean_ctor_get(v___y_3252_, 0);
                    crate::leanh::lean_dec(v_unused_3267_);
                    v___x_3259_ = v___y_3252_;
                    v_isShared_3260_ = v_isSharedCheck_3266_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buildTime_3257_);
                    crate::leanh::lean_inc(v_trace_3256_);
                    crate::leanh::lean_dec(v___y_3252_);
                    v___x_3259_ = crate::leanh::lean_box(0);
                    v_isShared_3260_ = v_isSharedCheck_3266_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3261_ = crate::leanh::lean_box(0);
                if v_isShared_3260_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3259_, 0, v_log_3246_);
                    v___x_3263_ = v___x_3259_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3265_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3265_, 0, v_log_3246_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3265_, 1, v_trace_3256_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3265_, 2, v_buildTime_3257_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3265_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_action_3254_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3265_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_3255_,
                    );
                    v___x_3263_ = v_reuseFailAlloc_3265_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3264_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3264_, 0, v___x_3261_);
                crate::leanh::lean_ctor_set(v___x_3264_, 1, v___x_3263_);
                return v___x_3264_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instMonadStateOfLogJobM___lam__1___boxed(
    mut v_log_3268_: *mut crate::leanh::LeanObject,
    mut v___y_3269_: *mut crate::leanh::LeanObject,
    mut v___y_3270_: *mut crate::leanh::LeanObject,
    mut v___y_3271_: *mut crate::leanh::LeanObject,
    mut v___y_3272_: *mut crate::leanh::LeanObject,
    mut v___y_3273_: *mut crate::leanh::LeanObject,
    mut v___y_3274_: *mut crate::leanh::LeanObject,
    mut v___y_3275_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3276_ = l_Lake_instMonadStateOfLogJobM___lam__1(
        v_log_3268_,
        v___y_3269_,
        v___y_3270_,
        v___y_3271_,
        v___y_3272_,
        v___y_3273_,
        v___y_3274_,
    );
    crate::leanh::lean_dec_ref(v___y_3273_);
    crate::leanh::lean_dec(v___y_3272_);
    crate::leanh::lean_dec(v___y_3271_);
    crate::leanh::lean_dec(v___y_3270_);
    crate::leanh::lean_dec_ref(v___y_3269_);
    return v_res_3276_;
}
pub unsafe fn l_Lake_instMonadStateOfLogJobM___lam__2(
    mut v_00_u03b1_3277_: *mut crate::leanh::LeanObject,
    mut v_f_3278_: *mut crate::leanh::LeanObject,
    mut v___y_3279_: *mut crate::leanh::LeanObject,
    mut v___y_3280_: *mut crate::leanh::LeanObject,
    mut v___y_3281_: *mut crate::leanh::LeanObject,
    mut v___y_3282_: *mut crate::leanh::LeanObject,
    mut v___y_3283_: *mut crate::leanh::LeanObject,
    mut v___y_3284_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_log_3286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_action_3287_: u8 = 0;
    let mut v_wantsRebuild_3288_: u8 = 0;
    let mut v_trace_3289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildTime_3290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3293_: u8 = 0;
    let mut v___x_3294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3299_: u8 = 0;
    let mut v___x_3301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3306_: u8 = 0;
    let mut v_isSharedCheck_3307_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_log_3286_ = crate::leanh::lean_ctor_get(v___y_3284_, 0);
                v_action_3287_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_3284_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_wantsRebuild_3288_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_3284_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                );
                v_trace_3289_ = crate::leanh::lean_ctor_get(v___y_3284_, 1);
                v_buildTime_3290_ = crate::leanh::lean_ctor_get(v___y_3284_, 2);
                v_isSharedCheck_3307_ = (!crate::leanh::lean_is_exclusive(v___y_3284_)) as u8;
                if v_isSharedCheck_3307_ == 0 {
                    v___x_3292_ = v___y_3284_;
                    v_isShared_3293_ = v_isSharedCheck_3307_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buildTime_3290_);
                    crate::leanh::lean_inc(v_trace_3289_);
                    crate::leanh::lean_inc(v_log_3286_);
                    crate::leanh::lean_dec(v___y_3284_);
                    v___x_3292_ = crate::leanh::lean_box(0);
                    v_isShared_3293_ = v_isSharedCheck_3307_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3294_ = crate::leanh::lean_apply_1(v_f_3278_, v_log_3286_);
                v_fst_3295_ = crate::leanh::lean_ctor_get(v___x_3294_, 0);
                v_snd_3296_ = crate::leanh::lean_ctor_get(v___x_3294_, 1);
                v_isSharedCheck_3306_ = (!crate::leanh::lean_is_exclusive(v___x_3294_)) as u8;
                if v_isSharedCheck_3306_ == 0 {
                    v___x_3298_ = v___x_3294_;
                    v_isShared_3299_ = v_isSharedCheck_3306_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3296_);
                    crate::leanh::lean_inc(v_fst_3295_);
                    crate::leanh::lean_dec(v___x_3294_);
                    v___x_3298_ = crate::leanh::lean_box(0);
                    v_isShared_3299_ = v_isSharedCheck_3306_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_3293_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3292_, 0, v_snd_3296_);
                    v___x_3301_ = v___x_3292_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3305_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3305_, 0, v_snd_3296_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3305_, 1, v_trace_3289_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3305_, 2, v_buildTime_3290_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3305_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_action_3287_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3305_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_3288_,
                    );
                    v___x_3301_ = v_reuseFailAlloc_3305_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3299_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3298_, 1, v___x_3301_);
                    v___x_3303_ = v___x_3298_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3304_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3304_, 0, v_fst_3295_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3304_, 1, v___x_3301_);
                    v___x_3303_ = v_reuseFailAlloc_3304_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3303_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instMonadStateOfLogJobM___lam__2___boxed(
    mut v_00_u03b1_3308_: *mut crate::leanh::LeanObject,
    mut v_f_3309_: *mut crate::leanh::LeanObject,
    mut v___y_3310_: *mut crate::leanh::LeanObject,
    mut v___y_3311_: *mut crate::leanh::LeanObject,
    mut v___y_3312_: *mut crate::leanh::LeanObject,
    mut v___y_3313_: *mut crate::leanh::LeanObject,
    mut v___y_3314_: *mut crate::leanh::LeanObject,
    mut v___y_3315_: *mut crate::leanh::LeanObject,
    mut v___y_3316_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3317_ = l_Lake_instMonadStateOfLogJobM___lam__2(
        v_00_u03b1_3308_,
        v_f_3309_,
        v___y_3310_,
        v___y_3311_,
        v___y_3312_,
        v___y_3313_,
        v___y_3314_,
        v___y_3315_,
    );
    crate::leanh::lean_dec_ref(v___y_3314_);
    crate::leanh::lean_dec(v___y_3313_);
    crate::leanh::lean_dec(v___y_3312_);
    crate::leanh::lean_dec(v___y_3311_);
    crate::leanh::lean_dec_ref(v___y_3310_);
    return v_res_3317_;
}
pub unsafe fn l_Lake_instMonadErrorJobM___lam__0(
    mut v_00_u03b1_3329_: *mut crate::leanh::LeanObject,
    mut v___y_3330_: *mut crate::leanh::LeanObject,
    mut v___y_3331_: *mut crate::leanh::LeanObject,
    mut v___y_3332_: *mut crate::leanh::LeanObject,
    mut v___y_3333_: *mut crate::leanh::LeanObject,
    mut v___y_3334_: *mut crate::leanh::LeanObject,
    mut v___y_3335_: *mut crate::leanh::LeanObject,
    mut v___y_3336_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_log_3338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_action_3339_: u8 = 0;
    let mut v_wantsRebuild_3340_: u8 = 0;
    let mut v_trace_3341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildTime_3342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3345_: u8 = 0;
    let mut v___x_3346_: u8 = 0;
    let mut v___x_3347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3354_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_log_3338_ = crate::leanh::lean_ctor_get(v___y_3336_, 0);
                v_action_3339_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_3336_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_wantsRebuild_3340_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_3336_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                );
                v_trace_3341_ = crate::leanh::lean_ctor_get(v___y_3336_, 1);
                v_buildTime_3342_ = crate::leanh::lean_ctor_get(v___y_3336_, 2);
                v_isSharedCheck_3354_ = (!crate::leanh::lean_is_exclusive(v___y_3336_)) as u8;
                if v_isSharedCheck_3354_ == 0 {
                    v___x_3344_ = v___y_3336_;
                    v_isShared_3345_ = v_isSharedCheck_3354_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buildTime_3342_);
                    crate::leanh::lean_inc(v_trace_3341_);
                    crate::leanh::lean_inc(v_log_3338_);
                    crate::leanh::lean_dec(v___y_3336_);
                    v___x_3344_ = crate::leanh::lean_box(0);
                    v_isShared_3345_ = v_isSharedCheck_3354_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3346_ = 3;
                v___x_3347_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3347_, 0, v___y_3330_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3347_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_3346_,
                );
                v___x_3348_ = lean_array_get_size(v_log_3338_);
                v___x_3349_ = lean_array_push(v_log_3338_, v___x_3347_);
                if v_isShared_3345_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3344_, 0, v___x_3349_);
                    v___x_3351_ = v___x_3344_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3353_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3353_, 0, v___x_3349_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3353_, 1, v_trace_3341_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3353_, 2, v_buildTime_3342_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3353_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_action_3339_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3353_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_3340_,
                    );
                    v___x_3351_ = v_reuseFailAlloc_3353_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3352_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3352_, 0, v___x_3348_);
                crate::leanh::lean_ctor_set(v___x_3352_, 1, v___x_3351_);
                return v___x_3352_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instMonadErrorJobM___lam__0___boxed(
    mut v_00_u03b1_3355_: *mut crate::leanh::LeanObject,
    mut v___y_3356_: *mut crate::leanh::LeanObject,
    mut v___y_3357_: *mut crate::leanh::LeanObject,
    mut v___y_3358_: *mut crate::leanh::LeanObject,
    mut v___y_3359_: *mut crate::leanh::LeanObject,
    mut v___y_3360_: *mut crate::leanh::LeanObject,
    mut v___y_3361_: *mut crate::leanh::LeanObject,
    mut v___y_3362_: *mut crate::leanh::LeanObject,
    mut v___y_3363_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3364_ = l_Lake_instMonadErrorJobM___lam__0(
        v_00_u03b1_3355_,
        v___y_3356_,
        v___y_3357_,
        v___y_3358_,
        v___y_3359_,
        v___y_3360_,
        v___y_3361_,
        v___y_3362_,
    );
    crate::leanh::lean_dec_ref(v___y_3361_);
    crate::leanh::lean_dec(v___y_3360_);
    crate::leanh::lean_dec(v___y_3359_);
    crate::leanh::lean_dec(v___y_3358_);
    crate::leanh::lean_dec_ref(v___y_3357_);
    return v_res_3364_;
}
pub unsafe fn l_Lake_instAlternativeJobM___lam__0(
    mut v_00_u03b1_3367_: *mut crate::leanh::LeanObject,
    mut v___y_3368_: *mut crate::leanh::LeanObject,
    mut v___y_3369_: *mut crate::leanh::LeanObject,
    mut v___y_3370_: *mut crate::leanh::LeanObject,
    mut v___y_3371_: *mut crate::leanh::LeanObject,
    mut v___y_3372_: *mut crate::leanh::LeanObject,
    mut v___y_3373_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_log_3375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_log_3375_ = crate::leanh::lean_ctor_get(v___y_3373_, 0);
    v___x_3376_ = lean_array_get_size(v_log_3375_);
    v___x_3377_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3377_, 0, v___x_3376_);
    crate::leanh::lean_ctor_set(v___x_3377_, 1, v___y_3373_);
    return v___x_3377_;
}
pub unsafe fn l_Lake_instAlternativeJobM___lam__0___boxed(
    mut v_00_u03b1_3378_: *mut crate::leanh::LeanObject,
    mut v___y_3379_: *mut crate::leanh::LeanObject,
    mut v___y_3380_: *mut crate::leanh::LeanObject,
    mut v___y_3381_: *mut crate::leanh::LeanObject,
    mut v___y_3382_: *mut crate::leanh::LeanObject,
    mut v___y_3383_: *mut crate::leanh::LeanObject,
    mut v___y_3384_: *mut crate::leanh::LeanObject,
    mut v___y_3385_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3386_ = l_Lake_instAlternativeJobM___lam__0(
        v_00_u03b1_3378_,
        v___y_3379_,
        v___y_3380_,
        v___y_3381_,
        v___y_3382_,
        v___y_3383_,
        v___y_3384_,
    );
    crate::leanh::lean_dec_ref(v___y_3383_);
    crate::leanh::lean_dec(v___y_3382_);
    crate::leanh::lean_dec(v___y_3381_);
    crate::leanh::lean_dec(v___y_3380_);
    crate::leanh::lean_dec_ref(v___y_3379_);
    return v_res_3386_;
}
pub unsafe fn l_Lake_instAlternativeJobM___lam__1(
    mut v_00_u03b1_3387_: *mut crate::leanh::LeanObject,
    mut v___y_3388_: *mut crate::leanh::LeanObject,
    mut v___y_3389_: *mut crate::leanh::LeanObject,
    mut v___y_3390_: *mut crate::leanh::LeanObject,
    mut v___y_3391_: *mut crate::leanh::LeanObject,
    mut v___y_3392_: *mut crate::leanh::LeanObject,
    mut v___y_3393_: *mut crate::leanh::LeanObject,
    mut v___y_3394_: *mut crate::leanh::LeanObject,
    mut v___y_3395_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_log_3400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_action_3401_: u8 = 0;
    let mut v_wantsRebuild_3402_: u8 = 0;
    let mut v_trace_3403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildTime_3404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3407_: u8 = 0;
    let mut v___x_3408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3414_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v___y_3394_);
                crate::leanh::lean_inc(v___y_3393_);
                crate::leanh::lean_inc(v___y_3392_);
                crate::leanh::lean_inc(v___y_3391_);
                crate::leanh::lean_inc_ref(v___y_3390_);
                v___x_3397_ = crate::leanh::lean_apply_7(
                    v___y_3388_,
                    v___y_3390_,
                    v___y_3391_,
                    v___y_3392_,
                    v___y_3393_,
                    v___y_3394_,
                    v___y_3395_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_3397_) == 0 {
                    crate::leanh::lean_dec_ref(v___y_3390_);
                    crate::leanh::lean_dec_ref(v___y_3389_);
                    return v___x_3397_;
                } else {
                    v_a_3398_ = crate::leanh::lean_ctor_get(v___x_3397_, 1);
                    crate::leanh::lean_inc(v_a_3398_);
                    v_a_3399_ = crate::leanh::lean_ctor_get(v___x_3397_, 0);
                    crate::leanh::lean_inc(v_a_3399_);
                    crate::leanh::lean_dec_ref_known(v___x_3397_, 2);
                    v_log_3400_ = crate::leanh::lean_ctor_get(v_a_3398_, 0);
                    v_action_3401_ = crate::leanh::lean_ctor_get_uint8(
                        v_a_3398_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    );
                    v_wantsRebuild_3402_ = crate::leanh::lean_ctor_get_uint8(
                        v_a_3398_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                    );
                    v_trace_3403_ = crate::leanh::lean_ctor_get(v_a_3398_, 1);
                    v_buildTime_3404_ = crate::leanh::lean_ctor_get(v_a_3398_, 2);
                    v_isSharedCheck_3414_ = (!crate::leanh::lean_is_exclusive(v_a_3398_)) as u8;
                    if v_isSharedCheck_3414_ == 0 {
                        v___x_3406_ = v_a_3398_;
                        v_isShared_3407_ = v_isSharedCheck_3414_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_buildTime_3404_);
                        crate::leanh::lean_inc(v_trace_3403_);
                        crate::leanh::lean_inc(v_log_3400_);
                        crate::leanh::lean_dec(v_a_3398_);
                        v___x_3406_ = crate::leanh::lean_box(0);
                        v_isShared_3407_ = v_isSharedCheck_3414_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3408_ = l_Array_shrink___redArg(v_log_3400_, v_a_3399_);
                crate::leanh::lean_dec(v_a_3399_);
                if v_isShared_3407_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3406_, 0, v___x_3408_);
                    v___x_3410_ = v___x_3406_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3413_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3413_, 0, v___x_3408_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3413_, 1, v_trace_3403_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3413_, 2, v_buildTime_3404_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3413_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_action_3401_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3413_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_3402_,
                    );
                    v___x_3410_ = v_reuseFailAlloc_3413_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3411_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc_ref(v___y_3394_);
                crate::leanh::lean_inc(v___y_3393_);
                crate::leanh::lean_inc(v___y_3392_);
                crate::leanh::lean_inc(v___y_3391_);
                v___x_3412_ = crate::leanh::lean_apply_8(
                    v___y_3389_,
                    v___x_3411_,
                    v___y_3390_,
                    v___y_3391_,
                    v___y_3392_,
                    v___y_3393_,
                    v___y_3394_,
                    v___x_3410_,
                    crate::leanh::lean_box(0),
                );
                return v___x_3412_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instAlternativeJobM___lam__1___boxed(
    mut v_00_u03b1_3415_: *mut crate::leanh::LeanObject,
    mut v___y_3416_: *mut crate::leanh::LeanObject,
    mut v___y_3417_: *mut crate::leanh::LeanObject,
    mut v___y_3418_: *mut crate::leanh::LeanObject,
    mut v___y_3419_: *mut crate::leanh::LeanObject,
    mut v___y_3420_: *mut crate::leanh::LeanObject,
    mut v___y_3421_: *mut crate::leanh::LeanObject,
    mut v___y_3422_: *mut crate::leanh::LeanObject,
    mut v___y_3423_: *mut crate::leanh::LeanObject,
    mut v___y_3424_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3425_ = l_Lake_instAlternativeJobM___lam__1(
        v_00_u03b1_3415_,
        v___y_3416_,
        v___y_3417_,
        v___y_3418_,
        v___y_3419_,
        v___y_3420_,
        v___y_3421_,
        v___y_3422_,
        v___y_3423_,
    );
    crate::leanh::lean_dec_ref(v___y_3422_);
    crate::leanh::lean_dec(v___y_3421_);
    crate::leanh::lean_dec(v___y_3420_);
    crate::leanh::lean_dec(v___y_3419_);
    return v_res_3425_;
}
pub unsafe fn _init_l_Lake_instAlternativeJobM() -> *mut crate::leanh::LeanObject {
    let mut v___x_3428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_3431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3428_ = l_instMonadBaseIO;
    v_toApplicative_3429_ = crate::leanh::lean_ctor_get(v___x_3428_, 0);
    v_toBind_3430_ = crate::leanh::lean_ctor_get(v___x_3428_, 1);
    v_toFunctor_3431_ = crate::leanh::lean_ctor_get(v_toApplicative_3429_, 0);
    v_toPure_3432_ = crate::leanh::lean_ctor_get(v_toApplicative_3429_, 1);
    crate::leanh::lean_inc_n(v_toBind_3430_, 3);
    crate::leanh::lean_inc_n(v_toPure_3432_, 5);
    v___f_3433_ = crate::leanh::lean_alloc_closure(
        l_Lake_EStateT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3433_, 0, v_toPure_3432_);
    crate::leanh::lean_closure_set(v___f_3433_, 1, v_toBind_3430_);
    v___f_3434_ = crate::leanh::lean_alloc_closure(
        l_Lake_EStateT_instMonad___redArg___lam__3 as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3434_, 0, v_toPure_3432_);
    crate::leanh::lean_closure_set(v___f_3434_, 1, v_toBind_3430_);
    crate::leanh::lean_inc_ref(v___f_3433_);
    v___f_3435_ = crate::leanh::lean_alloc_closure(
        l_Lake_EStateT_instMonad___redArg___lam__5 as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3435_, 0, v_toPure_3432_);
    crate::leanh::lean_closure_set(v___f_3435_, 1, v___f_3433_);
    crate::leanh::lean_inc_ref_n(v_toFunctor_3431_, 2);
    v___f_3436_ = crate::leanh::lean_alloc_closure(
        l_Lake_EStateT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
        8,
        3,
    );
    crate::leanh::lean_closure_set(v___f_3436_, 0, v_toFunctor_3431_);
    crate::leanh::lean_closure_set(v___f_3436_, 1, v_toPure_3432_);
    crate::leanh::lean_closure_set(v___f_3436_, 2, v_toBind_3430_);
    v___x_3437_ = l_Lake_EStateT_instFunctor___redArg(v_toFunctor_3431_);
    v___f_3438_ = crate::leanh::lean_alloc_closure(
        l_Lake_EStateT_instPure___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3438_, 0, v_toPure_3432_);
    v___x_3439_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3439_, 0, v___x_3437_);
    crate::leanh::lean_ctor_set(v___x_3439_, 1, v___f_3438_);
    crate::leanh::lean_ctor_set(v___x_3439_, 2, v___f_3436_);
    crate::leanh::lean_ctor_set(v___x_3439_, 3, v___f_3435_);
    crate::leanh::lean_ctor_set(v___x_3439_, 4, v___f_3434_);
    v___x_3440_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3440_, 0, v___x_3439_);
    crate::leanh::lean_ctor_set(v___x_3440_, 1, v___f_3433_);
    v___x_3441_ = l_ReaderT_instMonad___redArg(v___x_3440_);
    v___x_3442_ = l_StateRefT_x27_instMonad___redArg(v___x_3441_);
    v___x_3443_ = l_ReaderT_instMonad___redArg(v___x_3442_);
    v___x_3444_ = l_ReaderT_instMonad___redArg(v___x_3443_);
    v___x_3445_ = l_Lake_EquipT_instMonad___redArg(v___x_3444_);
    v_toApplicative_3446_ = crate::leanh::lean_ctor_get(v___x_3445_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_3446_);
    crate::leanh::lean_dec_ref(v___x_3445_);
    v___f_3447_ = l_Lake_instAlternativeJobM___closed__0;
    v___f_3448_ = l_Lake_instAlternativeJobM___closed__1;
    v___x_3449_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3449_, 0, v_toApplicative_3446_);
    crate::leanh::lean_ctor_set(v___x_3449_, 1, v___f_3447_);
    crate::leanh::lean_ctor_set(v___x_3449_, 2, v___f_3448_);
    return v___x_3449_;
}
pub unsafe fn l_Lake_instMonadLiftLogIOJobM___lam__0(
    mut v_00_u03b1_3450_: *mut crate::leanh::LeanObject,
    mut v___y_3451_: *mut crate::leanh::LeanObject,
    mut v___y_3452_: *mut crate::leanh::LeanObject,
    mut v___y_3453_: *mut crate::leanh::LeanObject,
    mut v___y_3454_: *mut crate::leanh::LeanObject,
    mut v___y_3455_: *mut crate::leanh::LeanObject,
    mut v___y_3456_: *mut crate::leanh::LeanObject,
    mut v___y_3457_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_log_3459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_action_3460_: u8 = 0;
    let mut v_wantsRebuild_3461_: u8 = 0;
    let mut v_trace_3462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildTime_3463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3466_: u8 = 0;
    let mut v___x_3467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3472_: u8 = 0;
    let mut v___x_3474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3479_: u8 = 0;
    let mut v_a_3480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3484_: u8 = 0;
    let mut v___x_3486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3491_: u8 = 0;
    let mut v_isSharedCheck_3492_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_log_3459_ = crate::leanh::lean_ctor_get(v___y_3457_, 0);
                v_action_3460_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_3457_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_wantsRebuild_3461_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_3457_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                );
                v_trace_3462_ = crate::leanh::lean_ctor_get(v___y_3457_, 1);
                v_buildTime_3463_ = crate::leanh::lean_ctor_get(v___y_3457_, 2);
                v_isSharedCheck_3492_ = (!crate::leanh::lean_is_exclusive(v___y_3457_)) as u8;
                if v_isSharedCheck_3492_ == 0 {
                    v___x_3465_ = v___y_3457_;
                    v_isShared_3466_ = v_isSharedCheck_3492_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buildTime_3463_);
                    crate::leanh::lean_inc(v_trace_3462_);
                    crate::leanh::lean_inc(v_log_3459_);
                    crate::leanh::lean_dec(v___y_3457_);
                    v___x_3465_ = crate::leanh::lean_box(0);
                    v_isShared_3466_ = v_isSharedCheck_3492_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3467_ =
                    crate::leanh::lean_apply_2(v___y_3451_, v_log_3459_, crate::leanh::lean_box(0));
                if crate::leanh::lean_obj_tag(v___x_3467_) == 0 {
                    v_a_3468_ = crate::leanh::lean_ctor_get(v___x_3467_, 0);
                    v_a_3469_ = crate::leanh::lean_ctor_get(v___x_3467_, 1);
                    v_isSharedCheck_3479_ = (!crate::leanh::lean_is_exclusive(v___x_3467_)) as u8;
                    if v_isSharedCheck_3479_ == 0 {
                        v___x_3471_ = v___x_3467_;
                        v_isShared_3472_ = v_isSharedCheck_3479_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3469_);
                        crate::leanh::lean_inc(v_a_3468_);
                        crate::leanh::lean_dec(v___x_3467_);
                        v___x_3471_ = crate::leanh::lean_box(0);
                        v_isShared_3472_ = v_isSharedCheck_3479_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_3480_ = crate::leanh::lean_ctor_get(v___x_3467_, 0);
                    v_a_3481_ = crate::leanh::lean_ctor_get(v___x_3467_, 1);
                    v_isSharedCheck_3491_ = (!crate::leanh::lean_is_exclusive(v___x_3467_)) as u8;
                    if v_isSharedCheck_3491_ == 0 {
                        v___x_3483_ = v___x_3467_;
                        v_isShared_3484_ = v_isSharedCheck_3491_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3481_);
                        crate::leanh::lean_inc(v_a_3480_);
                        crate::leanh::lean_dec(v___x_3467_);
                        v___x_3483_ = crate::leanh::lean_box(0);
                        v_isShared_3484_ = v_isSharedCheck_3491_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3466_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3465_, 0, v_a_3469_);
                    v___x_3474_ = v___x_3465_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3478_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3478_, 0, v_a_3469_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3478_, 1, v_trace_3462_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3478_, 2, v_buildTime_3463_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3478_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_action_3460_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3478_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_3461_,
                    );
                    v___x_3474_ = v_reuseFailAlloc_3478_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3472_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3471_, 1, v___x_3474_);
                    v___x_3476_ = v___x_3471_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3477_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3477_, 0, v_a_3468_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3477_, 1, v___x_3474_);
                    v___x_3476_ = v_reuseFailAlloc_3477_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3476_;
            }
            5 => {
                if v_isShared_3466_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3465_, 0, v_a_3481_);
                    v___x_3486_ = v___x_3465_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3490_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3490_, 0, v_a_3481_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3490_, 1, v_trace_3462_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3490_, 2, v_buildTime_3463_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3490_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_action_3460_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3490_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_3461_,
                    );
                    v___x_3486_ = v_reuseFailAlloc_3490_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_3484_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3483_, 1, v___x_3486_);
                    v___x_3488_ = v___x_3483_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3489_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3489_, 0, v_a_3480_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3489_, 1, v___x_3486_);
                    v___x_3488_ = v_reuseFailAlloc_3489_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3488_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instMonadLiftLogIOJobM___lam__0___boxed(
    mut v_00_u03b1_3493_: *mut crate::leanh::LeanObject,
    mut v___y_3494_: *mut crate::leanh::LeanObject,
    mut v___y_3495_: *mut crate::leanh::LeanObject,
    mut v___y_3496_: *mut crate::leanh::LeanObject,
    mut v___y_3497_: *mut crate::leanh::LeanObject,
    mut v___y_3498_: *mut crate::leanh::LeanObject,
    mut v___y_3499_: *mut crate::leanh::LeanObject,
    mut v___y_3500_: *mut crate::leanh::LeanObject,
    mut v___y_3501_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3502_ = l_Lake_instMonadLiftLogIOJobM___lam__0(
        v_00_u03b1_3493_,
        v___y_3494_,
        v___y_3495_,
        v___y_3496_,
        v___y_3497_,
        v___y_3498_,
        v___y_3499_,
        v___y_3500_,
    );
    crate::leanh::lean_dec_ref(v___y_3499_);
    crate::leanh::lean_dec(v___y_3498_);
    crate::leanh::lean_dec(v___y_3497_);
    crate::leanh::lean_dec(v___y_3496_);
    crate::leanh::lean_dec_ref(v___y_3495_);
    return v_res_3502_;
}
pub unsafe fn l_Lake_updateAction___redArg(
    mut v_action_3505_: u8,
    mut v_a_3506_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_log_3508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_action_3509_: u8 = 0;
    let mut v_wantsRebuild_3510_: u8 = 0;
    let mut v_trace_3511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildTime_3512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3515_: u8 = 0;
    let mut v___x_3516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3517_: u8 = 0;
    let mut v___x_3519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3522_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_log_3508_ = crate::leanh::lean_ctor_get(v_a_3506_, 0);
                v_action_3509_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_3506_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_wantsRebuild_3510_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_3506_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                );
                v_trace_3511_ = crate::leanh::lean_ctor_get(v_a_3506_, 1);
                v_buildTime_3512_ = crate::leanh::lean_ctor_get(v_a_3506_, 2);
                v_isSharedCheck_3522_ = (!crate::leanh::lean_is_exclusive(v_a_3506_)) as u8;
                if v_isSharedCheck_3522_ == 0 {
                    v___x_3514_ = v_a_3506_;
                    v_isShared_3515_ = v_isSharedCheck_3522_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buildTime_3512_);
                    crate::leanh::lean_inc(v_trace_3511_);
                    crate::leanh::lean_inc(v_log_3508_);
                    crate::leanh::lean_dec(v_a_3506_);
                    v___x_3514_ = crate::leanh::lean_box(0);
                    v_isShared_3515_ = v_isSharedCheck_3522_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3516_ = crate::leanh::lean_box(0);
                v___x_3517_ = l_Lake_JobAction_merge(v_action_3509_, v_action_3505_);
                if v_isShared_3515_ == 0 {
                    v___x_3519_ = v___x_3514_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3521_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3521_, 0, v_log_3508_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3521_, 1, v_trace_3511_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3521_, 2, v_buildTime_3512_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3521_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_3510_,
                    );
                    v___x_3519_ = v_reuseFailAlloc_3521_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3519_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_3517_,
                );
                v___x_3520_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3520_, 0, v___x_3516_);
                crate::leanh::lean_ctor_set(v___x_3520_, 1, v___x_3519_);
                return v___x_3520_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_updateAction___redArg___boxed(
    mut v_action_3523_: *mut crate::leanh::LeanObject,
    mut v_a_3524_: *mut crate::leanh::LeanObject,
    mut v_a_3525_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_action_boxed_3526_: u8 = 0;
    let mut v_res_3527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_action_boxed_3526_ = (crate::leanh::lean_unbox(v_action_3523_) as u8);
    v_res_3527_ = l_Lake_updateAction___redArg(v_action_boxed_3526_, v_a_3524_);
    return v_res_3527_;
}
pub unsafe fn l_Lake_updateAction(
    mut v_action_3528_: u8,
    mut v_a_3529_: *mut crate::leanh::LeanObject,
    mut v_a_3530_: *mut crate::leanh::LeanObject,
    mut v_a_3531_: *mut crate::leanh::LeanObject,
    mut v_a_3532_: *mut crate::leanh::LeanObject,
    mut v_a_3533_: *mut crate::leanh::LeanObject,
    mut v_a_3534_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_log_3536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_action_3537_: u8 = 0;
    let mut v_wantsRebuild_3538_: u8 = 0;
    let mut v_trace_3539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildTime_3540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3543_: u8 = 0;
    let mut v___x_3544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3545_: u8 = 0;
    let mut v___x_3547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3550_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_log_3536_ = crate::leanh::lean_ctor_get(v_a_3534_, 0);
                v_action_3537_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_3534_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_wantsRebuild_3538_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_3534_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                );
                v_trace_3539_ = crate::leanh::lean_ctor_get(v_a_3534_, 1);
                v_buildTime_3540_ = crate::leanh::lean_ctor_get(v_a_3534_, 2);
                v_isSharedCheck_3550_ = (!crate::leanh::lean_is_exclusive(v_a_3534_)) as u8;
                if v_isSharedCheck_3550_ == 0 {
                    v___x_3542_ = v_a_3534_;
                    v_isShared_3543_ = v_isSharedCheck_3550_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buildTime_3540_);
                    crate::leanh::lean_inc(v_trace_3539_);
                    crate::leanh::lean_inc(v_log_3536_);
                    crate::leanh::lean_dec(v_a_3534_);
                    v___x_3542_ = crate::leanh::lean_box(0);
                    v_isShared_3543_ = v_isSharedCheck_3550_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3544_ = crate::leanh::lean_box(0);
                v___x_3545_ = l_Lake_JobAction_merge(v_action_3537_, v_action_3528_);
                if v_isShared_3543_ == 0 {
                    v___x_3547_ = v___x_3542_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3549_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3549_, 0, v_log_3536_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3549_, 1, v_trace_3539_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3549_, 2, v_buildTime_3540_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3549_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_3538_,
                    );
                    v___x_3547_ = v_reuseFailAlloc_3549_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3547_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_3545_,
                );
                v___x_3548_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3548_, 0, v___x_3544_);
                crate::leanh::lean_ctor_set(v___x_3548_, 1, v___x_3547_);
                return v___x_3548_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_updateAction___boxed(
    mut v_action_3551_: *mut crate::leanh::LeanObject,
    mut v_a_3552_: *mut crate::leanh::LeanObject,
    mut v_a_3553_: *mut crate::leanh::LeanObject,
    mut v_a_3554_: *mut crate::leanh::LeanObject,
    mut v_a_3555_: *mut crate::leanh::LeanObject,
    mut v_a_3556_: *mut crate::leanh::LeanObject,
    mut v_a_3557_: *mut crate::leanh::LeanObject,
    mut v_a_3558_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_action_boxed_3559_: u8 = 0;
    let mut v_res_3560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_action_boxed_3559_ = (crate::leanh::lean_unbox(v_action_3551_) as u8);
    v_res_3560_ = l_Lake_updateAction(
        v_action_boxed_3559_,
        v_a_3552_,
        v_a_3553_,
        v_a_3554_,
        v_a_3555_,
        v_a_3556_,
        v_a_3557_,
    );
    crate::leanh::lean_dec_ref(v_a_3556_);
    crate::leanh::lean_dec(v_a_3555_);
    crate::leanh::lean_dec(v_a_3554_);
    crate::leanh::lean_dec(v_a_3553_);
    crate::leanh::lean_dec_ref(v_a_3552_);
    return v_res_3560_;
}
pub unsafe fn l_Lake_getTrace___redArg(
    mut v_a_3561_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_trace_3563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_trace_3563_ = crate::leanh::lean_ctor_get(v_a_3561_, 1);
    crate::leanh::lean_inc_ref(v_trace_3563_);
    v___x_3564_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3564_, 0, v_trace_3563_);
    crate::leanh::lean_ctor_set(v___x_3564_, 1, v_a_3561_);
    return v___x_3564_;
}
pub unsafe fn l_Lake_getTrace___redArg___boxed(
    mut v_a_3565_: *mut crate::leanh::LeanObject,
    mut v_a_3566_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3567_ = l_Lake_getTrace___redArg(v_a_3565_);
    return v_res_3567_;
}
pub unsafe fn l_Lake_getTrace(
    mut v_a_3568_: *mut crate::leanh::LeanObject,
    mut v_a_3569_: *mut crate::leanh::LeanObject,
    mut v_a_3570_: *mut crate::leanh::LeanObject,
    mut v_a_3571_: *mut crate::leanh::LeanObject,
    mut v_a_3572_: *mut crate::leanh::LeanObject,
    mut v_a_3573_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_trace_3575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_trace_3575_ = crate::leanh::lean_ctor_get(v_a_3573_, 1);
    crate::leanh::lean_inc_ref(v_trace_3575_);
    v___x_3576_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3576_, 0, v_trace_3575_);
    crate::leanh::lean_ctor_set(v___x_3576_, 1, v_a_3573_);
    return v___x_3576_;
}
pub unsafe fn l_Lake_getTrace___boxed(
    mut v_a_3577_: *mut crate::leanh::LeanObject,
    mut v_a_3578_: *mut crate::leanh::LeanObject,
    mut v_a_3579_: *mut crate::leanh::LeanObject,
    mut v_a_3580_: *mut crate::leanh::LeanObject,
    mut v_a_3581_: *mut crate::leanh::LeanObject,
    mut v_a_3582_: *mut crate::leanh::LeanObject,
    mut v_a_3583_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3584_ = l_Lake_getTrace(
        v_a_3577_, v_a_3578_, v_a_3579_, v_a_3580_, v_a_3581_, v_a_3582_,
    );
    crate::leanh::lean_dec_ref(v_a_3581_);
    crate::leanh::lean_dec(v_a_3580_);
    crate::leanh::lean_dec(v_a_3579_);
    crate::leanh::lean_dec(v_a_3578_);
    crate::leanh::lean_dec_ref(v_a_3577_);
    return v_res_3584_;
}
pub unsafe fn l_Lake_setTrace___redArg(
    mut v_trace_3585_: *mut crate::leanh::LeanObject,
    mut v_a_3586_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_log_3588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_action_3589_: u8 = 0;
    let mut v_wantsRebuild_3590_: u8 = 0;
    let mut v_buildTime_3591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3594_: u8 = 0;
    let mut v___x_3595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3600_: u8 = 0;
    let mut v_unused_3601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_log_3588_ = crate::leanh::lean_ctor_get(v_a_3586_, 0);
                v_action_3589_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_3586_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_wantsRebuild_3590_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_3586_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                );
                v_buildTime_3591_ = crate::leanh::lean_ctor_get(v_a_3586_, 2);
                v_isSharedCheck_3600_ = (!crate::leanh::lean_is_exclusive(v_a_3586_)) as u8;
                if v_isSharedCheck_3600_ == 0 {
                    v_unused_3601_ = crate::leanh::lean_ctor_get(v_a_3586_, 1);
                    crate::leanh::lean_dec(v_unused_3601_);
                    v___x_3593_ = v_a_3586_;
                    v_isShared_3594_ = v_isSharedCheck_3600_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buildTime_3591_);
                    crate::leanh::lean_inc(v_log_3588_);
                    crate::leanh::lean_dec(v_a_3586_);
                    v___x_3593_ = crate::leanh::lean_box(0);
                    v_isShared_3594_ = v_isSharedCheck_3600_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3595_ = crate::leanh::lean_box(0);
                if v_isShared_3594_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3593_, 1, v_trace_3585_);
                    v___x_3597_ = v___x_3593_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3599_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3599_, 0, v_log_3588_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3599_, 1, v_trace_3585_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3599_, 2, v_buildTime_3591_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3599_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_action_3589_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3599_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_3590_,
                    );
                    v___x_3597_ = v_reuseFailAlloc_3599_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3598_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3598_, 0, v___x_3595_);
                crate::leanh::lean_ctor_set(v___x_3598_, 1, v___x_3597_);
                return v___x_3598_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_setTrace___redArg___boxed(
    mut v_trace_3602_: *mut crate::leanh::LeanObject,
    mut v_a_3603_: *mut crate::leanh::LeanObject,
    mut v_a_3604_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3605_ = l_Lake_setTrace___redArg(v_trace_3602_, v_a_3603_);
    return v_res_3605_;
}
pub unsafe fn l_Lake_setTrace(
    mut v_trace_3606_: *mut crate::leanh::LeanObject,
    mut v_a_3607_: *mut crate::leanh::LeanObject,
    mut v_a_3608_: *mut crate::leanh::LeanObject,
    mut v_a_3609_: *mut crate::leanh::LeanObject,
    mut v_a_3610_: *mut crate::leanh::LeanObject,
    mut v_a_3611_: *mut crate::leanh::LeanObject,
    mut v_a_3612_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_log_3614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_action_3615_: u8 = 0;
    let mut v_wantsRebuild_3616_: u8 = 0;
    let mut v_buildTime_3617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3620_: u8 = 0;
    let mut v___x_3621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3626_: u8 = 0;
    let mut v_unused_3627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_log_3614_ = crate::leanh::lean_ctor_get(v_a_3612_, 0);
                v_action_3615_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_3612_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_wantsRebuild_3616_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_3612_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                );
                v_buildTime_3617_ = crate::leanh::lean_ctor_get(v_a_3612_, 2);
                v_isSharedCheck_3626_ = (!crate::leanh::lean_is_exclusive(v_a_3612_)) as u8;
                if v_isSharedCheck_3626_ == 0 {
                    v_unused_3627_ = crate::leanh::lean_ctor_get(v_a_3612_, 1);
                    crate::leanh::lean_dec(v_unused_3627_);
                    v___x_3619_ = v_a_3612_;
                    v_isShared_3620_ = v_isSharedCheck_3626_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buildTime_3617_);
                    crate::leanh::lean_inc(v_log_3614_);
                    crate::leanh::lean_dec(v_a_3612_);
                    v___x_3619_ = crate::leanh::lean_box(0);
                    v_isShared_3620_ = v_isSharedCheck_3626_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3621_ = crate::leanh::lean_box(0);
                if v_isShared_3620_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3619_, 1, v_trace_3606_);
                    v___x_3623_ = v___x_3619_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3625_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3625_, 0, v_log_3614_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3625_, 1, v_trace_3606_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3625_, 2, v_buildTime_3617_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3625_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_action_3615_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3625_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_3616_,
                    );
                    v___x_3623_ = v_reuseFailAlloc_3625_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3624_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3624_, 0, v___x_3621_);
                crate::leanh::lean_ctor_set(v___x_3624_, 1, v___x_3623_);
                return v___x_3624_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_setTrace___boxed(
    mut v_trace_3628_: *mut crate::leanh::LeanObject,
    mut v_a_3629_: *mut crate::leanh::LeanObject,
    mut v_a_3630_: *mut crate::leanh::LeanObject,
    mut v_a_3631_: *mut crate::leanh::LeanObject,
    mut v_a_3632_: *mut crate::leanh::LeanObject,
    mut v_a_3633_: *mut crate::leanh::LeanObject,
    mut v_a_3634_: *mut crate::leanh::LeanObject,
    mut v_a_3635_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3636_ = l_Lake_setTrace(
        v_trace_3628_,
        v_a_3629_,
        v_a_3630_,
        v_a_3631_,
        v_a_3632_,
        v_a_3633_,
        v_a_3634_,
    );
    crate::leanh::lean_dec_ref(v_a_3633_);
    crate::leanh::lean_dec(v_a_3632_);
    crate::leanh::lean_dec(v_a_3631_);
    crate::leanh::lean_dec(v_a_3630_);
    crate::leanh::lean_dec_ref(v_a_3629_);
    return v_res_3636_;
}
pub unsafe fn l_Lake_newTrace___redArg(
    mut v_caption_3637_: *mut crate::leanh::LeanObject,
    mut v_a_3638_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_log_3640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_action_3641_: u8 = 0;
    let mut v_wantsRebuild_3642_: u8 = 0;
    let mut v_buildTime_3643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3646_: u8 = 0;
    let mut v___x_3647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3653_: u8 = 0;
    let mut v_unused_3654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_log_3640_ = crate::leanh::lean_ctor_get(v_a_3638_, 0);
                v_action_3641_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_3638_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_wantsRebuild_3642_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_3638_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                );
                v_buildTime_3643_ = crate::leanh::lean_ctor_get(v_a_3638_, 2);
                v_isSharedCheck_3653_ = (!crate::leanh::lean_is_exclusive(v_a_3638_)) as u8;
                if v_isSharedCheck_3653_ == 0 {
                    v_unused_3654_ = crate::leanh::lean_ctor_get(v_a_3638_, 1);
                    crate::leanh::lean_dec(v_unused_3654_);
                    v___x_3645_ = v_a_3638_;
                    v_isShared_3646_ = v_isSharedCheck_3653_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buildTime_3643_);
                    crate::leanh::lean_inc(v_log_3640_);
                    crate::leanh::lean_dec(v_a_3638_);
                    v___x_3645_ = crate::leanh::lean_box(0);
                    v_isShared_3646_ = v_isSharedCheck_3653_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3647_ = l_Lake_BuildTrace_nil(v_caption_3637_);
                v___x_3648_ = crate::leanh::lean_box(0);
                if v_isShared_3646_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3645_, 1, v___x_3647_);
                    v___x_3650_ = v___x_3645_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3652_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3652_, 0, v_log_3640_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3652_, 1, v___x_3647_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3652_, 2, v_buildTime_3643_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3652_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_action_3641_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3652_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_3642_,
                    );
                    v___x_3650_ = v_reuseFailAlloc_3652_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3651_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3651_, 0, v___x_3648_);
                crate::leanh::lean_ctor_set(v___x_3651_, 1, v___x_3650_);
                return v___x_3651_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_newTrace___redArg___boxed(
    mut v_caption_3655_: *mut crate::leanh::LeanObject,
    mut v_a_3656_: *mut crate::leanh::LeanObject,
    mut v_a_3657_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3658_ = l_Lake_newTrace___redArg(v_caption_3655_, v_a_3656_);
    return v_res_3658_;
}
pub unsafe fn l_Lake_newTrace(
    mut v_caption_3659_: *mut crate::leanh::LeanObject,
    mut v_a_3660_: *mut crate::leanh::LeanObject,
    mut v_a_3661_: *mut crate::leanh::LeanObject,
    mut v_a_3662_: *mut crate::leanh::LeanObject,
    mut v_a_3663_: *mut crate::leanh::LeanObject,
    mut v_a_3664_: *mut crate::leanh::LeanObject,
    mut v_a_3665_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_log_3667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_action_3668_: u8 = 0;
    let mut v_wantsRebuild_3669_: u8 = 0;
    let mut v_buildTime_3670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3673_: u8 = 0;
    let mut v___x_3674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3680_: u8 = 0;
    let mut v_unused_3681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_log_3667_ = crate::leanh::lean_ctor_get(v_a_3665_, 0);
                v_action_3668_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_3665_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_wantsRebuild_3669_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_3665_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                );
                v_buildTime_3670_ = crate::leanh::lean_ctor_get(v_a_3665_, 2);
                v_isSharedCheck_3680_ = (!crate::leanh::lean_is_exclusive(v_a_3665_)) as u8;
                if v_isSharedCheck_3680_ == 0 {
                    v_unused_3681_ = crate::leanh::lean_ctor_get(v_a_3665_, 1);
                    crate::leanh::lean_dec(v_unused_3681_);
                    v___x_3672_ = v_a_3665_;
                    v_isShared_3673_ = v_isSharedCheck_3680_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buildTime_3670_);
                    crate::leanh::lean_inc(v_log_3667_);
                    crate::leanh::lean_dec(v_a_3665_);
                    v___x_3672_ = crate::leanh::lean_box(0);
                    v_isShared_3673_ = v_isSharedCheck_3680_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3674_ = l_Lake_BuildTrace_nil(v_caption_3659_);
                v___x_3675_ = crate::leanh::lean_box(0);
                if v_isShared_3673_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3672_, 1, v___x_3674_);
                    v___x_3677_ = v___x_3672_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3679_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3679_, 0, v_log_3667_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3679_, 1, v___x_3674_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3679_, 2, v_buildTime_3670_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3679_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_action_3668_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3679_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_3669_,
                    );
                    v___x_3677_ = v_reuseFailAlloc_3679_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3678_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3678_, 0, v___x_3675_);
                crate::leanh::lean_ctor_set(v___x_3678_, 1, v___x_3677_);
                return v___x_3678_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_newTrace___boxed(
    mut v_caption_3682_: *mut crate::leanh::LeanObject,
    mut v_a_3683_: *mut crate::leanh::LeanObject,
    mut v_a_3684_: *mut crate::leanh::LeanObject,
    mut v_a_3685_: *mut crate::leanh::LeanObject,
    mut v_a_3686_: *mut crate::leanh::LeanObject,
    mut v_a_3687_: *mut crate::leanh::LeanObject,
    mut v_a_3688_: *mut crate::leanh::LeanObject,
    mut v_a_3689_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3690_ = l_Lake_newTrace(
        v_caption_3682_,
        v_a_3683_,
        v_a_3684_,
        v_a_3685_,
        v_a_3686_,
        v_a_3687_,
        v_a_3688_,
    );
    crate::leanh::lean_dec_ref(v_a_3687_);
    crate::leanh::lean_dec(v_a_3686_);
    crate::leanh::lean_dec(v_a_3685_);
    crate::leanh::lean_dec(v_a_3684_);
    crate::leanh::lean_dec_ref(v_a_3683_);
    return v_res_3690_;
}
pub unsafe fn l_Lake_modifyTrace___redArg(
    mut v_f_3691_: *mut crate::leanh::LeanObject,
    mut v_a_3692_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_log_3694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_action_3695_: u8 = 0;
    let mut v_wantsRebuild_3696_: u8 = 0;
    let mut v_trace_3697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildTime_3698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3701_: u8 = 0;
    let mut v___x_3702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3708_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_log_3694_ = crate::leanh::lean_ctor_get(v_a_3692_, 0);
                v_action_3695_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_3692_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_wantsRebuild_3696_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_3692_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                );
                v_trace_3697_ = crate::leanh::lean_ctor_get(v_a_3692_, 1);
                v_buildTime_3698_ = crate::leanh::lean_ctor_get(v_a_3692_, 2);
                v_isSharedCheck_3708_ = (!crate::leanh::lean_is_exclusive(v_a_3692_)) as u8;
                if v_isSharedCheck_3708_ == 0 {
                    v___x_3700_ = v_a_3692_;
                    v_isShared_3701_ = v_isSharedCheck_3708_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buildTime_3698_);
                    crate::leanh::lean_inc(v_trace_3697_);
                    crate::leanh::lean_inc(v_log_3694_);
                    crate::leanh::lean_dec(v_a_3692_);
                    v___x_3700_ = crate::leanh::lean_box(0);
                    v_isShared_3701_ = v_isSharedCheck_3708_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3702_ = crate::leanh::lean_box(0);
                v___x_3703_ = crate::leanh::lean_apply_1(v_f_3691_, v_trace_3697_);
                if v_isShared_3701_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3700_, 1, v___x_3703_);
                    v___x_3705_ = v___x_3700_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3707_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3707_, 0, v_log_3694_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3707_, 1, v___x_3703_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3707_, 2, v_buildTime_3698_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3707_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_action_3695_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3707_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_3696_,
                    );
                    v___x_3705_ = v_reuseFailAlloc_3707_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3706_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3706_, 0, v___x_3702_);
                crate::leanh::lean_ctor_set(v___x_3706_, 1, v___x_3705_);
                return v___x_3706_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_modifyTrace___redArg___boxed(
    mut v_f_3709_: *mut crate::leanh::LeanObject,
    mut v_a_3710_: *mut crate::leanh::LeanObject,
    mut v_a_3711_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3712_ = l_Lake_modifyTrace___redArg(v_f_3709_, v_a_3710_);
    return v_res_3712_;
}
pub unsafe fn l_Lake_modifyTrace(
    mut v_f_3713_: *mut crate::leanh::LeanObject,
    mut v_a_3714_: *mut crate::leanh::LeanObject,
    mut v_a_3715_: *mut crate::leanh::LeanObject,
    mut v_a_3716_: *mut crate::leanh::LeanObject,
    mut v_a_3717_: *mut crate::leanh::LeanObject,
    mut v_a_3718_: *mut crate::leanh::LeanObject,
    mut v_a_3719_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_log_3721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_action_3722_: u8 = 0;
    let mut v_wantsRebuild_3723_: u8 = 0;
    let mut v_trace_3724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildTime_3725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3728_: u8 = 0;
    let mut v___x_3729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3735_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_log_3721_ = crate::leanh::lean_ctor_get(v_a_3719_, 0);
                v_action_3722_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_3719_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_wantsRebuild_3723_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_3719_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                );
                v_trace_3724_ = crate::leanh::lean_ctor_get(v_a_3719_, 1);
                v_buildTime_3725_ = crate::leanh::lean_ctor_get(v_a_3719_, 2);
                v_isSharedCheck_3735_ = (!crate::leanh::lean_is_exclusive(v_a_3719_)) as u8;
                if v_isSharedCheck_3735_ == 0 {
                    v___x_3727_ = v_a_3719_;
                    v_isShared_3728_ = v_isSharedCheck_3735_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buildTime_3725_);
                    crate::leanh::lean_inc(v_trace_3724_);
                    crate::leanh::lean_inc(v_log_3721_);
                    crate::leanh::lean_dec(v_a_3719_);
                    v___x_3727_ = crate::leanh::lean_box(0);
                    v_isShared_3728_ = v_isSharedCheck_3735_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3729_ = crate::leanh::lean_box(0);
                v___x_3730_ = crate::leanh::lean_apply_1(v_f_3713_, v_trace_3724_);
                if v_isShared_3728_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3727_, 1, v___x_3730_);
                    v___x_3732_ = v___x_3727_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3734_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3734_, 0, v_log_3721_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3734_, 1, v___x_3730_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3734_, 2, v_buildTime_3725_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3734_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_action_3722_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3734_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_3723_,
                    );
                    v___x_3732_ = v_reuseFailAlloc_3734_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3733_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3733_, 0, v___x_3729_);
                crate::leanh::lean_ctor_set(v___x_3733_, 1, v___x_3732_);
                return v___x_3733_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_modifyTrace___boxed(
    mut v_f_3736_: *mut crate::leanh::LeanObject,
    mut v_a_3737_: *mut crate::leanh::LeanObject,
    mut v_a_3738_: *mut crate::leanh::LeanObject,
    mut v_a_3739_: *mut crate::leanh::LeanObject,
    mut v_a_3740_: *mut crate::leanh::LeanObject,
    mut v_a_3741_: *mut crate::leanh::LeanObject,
    mut v_a_3742_: *mut crate::leanh::LeanObject,
    mut v_a_3743_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3744_ = l_Lake_modifyTrace(
        v_f_3736_, v_a_3737_, v_a_3738_, v_a_3739_, v_a_3740_, v_a_3741_, v_a_3742_,
    );
    crate::leanh::lean_dec_ref(v_a_3741_);
    crate::leanh::lean_dec(v_a_3740_);
    crate::leanh::lean_dec(v_a_3739_);
    crate::leanh::lean_dec(v_a_3738_);
    crate::leanh::lean_dec_ref(v_a_3737_);
    return v_res_3744_;
}
pub unsafe fn l_Lake_setTraceCaption___redArg(
    mut v_caption_3745_: *mut crate::leanh::LeanObject,
    mut v_a_3746_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_trace_3748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_log_3749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_action_3750_: u8 = 0;
    let mut v_wantsRebuild_3751_: u8 = 0;
    let mut v_buildTime_3752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3755_: u8 = 0;
    let mut v_inputs_3756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hash_3757_: u64 = 0;
    let mut v_mtime_3758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3761_: u8 = 0;
    let mut v___x_3762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3770_: u8 = 0;
    let mut v_unused_3771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3772_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_trace_3748_ = crate::leanh::lean_ctor_get(v_a_3746_, 1);
                v_log_3749_ = crate::leanh::lean_ctor_get(v_a_3746_, 0);
                v_action_3750_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_3746_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_wantsRebuild_3751_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_3746_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                );
                v_buildTime_3752_ = crate::leanh::lean_ctor_get(v_a_3746_, 2);
                v_isSharedCheck_3772_ = (!crate::leanh::lean_is_exclusive(v_a_3746_)) as u8;
                if v_isSharedCheck_3772_ == 0 {
                    v___x_3754_ = v_a_3746_;
                    v_isShared_3755_ = v_isSharedCheck_3772_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buildTime_3752_);
                    crate::leanh::lean_inc(v_trace_3748_);
                    crate::leanh::lean_inc(v_log_3749_);
                    crate::leanh::lean_dec(v_a_3746_);
                    v___x_3754_ = crate::leanh::lean_box(0);
                    v_isShared_3755_ = v_isSharedCheck_3772_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_inputs_3756_ = crate::leanh::lean_ctor_get(v_trace_3748_, 1);
                v_hash_3757_ = crate::leanh::lean_ctor_get_uint64(
                    v_trace_3748_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_mtime_3758_ = crate::leanh::lean_ctor_get(v_trace_3748_, 2);
                v_isSharedCheck_3770_ = (!crate::leanh::lean_is_exclusive(v_trace_3748_)) as u8;
                if v_isSharedCheck_3770_ == 0 {
                    v_unused_3771_ = crate::leanh::lean_ctor_get(v_trace_3748_, 0);
                    crate::leanh::lean_dec(v_unused_3771_);
                    v___x_3760_ = v_trace_3748_;
                    v_isShared_3761_ = v_isSharedCheck_3770_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_mtime_3758_);
                    crate::leanh::lean_inc(v_inputs_3756_);
                    crate::leanh::lean_dec(v_trace_3748_);
                    v___x_3760_ = crate::leanh::lean_box(0);
                    v_isShared_3761_ = v_isSharedCheck_3770_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3762_ = crate::leanh::lean_box(0);
                if v_isShared_3761_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3760_, 0, v_caption_3745_);
                    v___x_3764_ = v___x_3760_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3769_ = crate::leanh::lean_alloc_ctor(0, 3, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3769_, 0, v_caption_3745_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3769_, 1, v_inputs_3756_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3769_, 2, v_mtime_3758_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_3769_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_hash_3757_,
                    );
                    v___x_3764_ = v_reuseFailAlloc_3769_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3755_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3754_, 1, v___x_3764_);
                    v___x_3766_ = v___x_3754_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3768_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3768_, 0, v_log_3749_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3768_, 1, v___x_3764_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3768_, 2, v_buildTime_3752_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3768_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_action_3750_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3768_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_3751_,
                    );
                    v___x_3766_ = v_reuseFailAlloc_3768_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3767_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3767_, 0, v___x_3762_);
                crate::leanh::lean_ctor_set(v___x_3767_, 1, v___x_3766_);
                return v___x_3767_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_setTraceCaption___redArg___boxed(
    mut v_caption_3773_: *mut crate::leanh::LeanObject,
    mut v_a_3774_: *mut crate::leanh::LeanObject,
    mut v_a_3775_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3776_ = l_Lake_setTraceCaption___redArg(v_caption_3773_, v_a_3774_);
    return v_res_3776_;
}
pub unsafe fn l_Lake_setTraceCaption(
    mut v_caption_3777_: *mut crate::leanh::LeanObject,
    mut v_a_3778_: *mut crate::leanh::LeanObject,
    mut v_a_3779_: *mut crate::leanh::LeanObject,
    mut v_a_3780_: *mut crate::leanh::LeanObject,
    mut v_a_3781_: *mut crate::leanh::LeanObject,
    mut v_a_3782_: *mut crate::leanh::LeanObject,
    mut v_a_3783_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_trace_3785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_log_3786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_action_3787_: u8 = 0;
    let mut v_wantsRebuild_3788_: u8 = 0;
    let mut v_buildTime_3789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3792_: u8 = 0;
    let mut v_inputs_3793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hash_3794_: u64 = 0;
    let mut v_mtime_3795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3798_: u8 = 0;
    let mut v___x_3799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3807_: u8 = 0;
    let mut v_unused_3808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3809_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_trace_3785_ = crate::leanh::lean_ctor_get(v_a_3783_, 1);
                v_log_3786_ = crate::leanh::lean_ctor_get(v_a_3783_, 0);
                v_action_3787_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_3783_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_wantsRebuild_3788_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_3783_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                );
                v_buildTime_3789_ = crate::leanh::lean_ctor_get(v_a_3783_, 2);
                v_isSharedCheck_3809_ = (!crate::leanh::lean_is_exclusive(v_a_3783_)) as u8;
                if v_isSharedCheck_3809_ == 0 {
                    v___x_3791_ = v_a_3783_;
                    v_isShared_3792_ = v_isSharedCheck_3809_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buildTime_3789_);
                    crate::leanh::lean_inc(v_trace_3785_);
                    crate::leanh::lean_inc(v_log_3786_);
                    crate::leanh::lean_dec(v_a_3783_);
                    v___x_3791_ = crate::leanh::lean_box(0);
                    v_isShared_3792_ = v_isSharedCheck_3809_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_inputs_3793_ = crate::leanh::lean_ctor_get(v_trace_3785_, 1);
                v_hash_3794_ = crate::leanh::lean_ctor_get_uint64(
                    v_trace_3785_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_mtime_3795_ = crate::leanh::lean_ctor_get(v_trace_3785_, 2);
                v_isSharedCheck_3807_ = (!crate::leanh::lean_is_exclusive(v_trace_3785_)) as u8;
                if v_isSharedCheck_3807_ == 0 {
                    v_unused_3808_ = crate::leanh::lean_ctor_get(v_trace_3785_, 0);
                    crate::leanh::lean_dec(v_unused_3808_);
                    v___x_3797_ = v_trace_3785_;
                    v_isShared_3798_ = v_isSharedCheck_3807_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_mtime_3795_);
                    crate::leanh::lean_inc(v_inputs_3793_);
                    crate::leanh::lean_dec(v_trace_3785_);
                    v___x_3797_ = crate::leanh::lean_box(0);
                    v_isShared_3798_ = v_isSharedCheck_3807_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3799_ = crate::leanh::lean_box(0);
                if v_isShared_3798_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3797_, 0, v_caption_3777_);
                    v___x_3801_ = v___x_3797_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3806_ = crate::leanh::lean_alloc_ctor(0, 3, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3806_, 0, v_caption_3777_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3806_, 1, v_inputs_3793_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3806_, 2, v_mtime_3795_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_3806_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_hash_3794_,
                    );
                    v___x_3801_ = v_reuseFailAlloc_3806_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3792_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3791_, 1, v___x_3801_);
                    v___x_3803_ = v___x_3791_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3805_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3805_, 0, v_log_3786_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3805_, 1, v___x_3801_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3805_, 2, v_buildTime_3789_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3805_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_action_3787_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3805_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_3788_,
                    );
                    v___x_3803_ = v_reuseFailAlloc_3805_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3804_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3804_, 0, v___x_3799_);
                crate::leanh::lean_ctor_set(v___x_3804_, 1, v___x_3803_);
                return v___x_3804_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_setTraceCaption___boxed(
    mut v_caption_3810_: *mut crate::leanh::LeanObject,
    mut v_a_3811_: *mut crate::leanh::LeanObject,
    mut v_a_3812_: *mut crate::leanh::LeanObject,
    mut v_a_3813_: *mut crate::leanh::LeanObject,
    mut v_a_3814_: *mut crate::leanh::LeanObject,
    mut v_a_3815_: *mut crate::leanh::LeanObject,
    mut v_a_3816_: *mut crate::leanh::LeanObject,
    mut v_a_3817_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3818_ = l_Lake_setTraceCaption(
        v_caption_3810_,
        v_a_3811_,
        v_a_3812_,
        v_a_3813_,
        v_a_3814_,
        v_a_3815_,
        v_a_3816_,
    );
    crate::leanh::lean_dec_ref(v_a_3815_);
    crate::leanh::lean_dec(v_a_3814_);
    crate::leanh::lean_dec(v_a_3813_);
    crate::leanh::lean_dec(v_a_3812_);
    crate::leanh::lean_dec_ref(v_a_3811_);
    return v_res_3818_;
}
pub unsafe fn _init_l_Lake_takeTrace___redArg___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_3820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3820_ = l_Lake_takeTrace___redArg___closed__0;
    v___x_3821_ = l_Lake_BuildTrace_nil(v___x_3820_);
    return v___x_3821_;
}
pub unsafe fn l_Lake_takeTrace___redArg(
    mut v_a_3822_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_log_3824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_action_3825_: u8 = 0;
    let mut v_wantsRebuild_3826_: u8 = 0;
    let mut v_trace_3827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildTime_3828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3831_: u8 = 0;
    let mut v___x_3832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3837_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_log_3824_ = crate::leanh::lean_ctor_get(v_a_3822_, 0);
                v_action_3825_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_3822_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_wantsRebuild_3826_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_3822_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                );
                v_trace_3827_ = crate::leanh::lean_ctor_get(v_a_3822_, 1);
                v_buildTime_3828_ = crate::leanh::lean_ctor_get(v_a_3822_, 2);
                v_isSharedCheck_3837_ = (!crate::leanh::lean_is_exclusive(v_a_3822_)) as u8;
                if v_isSharedCheck_3837_ == 0 {
                    v___x_3830_ = v_a_3822_;
                    v_isShared_3831_ = v_isSharedCheck_3837_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buildTime_3828_);
                    crate::leanh::lean_inc(v_trace_3827_);
                    crate::leanh::lean_inc(v_log_3824_);
                    crate::leanh::lean_dec(v_a_3822_);
                    v___x_3830_ = crate::leanh::lean_box(0);
                    v_isShared_3831_ = v_isSharedCheck_3837_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3832_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lake_takeTrace___redArg___closed__1),
                    core::ptr::addr_of_mut!(l_Lake_takeTrace___redArg___closed__1_once),
                    _init_l_Lake_takeTrace___redArg___closed__1,
                );
                if v_isShared_3831_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3830_, 1, v___x_3832_);
                    v___x_3834_ = v___x_3830_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3836_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3836_, 0, v_log_3824_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3836_, 1, v___x_3832_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3836_, 2, v_buildTime_3828_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3836_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_action_3825_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3836_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_3826_,
                    );
                    v___x_3834_ = v_reuseFailAlloc_3836_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3835_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3835_, 0, v_trace_3827_);
                crate::leanh::lean_ctor_set(v___x_3835_, 1, v___x_3834_);
                return v___x_3835_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_takeTrace___redArg___boxed(
    mut v_a_3838_: *mut crate::leanh::LeanObject,
    mut v_a_3839_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3840_ = l_Lake_takeTrace___redArg(v_a_3838_);
    return v_res_3840_;
}
pub unsafe fn l_Lake_takeTrace(
    mut v_a_3841_: *mut crate::leanh::LeanObject,
    mut v_a_3842_: *mut crate::leanh::LeanObject,
    mut v_a_3843_: *mut crate::leanh::LeanObject,
    mut v_a_3844_: *mut crate::leanh::LeanObject,
    mut v_a_3845_: *mut crate::leanh::LeanObject,
    mut v_a_3846_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_log_3848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_action_3849_: u8 = 0;
    let mut v_wantsRebuild_3850_: u8 = 0;
    let mut v_trace_3851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildTime_3852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3855_: u8 = 0;
    let mut v___x_3856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3861_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_log_3848_ = crate::leanh::lean_ctor_get(v_a_3846_, 0);
                v_action_3849_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_3846_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_wantsRebuild_3850_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_3846_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                );
                v_trace_3851_ = crate::leanh::lean_ctor_get(v_a_3846_, 1);
                v_buildTime_3852_ = crate::leanh::lean_ctor_get(v_a_3846_, 2);
                v_isSharedCheck_3861_ = (!crate::leanh::lean_is_exclusive(v_a_3846_)) as u8;
                if v_isSharedCheck_3861_ == 0 {
                    v___x_3854_ = v_a_3846_;
                    v_isShared_3855_ = v_isSharedCheck_3861_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buildTime_3852_);
                    crate::leanh::lean_inc(v_trace_3851_);
                    crate::leanh::lean_inc(v_log_3848_);
                    crate::leanh::lean_dec(v_a_3846_);
                    v___x_3854_ = crate::leanh::lean_box(0);
                    v_isShared_3855_ = v_isSharedCheck_3861_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3856_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lake_takeTrace___redArg___closed__1),
                    core::ptr::addr_of_mut!(l_Lake_takeTrace___redArg___closed__1_once),
                    _init_l_Lake_takeTrace___redArg___closed__1,
                );
                if v_isShared_3855_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3854_, 1, v___x_3856_);
                    v___x_3858_ = v___x_3854_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3860_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3860_, 0, v_log_3848_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3860_, 1, v___x_3856_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3860_, 2, v_buildTime_3852_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3860_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_action_3849_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3860_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_3850_,
                    );
                    v___x_3858_ = v_reuseFailAlloc_3860_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3859_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3859_, 0, v_trace_3851_);
                crate::leanh::lean_ctor_set(v___x_3859_, 1, v___x_3858_);
                return v___x_3859_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_takeTrace___boxed(
    mut v_a_3862_: *mut crate::leanh::LeanObject,
    mut v_a_3863_: *mut crate::leanh::LeanObject,
    mut v_a_3864_: *mut crate::leanh::LeanObject,
    mut v_a_3865_: *mut crate::leanh::LeanObject,
    mut v_a_3866_: *mut crate::leanh::LeanObject,
    mut v_a_3867_: *mut crate::leanh::LeanObject,
    mut v_a_3868_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3869_ = l_Lake_takeTrace(
        v_a_3862_, v_a_3863_, v_a_3864_, v_a_3865_, v_a_3866_, v_a_3867_,
    );
    crate::leanh::lean_dec_ref(v_a_3866_);
    crate::leanh::lean_dec(v_a_3865_);
    crate::leanh::lean_dec(v_a_3864_);
    crate::leanh::lean_dec(v_a_3863_);
    crate::leanh::lean_dec_ref(v_a_3862_);
    return v_res_3869_;
}
pub unsafe fn l_Lake_swapTrace___redArg(
    mut v_trace_3870_: *mut crate::leanh::LeanObject,
    mut v_a_3871_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_log_3873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_action_3874_: u8 = 0;
    let mut v_wantsRebuild_3875_: u8 = 0;
    let mut v_trace_3876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildTime_3877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3880_: u8 = 0;
    let mut v___x_3882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3885_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_log_3873_ = crate::leanh::lean_ctor_get(v_a_3871_, 0);
                v_action_3874_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_3871_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_wantsRebuild_3875_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_3871_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                );
                v_trace_3876_ = crate::leanh::lean_ctor_get(v_a_3871_, 1);
                v_buildTime_3877_ = crate::leanh::lean_ctor_get(v_a_3871_, 2);
                v_isSharedCheck_3885_ = (!crate::leanh::lean_is_exclusive(v_a_3871_)) as u8;
                if v_isSharedCheck_3885_ == 0 {
                    v___x_3879_ = v_a_3871_;
                    v_isShared_3880_ = v_isSharedCheck_3885_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buildTime_3877_);
                    crate::leanh::lean_inc(v_trace_3876_);
                    crate::leanh::lean_inc(v_log_3873_);
                    crate::leanh::lean_dec(v_a_3871_);
                    v___x_3879_ = crate::leanh::lean_box(0);
                    v_isShared_3880_ = v_isSharedCheck_3885_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_3880_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3879_, 1, v_trace_3870_);
                    v___x_3882_ = v___x_3879_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3884_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3884_, 0, v_log_3873_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3884_, 1, v_trace_3870_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3884_, 2, v_buildTime_3877_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3884_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_action_3874_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3884_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_3875_,
                    );
                    v___x_3882_ = v_reuseFailAlloc_3884_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3883_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3883_, 0, v_trace_3876_);
                crate::leanh::lean_ctor_set(v___x_3883_, 1, v___x_3882_);
                return v___x_3883_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_swapTrace___redArg___boxed(
    mut v_trace_3886_: *mut crate::leanh::LeanObject,
    mut v_a_3887_: *mut crate::leanh::LeanObject,
    mut v_a_3888_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3889_ = l_Lake_swapTrace___redArg(v_trace_3886_, v_a_3887_);
    return v_res_3889_;
}
pub unsafe fn l_Lake_swapTrace(
    mut v_trace_3890_: *mut crate::leanh::LeanObject,
    mut v_a_3891_: *mut crate::leanh::LeanObject,
    mut v_a_3892_: *mut crate::leanh::LeanObject,
    mut v_a_3893_: *mut crate::leanh::LeanObject,
    mut v_a_3894_: *mut crate::leanh::LeanObject,
    mut v_a_3895_: *mut crate::leanh::LeanObject,
    mut v_a_3896_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_log_3898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_action_3899_: u8 = 0;
    let mut v_wantsRebuild_3900_: u8 = 0;
    let mut v_trace_3901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildTime_3902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3905_: u8 = 0;
    let mut v___x_3907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3910_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_log_3898_ = crate::leanh::lean_ctor_get(v_a_3896_, 0);
                v_action_3899_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_3896_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_wantsRebuild_3900_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_3896_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                );
                v_trace_3901_ = crate::leanh::lean_ctor_get(v_a_3896_, 1);
                v_buildTime_3902_ = crate::leanh::lean_ctor_get(v_a_3896_, 2);
                v_isSharedCheck_3910_ = (!crate::leanh::lean_is_exclusive(v_a_3896_)) as u8;
                if v_isSharedCheck_3910_ == 0 {
                    v___x_3904_ = v_a_3896_;
                    v_isShared_3905_ = v_isSharedCheck_3910_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buildTime_3902_);
                    crate::leanh::lean_inc(v_trace_3901_);
                    crate::leanh::lean_inc(v_log_3898_);
                    crate::leanh::lean_dec(v_a_3896_);
                    v___x_3904_ = crate::leanh::lean_box(0);
                    v_isShared_3905_ = v_isSharedCheck_3910_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_3905_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3904_, 1, v_trace_3890_);
                    v___x_3907_ = v___x_3904_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3909_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3909_, 0, v_log_3898_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3909_, 1, v_trace_3890_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3909_, 2, v_buildTime_3902_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3909_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_action_3899_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3909_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_3900_,
                    );
                    v___x_3907_ = v_reuseFailAlloc_3909_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3908_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3908_, 0, v_trace_3901_);
                crate::leanh::lean_ctor_set(v___x_3908_, 1, v___x_3907_);
                return v___x_3908_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_swapTrace___boxed(
    mut v_trace_3911_: *mut crate::leanh::LeanObject,
    mut v_a_3912_: *mut crate::leanh::LeanObject,
    mut v_a_3913_: *mut crate::leanh::LeanObject,
    mut v_a_3914_: *mut crate::leanh::LeanObject,
    mut v_a_3915_: *mut crate::leanh::LeanObject,
    mut v_a_3916_: *mut crate::leanh::LeanObject,
    mut v_a_3917_: *mut crate::leanh::LeanObject,
    mut v_a_3918_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3919_ = l_Lake_swapTrace(
        v_trace_3911_,
        v_a_3912_,
        v_a_3913_,
        v_a_3914_,
        v_a_3915_,
        v_a_3916_,
        v_a_3917_,
    );
    crate::leanh::lean_dec_ref(v_a_3916_);
    crate::leanh::lean_dec(v_a_3915_);
    crate::leanh::lean_dec(v_a_3914_);
    crate::leanh::lean_dec(v_a_3913_);
    crate::leanh::lean_dec_ref(v_a_3912_);
    return v_res_3919_;
}
pub unsafe fn l_Lake_addTrace___redArg(
    mut v_trace_3920_: *mut crate::leanh::LeanObject,
    mut v_a_3921_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_log_3923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_action_3924_: u8 = 0;
    let mut v_wantsRebuild_3925_: u8 = 0;
    let mut v_trace_3926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildTime_3927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3930_: u8 = 0;
    let mut v___x_3931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3937_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_log_3923_ = crate::leanh::lean_ctor_get(v_a_3921_, 0);
                v_action_3924_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_3921_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_wantsRebuild_3925_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_3921_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                );
                v_trace_3926_ = crate::leanh::lean_ctor_get(v_a_3921_, 1);
                v_buildTime_3927_ = crate::leanh::lean_ctor_get(v_a_3921_, 2);
                v_isSharedCheck_3937_ = (!crate::leanh::lean_is_exclusive(v_a_3921_)) as u8;
                if v_isSharedCheck_3937_ == 0 {
                    v___x_3929_ = v_a_3921_;
                    v_isShared_3930_ = v_isSharedCheck_3937_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buildTime_3927_);
                    crate::leanh::lean_inc(v_trace_3926_);
                    crate::leanh::lean_inc(v_log_3923_);
                    crate::leanh::lean_dec(v_a_3921_);
                    v___x_3929_ = crate::leanh::lean_box(0);
                    v_isShared_3930_ = v_isSharedCheck_3937_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3931_ = crate::leanh::lean_box(0);
                v___x_3932_ = l_Lake_BuildTrace_mix(v_trace_3926_, v_trace_3920_);
                if v_isShared_3930_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3929_, 1, v___x_3932_);
                    v___x_3934_ = v___x_3929_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3936_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3936_, 0, v_log_3923_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3936_, 1, v___x_3932_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3936_, 2, v_buildTime_3927_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3936_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_action_3924_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3936_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_3925_,
                    );
                    v___x_3934_ = v_reuseFailAlloc_3936_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3935_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3935_, 0, v___x_3931_);
                crate::leanh::lean_ctor_set(v___x_3935_, 1, v___x_3934_);
                return v___x_3935_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_addTrace___redArg___boxed(
    mut v_trace_3938_: *mut crate::leanh::LeanObject,
    mut v_a_3939_: *mut crate::leanh::LeanObject,
    mut v_a_3940_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3941_ = l_Lake_addTrace___redArg(v_trace_3938_, v_a_3939_);
    return v_res_3941_;
}
pub unsafe fn l_Lake_addTrace(
    mut v_trace_3942_: *mut crate::leanh::LeanObject,
    mut v_a_3943_: *mut crate::leanh::LeanObject,
    mut v_a_3944_: *mut crate::leanh::LeanObject,
    mut v_a_3945_: *mut crate::leanh::LeanObject,
    mut v_a_3946_: *mut crate::leanh::LeanObject,
    mut v_a_3947_: *mut crate::leanh::LeanObject,
    mut v_a_3948_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_log_3950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_action_3951_: u8 = 0;
    let mut v_wantsRebuild_3952_: u8 = 0;
    let mut v_trace_3953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildTime_3954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3957_: u8 = 0;
    let mut v___x_3958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3964_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_log_3950_ = crate::leanh::lean_ctor_get(v_a_3948_, 0);
                v_action_3951_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_3948_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_wantsRebuild_3952_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_3948_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                );
                v_trace_3953_ = crate::leanh::lean_ctor_get(v_a_3948_, 1);
                v_buildTime_3954_ = crate::leanh::lean_ctor_get(v_a_3948_, 2);
                v_isSharedCheck_3964_ = (!crate::leanh::lean_is_exclusive(v_a_3948_)) as u8;
                if v_isSharedCheck_3964_ == 0 {
                    v___x_3956_ = v_a_3948_;
                    v_isShared_3957_ = v_isSharedCheck_3964_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buildTime_3954_);
                    crate::leanh::lean_inc(v_trace_3953_);
                    crate::leanh::lean_inc(v_log_3950_);
                    crate::leanh::lean_dec(v_a_3948_);
                    v___x_3956_ = crate::leanh::lean_box(0);
                    v_isShared_3957_ = v_isSharedCheck_3964_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3958_ = crate::leanh::lean_box(0);
                v___x_3959_ = l_Lake_BuildTrace_mix(v_trace_3953_, v_trace_3942_);
                if v_isShared_3957_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3956_, 1, v___x_3959_);
                    v___x_3961_ = v___x_3956_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3963_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3963_, 0, v_log_3950_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3963_, 1, v___x_3959_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3963_, 2, v_buildTime_3954_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3963_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_action_3951_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3963_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_3952_,
                    );
                    v___x_3961_ = v_reuseFailAlloc_3963_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3962_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3962_, 0, v___x_3958_);
                crate::leanh::lean_ctor_set(v___x_3962_, 1, v___x_3961_);
                return v___x_3962_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_addTrace___boxed(
    mut v_trace_3965_: *mut crate::leanh::LeanObject,
    mut v_a_3966_: *mut crate::leanh::LeanObject,
    mut v_a_3967_: *mut crate::leanh::LeanObject,
    mut v_a_3968_: *mut crate::leanh::LeanObject,
    mut v_a_3969_: *mut crate::leanh::LeanObject,
    mut v_a_3970_: *mut crate::leanh::LeanObject,
    mut v_a_3971_: *mut crate::leanh::LeanObject,
    mut v_a_3972_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3973_ = l_Lake_addTrace(
        v_trace_3965_,
        v_a_3966_,
        v_a_3967_,
        v_a_3968_,
        v_a_3969_,
        v_a_3970_,
        v_a_3971_,
    );
    crate::leanh::lean_dec_ref(v_a_3970_);
    crate::leanh::lean_dec(v_a_3969_);
    crate::leanh::lean_dec(v_a_3968_);
    crate::leanh::lean_dec(v_a_3967_);
    crate::leanh::lean_dec_ref(v_a_3966_);
    return v_res_3973_;
}
pub unsafe fn l_Lake_addSubTrace___redArg(
    mut v_caption_3974_: *mut crate::leanh::LeanObject,
    mut v_x_3975_: *mut crate::leanh::LeanObject,
    mut v_a_3976_: *mut crate::leanh::LeanObject,
    mut v_a_3977_: *mut crate::leanh::LeanObject,
    mut v_a_3978_: *mut crate::leanh::LeanObject,
    mut v_a_3979_: *mut crate::leanh::LeanObject,
    mut v_a_3980_: *mut crate::leanh::LeanObject,
    mut v_a_3981_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_log_3983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_action_3984_: u8 = 0;
    let mut v_wantsRebuild_3985_: u8 = 0;
    let mut v_trace_3986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildTime_3987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3990_: u8 = 0;
    let mut v___x_3991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3999_: u8 = 0;
    let mut v_log_4000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_action_4001_: u8 = 0;
    let mut v_wantsRebuild_4002_: u8 = 0;
    let mut v_trace_4003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildTime_4004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4007_: u8 = 0;
    let mut v___x_4008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4015_: u8 = 0;
    let mut v_isSharedCheck_4016_: u8 = 0;
    let mut v_reuseFailAlloc_4017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4018_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_log_3983_ = crate::leanh::lean_ctor_get(v_a_3981_, 0);
                v_action_3984_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_3981_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_wantsRebuild_3985_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_3981_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                );
                v_trace_3986_ = crate::leanh::lean_ctor_get(v_a_3981_, 1);
                v_buildTime_3987_ = crate::leanh::lean_ctor_get(v_a_3981_, 2);
                v_isSharedCheck_4018_ = (!crate::leanh::lean_is_exclusive(v_a_3981_)) as u8;
                if v_isSharedCheck_4018_ == 0 {
                    v___x_3989_ = v_a_3981_;
                    v_isShared_3990_ = v_isSharedCheck_4018_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buildTime_3987_);
                    crate::leanh::lean_inc(v_trace_3986_);
                    crate::leanh::lean_inc(v_log_3983_);
                    crate::leanh::lean_dec(v_a_3981_);
                    v___x_3989_ = crate::leanh::lean_box(0);
                    v_isShared_3990_ = v_isSharedCheck_4018_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3991_ = l_Lake_BuildTrace_nil(v_caption_3974_);
                if v_isShared_3990_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3989_, 1, v___x_3991_);
                    v___x_3993_ = v___x_3989_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4017_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4017_, 0, v_log_3983_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4017_, 1, v___x_3991_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4017_, 2, v_buildTime_3987_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4017_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_action_3984_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4017_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_3985_,
                    );
                    v___x_3993_ = v_reuseFailAlloc_4017_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc_ref(v_a_3980_);
                crate::leanh::lean_inc(v_a_3979_);
                crate::leanh::lean_inc(v_a_3978_);
                crate::leanh::lean_inc(v_a_3977_);
                v___x_3994_ = crate::leanh::lean_apply_7(
                    v_x_3975_,
                    v_a_3976_,
                    v_a_3977_,
                    v_a_3978_,
                    v_a_3979_,
                    v_a_3980_,
                    v___x_3993_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_3994_) == 0 {
                    v_a_3995_ = crate::leanh::lean_ctor_get(v___x_3994_, 1);
                    v_a_3996_ = crate::leanh::lean_ctor_get(v___x_3994_, 0);
                    v_isSharedCheck_4016_ = (!crate::leanh::lean_is_exclusive(v___x_3994_)) as u8;
                    if v_isSharedCheck_4016_ == 0 {
                        v___x_3998_ = v___x_3994_;
                        v_isShared_3999_ = v_isSharedCheck_4016_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3995_);
                        crate::leanh::lean_inc(v_a_3996_);
                        crate::leanh::lean_dec(v___x_3994_);
                        v___x_3998_ = crate::leanh::lean_box(0);
                        v_isShared_3999_ = v_isSharedCheck_4016_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_trace_3986_);
                    return v___x_3994_;
                }
            }
            3 => {
                v_log_4000_ = crate::leanh::lean_ctor_get(v_a_3995_, 0);
                v_action_4001_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_3995_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_wantsRebuild_4002_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_3995_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                );
                v_trace_4003_ = crate::leanh::lean_ctor_get(v_a_3995_, 1);
                v_buildTime_4004_ = crate::leanh::lean_ctor_get(v_a_3995_, 2);
                v_isSharedCheck_4015_ = (!crate::leanh::lean_is_exclusive(v_a_3995_)) as u8;
                if v_isSharedCheck_4015_ == 0 {
                    v___x_4006_ = v_a_3995_;
                    v_isShared_4007_ = v_isSharedCheck_4015_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buildTime_4004_);
                    crate::leanh::lean_inc(v_trace_4003_);
                    crate::leanh::lean_inc(v_log_4000_);
                    crate::leanh::lean_dec(v_a_3995_);
                    v___x_4006_ = crate::leanh::lean_box(0);
                    v_isShared_4007_ = v_isSharedCheck_4015_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4008_ = l_Lake_BuildTrace_mix(v_trace_3986_, v_trace_4003_);
                if v_isShared_4007_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4006_, 1, v___x_4008_);
                    v___x_4010_ = v___x_4006_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4014_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4014_, 0, v_log_4000_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4014_, 1, v___x_4008_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4014_, 2, v_buildTime_4004_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4014_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_action_4001_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4014_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_4002_,
                    );
                    v___x_4010_ = v_reuseFailAlloc_4014_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_3999_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3998_, 1, v___x_4010_);
                    v___x_4012_ = v___x_3998_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4013_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4013_, 0, v_a_3996_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4013_, 1, v___x_4010_);
                    v___x_4012_ = v_reuseFailAlloc_4013_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4012_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_addSubTrace___redArg___boxed(
    mut v_caption_4019_: *mut crate::leanh::LeanObject,
    mut v_x_4020_: *mut crate::leanh::LeanObject,
    mut v_a_4021_: *mut crate::leanh::LeanObject,
    mut v_a_4022_: *mut crate::leanh::LeanObject,
    mut v_a_4023_: *mut crate::leanh::LeanObject,
    mut v_a_4024_: *mut crate::leanh::LeanObject,
    mut v_a_4025_: *mut crate::leanh::LeanObject,
    mut v_a_4026_: *mut crate::leanh::LeanObject,
    mut v_a_4027_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4028_ = l_Lake_addSubTrace___redArg(
        v_caption_4019_,
        v_x_4020_,
        v_a_4021_,
        v_a_4022_,
        v_a_4023_,
        v_a_4024_,
        v_a_4025_,
        v_a_4026_,
    );
    crate::leanh::lean_dec_ref(v_a_4025_);
    crate::leanh::lean_dec(v_a_4024_);
    crate::leanh::lean_dec(v_a_4023_);
    crate::leanh::lean_dec(v_a_4022_);
    return v_res_4028_;
}
pub unsafe fn l_Lake_addSubTrace(
    mut v_00_u03b1_4029_: *mut crate::leanh::LeanObject,
    mut v_caption_4030_: *mut crate::leanh::LeanObject,
    mut v_x_4031_: *mut crate::leanh::LeanObject,
    mut v_a_4032_: *mut crate::leanh::LeanObject,
    mut v_a_4033_: *mut crate::leanh::LeanObject,
    mut v_a_4034_: *mut crate::leanh::LeanObject,
    mut v_a_4035_: *mut crate::leanh::LeanObject,
    mut v_a_4036_: *mut crate::leanh::LeanObject,
    mut v_a_4037_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_log_4039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_action_4040_: u8 = 0;
    let mut v_wantsRebuild_4041_: u8 = 0;
    let mut v_trace_4042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildTime_4043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4046_: u8 = 0;
    let mut v___x_4047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4055_: u8 = 0;
    let mut v_log_4056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_action_4057_: u8 = 0;
    let mut v_wantsRebuild_4058_: u8 = 0;
    let mut v_trace_4059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildTime_4060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4063_: u8 = 0;
    let mut v___x_4064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4071_: u8 = 0;
    let mut v_isSharedCheck_4072_: u8 = 0;
    let mut v_reuseFailAlloc_4073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4074_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_log_4039_ = crate::leanh::lean_ctor_get(v_a_4037_, 0);
                v_action_4040_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_4037_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_wantsRebuild_4041_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_4037_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                );
                v_trace_4042_ = crate::leanh::lean_ctor_get(v_a_4037_, 1);
                v_buildTime_4043_ = crate::leanh::lean_ctor_get(v_a_4037_, 2);
                v_isSharedCheck_4074_ = (!crate::leanh::lean_is_exclusive(v_a_4037_)) as u8;
                if v_isSharedCheck_4074_ == 0 {
                    v___x_4045_ = v_a_4037_;
                    v_isShared_4046_ = v_isSharedCheck_4074_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buildTime_4043_);
                    crate::leanh::lean_inc(v_trace_4042_);
                    crate::leanh::lean_inc(v_log_4039_);
                    crate::leanh::lean_dec(v_a_4037_);
                    v___x_4045_ = crate::leanh::lean_box(0);
                    v_isShared_4046_ = v_isSharedCheck_4074_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4047_ = l_Lake_BuildTrace_nil(v_caption_4030_);
                if v_isShared_4046_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4045_, 1, v___x_4047_);
                    v___x_4049_ = v___x_4045_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4073_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4073_, 0, v_log_4039_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4073_, 1, v___x_4047_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4073_, 2, v_buildTime_4043_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4073_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_action_4040_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4073_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_4041_,
                    );
                    v___x_4049_ = v_reuseFailAlloc_4073_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc_ref(v_a_4036_);
                crate::leanh::lean_inc(v_a_4035_);
                crate::leanh::lean_inc(v_a_4034_);
                crate::leanh::lean_inc(v_a_4033_);
                v___x_4050_ = crate::leanh::lean_apply_7(
                    v_x_4031_,
                    v_a_4032_,
                    v_a_4033_,
                    v_a_4034_,
                    v_a_4035_,
                    v_a_4036_,
                    v___x_4049_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_4050_) == 0 {
                    v_a_4051_ = crate::leanh::lean_ctor_get(v___x_4050_, 1);
                    v_a_4052_ = crate::leanh::lean_ctor_get(v___x_4050_, 0);
                    v_isSharedCheck_4072_ = (!crate::leanh::lean_is_exclusive(v___x_4050_)) as u8;
                    if v_isSharedCheck_4072_ == 0 {
                        v___x_4054_ = v___x_4050_;
                        v_isShared_4055_ = v_isSharedCheck_4072_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4051_);
                        crate::leanh::lean_inc(v_a_4052_);
                        crate::leanh::lean_dec(v___x_4050_);
                        v___x_4054_ = crate::leanh::lean_box(0);
                        v_isShared_4055_ = v_isSharedCheck_4072_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_trace_4042_);
                    return v___x_4050_;
                }
            }
            3 => {
                v_log_4056_ = crate::leanh::lean_ctor_get(v_a_4051_, 0);
                v_action_4057_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_4051_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_wantsRebuild_4058_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_4051_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                );
                v_trace_4059_ = crate::leanh::lean_ctor_get(v_a_4051_, 1);
                v_buildTime_4060_ = crate::leanh::lean_ctor_get(v_a_4051_, 2);
                v_isSharedCheck_4071_ = (!crate::leanh::lean_is_exclusive(v_a_4051_)) as u8;
                if v_isSharedCheck_4071_ == 0 {
                    v___x_4062_ = v_a_4051_;
                    v_isShared_4063_ = v_isSharedCheck_4071_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buildTime_4060_);
                    crate::leanh::lean_inc(v_trace_4059_);
                    crate::leanh::lean_inc(v_log_4056_);
                    crate::leanh::lean_dec(v_a_4051_);
                    v___x_4062_ = crate::leanh::lean_box(0);
                    v_isShared_4063_ = v_isSharedCheck_4071_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4064_ = l_Lake_BuildTrace_mix(v_trace_4042_, v_trace_4059_);
                if v_isShared_4063_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4062_, 1, v___x_4064_);
                    v___x_4066_ = v___x_4062_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4070_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4070_, 0, v_log_4056_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4070_, 1, v___x_4064_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4070_, 2, v_buildTime_4060_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4070_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_action_4057_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4070_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_4058_,
                    );
                    v___x_4066_ = v_reuseFailAlloc_4070_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_4055_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4054_, 1, v___x_4066_);
                    v___x_4068_ = v___x_4054_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4069_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4069_, 0, v_a_4052_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4069_, 1, v___x_4066_);
                    v___x_4068_ = v_reuseFailAlloc_4069_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4068_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_addSubTrace___boxed(
    mut v_00_u03b1_4075_: *mut crate::leanh::LeanObject,
    mut v_caption_4076_: *mut crate::leanh::LeanObject,
    mut v_x_4077_: *mut crate::leanh::LeanObject,
    mut v_a_4078_: *mut crate::leanh::LeanObject,
    mut v_a_4079_: *mut crate::leanh::LeanObject,
    mut v_a_4080_: *mut crate::leanh::LeanObject,
    mut v_a_4081_: *mut crate::leanh::LeanObject,
    mut v_a_4082_: *mut crate::leanh::LeanObject,
    mut v_a_4083_: *mut crate::leanh::LeanObject,
    mut v_a_4084_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4085_ = l_Lake_addSubTrace(
        v_00_u03b1_4075_,
        v_caption_4076_,
        v_x_4077_,
        v_a_4078_,
        v_a_4079_,
        v_a_4080_,
        v_a_4081_,
        v_a_4082_,
        v_a_4083_,
    );
    crate::leanh::lean_dec_ref(v_a_4082_);
    crate::leanh::lean_dec(v_a_4081_);
    crate::leanh::lean_dec(v_a_4080_);
    crate::leanh::lean_dec(v_a_4079_);
    return v_res_4085_;
}
pub unsafe fn l_Lake_SpawnM_ofFn___redArg(
    mut v_f_4086_: *mut crate::leanh::LeanObject,
    mut v_a_4087_: *mut crate::leanh::LeanObject,
    mut v_a_4088_: *mut crate::leanh::LeanObject,
    mut v_a_4089_: *mut crate::leanh::LeanObject,
    mut v_a_4090_: *mut crate::leanh::LeanObject,
    mut v_a_4091_: *mut crate::leanh::LeanObject,
    mut v_a_4092_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_a_4092_);
    crate::leanh::lean_inc_ref(v_a_4091_);
    crate::leanh::lean_inc(v_a_4090_);
    crate::leanh::lean_inc(v_a_4089_);
    crate::leanh::lean_inc(v_a_4088_);
    v___x_4094_ = crate::leanh::lean_apply_7(
        v_f_4086_,
        v_a_4087_,
        v_a_4088_,
        v_a_4089_,
        v_a_4090_,
        v_a_4091_,
        v_a_4092_,
        crate::leanh::lean_box(0),
    );
    return v___x_4094_;
}
pub unsafe fn l_Lake_SpawnM_ofFn___redArg___boxed(
    mut v_f_4095_: *mut crate::leanh::LeanObject,
    mut v_a_4096_: *mut crate::leanh::LeanObject,
    mut v_a_4097_: *mut crate::leanh::LeanObject,
    mut v_a_4098_: *mut crate::leanh::LeanObject,
    mut v_a_4099_: *mut crate::leanh::LeanObject,
    mut v_a_4100_: *mut crate::leanh::LeanObject,
    mut v_a_4101_: *mut crate::leanh::LeanObject,
    mut v_a_4102_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4103_ = l_Lake_SpawnM_ofFn___redArg(
        v_f_4095_, v_a_4096_, v_a_4097_, v_a_4098_, v_a_4099_, v_a_4100_, v_a_4101_,
    );
    crate::leanh::lean_dec_ref(v_a_4101_);
    crate::leanh::lean_dec_ref(v_a_4100_);
    crate::leanh::lean_dec(v_a_4099_);
    crate::leanh::lean_dec(v_a_4098_);
    crate::leanh::lean_dec(v_a_4097_);
    return v_res_4103_;
}
pub unsafe fn l_Lake_SpawnM_ofFn(
    mut v_00_u03b1_4104_: *mut crate::leanh::LeanObject,
    mut v_f_4105_: *mut crate::leanh::LeanObject,
    mut v_a_4106_: *mut crate::leanh::LeanObject,
    mut v_a_4107_: *mut crate::leanh::LeanObject,
    mut v_a_4108_: *mut crate::leanh::LeanObject,
    mut v_a_4109_: *mut crate::leanh::LeanObject,
    mut v_a_4110_: *mut crate::leanh::LeanObject,
    mut v_a_4111_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_a_4111_);
    crate::leanh::lean_inc_ref(v_a_4110_);
    crate::leanh::lean_inc(v_a_4109_);
    crate::leanh::lean_inc(v_a_4108_);
    crate::leanh::lean_inc(v_a_4107_);
    v___x_4113_ = crate::leanh::lean_apply_7(
        v_f_4105_,
        v_a_4106_,
        v_a_4107_,
        v_a_4108_,
        v_a_4109_,
        v_a_4110_,
        v_a_4111_,
        crate::leanh::lean_box(0),
    );
    return v___x_4113_;
}
pub unsafe fn l_Lake_SpawnM_ofFn___boxed(
    mut v_00_u03b1_4114_: *mut crate::leanh::LeanObject,
    mut v_f_4115_: *mut crate::leanh::LeanObject,
    mut v_a_4116_: *mut crate::leanh::LeanObject,
    mut v_a_4117_: *mut crate::leanh::LeanObject,
    mut v_a_4118_: *mut crate::leanh::LeanObject,
    mut v_a_4119_: *mut crate::leanh::LeanObject,
    mut v_a_4120_: *mut crate::leanh::LeanObject,
    mut v_a_4121_: *mut crate::leanh::LeanObject,
    mut v_a_4122_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4123_ = l_Lake_SpawnM_ofFn(
        v_00_u03b1_4114_,
        v_f_4115_,
        v_a_4116_,
        v_a_4117_,
        v_a_4118_,
        v_a_4119_,
        v_a_4120_,
        v_a_4121_,
    );
    crate::leanh::lean_dec_ref(v_a_4121_);
    crate::leanh::lean_dec_ref(v_a_4120_);
    crate::leanh::lean_dec(v_a_4119_);
    crate::leanh::lean_dec(v_a_4118_);
    crate::leanh::lean_dec(v_a_4117_);
    return v_res_4123_;
}
pub unsafe fn l_Lake_SpawnM_toFn___redArg(
    mut v_self_4124_: *mut crate::leanh::LeanObject,
    mut v_fetch_4125_: *mut crate::leanh::LeanObject,
    mut v_pkg_x3f_4126_: *mut crate::leanh::LeanObject,
    mut v_stack_4127_: *mut crate::leanh::LeanObject,
    mut v_store_4128_: *mut crate::leanh::LeanObject,
    mut v_ctx_4129_: *mut crate::leanh::LeanObject,
    mut v_s_4130_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4132_ = crate::leanh::lean_apply_7(
        v_self_4124_,
        v_fetch_4125_,
        v_pkg_x3f_4126_,
        v_stack_4127_,
        v_store_4128_,
        v_ctx_4129_,
        v_s_4130_,
        crate::leanh::lean_box(0),
    );
    return v___x_4132_;
}
pub unsafe fn l_Lake_SpawnM_toFn___redArg___boxed(
    mut v_self_4133_: *mut crate::leanh::LeanObject,
    mut v_fetch_4134_: *mut crate::leanh::LeanObject,
    mut v_pkg_x3f_4135_: *mut crate::leanh::LeanObject,
    mut v_stack_4136_: *mut crate::leanh::LeanObject,
    mut v_store_4137_: *mut crate::leanh::LeanObject,
    mut v_ctx_4138_: *mut crate::leanh::LeanObject,
    mut v_s_4139_: *mut crate::leanh::LeanObject,
    mut v_a_4140_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4141_ = l_Lake_SpawnM_toFn___redArg(
        v_self_4133_,
        v_fetch_4134_,
        v_pkg_x3f_4135_,
        v_stack_4136_,
        v_store_4137_,
        v_ctx_4138_,
        v_s_4139_,
    );
    return v_res_4141_;
}
pub unsafe fn l_Lake_SpawnM_toFn(
    mut v_00_u03b1_4142_: *mut crate::leanh::LeanObject,
    mut v_self_4143_: *mut crate::leanh::LeanObject,
    mut v_fetch_4144_: *mut crate::leanh::LeanObject,
    mut v_pkg_x3f_4145_: *mut crate::leanh::LeanObject,
    mut v_stack_4146_: *mut crate::leanh::LeanObject,
    mut v_store_4147_: *mut crate::leanh::LeanObject,
    mut v_ctx_4148_: *mut crate::leanh::LeanObject,
    mut v_s_4149_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4151_ = crate::leanh::lean_apply_7(
        v_self_4143_,
        v_fetch_4144_,
        v_pkg_x3f_4145_,
        v_stack_4146_,
        v_store_4147_,
        v_ctx_4148_,
        v_s_4149_,
        crate::leanh::lean_box(0),
    );
    return v___x_4151_;
}
pub unsafe fn l_Lake_SpawnM_toFn___boxed(
    mut v_00_u03b1_4152_: *mut crate::leanh::LeanObject,
    mut v_self_4153_: *mut crate::leanh::LeanObject,
    mut v_fetch_4154_: *mut crate::leanh::LeanObject,
    mut v_pkg_x3f_4155_: *mut crate::leanh::LeanObject,
    mut v_stack_4156_: *mut crate::leanh::LeanObject,
    mut v_store_4157_: *mut crate::leanh::LeanObject,
    mut v_ctx_4158_: *mut crate::leanh::LeanObject,
    mut v_s_4159_: *mut crate::leanh::LeanObject,
    mut v_a_4160_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4161_ = l_Lake_SpawnM_toFn(
        v_00_u03b1_4152_,
        v_self_4153_,
        v_fetch_4154_,
        v_pkg_x3f_4155_,
        v_stack_4156_,
        v_store_4157_,
        v_ctx_4158_,
        v_s_4159_,
    );
    return v_res_4161_;
}
pub unsafe fn l_Lake_JobM_runSpawnM___redArg(
    mut v_x_4162_: *mut crate::leanh::LeanObject,
    mut v_a_4163_: *mut crate::leanh::LeanObject,
    mut v_a_4164_: *mut crate::leanh::LeanObject,
    mut v_a_4165_: *mut crate::leanh::LeanObject,
    mut v_a_4166_: *mut crate::leanh::LeanObject,
    mut v_a_4167_: *mut crate::leanh::LeanObject,
    mut v_a_4168_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_trace_4170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_trace_4170_ = crate::leanh::lean_ctor_get(v_a_4168_, 1);
    crate::leanh::lean_inc_ref(v_trace_4170_);
    crate::leanh::lean_inc_ref(v_a_4167_);
    crate::leanh::lean_inc(v_a_4166_);
    crate::leanh::lean_inc(v_a_4165_);
    crate::leanh::lean_inc(v_a_4164_);
    v___x_4171_ = crate::leanh::lean_apply_7(
        v_x_4162_,
        v_a_4163_,
        v_a_4164_,
        v_a_4165_,
        v_a_4166_,
        v_a_4167_,
        v_trace_4170_,
        crate::leanh::lean_box(0),
    );
    v___x_4172_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4172_, 0, v___x_4171_);
    crate::leanh::lean_ctor_set(v___x_4172_, 1, v_a_4168_);
    return v___x_4172_;
}
pub unsafe fn l_Lake_JobM_runSpawnM___redArg___boxed(
    mut v_x_4173_: *mut crate::leanh::LeanObject,
    mut v_a_4174_: *mut crate::leanh::LeanObject,
    mut v_a_4175_: *mut crate::leanh::LeanObject,
    mut v_a_4176_: *mut crate::leanh::LeanObject,
    mut v_a_4177_: *mut crate::leanh::LeanObject,
    mut v_a_4178_: *mut crate::leanh::LeanObject,
    mut v_a_4179_: *mut crate::leanh::LeanObject,
    mut v_a_4180_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4181_ = l_Lake_JobM_runSpawnM___redArg(
        v_x_4173_, v_a_4174_, v_a_4175_, v_a_4176_, v_a_4177_, v_a_4178_, v_a_4179_,
    );
    crate::leanh::lean_dec_ref(v_a_4178_);
    crate::leanh::lean_dec(v_a_4177_);
    crate::leanh::lean_dec(v_a_4176_);
    crate::leanh::lean_dec(v_a_4175_);
    return v_res_4181_;
}
pub unsafe fn l_Lake_JobM_runSpawnM(
    mut v_00_u03b1_4182_: *mut crate::leanh::LeanObject,
    mut v_x_4183_: *mut crate::leanh::LeanObject,
    mut v_a_4184_: *mut crate::leanh::LeanObject,
    mut v_a_4185_: *mut crate::leanh::LeanObject,
    mut v_a_4186_: *mut crate::leanh::LeanObject,
    mut v_a_4187_: *mut crate::leanh::LeanObject,
    mut v_a_4188_: *mut crate::leanh::LeanObject,
    mut v_a_4189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_trace_4191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_trace_4191_ = crate::leanh::lean_ctor_get(v_a_4189_, 1);
    crate::leanh::lean_inc_ref(v_trace_4191_);
    crate::leanh::lean_inc_ref(v_a_4188_);
    crate::leanh::lean_inc(v_a_4187_);
    crate::leanh::lean_inc(v_a_4186_);
    crate::leanh::lean_inc(v_a_4185_);
    v___x_4192_ = crate::leanh::lean_apply_7(
        v_x_4183_,
        v_a_4184_,
        v_a_4185_,
        v_a_4186_,
        v_a_4187_,
        v_a_4188_,
        v_trace_4191_,
        crate::leanh::lean_box(0),
    );
    v___x_4193_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4193_, 0, v___x_4192_);
    crate::leanh::lean_ctor_set(v___x_4193_, 1, v_a_4189_);
    return v___x_4193_;
}
pub unsafe fn l_Lake_JobM_runSpawnM___boxed(
    mut v_00_u03b1_4194_: *mut crate::leanh::LeanObject,
    mut v_x_4195_: *mut crate::leanh::LeanObject,
    mut v_a_4196_: *mut crate::leanh::LeanObject,
    mut v_a_4197_: *mut crate::leanh::LeanObject,
    mut v_a_4198_: *mut crate::leanh::LeanObject,
    mut v_a_4199_: *mut crate::leanh::LeanObject,
    mut v_a_4200_: *mut crate::leanh::LeanObject,
    mut v_a_4201_: *mut crate::leanh::LeanObject,
    mut v_a_4202_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4203_ = l_Lake_JobM_runSpawnM(
        v_00_u03b1_4194_,
        v_x_4195_,
        v_a_4196_,
        v_a_4197_,
        v_a_4198_,
        v_a_4199_,
        v_a_4200_,
        v_a_4201_,
    );
    crate::leanh::lean_dec_ref(v_a_4200_);
    crate::leanh::lean_dec(v_a_4199_);
    crate::leanh::lean_dec(v_a_4198_);
    crate::leanh::lean_dec(v_a_4197_);
    return v_res_4203_;
}
pub unsafe fn l_Lake_FetchM_runJobM___redArg(
    mut v_x_4206_: *mut crate::leanh::LeanObject,
    mut v_a_4207_: *mut crate::leanh::LeanObject,
    mut v_a_4208_: *mut crate::leanh::LeanObject,
    mut v_a_4209_: *mut crate::leanh::LeanObject,
    mut v_a_4210_: *mut crate::leanh::LeanObject,
    mut v_a_4211_: *mut crate::leanh::LeanObject,
    mut v_a_4212_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4214_: u8 = 0;
    let mut v___x_4215_: u8 = 0;
    let mut v___x_4216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4224_: u8 = 0;
    let mut v_log_4225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4229_: u8 = 0;
    let mut v_a_4230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4234_: u8 = 0;
    let mut v_log_4235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4239_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4214_ = 0;
                v___x_4215_ = 0;
                v___x_4216_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lake_takeTrace___redArg___closed__1),
                    core::ptr::addr_of_mut!(l_Lake_takeTrace___redArg___closed__1_once),
                    _init_l_Lake_takeTrace___redArg___closed__1,
                );
                v___x_4217_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4218_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_4218_, 0, v_a_4212_);
                crate::leanh::lean_ctor_set(v___x_4218_, 1, v___x_4216_);
                crate::leanh::lean_ctor_set(v___x_4218_, 2, v___x_4217_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4218_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_4214_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4218_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                    v___x_4215_,
                );
                crate::leanh::lean_inc_ref(v_a_4211_);
                crate::leanh::lean_inc(v_a_4210_);
                crate::leanh::lean_inc(v_a_4209_);
                crate::leanh::lean_inc(v_a_4208_);
                v___x_4219_ = crate::leanh::lean_apply_7(
                    v_x_4206_,
                    v_a_4207_,
                    v_a_4208_,
                    v_a_4209_,
                    v_a_4210_,
                    v_a_4211_,
                    v___x_4218_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_4219_) == 0 {
                    v_a_4220_ = crate::leanh::lean_ctor_get(v___x_4219_, 1);
                    v_a_4221_ = crate::leanh::lean_ctor_get(v___x_4219_, 0);
                    v_isSharedCheck_4229_ = (!crate::leanh::lean_is_exclusive(v___x_4219_)) as u8;
                    if v_isSharedCheck_4229_ == 0 {
                        v___x_4223_ = v___x_4219_;
                        v_isShared_4224_ = v_isSharedCheck_4229_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4220_);
                        crate::leanh::lean_inc(v_a_4221_);
                        crate::leanh::lean_dec(v___x_4219_);
                        v___x_4223_ = crate::leanh::lean_box(0);
                        v_isShared_4224_ = v_isSharedCheck_4229_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4230_ = crate::leanh::lean_ctor_get(v___x_4219_, 1);
                    v_a_4231_ = crate::leanh::lean_ctor_get(v___x_4219_, 0);
                    v_isSharedCheck_4239_ = (!crate::leanh::lean_is_exclusive(v___x_4219_)) as u8;
                    if v_isSharedCheck_4239_ == 0 {
                        v___x_4233_ = v___x_4219_;
                        v_isShared_4234_ = v_isSharedCheck_4239_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4230_);
                        crate::leanh::lean_inc(v_a_4231_);
                        crate::leanh::lean_dec(v___x_4219_);
                        v___x_4233_ = crate::leanh::lean_box(0);
                        v_isShared_4234_ = v_isSharedCheck_4239_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_log_4225_ = crate::leanh::lean_ctor_get(v_a_4220_, 0);
                crate::leanh::lean_inc_ref(v_log_4225_);
                crate::leanh::lean_dec(v_a_4220_);
                if v_isShared_4224_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4223_, 1, v_log_4225_);
                    v___x_4227_ = v___x_4223_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4228_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4228_, 0, v_a_4221_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4228_, 1, v_log_4225_);
                    v___x_4227_ = v_reuseFailAlloc_4228_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4227_;
            }
            3 => {
                v_log_4235_ = crate::leanh::lean_ctor_get(v_a_4230_, 0);
                crate::leanh::lean_inc_ref(v_log_4235_);
                crate::leanh::lean_dec(v_a_4230_);
                if v_isShared_4234_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4233_, 1, v_log_4235_);
                    v___x_4237_ = v___x_4233_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4238_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4238_, 0, v_a_4231_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4238_, 1, v_log_4235_);
                    v___x_4237_ = v_reuseFailAlloc_4238_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4237_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_FetchM_runJobM___redArg___boxed(
    mut v_x_4240_: *mut crate::leanh::LeanObject,
    mut v_a_4241_: *mut crate::leanh::LeanObject,
    mut v_a_4242_: *mut crate::leanh::LeanObject,
    mut v_a_4243_: *mut crate::leanh::LeanObject,
    mut v_a_4244_: *mut crate::leanh::LeanObject,
    mut v_a_4245_: *mut crate::leanh::LeanObject,
    mut v_a_4246_: *mut crate::leanh::LeanObject,
    mut v_a_4247_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4248_ = l_Lake_FetchM_runJobM___redArg(
        v_x_4240_, v_a_4241_, v_a_4242_, v_a_4243_, v_a_4244_, v_a_4245_, v_a_4246_,
    );
    crate::leanh::lean_dec_ref(v_a_4245_);
    crate::leanh::lean_dec(v_a_4244_);
    crate::leanh::lean_dec(v_a_4243_);
    crate::leanh::lean_dec(v_a_4242_);
    return v_res_4248_;
}
pub unsafe fn l_Lake_FetchM_runJobM(
    mut v_00_u03b1_4249_: *mut crate::leanh::LeanObject,
    mut v_x_4250_: *mut crate::leanh::LeanObject,
    mut v_a_4251_: *mut crate::leanh::LeanObject,
    mut v_a_4252_: *mut crate::leanh::LeanObject,
    mut v_a_4253_: *mut crate::leanh::LeanObject,
    mut v_a_4254_: *mut crate::leanh::LeanObject,
    mut v_a_4255_: *mut crate::leanh::LeanObject,
    mut v_a_4256_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4258_: u8 = 0;
    let mut v___x_4259_: u8 = 0;
    let mut v___x_4260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4268_: u8 = 0;
    let mut v_log_4269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4273_: u8 = 0;
    let mut v_a_4274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4278_: u8 = 0;
    let mut v_log_4279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4283_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4258_ = 0;
                v___x_4259_ = 0;
                v___x_4260_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lake_takeTrace___redArg___closed__1),
                    core::ptr::addr_of_mut!(l_Lake_takeTrace___redArg___closed__1_once),
                    _init_l_Lake_takeTrace___redArg___closed__1,
                );
                v___x_4261_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4262_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_4262_, 0, v_a_4256_);
                crate::leanh::lean_ctor_set(v___x_4262_, 1, v___x_4260_);
                crate::leanh::lean_ctor_set(v___x_4262_, 2, v___x_4261_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4262_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_4258_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4262_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                    v___x_4259_,
                );
                crate::leanh::lean_inc_ref(v_a_4255_);
                crate::leanh::lean_inc(v_a_4254_);
                crate::leanh::lean_inc(v_a_4253_);
                crate::leanh::lean_inc(v_a_4252_);
                v___x_4263_ = crate::leanh::lean_apply_7(
                    v_x_4250_,
                    v_a_4251_,
                    v_a_4252_,
                    v_a_4253_,
                    v_a_4254_,
                    v_a_4255_,
                    v___x_4262_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_4263_) == 0 {
                    v_a_4264_ = crate::leanh::lean_ctor_get(v___x_4263_, 1);
                    v_a_4265_ = crate::leanh::lean_ctor_get(v___x_4263_, 0);
                    v_isSharedCheck_4273_ = (!crate::leanh::lean_is_exclusive(v___x_4263_)) as u8;
                    if v_isSharedCheck_4273_ == 0 {
                        v___x_4267_ = v___x_4263_;
                        v_isShared_4268_ = v_isSharedCheck_4273_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4264_);
                        crate::leanh::lean_inc(v_a_4265_);
                        crate::leanh::lean_dec(v___x_4263_);
                        v___x_4267_ = crate::leanh::lean_box(0);
                        v_isShared_4268_ = v_isSharedCheck_4273_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4274_ = crate::leanh::lean_ctor_get(v___x_4263_, 1);
                    v_a_4275_ = crate::leanh::lean_ctor_get(v___x_4263_, 0);
                    v_isSharedCheck_4283_ = (!crate::leanh::lean_is_exclusive(v___x_4263_)) as u8;
                    if v_isSharedCheck_4283_ == 0 {
                        v___x_4277_ = v___x_4263_;
                        v_isShared_4278_ = v_isSharedCheck_4283_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4274_);
                        crate::leanh::lean_inc(v_a_4275_);
                        crate::leanh::lean_dec(v___x_4263_);
                        v___x_4277_ = crate::leanh::lean_box(0);
                        v_isShared_4278_ = v_isSharedCheck_4283_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_log_4269_ = crate::leanh::lean_ctor_get(v_a_4264_, 0);
                crate::leanh::lean_inc_ref(v_log_4269_);
                crate::leanh::lean_dec(v_a_4264_);
                if v_isShared_4268_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4267_, 1, v_log_4269_);
                    v___x_4271_ = v___x_4267_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4272_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4272_, 0, v_a_4265_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4272_, 1, v_log_4269_);
                    v___x_4271_ = v_reuseFailAlloc_4272_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4271_;
            }
            3 => {
                v_log_4279_ = crate::leanh::lean_ctor_get(v_a_4274_, 0);
                crate::leanh::lean_inc_ref(v_log_4279_);
                crate::leanh::lean_dec(v_a_4274_);
                if v_isShared_4278_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4277_, 1, v_log_4279_);
                    v___x_4281_ = v___x_4277_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4282_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4282_, 0, v_a_4275_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4282_, 1, v_log_4279_);
                    v___x_4281_ = v_reuseFailAlloc_4282_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4281_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_FetchM_runJobM___boxed(
    mut v_00_u03b1_4284_: *mut crate::leanh::LeanObject,
    mut v_x_4285_: *mut crate::leanh::LeanObject,
    mut v_a_4286_: *mut crate::leanh::LeanObject,
    mut v_a_4287_: *mut crate::leanh::LeanObject,
    mut v_a_4288_: *mut crate::leanh::LeanObject,
    mut v_a_4289_: *mut crate::leanh::LeanObject,
    mut v_a_4290_: *mut crate::leanh::LeanObject,
    mut v_a_4291_: *mut crate::leanh::LeanObject,
    mut v_a_4292_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4293_ = l_Lake_FetchM_runJobM(
        v_00_u03b1_4284_,
        v_x_4285_,
        v_a_4286_,
        v_a_4287_,
        v_a_4288_,
        v_a_4289_,
        v_a_4290_,
        v_a_4291_,
    );
    crate::leanh::lean_dec_ref(v_a_4290_);
    crate::leanh::lean_dec(v_a_4289_);
    crate::leanh::lean_dec(v_a_4288_);
    crate::leanh::lean_dec(v_a_4287_);
    return v_res_4293_;
}
pub unsafe fn l_Lake_JobM_runFetchM___redArg(
    mut v_x_4296_: *mut crate::leanh::LeanObject,
    mut v_a_4297_: *mut crate::leanh::LeanObject,
    mut v_a_4298_: *mut crate::leanh::LeanObject,
    mut v_a_4299_: *mut crate::leanh::LeanObject,
    mut v_a_4300_: *mut crate::leanh::LeanObject,
    mut v_a_4301_: *mut crate::leanh::LeanObject,
    mut v_a_4302_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_log_4304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_action_4305_: u8 = 0;
    let mut v_wantsRebuild_4306_: u8 = 0;
    let mut v_trace_4307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildTime_4308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4311_: u8 = 0;
    let mut v___x_4312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4317_: u8 = 0;
    let mut v___x_4319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4324_: u8 = 0;
    let mut v_a_4325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4329_: u8 = 0;
    let mut v___x_4331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4336_: u8 = 0;
    let mut v_isSharedCheck_4337_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_log_4304_ = crate::leanh::lean_ctor_get(v_a_4302_, 0);
                v_action_4305_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_4302_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_wantsRebuild_4306_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_4302_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                );
                v_trace_4307_ = crate::leanh::lean_ctor_get(v_a_4302_, 1);
                v_buildTime_4308_ = crate::leanh::lean_ctor_get(v_a_4302_, 2);
                v_isSharedCheck_4337_ = (!crate::leanh::lean_is_exclusive(v_a_4302_)) as u8;
                if v_isSharedCheck_4337_ == 0 {
                    v___x_4310_ = v_a_4302_;
                    v_isShared_4311_ = v_isSharedCheck_4337_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buildTime_4308_);
                    crate::leanh::lean_inc(v_trace_4307_);
                    crate::leanh::lean_inc(v_log_4304_);
                    crate::leanh::lean_dec(v_a_4302_);
                    v___x_4310_ = crate::leanh::lean_box(0);
                    v_isShared_4311_ = v_isSharedCheck_4337_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_a_4301_);
                crate::leanh::lean_inc(v_a_4300_);
                crate::leanh::lean_inc(v_a_4299_);
                crate::leanh::lean_inc(v_a_4298_);
                v___x_4312_ = crate::leanh::lean_apply_7(
                    v_x_4296_,
                    v_a_4297_,
                    v_a_4298_,
                    v_a_4299_,
                    v_a_4300_,
                    v_a_4301_,
                    v_log_4304_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_4312_) == 0 {
                    v_a_4313_ = crate::leanh::lean_ctor_get(v___x_4312_, 0);
                    v_a_4314_ = crate::leanh::lean_ctor_get(v___x_4312_, 1);
                    v_isSharedCheck_4324_ = (!crate::leanh::lean_is_exclusive(v___x_4312_)) as u8;
                    if v_isSharedCheck_4324_ == 0 {
                        v___x_4316_ = v___x_4312_;
                        v_isShared_4317_ = v_isSharedCheck_4324_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4314_);
                        crate::leanh::lean_inc(v_a_4313_);
                        crate::leanh::lean_dec(v___x_4312_);
                        v___x_4316_ = crate::leanh::lean_box(0);
                        v_isShared_4317_ = v_isSharedCheck_4324_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_4325_ = crate::leanh::lean_ctor_get(v___x_4312_, 0);
                    v_a_4326_ = crate::leanh::lean_ctor_get(v___x_4312_, 1);
                    v_isSharedCheck_4336_ = (!crate::leanh::lean_is_exclusive(v___x_4312_)) as u8;
                    if v_isSharedCheck_4336_ == 0 {
                        v___x_4328_ = v___x_4312_;
                        v_isShared_4329_ = v_isSharedCheck_4336_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4326_);
                        crate::leanh::lean_inc(v_a_4325_);
                        crate::leanh::lean_dec(v___x_4312_);
                        v___x_4328_ = crate::leanh::lean_box(0);
                        v_isShared_4329_ = v_isSharedCheck_4336_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_4311_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4310_, 0, v_a_4314_);
                    v___x_4319_ = v___x_4310_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4323_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4323_, 0, v_a_4314_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4323_, 1, v_trace_4307_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4323_, 2, v_buildTime_4308_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4323_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_action_4305_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4323_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_4306_,
                    );
                    v___x_4319_ = v_reuseFailAlloc_4323_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4317_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4316_, 1, v___x_4319_);
                    v___x_4321_ = v___x_4316_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4322_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4322_, 0, v_a_4313_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4322_, 1, v___x_4319_);
                    v___x_4321_ = v_reuseFailAlloc_4322_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4321_;
            }
            5 => {
                if v_isShared_4311_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4310_, 0, v_a_4326_);
                    v___x_4331_ = v___x_4310_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4335_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4335_, 0, v_a_4326_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4335_, 1, v_trace_4307_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4335_, 2, v_buildTime_4308_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4335_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_action_4305_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4335_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_4306_,
                    );
                    v___x_4331_ = v_reuseFailAlloc_4335_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_4329_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4328_, 1, v___x_4331_);
                    v___x_4333_ = v___x_4328_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4334_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4334_, 0, v_a_4325_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4334_, 1, v___x_4331_);
                    v___x_4333_ = v_reuseFailAlloc_4334_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4333_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_JobM_runFetchM___redArg___boxed(
    mut v_x_4338_: *mut crate::leanh::LeanObject,
    mut v_a_4339_: *mut crate::leanh::LeanObject,
    mut v_a_4340_: *mut crate::leanh::LeanObject,
    mut v_a_4341_: *mut crate::leanh::LeanObject,
    mut v_a_4342_: *mut crate::leanh::LeanObject,
    mut v_a_4343_: *mut crate::leanh::LeanObject,
    mut v_a_4344_: *mut crate::leanh::LeanObject,
    mut v_a_4345_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4346_ = l_Lake_JobM_runFetchM___redArg(
        v_x_4338_, v_a_4339_, v_a_4340_, v_a_4341_, v_a_4342_, v_a_4343_, v_a_4344_,
    );
    crate::leanh::lean_dec_ref(v_a_4343_);
    crate::leanh::lean_dec(v_a_4342_);
    crate::leanh::lean_dec(v_a_4341_);
    crate::leanh::lean_dec(v_a_4340_);
    return v_res_4346_;
}
pub unsafe fn l_Lake_JobM_runFetchM(
    mut v_00_u03b1_4347_: *mut crate::leanh::LeanObject,
    mut v_x_4348_: *mut crate::leanh::LeanObject,
    mut v_a_4349_: *mut crate::leanh::LeanObject,
    mut v_a_4350_: *mut crate::leanh::LeanObject,
    mut v_a_4351_: *mut crate::leanh::LeanObject,
    mut v_a_4352_: *mut crate::leanh::LeanObject,
    mut v_a_4353_: *mut crate::leanh::LeanObject,
    mut v_a_4354_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_log_4356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_action_4357_: u8 = 0;
    let mut v_wantsRebuild_4358_: u8 = 0;
    let mut v_trace_4359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildTime_4360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4363_: u8 = 0;
    let mut v___x_4364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4369_: u8 = 0;
    let mut v___x_4371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4376_: u8 = 0;
    let mut v_a_4377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4381_: u8 = 0;
    let mut v___x_4383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4388_: u8 = 0;
    let mut v_isSharedCheck_4389_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_log_4356_ = crate::leanh::lean_ctor_get(v_a_4354_, 0);
                v_action_4357_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_4354_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_wantsRebuild_4358_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_4354_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                );
                v_trace_4359_ = crate::leanh::lean_ctor_get(v_a_4354_, 1);
                v_buildTime_4360_ = crate::leanh::lean_ctor_get(v_a_4354_, 2);
                v_isSharedCheck_4389_ = (!crate::leanh::lean_is_exclusive(v_a_4354_)) as u8;
                if v_isSharedCheck_4389_ == 0 {
                    v___x_4362_ = v_a_4354_;
                    v_isShared_4363_ = v_isSharedCheck_4389_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buildTime_4360_);
                    crate::leanh::lean_inc(v_trace_4359_);
                    crate::leanh::lean_inc(v_log_4356_);
                    crate::leanh::lean_dec(v_a_4354_);
                    v___x_4362_ = crate::leanh::lean_box(0);
                    v_isShared_4363_ = v_isSharedCheck_4389_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_a_4353_);
                crate::leanh::lean_inc(v_a_4352_);
                crate::leanh::lean_inc(v_a_4351_);
                crate::leanh::lean_inc(v_a_4350_);
                v___x_4364_ = crate::leanh::lean_apply_7(
                    v_x_4348_,
                    v_a_4349_,
                    v_a_4350_,
                    v_a_4351_,
                    v_a_4352_,
                    v_a_4353_,
                    v_log_4356_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_4364_) == 0 {
                    v_a_4365_ = crate::leanh::lean_ctor_get(v___x_4364_, 0);
                    v_a_4366_ = crate::leanh::lean_ctor_get(v___x_4364_, 1);
                    v_isSharedCheck_4376_ = (!crate::leanh::lean_is_exclusive(v___x_4364_)) as u8;
                    if v_isSharedCheck_4376_ == 0 {
                        v___x_4368_ = v___x_4364_;
                        v_isShared_4369_ = v_isSharedCheck_4376_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4366_);
                        crate::leanh::lean_inc(v_a_4365_);
                        crate::leanh::lean_dec(v___x_4364_);
                        v___x_4368_ = crate::leanh::lean_box(0);
                        v_isShared_4369_ = v_isSharedCheck_4376_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_4377_ = crate::leanh::lean_ctor_get(v___x_4364_, 0);
                    v_a_4378_ = crate::leanh::lean_ctor_get(v___x_4364_, 1);
                    v_isSharedCheck_4388_ = (!crate::leanh::lean_is_exclusive(v___x_4364_)) as u8;
                    if v_isSharedCheck_4388_ == 0 {
                        v___x_4380_ = v___x_4364_;
                        v_isShared_4381_ = v_isSharedCheck_4388_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4378_);
                        crate::leanh::lean_inc(v_a_4377_);
                        crate::leanh::lean_dec(v___x_4364_);
                        v___x_4380_ = crate::leanh::lean_box(0);
                        v_isShared_4381_ = v_isSharedCheck_4388_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_4363_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4362_, 0, v_a_4366_);
                    v___x_4371_ = v___x_4362_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4375_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4375_, 0, v_a_4366_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4375_, 1, v_trace_4359_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4375_, 2, v_buildTime_4360_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4375_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_action_4357_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4375_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_4358_,
                    );
                    v___x_4371_ = v_reuseFailAlloc_4375_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4369_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4368_, 1, v___x_4371_);
                    v___x_4373_ = v___x_4368_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4374_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4374_, 0, v_a_4365_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4374_, 1, v___x_4371_);
                    v___x_4373_ = v_reuseFailAlloc_4374_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4373_;
            }
            5 => {
                if v_isShared_4363_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4362_, 0, v_a_4378_);
                    v___x_4383_ = v___x_4362_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4387_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4387_, 0, v_a_4378_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4387_, 1, v_trace_4359_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4387_, 2, v_buildTime_4360_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4387_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_action_4357_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4387_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_4358_,
                    );
                    v___x_4383_ = v_reuseFailAlloc_4387_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_4381_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4380_, 1, v___x_4383_);
                    v___x_4385_ = v___x_4380_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4386_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4386_, 0, v_a_4377_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4386_, 1, v___x_4383_);
                    v___x_4385_ = v_reuseFailAlloc_4386_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4385_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_JobM_runFetchM___boxed(
    mut v_00_u03b1_4390_: *mut crate::leanh::LeanObject,
    mut v_x_4391_: *mut crate::leanh::LeanObject,
    mut v_a_4392_: *mut crate::leanh::LeanObject,
    mut v_a_4393_: *mut crate::leanh::LeanObject,
    mut v_a_4394_: *mut crate::leanh::LeanObject,
    mut v_a_4395_: *mut crate::leanh::LeanObject,
    mut v_a_4396_: *mut crate::leanh::LeanObject,
    mut v_a_4397_: *mut crate::leanh::LeanObject,
    mut v_a_4398_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4399_ = l_Lake_JobM_runFetchM(
        v_00_u03b1_4390_,
        v_x_4391_,
        v_a_4392_,
        v_a_4393_,
        v_a_4394_,
        v_a_4395_,
        v_a_4396_,
        v_a_4397_,
    );
    crate::leanh::lean_dec_ref(v_a_4396_);
    crate::leanh::lean_dec(v_a_4395_);
    crate::leanh::lean_dec(v_a_4394_);
    crate::leanh::lean_dec(v_a_4393_);
    return v_res_4399_;
}
pub unsafe fn l_Lake_Job_bindTask___redArg___lam__0(
    mut v_inst_4402_: *mut crate::leanh::LeanObject,
    mut v_caption_4403_: *mut crate::leanh::LeanObject,
    mut v_optional_4404_: u8,
    mut v_toPure_4405_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4406_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4407_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_4407_, 0, v_____do__lift_4406_);
    crate::leanh::lean_ctor_set(v___x_4407_, 1, v_inst_4402_);
    crate::leanh::lean_ctor_set(v___x_4407_, 2, v_caption_4403_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_4407_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v_optional_4404_,
    );
    v___x_4408_ =
        crate::leanh::lean_apply_2(v_toPure_4405_, crate::leanh::lean_box(0), v___x_4407_);
    return v___x_4408_;
}
pub unsafe fn l_Lake_Job_bindTask___redArg___lam__0___boxed(
    mut v_inst_4409_: *mut crate::leanh::LeanObject,
    mut v_caption_4410_: *mut crate::leanh::LeanObject,
    mut v_optional_4411_: *mut crate::leanh::LeanObject,
    mut v_toPure_4412_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4413_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_optional_boxed_4414_: u8 = 0;
    let mut v_res_4415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_optional_boxed_4414_ = (crate::leanh::lean_unbox(v_optional_4411_) as u8);
    v_res_4415_ = l_Lake_Job_bindTask___redArg___lam__0(
        v_inst_4409_,
        v_caption_4410_,
        v_optional_boxed_4414_,
        v_toPure_4412_,
        v_____do__lift_4413_,
    );
    return v_res_4415_;
}
pub unsafe fn l_Lake_Job_bindTask___redArg(
    mut v_inst_4416_: *mut crate::leanh::LeanObject,
    mut v_inst_4417_: *mut crate::leanh::LeanObject,
    mut v_f_4418_: *mut crate::leanh::LeanObject,
    mut v_self_4419_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_4420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_task_4422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_caption_4423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_optional_4424_: u8 = 0;
    let mut v_toPure_4425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4420_ = crate::leanh::lean_ctor_get(v_inst_4416_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_4420_);
    v_toBind_4421_ = crate::leanh::lean_ctor_get(v_inst_4416_, 1);
    crate::leanh::lean_inc(v_toBind_4421_);
    crate::leanh::lean_dec_ref(v_inst_4416_);
    v_task_4422_ = crate::leanh::lean_ctor_get(v_self_4419_, 0);
    crate::leanh::lean_inc_ref(v_task_4422_);
    v_caption_4423_ = crate::leanh::lean_ctor_get(v_self_4419_, 2);
    crate::leanh::lean_inc_ref(v_caption_4423_);
    v_optional_4424_ = crate::leanh::lean_ctor_get_uint8(
        v_self_4419_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
    );
    crate::leanh::lean_dec_ref(v_self_4419_);
    v_toPure_4425_ = crate::leanh::lean_ctor_get(v_toApplicative_4420_, 1);
    crate::leanh::lean_inc(v_toPure_4425_);
    crate::leanh::lean_dec_ref(v_toApplicative_4420_);
    v___x_4426_ = crate::leanh::lean_apply_1(v_f_4418_, v_task_4422_);
    v___x_4427_ = crate::leanh::lean_box((v_optional_4424_) as usize);
    v___f_4428_ = crate::leanh::lean_alloc_closure(
        l_Lake_Job_bindTask___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_4428_, 0, v_inst_4417_);
    crate::leanh::lean_closure_set(v___f_4428_, 1, v_caption_4423_);
    crate::leanh::lean_closure_set(v___f_4428_, 2, v___x_4427_);
    crate::leanh::lean_closure_set(v___f_4428_, 3, v_toPure_4425_);
    v___x_4429_ = crate::leanh::lean_apply_4(
        v_toBind_4421_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4426_,
        v___f_4428_,
    );
    return v___x_4429_;
}
pub unsafe fn l_Lake_Job_bindTask(
    mut v_m_4430_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4431_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_4432_: *mut crate::leanh::LeanObject,
    mut v_inst_4433_: *mut crate::leanh::LeanObject,
    mut v_inst_4434_: *mut crate::leanh::LeanObject,
    mut v_f_4435_: *mut crate::leanh::LeanObject,
    mut v_self_4436_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_4437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_task_4439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_caption_4440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_optional_4441_: u8 = 0;
    let mut v_toPure_4442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4437_ = crate::leanh::lean_ctor_get(v_inst_4433_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_4437_);
    v_toBind_4438_ = crate::leanh::lean_ctor_get(v_inst_4433_, 1);
    crate::leanh::lean_inc(v_toBind_4438_);
    crate::leanh::lean_dec_ref(v_inst_4433_);
    v_task_4439_ = crate::leanh::lean_ctor_get(v_self_4436_, 0);
    crate::leanh::lean_inc_ref(v_task_4439_);
    v_caption_4440_ = crate::leanh::lean_ctor_get(v_self_4436_, 2);
    crate::leanh::lean_inc_ref(v_caption_4440_);
    v_optional_4441_ = crate::leanh::lean_ctor_get_uint8(
        v_self_4436_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
    );
    crate::leanh::lean_dec_ref(v_self_4436_);
    v_toPure_4442_ = crate::leanh::lean_ctor_get(v_toApplicative_4437_, 1);
    crate::leanh::lean_inc(v_toPure_4442_);
    crate::leanh::lean_dec_ref(v_toApplicative_4437_);
    v___x_4443_ = crate::leanh::lean_apply_1(v_f_4435_, v_task_4439_);
    v___x_4444_ = crate::leanh::lean_box((v_optional_4441_) as usize);
    v___f_4445_ = crate::leanh::lean_alloc_closure(
        l_Lake_Job_bindTask___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_4445_, 0, v_inst_4434_);
    crate::leanh::lean_closure_set(v___f_4445_, 1, v_caption_4440_);
    crate::leanh::lean_closure_set(v___f_4445_, 2, v___x_4444_);
    crate::leanh::lean_closure_set(v___f_4445_, 3, v_toPure_4442_);
    v___x_4446_ = crate::leanh::lean_apply_4(
        v_toBind_4438_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4443_,
        v___f_4445_,
    );
    return v___x_4446_;
}
pub unsafe fn l_panic___at___00Lake_Job_sync_spec__0(
    mut v_msg_4448_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4449_ = l_panic___at___00Lake_Job_sync_spec__0___closed__0;
    v___x_4450_ = lean_panic_fn_borrowed(v___x_4449_, v_msg_4448_);
    return v___x_4450_;
}
pub unsafe fn l_Lake_Job_sync___redArg___lam__0(
    mut v_val_4451_: *mut crate::leanh::LeanObject,
    mut v_val_4452_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_4453_: *mut crate::leanh::LeanObject,
    mut v___y_4454_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4456_ = lean_get_set_stdout(v_val_4451_);
    crate::leanh::lean_dec_ref(v___x_4456_);
    v___x_4457_ = lean_get_set_stderr(v_val_4452_);
    crate::leanh::lean_dec_ref(v___x_4457_);
    v___x_4458_ = crate::leanh::lean_box(0);
    v___x_4459_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4459_, 0, v___x_4458_);
    crate::leanh::lean_ctor_set(v___x_4459_, 1, v___y_4454_);
    return v___x_4459_;
}
pub unsafe fn l_Lake_Job_sync___redArg___lam__0___boxed(
    mut v_val_4460_: *mut crate::leanh::LeanObject,
    mut v_val_4461_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_4462_: *mut crate::leanh::LeanObject,
    mut v___y_4463_: *mut crate::leanh::LeanObject,
    mut v___y_4464_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4465_ =
        l_Lake_Job_sync___redArg___lam__0(v_val_4460_, v_val_4461_, v_a_x3f_4462_, v___y_4463_);
    crate::leanh::lean_dec(v_a_x3f_4462_);
    return v_res_4465_;
}
pub unsafe fn l_Lake_Job_sync___redArg___lam__1(
    mut v_a_4466_: *mut crate::leanh::LeanObject,
    mut v_____r_4467_: *mut crate::leanh::LeanObject,
    mut v___y_4468_: *mut crate::leanh::LeanObject,
    mut v___y_4469_: *mut crate::leanh::LeanObject,
    mut v___y_4470_: *mut crate::leanh::LeanObject,
    mut v___y_4471_: *mut crate::leanh::LeanObject,
    mut v___y_4472_: *mut crate::leanh::LeanObject,
    mut v___y_4473_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4475_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4475_, 0, v_a_4466_);
    crate::leanh::lean_ctor_set(v___x_4475_, 1, v___y_4473_);
    return v___x_4475_;
}
pub unsafe fn l_Lake_Job_sync___redArg___lam__1___boxed(
    mut v_a_4476_: *mut crate::leanh::LeanObject,
    mut v_____r_4477_: *mut crate::leanh::LeanObject,
    mut v___y_4478_: *mut crate::leanh::LeanObject,
    mut v___y_4479_: *mut crate::leanh::LeanObject,
    mut v___y_4480_: *mut crate::leanh::LeanObject,
    mut v___y_4481_: *mut crate::leanh::LeanObject,
    mut v___y_4482_: *mut crate::leanh::LeanObject,
    mut v___y_4483_: *mut crate::leanh::LeanObject,
    mut v___y_4484_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4485_ = l_Lake_Job_sync___redArg___lam__1(
        v_a_4476_,
        v_____r_4477_,
        v___y_4478_,
        v___y_4479_,
        v___y_4480_,
        v___y_4481_,
        v___y_4482_,
        v___y_4483_,
    );
    crate::leanh::lean_dec_ref(v___y_4482_);
    crate::leanh::lean_dec(v___y_4481_);
    crate::leanh::lean_dec(v___y_4480_);
    crate::leanh::lean_dec(v___y_4479_);
    crate::leanh::lean_dec_ref(v___y_4478_);
    return v_res_4485_;
}
pub unsafe fn _init_l_Lake_Job_sync___redArg___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_4486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4486_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4487_ = l_ByteArray_empty;
    v___x_4488_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4488_, 0, v___x_4487_);
    crate::leanh::lean_ctor_set(v___x_4488_, 1, v___x_4486_);
    return v___x_4488_;
}
pub unsafe fn _init_l_Lake_Job_sync___redArg___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_4491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4493_: u8 = 0;
    let mut v___x_4494_: u8 = 0;
    let mut v___x_4495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4491_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4492_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_takeTrace___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lake_takeTrace___redArg___closed__1_once),
        _init_l_Lake_takeTrace___redArg___closed__1,
    );
    v___x_4493_ = 0;
    v___x_4494_ = 0;
    v___x_4495_ = l_Lake_Job_sync___redArg___closed__1;
    v___x_4496_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_4496_, 0, v___x_4495_);
    crate::leanh::lean_ctor_set(v___x_4496_, 1, v___x_4492_);
    crate::leanh::lean_ctor_set(v___x_4496_, 2, v___x_4491_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_4496_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v___x_4494_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_4496_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
        v___x_4493_,
    );
    return v___x_4496_;
}
pub unsafe fn _init_l_Lake_Job_sync___redArg___closed__7() -> *mut crate::leanh::LeanObject {
    let mut v___x_4501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4501_ = l_Lake_Job_sync___redArg___closed__6;
    v___x_4502_ = crate::leanh::lean_unsigned_to_nat(46);
    v___x_4503_ = crate::leanh::lean_unsigned_to_nat(193);
    v___x_4504_ = l_Lake_Job_sync___redArg___closed__5;
    v___x_4505_ = l_Lake_Job_sync___redArg___closed__4;
    v___x_4506_ = l_mkPanicMessageWithDecl(
        v___x_4505_,
        v___x_4504_,
        v___x_4503_,
        v___x_4502_,
        v___x_4501_,
    );
    return v___x_4506_;
}
pub unsafe fn l_Lake_Job_sync___redArg(
    mut v_inst_4507_: *mut crate::leanh::LeanObject,
    mut v_act_4508_: *mut crate::leanh::LeanObject,
    mut v_caption_4509_: *mut crate::leanh::LeanObject,
    mut v_a_4510_: *mut crate::leanh::LeanObject,
    mut v_a_4511_: *mut crate::leanh::LeanObject,
    mut v_a_4512_: *mut crate::leanh::LeanObject,
    mut v_a_4513_: *mut crate::leanh::LeanObject,
    mut v_a_4514_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_4517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4519_: u8 = 0;
    let mut v___x_4520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_log_4541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_action_4542_: u8 = 0;
    let mut v_wantsRebuild_4543_: u8 = 0;
    let mut v_trace_4544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildTime_4545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_4546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4550_: u8 = 0;
    let mut v___x_4552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4553_: u8 = 0;
    let mut v___x_4554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4559_: u8 = 0;
    let mut v___x_4560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4567_: u8 = 0;
    let mut v_unused_4568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4573_: u8 = 0;
    let mut v___x_4574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4527_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4528_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lake_Job_sync___redArg___closed__0),
                    core::ptr::addr_of_mut!(l_Lake_Job_sync___redArg___closed__0_once),
                    _init_l_Lake_Job_sync___redArg___closed__0,
                );
                v___x_4529_ = lean_st_mk_ref(v___x_4528_);
                crate::leanh::lean_inc(v___x_4529_);
                v___x_4530_ = l_IO_FS_Stream_ofBuffer(v___x_4529_);
                crate::leanh::lean_inc_ref(v___x_4530_);
                v___x_4531_ = lean_get_set_stdout(v___x_4530_);
                v___x_4532_ = lean_get_set_stderr(v___x_4530_);
                v___x_4533_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lake_Job_sync___redArg___closed__2),
                    core::ptr::addr_of_mut!(l_Lake_Job_sync___redArg___closed__2_once),
                    _init_l_Lake_Job_sync___redArg___closed__2,
                );
                crate::leanh::lean_inc_ref(v_a_4514_);
                crate::leanh::lean_inc(v_a_4513_);
                crate::leanh::lean_inc(v_a_4512_);
                crate::leanh::lean_inc(v_a_4511_);
                crate::leanh::lean_inc_ref(v_a_4510_);
                v___x_4534_ = crate::leanh::lean_apply_7(
                    v_act_4508_,
                    v_a_4510_,
                    v_a_4511_,
                    v_a_4512_,
                    v_a_4513_,
                    v_a_4514_,
                    v___x_4533_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_4534_) == 0 {
                    v_a_4535_ = crate::leanh::lean_ctor_get(v___x_4534_, 0);
                    crate::leanh::lean_inc_n(v_a_4535_, 2);
                    v_a_4536_ = crate::leanh::lean_ctor_get(v___x_4534_, 1);
                    crate::leanh::lean_inc(v_a_4536_);
                    crate::leanh::lean_dec_ref_known(v___x_4534_, 2);
                    v___x_4537_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4537_, 0, v_a_4535_);
                    v___x_4538_ = l_Lake_Job_sync___redArg___lam__0(
                        v___x_4531_,
                        v___x_4532_,
                        v___x_4537_,
                        v_a_4536_,
                    );
                    crate::leanh::lean_dec_ref_known(v___x_4537_, 1);
                    v_a_4539_ = crate::leanh::lean_ctor_get(v___x_4538_, 1);
                    crate::leanh::lean_inc(v_a_4539_);
                    crate::leanh::lean_dec_ref(v___x_4538_);
                    v___x_4540_ = lean_st_ref_get(v___x_4529_);
                    crate::leanh::lean_dec(v___x_4529_);
                    v_log_4541_ = crate::leanh::lean_ctor_get(v_a_4539_, 0);
                    v_action_4542_ = crate::leanh::lean_ctor_get_uint8(
                        v_a_4539_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    );
                    v_wantsRebuild_4543_ = crate::leanh::lean_ctor_get_uint8(
                        v_a_4539_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                    );
                    v_trace_4544_ = crate::leanh::lean_ctor_get(v_a_4539_, 1);
                    v_buildTime_4545_ = crate::leanh::lean_ctor_get(v_a_4539_, 2);
                    v_data_4546_ = crate::leanh::lean_ctor_get(v___x_4540_, 0);
                    crate::leanh::lean_inc_ref(v_data_4546_);
                    crate::leanh::lean_dec(v___x_4540_);
                    v___x_4573_ = lean_string_validate_utf8(v_data_4546_);
                    if v___x_4573_ == 0 {
                        crate::leanh::lean_dec_ref(v_data_4546_);
                        v___x_4574_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_Job_sync___redArg___closed__7),
                            core::ptr::addr_of_mut!(l_Lake_Job_sync___redArg___closed__7_once),
                            _init_l_Lake_Job_sync___redArg___closed__7,
                        );
                        v___x_4575_ = l_panic___at___00Lake_Job_sync_spec__0(v___x_4574_);
                        v___y_4548_ = v___x_4575_;
                        state = 4;
                        continue;
                    } else {
                        v___x_4576_ = lean_string_from_utf8_unchecked(v_data_4546_);
                        v___y_4548_ = v___x_4576_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_4529_);
                    crate::leanh::lean_dec_ref(v_a_4510_);
                    v_a_4577_ = crate::leanh::lean_ctor_get(v___x_4534_, 0);
                    crate::leanh::lean_inc(v_a_4577_);
                    v_a_4578_ = crate::leanh::lean_ctor_get(v___x_4534_, 1);
                    crate::leanh::lean_inc(v_a_4578_);
                    crate::leanh::lean_dec_ref_known(v___x_4534_, 2);
                    v___x_4579_ = crate::leanh::lean_box(0);
                    v___x_4580_ = l_Lake_Job_sync___redArg___lam__0(
                        v___x_4531_,
                        v___x_4532_,
                        v___x_4579_,
                        v_a_4578_,
                    );
                    v_a_4581_ = crate::leanh::lean_ctor_get(v___x_4580_, 1);
                    crate::leanh::lean_inc(v_a_4581_);
                    crate::leanh::lean_dec_ref(v___x_4580_);
                    v_a_4524_ = v_a_4577_;
                    v_a_4525_ = v_a_4581_;
                    state = 3;
                    continue;
                }
            }
            1 => {
                v___x_4518_ = lean_task_pure(v_val_4517_);
                v___x_4519_ = 0;
                v___x_4520_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4520_, 0, v___x_4518_);
                crate::leanh::lean_ctor_set(v___x_4520_, 1, v_inst_4507_);
                crate::leanh::lean_ctor_set(v___x_4520_, 2, v_caption_4509_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4520_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_4519_,
                );
                return v___x_4520_;
            }
            2 => {
                v_val_4517_ = v___y_4522_;
                state = 1;
                continue;
            }
            3 => {
                v___x_4526_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4526_, 0, v_a_4524_);
                crate::leanh::lean_ctor_set(v___x_4526_, 1, v_a_4525_);
                v_val_4517_ = v___x_4526_;
                state = 1;
                continue;
            }
            4 => {
                v___x_4549_ = lean_string_utf8_byte_size(v___y_4548_);
                v___x_4550_ = lean_nat_dec_eq(v___x_4549_, v___x_4527_);
                if v___x_4550_ == 0 {
                    crate::leanh::lean_inc(v_buildTime_4545_);
                    crate::leanh::lean_inc_ref(v_trace_4544_);
                    crate::leanh::lean_inc_ref(v_log_4541_);
                    v_isSharedCheck_4567_ = (!crate::leanh::lean_is_exclusive(v_a_4539_)) as u8;
                    if v_isSharedCheck_4567_ == 0 {
                        v_unused_4568_ = crate::leanh::lean_ctor_get(v_a_4539_, 2);
                        crate::leanh::lean_dec(v_unused_4568_);
                        v_unused_4569_ = crate::leanh::lean_ctor_get(v_a_4539_, 1);
                        crate::leanh::lean_dec(v_unused_4569_);
                        v_unused_4570_ = crate::leanh::lean_ctor_get(v_a_4539_, 0);
                        crate::leanh::lean_dec(v_unused_4570_);
                        v___x_4552_ = v_a_4539_;
                        v_isShared_4553_ = v_isSharedCheck_4567_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_a_4539_);
                        v___x_4552_ = crate::leanh::lean_box(0);
                        v_isShared_4553_ = v_isSharedCheck_4567_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_4548_);
                    v___x_4571_ = crate::leanh::lean_box(0);
                    v___x_4572_ = l_Lake_Job_sync___redArg___lam__1(
                        v_a_4535_,
                        v___x_4571_,
                        v_a_4510_,
                        v_a_4511_,
                        v_a_4512_,
                        v_a_4513_,
                        v_a_4514_,
                        v_a_4539_,
                    );
                    crate::leanh::lean_dec_ref(v_a_4510_);
                    v___y_4522_ = v___x_4572_;
                    state = 2;
                    continue;
                }
            }
            5 => {
                v___x_4554_ = l_Lake_Job_sync___redArg___closed__3;
                v___x_4555_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4555_, 0, v___y_4548_);
                crate::leanh::lean_ctor_set(v___x_4555_, 1, v___x_4527_);
                crate::leanh::lean_ctor_set(v___x_4555_, 2, v___x_4549_);
                v___x_4556_ = l_String_Slice_trimAscii(v___x_4555_);
                v___x_4557_ = l_String_Slice_toString(v___x_4556_);
                crate::leanh::lean_dec_ref(v___x_4556_);
                v___x_4558_ = lean_string_append(v___x_4554_, v___x_4557_);
                crate::leanh::lean_dec_ref(v___x_4557_);
                v___x_4559_ = 1;
                v___x_4560_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4560_, 0, v___x_4558_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4560_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_4559_,
                );
                v___x_4561_ = crate::leanh::lean_box(0);
                v___x_4562_ = lean_array_push(v_log_4541_, v___x_4560_);
                if v_isShared_4553_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4552_, 0, v___x_4562_);
                    v___x_4564_ = v___x_4552_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4566_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4566_, 0, v___x_4562_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4566_, 1, v_trace_4544_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4566_, 2, v_buildTime_4545_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4566_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_action_4542_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4566_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_4543_,
                    );
                    v___x_4564_ = v_reuseFailAlloc_4566_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_4565_ = l_Lake_Job_sync___redArg___lam__1(
                    v_a_4535_,
                    v___x_4561_,
                    v_a_4510_,
                    v_a_4511_,
                    v_a_4512_,
                    v_a_4513_,
                    v_a_4514_,
                    v___x_4564_,
                );
                crate::leanh::lean_dec_ref(v_a_4510_);
                v___y_4522_ = v___x_4565_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Job_sync___redArg___boxed(
    mut v_inst_4582_: *mut crate::leanh::LeanObject,
    mut v_act_4583_: *mut crate::leanh::LeanObject,
    mut v_caption_4584_: *mut crate::leanh::LeanObject,
    mut v_a_4585_: *mut crate::leanh::LeanObject,
    mut v_a_4586_: *mut crate::leanh::LeanObject,
    mut v_a_4587_: *mut crate::leanh::LeanObject,
    mut v_a_4588_: *mut crate::leanh::LeanObject,
    mut v_a_4589_: *mut crate::leanh::LeanObject,
    mut v_a_4590_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4591_ = l_Lake_Job_sync___redArg(
        v_inst_4582_,
        v_act_4583_,
        v_caption_4584_,
        v_a_4585_,
        v_a_4586_,
        v_a_4587_,
        v_a_4588_,
        v_a_4589_,
    );
    crate::leanh::lean_dec_ref(v_a_4589_);
    crate::leanh::lean_dec(v_a_4588_);
    crate::leanh::lean_dec(v_a_4587_);
    crate::leanh::lean_dec(v_a_4586_);
    return v_res_4591_;
}
pub unsafe fn l_Lake_Job_sync(
    mut v_00_u03b1_4592_: *mut crate::leanh::LeanObject,
    mut v_inst_4593_: *mut crate::leanh::LeanObject,
    mut v_act_4594_: *mut crate::leanh::LeanObject,
    mut v_caption_4595_: *mut crate::leanh::LeanObject,
    mut v_a_4596_: *mut crate::leanh::LeanObject,
    mut v_a_4597_: *mut crate::leanh::LeanObject,
    mut v_a_4598_: *mut crate::leanh::LeanObject,
    mut v_a_4599_: *mut crate::leanh::LeanObject,
    mut v_a_4600_: *mut crate::leanh::LeanObject,
    mut v_a_4601_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4603_ = l_Lake_Job_sync___redArg(
        v_inst_4593_,
        v_act_4594_,
        v_caption_4595_,
        v_a_4596_,
        v_a_4597_,
        v_a_4598_,
        v_a_4599_,
        v_a_4600_,
    );
    return v___x_4603_;
}
pub unsafe fn l_Lake_Job_sync___boxed(
    mut v_00_u03b1_4604_: *mut crate::leanh::LeanObject,
    mut v_inst_4605_: *mut crate::leanh::LeanObject,
    mut v_act_4606_: *mut crate::leanh::LeanObject,
    mut v_caption_4607_: *mut crate::leanh::LeanObject,
    mut v_a_4608_: *mut crate::leanh::LeanObject,
    mut v_a_4609_: *mut crate::leanh::LeanObject,
    mut v_a_4610_: *mut crate::leanh::LeanObject,
    mut v_a_4611_: *mut crate::leanh::LeanObject,
    mut v_a_4612_: *mut crate::leanh::LeanObject,
    mut v_a_4613_: *mut crate::leanh::LeanObject,
    mut v_a_4614_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4615_ = l_Lake_Job_sync(
        v_00_u03b1_4604_,
        v_inst_4605_,
        v_act_4606_,
        v_caption_4607_,
        v_a_4608_,
        v_a_4609_,
        v_a_4610_,
        v_a_4611_,
        v_a_4612_,
        v_a_4613_,
    );
    crate::leanh::lean_dec_ref(v_a_4613_);
    crate::leanh::lean_dec_ref(v_a_4612_);
    crate::leanh::lean_dec(v_a_4611_);
    crate::leanh::lean_dec(v_a_4610_);
    crate::leanh::lean_dec(v_a_4609_);
    return v_res_4615_;
}
pub unsafe fn l_Lake_Job_async___redArg___lam__1(
    mut v___x_4616_: *mut crate::leanh::LeanObject,
    mut v___x_4617_: *mut crate::leanh::LeanObject,
    mut v___x_4618_: u8,
    mut v___x_4619_: u8,
    mut v___x_4620_: *mut crate::leanh::LeanObject,
    mut v___x_4621_: *mut crate::leanh::LeanObject,
    mut v_act_4622_: *mut crate::leanh::LeanObject,
    mut v_a_4623_: *mut crate::leanh::LeanObject,
    mut v_a_4624_: *mut crate::leanh::LeanObject,
    mut v_a_4625_: *mut crate::leanh::LeanObject,
    mut v_a_4626_: *mut crate::leanh::LeanObject,
    mut v_a_4627_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_4630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4643_: u8 = 0;
    let mut v___y_4645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_log_4653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_action_4654_: u8 = 0;
    let mut v_wantsRebuild_4655_: u8 = 0;
    let mut v_trace_4656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildTime_4657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4661_: u8 = 0;
    let mut v___x_4663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4664_: u8 = 0;
    let mut v___x_4665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4670_: u8 = 0;
    let mut v___x_4671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4676_: u8 = 0;
    let mut v_unused_4677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_4680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4681_: u8 = 0;
    let mut v___x_4682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4685_: u8 = 0;
    let mut v_a_4686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4633_ = lean_st_mk_ref(v___x_4616_);
                crate::leanh::lean_inc(v___x_4633_);
                v___x_4634_ = l_IO_FS_Stream_ofBuffer(v___x_4633_);
                crate::leanh::lean_inc_ref(v___x_4634_);
                v___x_4635_ = lean_get_set_stdout(v___x_4634_);
                v___x_4636_ = lean_get_set_stderr(v___x_4634_);
                crate::leanh::lean_inc(v___x_4621_);
                v___x_4637_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_4637_, 0, v___x_4617_);
                crate::leanh::lean_ctor_set(v___x_4637_, 1, v___x_4620_);
                crate::leanh::lean_ctor_set(v___x_4637_, 2, v___x_4621_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4637_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_4618_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4637_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                    v___x_4619_,
                );
                crate::leanh::lean_inc_ref(v_a_4627_);
                crate::leanh::lean_inc(v_a_4626_);
                crate::leanh::lean_inc(v_a_4625_);
                crate::leanh::lean_inc(v_a_4624_);
                v___x_4638_ = crate::leanh::lean_apply_7(
                    v_act_4622_,
                    v_a_4623_,
                    v_a_4624_,
                    v_a_4625_,
                    v_a_4626_,
                    v_a_4627_,
                    v___x_4637_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_4638_) == 0 {
                    v_a_4639_ = crate::leanh::lean_ctor_get(v___x_4638_, 0);
                    v_a_4640_ = crate::leanh::lean_ctor_get(v___x_4638_, 1);
                    v_isSharedCheck_4685_ = (!crate::leanh::lean_is_exclusive(v___x_4638_)) as u8;
                    if v_isSharedCheck_4685_ == 0 {
                        v___x_4642_ = v___x_4638_;
                        v_isShared_4643_ = v_isSharedCheck_4685_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4640_);
                        crate::leanh::lean_inc(v_a_4639_);
                        crate::leanh::lean_dec(v___x_4638_);
                        v___x_4642_ = crate::leanh::lean_box(0);
                        v_isShared_4643_ = v_isSharedCheck_4685_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_4633_);
                    crate::leanh::lean_dec(v___x_4621_);
                    v_a_4686_ = crate::leanh::lean_ctor_get(v___x_4638_, 0);
                    crate::leanh::lean_inc(v_a_4686_);
                    v_a_4687_ = crate::leanh::lean_ctor_get(v___x_4638_, 1);
                    crate::leanh::lean_inc(v_a_4687_);
                    crate::leanh::lean_dec_ref_known(v___x_4638_, 2);
                    v___x_4688_ = crate::leanh::lean_box(0);
                    v___x_4689_ = l_Lake_Job_sync___redArg___lam__0(
                        v___x_4635_,
                        v___x_4636_,
                        v___x_4688_,
                        v_a_4687_,
                    );
                    v_a_4690_ = crate::leanh::lean_ctor_get(v___x_4689_, 1);
                    crate::leanh::lean_inc(v_a_4690_);
                    crate::leanh::lean_dec_ref(v___x_4689_);
                    v_a_4630_ = v_a_4686_;
                    v_a_4631_ = v_a_4690_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4632_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4632_, 0, v_a_4630_);
                crate::leanh::lean_ctor_set(v___x_4632_, 1, v_a_4631_);
                return v___x_4632_;
            }
            2 => {
                crate::leanh::lean_inc(v_a_4639_);
                v___x_4649_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4649_, 0, v_a_4639_);
                v___x_4650_ = l_Lake_Job_sync___redArg___lam__0(
                    v___x_4635_,
                    v___x_4636_,
                    v___x_4649_,
                    v_a_4640_,
                );
                crate::leanh::lean_dec_ref_known(v___x_4649_, 1);
                v_a_4651_ = crate::leanh::lean_ctor_get(v___x_4650_, 1);
                crate::leanh::lean_inc(v_a_4651_);
                crate::leanh::lean_dec_ref(v___x_4650_);
                v___x_4652_ = lean_st_ref_get(v___x_4633_);
                crate::leanh::lean_dec(v___x_4633_);
                v_log_4653_ = crate::leanh::lean_ctor_get(v_a_4651_, 0);
                v_action_4654_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_4651_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_wantsRebuild_4655_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_4651_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                );
                v_trace_4656_ = crate::leanh::lean_ctor_get(v_a_4651_, 1);
                v_buildTime_4657_ = crate::leanh::lean_ctor_get(v_a_4651_, 2);
                v_data_4680_ = crate::leanh::lean_ctor_get(v___x_4652_, 0);
                crate::leanh::lean_inc_ref(v_data_4680_);
                crate::leanh::lean_dec(v___x_4652_);
                v___x_4681_ = lean_string_validate_utf8(v_data_4680_);
                if v___x_4681_ == 0 {
                    crate::leanh::lean_dec_ref(v_data_4680_);
                    v___x_4682_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_Job_sync___redArg___closed__7),
                        core::ptr::addr_of_mut!(l_Lake_Job_sync___redArg___closed__7_once),
                        _init_l_Lake_Job_sync___redArg___closed__7,
                    );
                    v___x_4683_ = l_panic___at___00Lake_Job_sync_spec__0(v___x_4682_);
                    v___y_4659_ = v___x_4683_;
                    state = 5;
                    continue;
                } else {
                    v___x_4684_ = lean_string_from_utf8_unchecked(v_data_4680_);
                    v___y_4659_ = v___x_4684_;
                    state = 5;
                    continue;
                }
            }
            3 => {
                if v_isShared_4643_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4642_, 1, v___y_4645_);
                    v___x_4647_ = v___x_4642_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4648_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4648_, 0, v_a_4639_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4648_, 1, v___y_4645_);
                    v___x_4647_ = v_reuseFailAlloc_4648_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4647_;
            }
            5 => {
                v___x_4660_ = lean_string_utf8_byte_size(v___y_4659_);
                v___x_4661_ = lean_nat_dec_eq(v___x_4660_, v___x_4621_);
                if v___x_4661_ == 0 {
                    crate::leanh::lean_inc(v_buildTime_4657_);
                    crate::leanh::lean_inc_ref(v_trace_4656_);
                    crate::leanh::lean_inc_ref(v_log_4653_);
                    v_isSharedCheck_4676_ = (!crate::leanh::lean_is_exclusive(v_a_4651_)) as u8;
                    if v_isSharedCheck_4676_ == 0 {
                        v_unused_4677_ = crate::leanh::lean_ctor_get(v_a_4651_, 2);
                        crate::leanh::lean_dec(v_unused_4677_);
                        v_unused_4678_ = crate::leanh::lean_ctor_get(v_a_4651_, 1);
                        crate::leanh::lean_dec(v_unused_4678_);
                        v_unused_4679_ = crate::leanh::lean_ctor_get(v_a_4651_, 0);
                        crate::leanh::lean_dec(v_unused_4679_);
                        v___x_4663_ = v_a_4651_;
                        v_isShared_4664_ = v_isSharedCheck_4676_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_a_4651_);
                        v___x_4663_ = crate::leanh::lean_box(0);
                        v_isShared_4664_ = v_isSharedCheck_4676_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_4659_);
                    crate::leanh::lean_dec(v___x_4621_);
                    v___y_4645_ = v_a_4651_;
                    state = 3;
                    continue;
                }
            }
            6 => {
                v___x_4665_ = l_Lake_Job_sync___redArg___closed__3;
                v___x_4666_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4666_, 0, v___y_4659_);
                crate::leanh::lean_ctor_set(v___x_4666_, 1, v___x_4621_);
                crate::leanh::lean_ctor_set(v___x_4666_, 2, v___x_4660_);
                v___x_4667_ = l_String_Slice_trimAscii(v___x_4666_);
                v___x_4668_ = l_String_Slice_toString(v___x_4667_);
                crate::leanh::lean_dec_ref(v___x_4667_);
                v___x_4669_ = lean_string_append(v___x_4665_, v___x_4668_);
                crate::leanh::lean_dec_ref(v___x_4668_);
                v___x_4670_ = 1;
                v___x_4671_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4671_, 0, v___x_4669_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4671_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_4670_,
                );
                v___x_4672_ = lean_array_push(v_log_4653_, v___x_4671_);
                if v_isShared_4664_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4663_, 0, v___x_4672_);
                    v___x_4674_ = v___x_4663_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4675_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4675_, 0, v___x_4672_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4675_, 1, v_trace_4656_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4675_, 2, v_buildTime_4657_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4675_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_action_4654_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4675_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_4655_,
                    );
                    v___x_4674_ = v_reuseFailAlloc_4675_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_4645_ = v___x_4674_;
                state = 3;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Job_async___redArg___lam__1___boxed(
    mut v___x_4691_: *mut crate::leanh::LeanObject,
    mut v___x_4692_: *mut crate::leanh::LeanObject,
    mut v___x_4693_: *mut crate::leanh::LeanObject,
    mut v___x_4694_: *mut crate::leanh::LeanObject,
    mut v___x_4695_: *mut crate::leanh::LeanObject,
    mut v___x_4696_: *mut crate::leanh::LeanObject,
    mut v_act_4697_: *mut crate::leanh::LeanObject,
    mut v_a_4698_: *mut crate::leanh::LeanObject,
    mut v_a_4699_: *mut crate::leanh::LeanObject,
    mut v_a_4700_: *mut crate::leanh::LeanObject,
    mut v_a_4701_: *mut crate::leanh::LeanObject,
    mut v_a_4702_: *mut crate::leanh::LeanObject,
    mut v___y_4703_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_22647__boxed_4704_: u8 = 0;
    let mut v___x_22648__boxed_4705_: u8 = 0;
    let mut v_res_4706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_22647__boxed_4704_ = (crate::leanh::lean_unbox(v___x_4693_) as u8);
    v___x_22648__boxed_4705_ = (crate::leanh::lean_unbox(v___x_4694_) as u8);
    v_res_4706_ = l_Lake_Job_async___redArg___lam__1(
        v___x_4691_,
        v___x_4692_,
        v___x_22647__boxed_4704_,
        v___x_22648__boxed_4705_,
        v___x_4695_,
        v___x_4696_,
        v_act_4697_,
        v_a_4698_,
        v_a_4699_,
        v_a_4700_,
        v_a_4701_,
        v_a_4702_,
    );
    crate::leanh::lean_dec_ref(v_a_4702_);
    crate::leanh::lean_dec(v_a_4701_);
    crate::leanh::lean_dec(v_a_4700_);
    crate::leanh::lean_dec(v_a_4699_);
    return v_res_4706_;
}
pub unsafe fn l_Lake_Job_async___redArg(
    mut v_inst_4707_: *mut crate::leanh::LeanObject,
    mut v_act_4708_: *mut crate::leanh::LeanObject,
    mut v_prio_4709_: *mut crate::leanh::LeanObject,
    mut v_caption_4710_: *mut crate::leanh::LeanObject,
    mut v_a_4711_: *mut crate::leanh::LeanObject,
    mut v_a_4712_: *mut crate::leanh::LeanObject,
    mut v_a_4713_: *mut crate::leanh::LeanObject,
    mut v_a_4714_: *mut crate::leanh::LeanObject,
    mut v_a_4715_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4720_: u8 = 0;
    let mut v___x_4721_: u8 = 0;
    let mut v___x_4722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4717_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4718_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Job_sync___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lake_Job_sync___redArg___closed__0_once),
        _init_l_Lake_Job_sync___redArg___closed__0,
    );
    v___x_4719_ = l_Lake_Job_sync___redArg___closed__1;
    v___x_4720_ = 0;
    v___x_4721_ = 0;
    v___x_4722_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_takeTrace___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lake_takeTrace___redArg___closed__1_once),
        _init_l_Lake_takeTrace___redArg___closed__1,
    );
    v___x_4723_ = crate::leanh::lean_box((v___x_4720_) as usize);
    v___x_4724_ = crate::leanh::lean_box((v___x_4721_) as usize);
    crate::leanh::lean_inc_ref(v_a_4715_);
    crate::leanh::lean_inc(v_a_4714_);
    crate::leanh::lean_inc(v_a_4713_);
    crate::leanh::lean_inc(v_a_4712_);
    v___f_4725_ = crate::leanh::lean_alloc_closure(
        l_Lake_Job_async___redArg___lam__1___boxed as *mut core::ffi::c_void,
        13,
        12,
    );
    crate::leanh::lean_closure_set(v___f_4725_, 0, v___x_4718_);
    crate::leanh::lean_closure_set(v___f_4725_, 1, v___x_4719_);
    crate::leanh::lean_closure_set(v___f_4725_, 2, v___x_4723_);
    crate::leanh::lean_closure_set(v___f_4725_, 3, v___x_4724_);
    crate::leanh::lean_closure_set(v___f_4725_, 4, v___x_4722_);
    crate::leanh::lean_closure_set(v___f_4725_, 5, v___x_4717_);
    crate::leanh::lean_closure_set(v___f_4725_, 6, v_act_4708_);
    crate::leanh::lean_closure_set(v___f_4725_, 7, v_a_4711_);
    crate::leanh::lean_closure_set(v___f_4725_, 8, v_a_4712_);
    crate::leanh::lean_closure_set(v___f_4725_, 9, v_a_4713_);
    crate::leanh::lean_closure_set(v___f_4725_, 10, v_a_4714_);
    crate::leanh::lean_closure_set(v___f_4725_, 11, v_a_4715_);
    v___x_4726_ = lean_io_as_task(v___f_4725_, v_prio_4709_);
    v___x_4727_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_4727_, 0, v___x_4726_);
    crate::leanh::lean_ctor_set(v___x_4727_, 1, v_inst_4707_);
    crate::leanh::lean_ctor_set(v___x_4727_, 2, v_caption_4710_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_4727_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v___x_4721_,
    );
    return v___x_4727_;
}
pub unsafe fn l_Lake_Job_async___redArg___boxed(
    mut v_inst_4728_: *mut crate::leanh::LeanObject,
    mut v_act_4729_: *mut crate::leanh::LeanObject,
    mut v_prio_4730_: *mut crate::leanh::LeanObject,
    mut v_caption_4731_: *mut crate::leanh::LeanObject,
    mut v_a_4732_: *mut crate::leanh::LeanObject,
    mut v_a_4733_: *mut crate::leanh::LeanObject,
    mut v_a_4734_: *mut crate::leanh::LeanObject,
    mut v_a_4735_: *mut crate::leanh::LeanObject,
    mut v_a_4736_: *mut crate::leanh::LeanObject,
    mut v_a_4737_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4738_ = l_Lake_Job_async___redArg(
        v_inst_4728_,
        v_act_4729_,
        v_prio_4730_,
        v_caption_4731_,
        v_a_4732_,
        v_a_4733_,
        v_a_4734_,
        v_a_4735_,
        v_a_4736_,
    );
    crate::leanh::lean_dec_ref(v_a_4736_);
    crate::leanh::lean_dec(v_a_4735_);
    crate::leanh::lean_dec(v_a_4734_);
    crate::leanh::lean_dec(v_a_4733_);
    return v_res_4738_;
}
pub unsafe fn l_Lake_Job_async(
    mut v_00_u03b1_4739_: *mut crate::leanh::LeanObject,
    mut v_inst_4740_: *mut crate::leanh::LeanObject,
    mut v_act_4741_: *mut crate::leanh::LeanObject,
    mut v_prio_4742_: *mut crate::leanh::LeanObject,
    mut v_caption_4743_: *mut crate::leanh::LeanObject,
    mut v_a_4744_: *mut crate::leanh::LeanObject,
    mut v_a_4745_: *mut crate::leanh::LeanObject,
    mut v_a_4746_: *mut crate::leanh::LeanObject,
    mut v_a_4747_: *mut crate::leanh::LeanObject,
    mut v_a_4748_: *mut crate::leanh::LeanObject,
    mut v_a_4749_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4751_ = l_Lake_Job_async___redArg(
        v_inst_4740_,
        v_act_4741_,
        v_prio_4742_,
        v_caption_4743_,
        v_a_4744_,
        v_a_4745_,
        v_a_4746_,
        v_a_4747_,
        v_a_4748_,
    );
    return v___x_4751_;
}
pub unsafe fn l_Lake_Job_async___boxed(
    mut v_00_u03b1_4752_: *mut crate::leanh::LeanObject,
    mut v_inst_4753_: *mut crate::leanh::LeanObject,
    mut v_act_4754_: *mut crate::leanh::LeanObject,
    mut v_prio_4755_: *mut crate::leanh::LeanObject,
    mut v_caption_4756_: *mut crate::leanh::LeanObject,
    mut v_a_4757_: *mut crate::leanh::LeanObject,
    mut v_a_4758_: *mut crate::leanh::LeanObject,
    mut v_a_4759_: *mut crate::leanh::LeanObject,
    mut v_a_4760_: *mut crate::leanh::LeanObject,
    mut v_a_4761_: *mut crate::leanh::LeanObject,
    mut v_a_4762_: *mut crate::leanh::LeanObject,
    mut v_a_4763_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4764_ = l_Lake_Job_async(
        v_00_u03b1_4752_,
        v_inst_4753_,
        v_act_4754_,
        v_prio_4755_,
        v_caption_4756_,
        v_a_4757_,
        v_a_4758_,
        v_a_4759_,
        v_a_4760_,
        v_a_4761_,
        v_a_4762_,
    );
    crate::leanh::lean_dec_ref(v_a_4762_);
    crate::leanh::lean_dec_ref(v_a_4761_);
    crate::leanh::lean_dec(v_a_4760_);
    crate::leanh::lean_dec(v_a_4759_);
    crate::leanh::lean_dec(v_a_4758_);
    return v_res_4764_;
}
pub unsafe fn l_Lake_Job_wait___redArg(
    mut v_self_4765_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_task_4767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_task_4767_ = crate::leanh::lean_ctor_get(v_self_4765_, 0);
    crate::leanh::lean_inc_ref(v_task_4767_);
    crate::leanh::lean_dec_ref(v_self_4765_);
    v___x_4768_ = lean_io_wait(v_task_4767_);
    return v___x_4768_;
}
pub unsafe fn l_Lake_Job_wait___redArg___boxed(
    mut v_self_4769_: *mut crate::leanh::LeanObject,
    mut v_a_4770_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4771_ = l_Lake_Job_wait___redArg(v_self_4769_);
    return v_res_4771_;
}
pub unsafe fn l_Lake_Job_wait(
    mut v_00_u03b1_4772_: *mut crate::leanh::LeanObject,
    mut v_self_4773_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_task_4775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_task_4775_ = crate::leanh::lean_ctor_get(v_self_4773_, 0);
    crate::leanh::lean_inc_ref(v_task_4775_);
    crate::leanh::lean_dec_ref(v_self_4773_);
    v___x_4776_ = lean_io_wait(v_task_4775_);
    return v___x_4776_;
}
pub unsafe fn l_Lake_Job_wait___boxed(
    mut v_00_u03b1_4777_: *mut crate::leanh::LeanObject,
    mut v_self_4778_: *mut crate::leanh::LeanObject,
    mut v_a_4779_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4780_ = l_Lake_Job_wait(v_00_u03b1_4777_, v_self_4778_);
    return v_res_4780_;
}
pub unsafe fn l_Lake_Job_wait_x3f___redArg(
    mut v_self_4781_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_task_4783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_task_4783_ = crate::leanh::lean_ctor_get(v_self_4781_, 0);
    crate::leanh::lean_inc_ref(v_task_4783_);
    crate::leanh::lean_dec_ref(v_self_4781_);
    v___x_4784_ = lean_io_wait(v_task_4783_);
    if crate::leanh::lean_obj_tag(v___x_4784_) == 0 {
        let mut v_a_4785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_4785_ = crate::leanh::lean_ctor_get(v___x_4784_, 0);
        crate::leanh::lean_inc(v_a_4785_);
        crate::leanh::lean_dec_ref_known(v___x_4784_, 2);
        v___x_4786_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4786_, 0, v_a_4785_);
        return v___x_4786_;
    } else {
        let mut v___x_4787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref_known(v___x_4784_, 2);
        v___x_4787_ = crate::leanh::lean_box(0);
        return v___x_4787_;
    }
}
pub unsafe fn l_Lake_Job_wait_x3f___redArg___boxed(
    mut v_self_4788_: *mut crate::leanh::LeanObject,
    mut v_a_4789_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4790_ = l_Lake_Job_wait_x3f___redArg(v_self_4788_);
    return v_res_4790_;
}
pub unsafe fn l_Lake_Job_wait_x3f(
    mut v_00_u03b1_4791_: *mut crate::leanh::LeanObject,
    mut v_self_4792_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_task_4794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_task_4794_ = crate::leanh::lean_ctor_get(v_self_4792_, 0);
    crate::leanh::lean_inc_ref(v_task_4794_);
    crate::leanh::lean_dec_ref(v_self_4792_);
    v___x_4795_ = lean_io_wait(v_task_4794_);
    if crate::leanh::lean_obj_tag(v___x_4795_) == 0 {
        let mut v_a_4796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_4796_ = crate::leanh::lean_ctor_get(v___x_4795_, 0);
        crate::leanh::lean_inc(v_a_4796_);
        crate::leanh::lean_dec_ref_known(v___x_4795_, 2);
        v___x_4797_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4797_, 0, v_a_4796_);
        return v___x_4797_;
    } else {
        let mut v___x_4798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref_known(v___x_4795_, 2);
        v___x_4798_ = crate::leanh::lean_box(0);
        return v___x_4798_;
    }
}
pub unsafe fn l_Lake_Job_wait_x3f___boxed(
    mut v_00_u03b1_4799_: *mut crate::leanh::LeanObject,
    mut v_self_4800_: *mut crate::leanh::LeanObject,
    mut v_a_4801_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4802_ = l_Lake_Job_wait_x3f(v_00_u03b1_4799_, v_self_4800_);
    return v_res_4802_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_await_spec__0(
    mut v_as_4803_: *mut crate::leanh::LeanObject,
    mut v_i_4804_: usize,
    mut v_stop_4805_: usize,
    mut v_b_4806_: *mut crate::leanh::LeanObject,
    mut v___y_4807_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4809_: u8 = 0;
    let mut v___x_4810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4813_: usize = 0;
    let mut v___x_4814_: usize = 0;
    let mut v___x_4816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4809_ = lean_usize_dec_eq(v_i_4804_, v_stop_4805_);
                if v___x_4809_ == 0 {
                    v___x_4810_ = lean_array_uget_borrowed(v_as_4803_, v_i_4804_);
                    v___x_4811_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc(v___x_4810_);
                    v___x_4812_ = lean_array_push(v___y_4807_, v___x_4810_);
                    v___x_4813_ = 1usize;
                    v___x_4814_ = lean_usize_add(v_i_4804_, v___x_4813_);
                    v_i_4804_ = v___x_4814_;
                    v_b_4806_ = v___x_4811_;
                    v___y_4807_ = v___x_4812_;
                    state = 0;
                    continue;
                } else {
                    v___x_4816_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4816_, 0, v_b_4806_);
                    crate::leanh::lean_ctor_set(v___x_4816_, 1, v___y_4807_);
                    return v___x_4816_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_await_spec__0___boxed(
    mut v_as_4817_: *mut crate::leanh::LeanObject,
    mut v_i_4818_: *mut crate::leanh::LeanObject,
    mut v_stop_4819_: *mut crate::leanh::LeanObject,
    mut v_b_4820_: *mut crate::leanh::LeanObject,
    mut v___y_4821_: *mut crate::leanh::LeanObject,
    mut v___y_4822_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_4823_: usize = 0;
    let mut v_stop_boxed_4824_: usize = 0;
    let mut v_res_4825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4823_ = crate::leanh::lean_unbox_usize(v_i_4818_);
    crate::leanh::lean_dec(v_i_4818_);
    v_stop_boxed_4824_ = crate::leanh::lean_unbox_usize(v_stop_4819_);
    crate::leanh::lean_dec(v_stop_4819_);
    v_res_4825_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_await_spec__0(v_as_4817_, v_i_boxed_4823_, v_stop_boxed_4824_, v_b_4820_, v___y_4821_);
    crate::leanh::lean_dec_ref(v_as_4817_);
    return v_res_4825_;
}
pub unsafe fn l_Lake_Job_await___redArg(
    mut v_self_4826_: *mut crate::leanh::LeanObject,
    mut v_a_4827_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_task_4829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4835_: u8 = 0;
    let mut v_a_4837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4848_: u8 = 0;
    let mut v___x_4850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4852_: u8 = 0;
    let mut v_log_4853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4856_: u8 = 0;
    let mut v___x_4857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4858_: u8 = 0;
    let mut v___x_4859_: usize = 0;
    let mut v___x_4860_: usize = 0;
    let mut v___x_4861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4862_: usize = 0;
    let mut v___x_4863_: usize = 0;
    let mut v___x_4864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4865_: u8 = 0;
    let mut v_a_4866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4870_: u8 = 0;
    let mut v_a_4872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4883_: u8 = 0;
    let mut v___x_4885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4887_: u8 = 0;
    let mut v_log_4888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4891_: u8 = 0;
    let mut v___x_4892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4893_: u8 = 0;
    let mut v___x_4894_: usize = 0;
    let mut v___x_4895_: usize = 0;
    let mut v___x_4896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4897_: usize = 0;
    let mut v___x_4898_: usize = 0;
    let mut v___x_4899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4900_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_task_4829_ = crate::leanh::lean_ctor_get(v_self_4826_, 0);
                crate::leanh::lean_inc_ref(v_task_4829_);
                crate::leanh::lean_dec_ref(v_self_4826_);
                v___x_4830_ = lean_io_wait(v_task_4829_);
                if crate::leanh::lean_obj_tag(v___x_4830_) == 0 {
                    v_a_4831_ = crate::leanh::lean_ctor_get(v___x_4830_, 0);
                    v_a_4832_ = crate::leanh::lean_ctor_get(v___x_4830_, 1);
                    v_isSharedCheck_4865_ = (!crate::leanh::lean_is_exclusive(v___x_4830_)) as u8;
                    if v_isSharedCheck_4865_ == 0 {
                        v___x_4834_ = v___x_4830_;
                        v_isShared_4835_ = v_isSharedCheck_4865_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4832_);
                        crate::leanh::lean_inc(v_a_4831_);
                        crate::leanh::lean_dec(v___x_4830_);
                        v___x_4834_ = crate::leanh::lean_box(0);
                        v_isShared_4835_ = v_isSharedCheck_4865_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4866_ = crate::leanh::lean_ctor_get(v___x_4830_, 0);
                    v_a_4867_ = crate::leanh::lean_ctor_get(v___x_4830_, 1);
                    v_isSharedCheck_4900_ = (!crate::leanh::lean_is_exclusive(v___x_4830_)) as u8;
                    if v_isSharedCheck_4900_ == 0 {
                        v___x_4869_ = v___x_4830_;
                        v_isShared_4870_ = v_isSharedCheck_4900_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4867_);
                        crate::leanh::lean_inc(v_a_4866_);
                        crate::leanh::lean_dec(v___x_4830_);
                        v___x_4869_ = crate::leanh::lean_box(0);
                        v_isShared_4870_ = v_isSharedCheck_4900_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_log_4853_ = crate::leanh::lean_ctor_get(v_a_4832_, 0);
                crate::leanh::lean_inc_ref(v_log_4853_);
                crate::leanh::lean_dec(v_a_4832_);
                v___x_4854_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4855_ = lean_array_get_size(v_log_4853_);
                v___x_4856_ = lean_nat_dec_lt(v___x_4854_, v___x_4855_);
                if v___x_4856_ == 0 {
                    crate::leanh::lean_dec_ref(v_log_4853_);
                    v_a_4837_ = v_a_4827_;
                    state = 2;
                    continue;
                } else {
                    v___x_4857_ = crate::leanh::lean_box(0);
                    v___x_4858_ = lean_nat_dec_le(v___x_4855_, v___x_4855_);
                    if v___x_4858_ == 0 {
                        if v___x_4856_ == 0 {
                            crate::leanh::lean_dec_ref(v_log_4853_);
                            v_a_4837_ = v_a_4827_;
                            state = 2;
                            continue;
                        } else {
                            v___x_4859_ = 0usize;
                            v___x_4860_ = lean_usize_of_nat(v___x_4855_);
                            v___x_4861_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_await_spec__0(v_log_4853_, v___x_4859_, v___x_4860_, v___x_4857_, v_a_4827_);
                            crate::leanh::lean_dec_ref(v_log_4853_);
                            v___y_4842_ = v___x_4861_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v___x_4862_ = 0usize;
                        v___x_4863_ = lean_usize_of_nat(v___x_4855_);
                        v___x_4864_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_await_spec__0(v_log_4853_, v___x_4862_, v___x_4863_, v___x_4857_, v_a_4827_);
                        crate::leanh::lean_dec_ref(v_log_4853_);
                        v___y_4842_ = v___x_4864_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_4835_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4834_, 1, v_a_4837_);
                    v___x_4839_ = v___x_4834_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4840_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4840_, 0, v_a_4831_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4840_, 1, v_a_4837_);
                    v___x_4839_ = v_reuseFailAlloc_4840_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4839_;
            }
            4 => {
                if crate::leanh::lean_obj_tag(v___y_4842_) == 0 {
                    v_a_4843_ = crate::leanh::lean_ctor_get(v___y_4842_, 1);
                    crate::leanh::lean_inc(v_a_4843_);
                    crate::leanh::lean_dec_ref_known(v___y_4842_, 2);
                    v_a_4837_ = v_a_4843_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_del_object(v___x_4834_);
                    crate::leanh::lean_dec(v_a_4831_);
                    v_a_4844_ = crate::leanh::lean_ctor_get(v___y_4842_, 0);
                    v_a_4845_ = crate::leanh::lean_ctor_get(v___y_4842_, 1);
                    v_isSharedCheck_4852_ = (!crate::leanh::lean_is_exclusive(v___y_4842_)) as u8;
                    if v_isSharedCheck_4852_ == 0 {
                        v___x_4847_ = v___y_4842_;
                        v_isShared_4848_ = v_isSharedCheck_4852_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4845_);
                        crate::leanh::lean_inc(v_a_4844_);
                        crate::leanh::lean_dec(v___y_4842_);
                        v___x_4847_ = crate::leanh::lean_box(0);
                        v_isShared_4848_ = v_isSharedCheck_4852_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_4848_ == 0 {
                    v___x_4850_ = v___x_4847_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4851_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4851_, 0, v_a_4844_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4851_, 1, v_a_4845_);
                    v___x_4850_ = v_reuseFailAlloc_4851_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4850_;
            }
            7 => {
                v_log_4888_ = crate::leanh::lean_ctor_get(v_a_4867_, 0);
                crate::leanh::lean_inc_ref(v_log_4888_);
                crate::leanh::lean_dec(v_a_4867_);
                v___x_4889_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4890_ = lean_array_get_size(v_log_4888_);
                v___x_4891_ = lean_nat_dec_lt(v___x_4889_, v___x_4890_);
                if v___x_4891_ == 0 {
                    crate::leanh::lean_dec_ref(v_log_4888_);
                    v_a_4872_ = v_a_4827_;
                    state = 8;
                    continue;
                } else {
                    v___x_4892_ = crate::leanh::lean_box(0);
                    v___x_4893_ = lean_nat_dec_le(v___x_4890_, v___x_4890_);
                    if v___x_4893_ == 0 {
                        if v___x_4891_ == 0 {
                            crate::leanh::lean_dec_ref(v_log_4888_);
                            v_a_4872_ = v_a_4827_;
                            state = 8;
                            continue;
                        } else {
                            v___x_4894_ = 0usize;
                            v___x_4895_ = lean_usize_of_nat(v___x_4890_);
                            v___x_4896_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_await_spec__0(v_log_4888_, v___x_4894_, v___x_4895_, v___x_4892_, v_a_4827_);
                            crate::leanh::lean_dec_ref(v_log_4888_);
                            v___y_4877_ = v___x_4896_;
                            state = 10;
                            continue;
                        }
                    } else {
                        v___x_4897_ = 0usize;
                        v___x_4898_ = lean_usize_of_nat(v___x_4890_);
                        v___x_4899_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_await_spec__0(v_log_4888_, v___x_4897_, v___x_4898_, v___x_4892_, v_a_4827_);
                        crate::leanh::lean_dec_ref(v_log_4888_);
                        v___y_4877_ = v___x_4899_;
                        state = 10;
                        continue;
                    }
                }
            }
            8 => {
                if v_isShared_4870_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4869_, 1, v_a_4872_);
                    v___x_4874_ = v___x_4869_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4875_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4875_, 0, v_a_4866_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4875_, 1, v_a_4872_);
                    v___x_4874_ = v_reuseFailAlloc_4875_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4874_;
            }
            10 => {
                if crate::leanh::lean_obj_tag(v___y_4877_) == 0 {
                    v_a_4878_ = crate::leanh::lean_ctor_get(v___y_4877_, 1);
                    crate::leanh::lean_inc(v_a_4878_);
                    crate::leanh::lean_dec_ref_known(v___y_4877_, 2);
                    v_a_4872_ = v_a_4878_;
                    state = 8;
                    continue;
                } else {
                    crate::leanh::lean_del_object(v___x_4869_);
                    crate::leanh::lean_dec(v_a_4866_);
                    v_a_4879_ = crate::leanh::lean_ctor_get(v___y_4877_, 0);
                    v_a_4880_ = crate::leanh::lean_ctor_get(v___y_4877_, 1);
                    v_isSharedCheck_4887_ = (!crate::leanh::lean_is_exclusive(v___y_4877_)) as u8;
                    if v_isSharedCheck_4887_ == 0 {
                        v___x_4882_ = v___y_4877_;
                        v_isShared_4883_ = v_isSharedCheck_4887_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4880_);
                        crate::leanh::lean_inc(v_a_4879_);
                        crate::leanh::lean_dec(v___y_4877_);
                        v___x_4882_ = crate::leanh::lean_box(0);
                        v_isShared_4883_ = v_isSharedCheck_4887_;
                        state = 11;
                        continue;
                    }
                }
            }
            11 => {
                if v_isShared_4883_ == 0 {
                    v___x_4885_ = v___x_4882_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4886_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4886_, 0, v_a_4879_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4886_, 1, v_a_4880_);
                    v___x_4885_ = v_reuseFailAlloc_4886_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4885_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Job_await___redArg___boxed(
    mut v_self_4901_: *mut crate::leanh::LeanObject,
    mut v_a_4902_: *mut crate::leanh::LeanObject,
    mut v_a_4903_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4904_ = l_Lake_Job_await___redArg(v_self_4901_, v_a_4902_);
    return v_res_4904_;
}
pub unsafe fn l_Lake_Job_await(
    mut v_00_u03b1_4905_: *mut crate::leanh::LeanObject,
    mut v_self_4906_: *mut crate::leanh::LeanObject,
    mut v_a_4907_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4909_ = l_Lake_Job_await___redArg(v_self_4906_, v_a_4907_);
    return v___x_4909_;
}
pub unsafe fn l_Lake_Job_await___boxed(
    mut v_00_u03b1_4910_: *mut crate::leanh::LeanObject,
    mut v_self_4911_: *mut crate::leanh::LeanObject,
    mut v_a_4912_: *mut crate::leanh::LeanObject,
    mut v_a_4913_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4914_ = l_Lake_Job_await(v_00_u03b1_4910_, v_self_4911_, v_a_4912_);
    return v_res_4914_;
}
pub unsafe fn l_Lake_Job_mapM___redArg___lam__1(
    mut v_a_4915_: *mut crate::leanh::LeanObject,
    mut v_f_4916_: *mut crate::leanh::LeanObject,
    mut v_a_4917_: *mut crate::leanh::LeanObject,
    mut v_a_4918_: *mut crate::leanh::LeanObject,
    mut v_a_4919_: *mut crate::leanh::LeanObject,
    mut v_a_4920_: *mut crate::leanh::LeanObject,
    mut v_a_4921_: *mut crate::leanh::LeanObject,
    mut v_x_4922_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_4925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_log_4936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_action_4937_: u8 = 0;
    let mut v_wantsRebuild_4938_: u8 = 0;
    let mut v_trace_4939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildTime_4940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4943_: u8 = 0;
    let mut v_trace_4944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4952_: u8 = 0;
    let mut v___y_4954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_log_4962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_action_4963_: u8 = 0;
    let mut v_wantsRebuild_4964_: u8 = 0;
    let mut v_trace_4965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildTime_4966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4970_: u8 = 0;
    let mut v___x_4972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4973_: u8 = 0;
    let mut v___x_4974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4979_: u8 = 0;
    let mut v___x_4980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4985_: u8 = 0;
    let mut v_unused_4986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_4989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4990_: u8 = 0;
    let mut v___x_4991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4994_: u8 = 0;
    let mut v_a_4995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5001_: u8 = 0;
    let mut v_a_5002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5006_: u8 = 0;
    let mut v___x_5008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5010_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4922_) == 0 {
                    v_a_4928_ = crate::leanh::lean_ctor_get(v_x_4922_, 0);
                    crate::leanh::lean_inc(v_a_4928_);
                    v_a_4929_ = crate::leanh::lean_ctor_get(v_x_4922_, 1);
                    crate::leanh::lean_inc(v_a_4929_);
                    crate::leanh::lean_dec_ref_known(v_x_4922_, 2);
                    v___x_4930_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4931_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_Job_sync___redArg___closed__0),
                        core::ptr::addr_of_mut!(l_Lake_Job_sync___redArg___closed__0_once),
                        _init_l_Lake_Job_sync___redArg___closed__0,
                    );
                    v___x_4932_ = lean_st_mk_ref(v___x_4931_);
                    crate::leanh::lean_inc(v___x_4932_);
                    v___x_4933_ = l_IO_FS_Stream_ofBuffer(v___x_4932_);
                    crate::leanh::lean_inc_ref(v___x_4933_);
                    v___x_4934_ = lean_get_set_stdout(v___x_4933_);
                    v___x_4935_ = lean_get_set_stderr(v___x_4933_);
                    v_log_4936_ = crate::leanh::lean_ctor_get(v_a_4929_, 0);
                    v_action_4937_ = crate::leanh::lean_ctor_get_uint8(
                        v_a_4929_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    );
                    v_wantsRebuild_4938_ = crate::leanh::lean_ctor_get_uint8(
                        v_a_4929_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                    );
                    v_trace_4939_ = crate::leanh::lean_ctor_get(v_a_4929_, 1);
                    v_buildTime_4940_ = crate::leanh::lean_ctor_get(v_a_4929_, 2);
                    v_isSharedCheck_5001_ = (!crate::leanh::lean_is_exclusive(v_a_4929_)) as u8;
                    if v_isSharedCheck_5001_ == 0 {
                        v___x_4942_ = v_a_4929_;
                        v_isShared_4943_ = v_isSharedCheck_5001_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_buildTime_4940_);
                        crate::leanh::lean_inc(v_trace_4939_);
                        crate::leanh::lean_inc(v_log_4936_);
                        crate::leanh::lean_dec(v_a_4929_);
                        v___x_4942_ = crate::leanh::lean_box(0);
                        v_isShared_4943_ = v_isSharedCheck_5001_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_a_4917_);
                    crate::leanh::lean_dec_ref(v_f_4916_);
                    v_a_5002_ = crate::leanh::lean_ctor_get(v_x_4922_, 0);
                    v_a_5003_ = crate::leanh::lean_ctor_get(v_x_4922_, 1);
                    v_isSharedCheck_5010_ = (!crate::leanh::lean_is_exclusive(v_x_4922_)) as u8;
                    if v_isSharedCheck_5010_ == 0 {
                        v___x_5005_ = v_x_4922_;
                        v_isShared_5006_ = v_isSharedCheck_5010_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5003_);
                        crate::leanh::lean_inc(v_a_5002_);
                        crate::leanh::lean_dec(v_x_4922_);
                        v___x_5005_ = crate::leanh::lean_box(0);
                        v_isShared_5006_ = v_isSharedCheck_5010_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4927_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4927_, 0, v_a_4925_);
                crate::leanh::lean_ctor_set(v___x_4927_, 1, v_a_4926_);
                return v___x_4927_;
            }
            2 => {
                crate::leanh::lean_inc_ref(v_a_4915_);
                v_trace_4944_ = l_Lake_BuildTrace_mix(v_a_4915_, v_trace_4939_);
                if v_isShared_4943_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4942_, 1, v_trace_4944_);
                    v___x_4946_ = v___x_4942_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5000_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5000_, 0, v_log_4936_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5000_, 1, v_trace_4944_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5000_, 2, v_buildTime_4940_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5000_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_action_4937_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5000_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_4938_,
                    );
                    v___x_4946_ = v_reuseFailAlloc_5000_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_inc_ref(v_a_4921_);
                crate::leanh::lean_inc(v_a_4920_);
                crate::leanh::lean_inc(v_a_4919_);
                crate::leanh::lean_inc(v_a_4918_);
                v___x_4947_ = crate::leanh::lean_apply_8(
                    v_f_4916_,
                    v_a_4928_,
                    v_a_4917_,
                    v_a_4918_,
                    v_a_4919_,
                    v_a_4920_,
                    v_a_4921_,
                    v___x_4946_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_4947_) == 0 {
                    v_a_4948_ = crate::leanh::lean_ctor_get(v___x_4947_, 0);
                    v_a_4949_ = crate::leanh::lean_ctor_get(v___x_4947_, 1);
                    v_isSharedCheck_4994_ = (!crate::leanh::lean_is_exclusive(v___x_4947_)) as u8;
                    if v_isSharedCheck_4994_ == 0 {
                        v___x_4951_ = v___x_4947_;
                        v_isShared_4952_ = v_isSharedCheck_4994_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4949_);
                        crate::leanh::lean_inc(v_a_4948_);
                        crate::leanh::lean_dec(v___x_4947_);
                        v___x_4951_ = crate::leanh::lean_box(0);
                        v_isShared_4952_ = v_isSharedCheck_4994_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_4932_);
                    v_a_4995_ = crate::leanh::lean_ctor_get(v___x_4947_, 0);
                    crate::leanh::lean_inc(v_a_4995_);
                    v_a_4996_ = crate::leanh::lean_ctor_get(v___x_4947_, 1);
                    crate::leanh::lean_inc(v_a_4996_);
                    crate::leanh::lean_dec_ref_known(v___x_4947_, 2);
                    v___x_4997_ = crate::leanh::lean_box(0);
                    v___x_4998_ = l_Lake_Job_sync___redArg___lam__0(
                        v___x_4934_,
                        v___x_4935_,
                        v___x_4997_,
                        v_a_4996_,
                    );
                    v_a_4999_ = crate::leanh::lean_ctor_get(v___x_4998_, 1);
                    crate::leanh::lean_inc(v_a_4999_);
                    crate::leanh::lean_dec_ref(v___x_4998_);
                    v_a_4925_ = v_a_4995_;
                    v_a_4926_ = v_a_4999_;
                    state = 1;
                    continue;
                }
            }
            4 => {
                crate::leanh::lean_inc(v_a_4948_);
                v___x_4958_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4958_, 0, v_a_4948_);
                v___x_4959_ = l_Lake_Job_sync___redArg___lam__0(
                    v___x_4934_,
                    v___x_4935_,
                    v___x_4958_,
                    v_a_4949_,
                );
                crate::leanh::lean_dec_ref_known(v___x_4958_, 1);
                v_a_4960_ = crate::leanh::lean_ctor_get(v___x_4959_, 1);
                crate::leanh::lean_inc(v_a_4960_);
                crate::leanh::lean_dec_ref(v___x_4959_);
                v___x_4961_ = lean_st_ref_get(v___x_4932_);
                crate::leanh::lean_dec(v___x_4932_);
                v_log_4962_ = crate::leanh::lean_ctor_get(v_a_4960_, 0);
                v_action_4963_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_4960_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_wantsRebuild_4964_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_4960_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                );
                v_trace_4965_ = crate::leanh::lean_ctor_get(v_a_4960_, 1);
                v_buildTime_4966_ = crate::leanh::lean_ctor_get(v_a_4960_, 2);
                v_data_4989_ = crate::leanh::lean_ctor_get(v___x_4961_, 0);
                crate::leanh::lean_inc_ref(v_data_4989_);
                crate::leanh::lean_dec(v___x_4961_);
                v___x_4990_ = lean_string_validate_utf8(v_data_4989_);
                if v___x_4990_ == 0 {
                    crate::leanh::lean_dec_ref(v_data_4989_);
                    v___x_4991_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_Job_sync___redArg___closed__7),
                        core::ptr::addr_of_mut!(l_Lake_Job_sync___redArg___closed__7_once),
                        _init_l_Lake_Job_sync___redArg___closed__7,
                    );
                    v___x_4992_ = l_panic___at___00Lake_Job_sync_spec__0(v___x_4991_);
                    v___y_4968_ = v___x_4992_;
                    state = 7;
                    continue;
                } else {
                    v___x_4993_ = lean_string_from_utf8_unchecked(v_data_4989_);
                    v___y_4968_ = v___x_4993_;
                    state = 7;
                    continue;
                }
            }
            5 => {
                if v_isShared_4952_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4951_, 1, v___y_4954_);
                    v___x_4956_ = v___x_4951_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4957_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4957_, 0, v_a_4948_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4957_, 1, v___y_4954_);
                    v___x_4956_ = v_reuseFailAlloc_4957_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4956_;
            }
            7 => {
                v___x_4969_ = lean_string_utf8_byte_size(v___y_4968_);
                v___x_4970_ = lean_nat_dec_eq(v___x_4969_, v___x_4930_);
                if v___x_4970_ == 0 {
                    crate::leanh::lean_inc(v_buildTime_4966_);
                    crate::leanh::lean_inc_ref(v_trace_4965_);
                    crate::leanh::lean_inc_ref(v_log_4962_);
                    v_isSharedCheck_4985_ = (!crate::leanh::lean_is_exclusive(v_a_4960_)) as u8;
                    if v_isSharedCheck_4985_ == 0 {
                        v_unused_4986_ = crate::leanh::lean_ctor_get(v_a_4960_, 2);
                        crate::leanh::lean_dec(v_unused_4986_);
                        v_unused_4987_ = crate::leanh::lean_ctor_get(v_a_4960_, 1);
                        crate::leanh::lean_dec(v_unused_4987_);
                        v_unused_4988_ = crate::leanh::lean_ctor_get(v_a_4960_, 0);
                        crate::leanh::lean_dec(v_unused_4988_);
                        v___x_4972_ = v_a_4960_;
                        v_isShared_4973_ = v_isSharedCheck_4985_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_a_4960_);
                        v___x_4972_ = crate::leanh::lean_box(0);
                        v_isShared_4973_ = v_isSharedCheck_4985_;
                        state = 8;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_4968_);
                    v___y_4954_ = v_a_4960_;
                    state = 5;
                    continue;
                }
            }
            8 => {
                v___x_4974_ = l_Lake_Job_sync___redArg___closed__3;
                v___x_4975_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4975_, 0, v___y_4968_);
                crate::leanh::lean_ctor_set(v___x_4975_, 1, v___x_4930_);
                crate::leanh::lean_ctor_set(v___x_4975_, 2, v___x_4969_);
                v___x_4976_ = l_String_Slice_trimAscii(v___x_4975_);
                v___x_4977_ = l_String_Slice_toString(v___x_4976_);
                crate::leanh::lean_dec_ref(v___x_4976_);
                v___x_4978_ = lean_string_append(v___x_4974_, v___x_4977_);
                crate::leanh::lean_dec_ref(v___x_4977_);
                v___x_4979_ = 1;
                v___x_4980_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4980_, 0, v___x_4978_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4980_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_4979_,
                );
                v___x_4981_ = lean_array_push(v_log_4962_, v___x_4980_);
                if v_isShared_4973_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4972_, 0, v___x_4981_);
                    v___x_4983_ = v___x_4972_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4984_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4984_, 0, v___x_4981_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4984_, 1, v_trace_4965_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4984_, 2, v_buildTime_4966_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4984_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_action_4963_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4984_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_4964_,
                    );
                    v___x_4983_ = v_reuseFailAlloc_4984_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___y_4954_ = v___x_4983_;
                state = 5;
                continue;
            }
            10 => {
                if v_isShared_5006_ == 0 {
                    v___x_5008_ = v___x_5005_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5009_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5009_, 0, v_a_5002_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5009_, 1, v_a_5003_);
                    v___x_5008_ = v_reuseFailAlloc_5009_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_5008_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Job_mapM___redArg___lam__1___boxed(
    mut v_a_5011_: *mut crate::leanh::LeanObject,
    mut v_f_5012_: *mut crate::leanh::LeanObject,
    mut v_a_5013_: *mut crate::leanh::LeanObject,
    mut v_a_5014_: *mut crate::leanh::LeanObject,
    mut v_a_5015_: *mut crate::leanh::LeanObject,
    mut v_a_5016_: *mut crate::leanh::LeanObject,
    mut v_a_5017_: *mut crate::leanh::LeanObject,
    mut v_x_5018_: *mut crate::leanh::LeanObject,
    mut v___y_5019_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5020_ = l_Lake_Job_mapM___redArg___lam__1(
        v_a_5011_, v_f_5012_, v_a_5013_, v_a_5014_, v_a_5015_, v_a_5016_, v_a_5017_, v_x_5018_,
    );
    crate::leanh::lean_dec_ref(v_a_5017_);
    crate::leanh::lean_dec(v_a_5016_);
    crate::leanh::lean_dec(v_a_5015_);
    crate::leanh::lean_dec(v_a_5014_);
    crate::leanh::lean_dec_ref(v_a_5011_);
    return v_res_5020_;
}
pub unsafe fn l_Lake_Job_mapM___redArg(
    mut v_kind_5021_: *mut crate::leanh::LeanObject,
    mut v_self_5022_: *mut crate::leanh::LeanObject,
    mut v_f_5023_: *mut crate::leanh::LeanObject,
    mut v_prio_5024_: *mut crate::leanh::LeanObject,
    mut v_sync_5025_: u8,
    mut v_a_5026_: *mut crate::leanh::LeanObject,
    mut v_a_5027_: *mut crate::leanh::LeanObject,
    mut v_a_5028_: *mut crate::leanh::LeanObject,
    mut v_a_5029_: *mut crate::leanh::LeanObject,
    mut v_a_5030_: *mut crate::leanh::LeanObject,
    mut v_a_5031_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_task_5033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_caption_5034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_optional_5035_: u8 = 0;
    let mut v___x_5037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5038_: u8 = 0;
    let mut v___f_5039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5044_: u8 = 0;
    let mut v_unused_5045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_task_5033_ = crate::leanh::lean_ctor_get(v_self_5022_, 0);
                v_caption_5034_ = crate::leanh::lean_ctor_get(v_self_5022_, 2);
                v_optional_5035_ = crate::leanh::lean_ctor_get_uint8(
                    v_self_5022_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_isSharedCheck_5044_ = (!crate::leanh::lean_is_exclusive(v_self_5022_)) as u8;
                if v_isSharedCheck_5044_ == 0 {
                    v_unused_5045_ = crate::leanh::lean_ctor_get(v_self_5022_, 1);
                    crate::leanh::lean_dec(v_unused_5045_);
                    v___x_5037_ = v_self_5022_;
                    v_isShared_5038_ = v_isSharedCheck_5044_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_caption_5034_);
                    crate::leanh::lean_inc(v_task_5033_);
                    crate::leanh::lean_dec(v_self_5022_);
                    v___x_5037_ = crate::leanh::lean_box(0);
                    v_isShared_5038_ = v_isSharedCheck_5044_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_a_5030_);
                crate::leanh::lean_inc(v_a_5029_);
                crate::leanh::lean_inc(v_a_5028_);
                crate::leanh::lean_inc(v_a_5027_);
                crate::leanh::lean_inc_ref(v_a_5031_);
                v___f_5039_ = crate::leanh::lean_alloc_closure(
                    l_Lake_Job_mapM___redArg___lam__1___boxed as *mut core::ffi::c_void,
                    9,
                    7,
                );
                crate::leanh::lean_closure_set(v___f_5039_, 0, v_a_5031_);
                crate::leanh::lean_closure_set(v___f_5039_, 1, v_f_5023_);
                crate::leanh::lean_closure_set(v___f_5039_, 2, v_a_5026_);
                crate::leanh::lean_closure_set(v___f_5039_, 3, v_a_5027_);
                crate::leanh::lean_closure_set(v___f_5039_, 4, v_a_5028_);
                crate::leanh::lean_closure_set(v___f_5039_, 5, v_a_5029_);
                crate::leanh::lean_closure_set(v___f_5039_, 6, v_a_5030_);
                v___x_5040_ =
                    lean_io_map_task(v___f_5039_, v_task_5033_, v_prio_5024_, v_sync_5025_);
                if v_isShared_5038_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5037_, 1, v_kind_5021_);
                    crate::leanh::lean_ctor_set(v___x_5037_, 0, v___x_5040_);
                    v___x_5042_ = v___x_5037_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5043_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5043_, 0, v___x_5040_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5043_, 1, v_kind_5021_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5043_, 2, v_caption_5034_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5043_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_optional_5035_,
                    );
                    v___x_5042_ = v_reuseFailAlloc_5043_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5042_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Job_mapM___redArg___boxed(
    mut v_kind_5046_: *mut crate::leanh::LeanObject,
    mut v_self_5047_: *mut crate::leanh::LeanObject,
    mut v_f_5048_: *mut crate::leanh::LeanObject,
    mut v_prio_5049_: *mut crate::leanh::LeanObject,
    mut v_sync_5050_: *mut crate::leanh::LeanObject,
    mut v_a_5051_: *mut crate::leanh::LeanObject,
    mut v_a_5052_: *mut crate::leanh::LeanObject,
    mut v_a_5053_: *mut crate::leanh::LeanObject,
    mut v_a_5054_: *mut crate::leanh::LeanObject,
    mut v_a_5055_: *mut crate::leanh::LeanObject,
    mut v_a_5056_: *mut crate::leanh::LeanObject,
    mut v_a_5057_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sync_boxed_5058_: u8 = 0;
    let mut v_res_5059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sync_boxed_5058_ = (crate::leanh::lean_unbox(v_sync_5050_) as u8);
    v_res_5059_ = l_Lake_Job_mapM___redArg(
        v_kind_5046_,
        v_self_5047_,
        v_f_5048_,
        v_prio_5049_,
        v_sync_boxed_5058_,
        v_a_5051_,
        v_a_5052_,
        v_a_5053_,
        v_a_5054_,
        v_a_5055_,
        v_a_5056_,
    );
    crate::leanh::lean_dec_ref(v_a_5056_);
    crate::leanh::lean_dec_ref(v_a_5055_);
    crate::leanh::lean_dec(v_a_5054_);
    crate::leanh::lean_dec(v_a_5053_);
    crate::leanh::lean_dec(v_a_5052_);
    return v_res_5059_;
}
pub unsafe fn l_Lake_Job_mapM(
    mut v_00_u03b2_5060_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_5061_: *mut crate::leanh::LeanObject,
    mut v_kind_5062_: *mut crate::leanh::LeanObject,
    mut v_self_5063_: *mut crate::leanh::LeanObject,
    mut v_f_5064_: *mut crate::leanh::LeanObject,
    mut v_prio_5065_: *mut crate::leanh::LeanObject,
    mut v_sync_5066_: u8,
    mut v_a_5067_: *mut crate::leanh::LeanObject,
    mut v_a_5068_: *mut crate::leanh::LeanObject,
    mut v_a_5069_: *mut crate::leanh::LeanObject,
    mut v_a_5070_: *mut crate::leanh::LeanObject,
    mut v_a_5071_: *mut crate::leanh::LeanObject,
    mut v_a_5072_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5074_ = l_Lake_Job_mapM___redArg(
        v_kind_5062_,
        v_self_5063_,
        v_f_5064_,
        v_prio_5065_,
        v_sync_5066_,
        v_a_5067_,
        v_a_5068_,
        v_a_5069_,
        v_a_5070_,
        v_a_5071_,
        v_a_5072_,
    );
    return v___x_5074_;
}
pub unsafe fn l_Lake_Job_mapM___boxed(
    mut v_00_u03b2_5075_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_5076_: *mut crate::leanh::LeanObject,
    mut v_kind_5077_: *mut crate::leanh::LeanObject,
    mut v_self_5078_: *mut crate::leanh::LeanObject,
    mut v_f_5079_: *mut crate::leanh::LeanObject,
    mut v_prio_5080_: *mut crate::leanh::LeanObject,
    mut v_sync_5081_: *mut crate::leanh::LeanObject,
    mut v_a_5082_: *mut crate::leanh::LeanObject,
    mut v_a_5083_: *mut crate::leanh::LeanObject,
    mut v_a_5084_: *mut crate::leanh::LeanObject,
    mut v_a_5085_: *mut crate::leanh::LeanObject,
    mut v_a_5086_: *mut crate::leanh::LeanObject,
    mut v_a_5087_: *mut crate::leanh::LeanObject,
    mut v_a_5088_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sync_boxed_5089_: u8 = 0;
    let mut v_res_5090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sync_boxed_5089_ = (crate::leanh::lean_unbox(v_sync_5081_) as u8);
    v_res_5090_ = l_Lake_Job_mapM(
        v_00_u03b2_5075_,
        v_00_u03b1_5076_,
        v_kind_5077_,
        v_self_5078_,
        v_f_5079_,
        v_prio_5080_,
        v_sync_boxed_5089_,
        v_a_5082_,
        v_a_5083_,
        v_a_5084_,
        v_a_5085_,
        v_a_5086_,
        v_a_5087_,
    );
    crate::leanh::lean_dec_ref(v_a_5087_);
    crate::leanh::lean_dec_ref(v_a_5086_);
    crate::leanh::lean_dec(v_a_5085_);
    crate::leanh::lean_dec(v_a_5084_);
    crate::leanh::lean_dec(v_a_5083_);
    return v_res_5090_;
}
pub unsafe fn l_Lake_Job_bindM___redArg___lam__0(
    mut v_val_5091_: *mut crate::leanh::LeanObject,
    mut v_val_5092_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_5093_: *mut crate::leanh::LeanObject,
    mut v___y_5094_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5096_ = lean_get_set_stdout(v_val_5091_);
    crate::leanh::lean_dec_ref(v___x_5096_);
    v___x_5097_ = lean_get_set_stderr(v_val_5092_);
    crate::leanh::lean_dec_ref(v___x_5097_);
    v___x_5098_ = crate::leanh::lean_box(0);
    v___x_5099_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5099_, 0, v___x_5098_);
    crate::leanh::lean_ctor_set(v___x_5099_, 1, v___y_5094_);
    return v___x_5099_;
}
pub unsafe fn l_Lake_Job_bindM___redArg___lam__0___boxed(
    mut v_val_5100_: *mut crate::leanh::LeanObject,
    mut v_val_5101_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_5102_: *mut crate::leanh::LeanObject,
    mut v___y_5103_: *mut crate::leanh::LeanObject,
    mut v___y_5104_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5105_ =
        l_Lake_Job_bindM___redArg___lam__0(v_val_5100_, v_val_5101_, v_a_x3f_5102_, v___y_5103_);
    crate::leanh::lean_dec(v_a_x3f_5102_);
    return v_res_5105_;
}
pub unsafe fn l_Lake_Job_bindM___redArg___lam__1(
    mut v_a_5106_: *mut crate::leanh::LeanObject,
    mut v_x_5107_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_5108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5112_: u8 = 0;
    let mut v___x_5113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_log_5114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_action_5115_: u8 = 0;
    let mut v_wantsRebuild_5116_: u8 = 0;
    let mut v_buildTime_5117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trace_5118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5121_: u8 = 0;
    let mut v___x_5123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5128_: u8 = 0;
    let mut v_unused_5129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5131_: u8 = 0;
    let mut v_a_5132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5136_: u8 = 0;
    let mut v_log_5137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_log_5139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_action_5140_: u8 = 0;
    let mut v_wantsRebuild_5141_: u8 = 0;
    let mut v_buildTime_5142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trace_5143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5146_: u8 = 0;
    let mut v___x_5147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5155_: u8 = 0;
    let mut v_unused_5156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5158_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5107_) == 0 {
                    v_a_5108_ = crate::leanh::lean_ctor_get(v_x_5107_, 0);
                    v_a_5109_ = crate::leanh::lean_ctor_get(v_x_5107_, 1);
                    v_isSharedCheck_5131_ = (!crate::leanh::lean_is_exclusive(v_x_5107_)) as u8;
                    if v_isSharedCheck_5131_ == 0 {
                        v___x_5111_ = v_x_5107_;
                        v_isShared_5112_ = v_isSharedCheck_5131_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5109_);
                        crate::leanh::lean_inc(v_a_5108_);
                        crate::leanh::lean_dec(v_x_5107_);
                        v___x_5111_ = crate::leanh::lean_box(0);
                        v_isShared_5112_ = v_isSharedCheck_5131_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5132_ = crate::leanh::lean_ctor_get(v_x_5107_, 0);
                    v_a_5133_ = crate::leanh::lean_ctor_get(v_x_5107_, 1);
                    v_isSharedCheck_5158_ = (!crate::leanh::lean_is_exclusive(v_x_5107_)) as u8;
                    if v_isSharedCheck_5158_ == 0 {
                        v___x_5135_ = v_x_5107_;
                        v_isShared_5136_ = v_isSharedCheck_5158_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5133_);
                        crate::leanh::lean_inc(v_a_5132_);
                        crate::leanh::lean_dec(v_x_5107_);
                        v___x_5135_ = crate::leanh::lean_box(0);
                        v_isShared_5136_ = v_isSharedCheck_5158_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_a_5109_);
                v___x_5113_ = l_Lake_JobState_merge(v_a_5106_, v_a_5109_);
                v_log_5114_ = crate::leanh::lean_ctor_get(v___x_5113_, 0);
                crate::leanh::lean_inc_ref(v_log_5114_);
                v_action_5115_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_5113_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_wantsRebuild_5116_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_5113_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                );
                v_buildTime_5117_ = crate::leanh::lean_ctor_get(v___x_5113_, 2);
                crate::leanh::lean_inc(v_buildTime_5117_);
                crate::leanh::lean_dec_ref(v___x_5113_);
                v_trace_5118_ = crate::leanh::lean_ctor_get(v_a_5109_, 1);
                v_isSharedCheck_5128_ = (!crate::leanh::lean_is_exclusive(v_a_5109_)) as u8;
                if v_isSharedCheck_5128_ == 0 {
                    v_unused_5129_ = crate::leanh::lean_ctor_get(v_a_5109_, 2);
                    crate::leanh::lean_dec(v_unused_5129_);
                    v_unused_5130_ = crate::leanh::lean_ctor_get(v_a_5109_, 0);
                    crate::leanh::lean_dec(v_unused_5130_);
                    v___x_5120_ = v_a_5109_;
                    v_isShared_5121_ = v_isSharedCheck_5128_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_trace_5118_);
                    crate::leanh::lean_dec(v_a_5109_);
                    v___x_5120_ = crate::leanh::lean_box(0);
                    v_isShared_5121_ = v_isSharedCheck_5128_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_5121_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5120_, 2, v_buildTime_5117_);
                    crate::leanh::lean_ctor_set(v___x_5120_, 0, v_log_5114_);
                    v___x_5123_ = v___x_5120_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5127_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5127_, 0, v_log_5114_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5127_, 1, v_trace_5118_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5127_, 2, v_buildTime_5117_);
                    v___x_5123_ = v_reuseFailAlloc_5127_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5123_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v_action_5115_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5123_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                    v_wantsRebuild_5116_,
                );
                if v_isShared_5112_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5111_, 1, v___x_5123_);
                    v___x_5125_ = v___x_5111_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5126_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5126_, 0, v_a_5108_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5126_, 1, v___x_5123_);
                    v___x_5125_ = v_reuseFailAlloc_5126_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5125_;
            }
            5 => {
                v_log_5137_ = crate::leanh::lean_ctor_get(v_a_5106_, 0);
                crate::leanh::lean_inc_ref(v_log_5137_);
                crate::leanh::lean_inc(v_a_5133_);
                v___x_5138_ = l_Lake_JobState_merge(v_a_5106_, v_a_5133_);
                v_log_5139_ = crate::leanh::lean_ctor_get(v___x_5138_, 0);
                crate::leanh::lean_inc_ref(v_log_5139_);
                v_action_5140_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_5138_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_wantsRebuild_5141_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_5138_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                );
                v_buildTime_5142_ = crate::leanh::lean_ctor_get(v___x_5138_, 2);
                crate::leanh::lean_inc(v_buildTime_5142_);
                crate::leanh::lean_dec_ref(v___x_5138_);
                v_trace_5143_ = crate::leanh::lean_ctor_get(v_a_5133_, 1);
                v_isSharedCheck_5155_ = (!crate::leanh::lean_is_exclusive(v_a_5133_)) as u8;
                if v_isSharedCheck_5155_ == 0 {
                    v_unused_5156_ = crate::leanh::lean_ctor_get(v_a_5133_, 2);
                    crate::leanh::lean_dec(v_unused_5156_);
                    v_unused_5157_ = crate::leanh::lean_ctor_get(v_a_5133_, 0);
                    crate::leanh::lean_dec(v_unused_5157_);
                    v___x_5145_ = v_a_5133_;
                    v_isShared_5146_ = v_isSharedCheck_5155_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_trace_5143_);
                    crate::leanh::lean_dec(v_a_5133_);
                    v___x_5145_ = crate::leanh::lean_box(0);
                    v_isShared_5146_ = v_isSharedCheck_5155_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_5147_ = lean_array_get_size(v_log_5137_);
                crate::leanh::lean_dec_ref(v_log_5137_);
                v___x_5148_ = lean_nat_add(v___x_5147_, v_a_5132_);
                crate::leanh::lean_dec(v_a_5132_);
                if v_isShared_5146_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5145_, 2, v_buildTime_5142_);
                    crate::leanh::lean_ctor_set(v___x_5145_, 0, v_log_5139_);
                    v___x_5150_ = v___x_5145_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5154_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5154_, 0, v_log_5139_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5154_, 1, v_trace_5143_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5154_, 2, v_buildTime_5142_);
                    v___x_5150_ = v_reuseFailAlloc_5154_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5150_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v_action_5140_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5150_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                    v_wantsRebuild_5141_,
                );
                if v_isShared_5136_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5135_, 1, v___x_5150_);
                    crate::leanh::lean_ctor_set(v___x_5135_, 0, v___x_5148_);
                    v___x_5152_ = v___x_5135_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5153_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5153_, 0, v___x_5148_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5153_, 1, v___x_5150_);
                    v___x_5152_ = v_reuseFailAlloc_5153_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5152_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Job_bindM___redArg___lam__2(
    mut v_a_5159_: *mut crate::leanh::LeanObject,
    mut v_____r_5160_: *mut crate::leanh::LeanObject,
    mut v___y_5161_: *mut crate::leanh::LeanObject,
    mut v___y_5162_: *mut crate::leanh::LeanObject,
    mut v___y_5163_: *mut crate::leanh::LeanObject,
    mut v___y_5164_: *mut crate::leanh::LeanObject,
    mut v___y_5165_: *mut crate::leanh::LeanObject,
    mut v___y_5166_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5168_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5168_, 0, v_a_5159_);
    crate::leanh::lean_ctor_set(v___x_5168_, 1, v___y_5166_);
    return v___x_5168_;
}
pub unsafe fn l_Lake_Job_bindM___redArg___lam__2___boxed(
    mut v_a_5169_: *mut crate::leanh::LeanObject,
    mut v_____r_5170_: *mut crate::leanh::LeanObject,
    mut v___y_5171_: *mut crate::leanh::LeanObject,
    mut v___y_5172_: *mut crate::leanh::LeanObject,
    mut v___y_5173_: *mut crate::leanh::LeanObject,
    mut v___y_5174_: *mut crate::leanh::LeanObject,
    mut v___y_5175_: *mut crate::leanh::LeanObject,
    mut v___y_5176_: *mut crate::leanh::LeanObject,
    mut v___y_5177_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5178_ = l_Lake_Job_bindM___redArg___lam__2(
        v_a_5169_,
        v_____r_5170_,
        v___y_5171_,
        v___y_5172_,
        v___y_5173_,
        v___y_5174_,
        v___y_5175_,
        v___y_5176_,
    );
    crate::leanh::lean_dec_ref(v___y_5175_);
    crate::leanh::lean_dec(v___y_5174_);
    crate::leanh::lean_dec(v___y_5173_);
    crate::leanh::lean_dec(v___y_5172_);
    crate::leanh::lean_dec_ref(v___y_5171_);
    return v_res_5178_;
}
pub unsafe fn l_Lake_Job_bindM___redArg___lam__3(
    mut v_a_5179_: *mut crate::leanh::LeanObject,
    mut v_f_5180_: *mut crate::leanh::LeanObject,
    mut v_a_5181_: *mut crate::leanh::LeanObject,
    mut v_a_5182_: *mut crate::leanh::LeanObject,
    mut v_a_5183_: *mut crate::leanh::LeanObject,
    mut v_a_5184_: *mut crate::leanh::LeanObject,
    mut v_a_5185_: *mut crate::leanh::LeanObject,
    mut v_prio_5186_: *mut crate::leanh::LeanObject,
    mut v_x_5187_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_5190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_task_5198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5200_: u8 = 0;
    let mut v___x_5201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_log_5212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_action_5213_: u8 = 0;
    let mut v_wantsRebuild_5214_: u8 = 0;
    let mut v_trace_5215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildTime_5216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5219_: u8 = 0;
    let mut v_trace_5220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_log_5230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_action_5231_: u8 = 0;
    let mut v_wantsRebuild_5232_: u8 = 0;
    let mut v_trace_5233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildTime_5234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_5235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5239_: u8 = 0;
    let mut v___x_5241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5242_: u8 = 0;
    let mut v___x_5243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5248_: u8 = 0;
    let mut v___x_5249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5256_: u8 = 0;
    let mut v_unused_5257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5262_: u8 = 0;
    let mut v___x_5263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5272_: u8 = 0;
    let mut v_a_5273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5277_: u8 = 0;
    let mut v___x_5279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5282_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5187_) == 0 {
                    v_a_5204_ = crate::leanh::lean_ctor_get(v_x_5187_, 0);
                    crate::leanh::lean_inc(v_a_5204_);
                    v_a_5205_ = crate::leanh::lean_ctor_get(v_x_5187_, 1);
                    crate::leanh::lean_inc(v_a_5205_);
                    crate::leanh::lean_dec_ref_known(v_x_5187_, 2);
                    v___x_5206_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_5207_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_Job_sync___redArg___closed__0),
                        core::ptr::addr_of_mut!(l_Lake_Job_sync___redArg___closed__0_once),
                        _init_l_Lake_Job_sync___redArg___closed__0,
                    );
                    v___x_5208_ = lean_st_mk_ref(v___x_5207_);
                    crate::leanh::lean_inc(v___x_5208_);
                    v___x_5209_ = l_IO_FS_Stream_ofBuffer(v___x_5208_);
                    crate::leanh::lean_inc_ref(v___x_5209_);
                    v___x_5210_ = lean_get_set_stdout(v___x_5209_);
                    v___x_5211_ = lean_get_set_stderr(v___x_5209_);
                    v_log_5212_ = crate::leanh::lean_ctor_get(v_a_5205_, 0);
                    v_action_5213_ = crate::leanh::lean_ctor_get_uint8(
                        v_a_5205_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    );
                    v_wantsRebuild_5214_ = crate::leanh::lean_ctor_get_uint8(
                        v_a_5205_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                    );
                    v_trace_5215_ = crate::leanh::lean_ctor_get(v_a_5205_, 1);
                    v_buildTime_5216_ = crate::leanh::lean_ctor_get(v_a_5205_, 2);
                    v_isSharedCheck_5272_ = (!crate::leanh::lean_is_exclusive(v_a_5205_)) as u8;
                    if v_isSharedCheck_5272_ == 0 {
                        v___x_5218_ = v_a_5205_;
                        v_isShared_5219_ = v_isSharedCheck_5272_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_buildTime_5216_);
                        crate::leanh::lean_inc(v_trace_5215_);
                        crate::leanh::lean_inc(v_log_5212_);
                        crate::leanh::lean_dec(v_a_5205_);
                        v___x_5218_ = crate::leanh::lean_box(0);
                        v_isShared_5219_ = v_isSharedCheck_5272_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_prio_5186_);
                    crate::leanh::lean_dec_ref(v_a_5181_);
                    crate::leanh::lean_dec_ref(v_f_5180_);
                    v_a_5273_ = crate::leanh::lean_ctor_get(v_x_5187_, 0);
                    v_a_5274_ = crate::leanh::lean_ctor_get(v_x_5187_, 1);
                    v_isSharedCheck_5282_ = (!crate::leanh::lean_is_exclusive(v_x_5187_)) as u8;
                    if v_isSharedCheck_5282_ == 0 {
                        v___x_5276_ = v_x_5187_;
                        v_isShared_5277_ = v_isSharedCheck_5282_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5274_);
                        crate::leanh::lean_inc(v_a_5273_);
                        crate::leanh::lean_dec(v_x_5187_);
                        v___x_5276_ = crate::leanh::lean_box(0);
                        v_isShared_5277_ = v_isSharedCheck_5282_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5192_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5192_, 0, v_a_5190_);
                crate::leanh::lean_ctor_set(v___x_5192_, 1, v_a_5191_);
                v___x_5193_ = lean_task_pure(v___x_5192_);
                return v___x_5193_;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v___y_5195_) == 0 {
                    v_a_5196_ = crate::leanh::lean_ctor_get(v___y_5195_, 0);
                    crate::leanh::lean_inc(v_a_5196_);
                    v_a_5197_ = crate::leanh::lean_ctor_get(v___y_5195_, 1);
                    crate::leanh::lean_inc(v_a_5197_);
                    crate::leanh::lean_dec_ref_known(v___y_5195_, 2);
                    v_task_5198_ = crate::leanh::lean_ctor_get(v_a_5196_, 0);
                    crate::leanh::lean_inc_ref(v_task_5198_);
                    crate::leanh::lean_dec(v_a_5196_);
                    v___f_5199_ = crate::leanh::lean_alloc_closure(
                        l_Lake_Job_bindM___redArg___lam__1 as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_5199_, 0, v_a_5197_);
                    v___x_5200_ = 1;
                    v___x_5201_ =
                        lean_task_map(v___f_5199_, v_task_5198_, v_prio_5186_, v___x_5200_);
                    return v___x_5201_;
                } else {
                    crate::leanh::lean_dec(v_prio_5186_);
                    v_a_5202_ = crate::leanh::lean_ctor_get(v___y_5195_, 0);
                    crate::leanh::lean_inc(v_a_5202_);
                    v_a_5203_ = crate::leanh::lean_ctor_get(v___y_5195_, 1);
                    crate::leanh::lean_inc(v_a_5203_);
                    crate::leanh::lean_dec_ref_known(v___y_5195_, 2);
                    v_a_5190_ = v_a_5202_;
                    v_a_5191_ = v_a_5203_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_inc_ref(v_a_5179_);
                v_trace_5220_ = l_Lake_BuildTrace_mix(v_a_5179_, v_trace_5215_);
                if v_isShared_5219_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5218_, 1, v_trace_5220_);
                    v___x_5222_ = v___x_5218_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5271_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5271_, 0, v_log_5212_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5271_, 1, v_trace_5220_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5271_, 2, v_buildTime_5216_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5271_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_action_5213_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5271_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_5214_,
                    );
                    v___x_5222_ = v_reuseFailAlloc_5271_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                crate::leanh::lean_inc_ref(v_a_5185_);
                crate::leanh::lean_inc(v_a_5184_);
                crate::leanh::lean_inc(v_a_5183_);
                crate::leanh::lean_inc(v_a_5182_);
                crate::leanh::lean_inc_ref(v_a_5181_);
                v___x_5223_ = crate::leanh::lean_apply_8(
                    v_f_5180_,
                    v_a_5204_,
                    v_a_5181_,
                    v_a_5182_,
                    v_a_5183_,
                    v_a_5184_,
                    v_a_5185_,
                    v___x_5222_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_5223_) == 0 {
                    v_a_5224_ = crate::leanh::lean_ctor_get(v___x_5223_, 0);
                    crate::leanh::lean_inc_n(v_a_5224_, 2);
                    v_a_5225_ = crate::leanh::lean_ctor_get(v___x_5223_, 1);
                    crate::leanh::lean_inc(v_a_5225_);
                    crate::leanh::lean_dec_ref_known(v___x_5223_, 2);
                    v___x_5226_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5226_, 0, v_a_5224_);
                    v___x_5227_ = l_Lake_Job_bindM___redArg___lam__0(
                        v___x_5210_,
                        v___x_5211_,
                        v___x_5226_,
                        v_a_5225_,
                    );
                    crate::leanh::lean_dec_ref_known(v___x_5226_, 1);
                    v_a_5228_ = crate::leanh::lean_ctor_get(v___x_5227_, 1);
                    crate::leanh::lean_inc(v_a_5228_);
                    crate::leanh::lean_dec_ref(v___x_5227_);
                    v___x_5229_ = lean_st_ref_get(v___x_5208_);
                    crate::leanh::lean_dec(v___x_5208_);
                    v_log_5230_ = crate::leanh::lean_ctor_get(v_a_5228_, 0);
                    v_action_5231_ = crate::leanh::lean_ctor_get_uint8(
                        v_a_5228_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    );
                    v_wantsRebuild_5232_ = crate::leanh::lean_ctor_get_uint8(
                        v_a_5228_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                    );
                    v_trace_5233_ = crate::leanh::lean_ctor_get(v_a_5228_, 1);
                    v_buildTime_5234_ = crate::leanh::lean_ctor_get(v_a_5228_, 2);
                    v_data_5235_ = crate::leanh::lean_ctor_get(v___x_5229_, 0);
                    crate::leanh::lean_inc_ref(v_data_5235_);
                    crate::leanh::lean_dec(v___x_5229_);
                    v___x_5262_ = lean_string_validate_utf8(v_data_5235_);
                    if v___x_5262_ == 0 {
                        crate::leanh::lean_dec_ref(v_data_5235_);
                        v___x_5263_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_Job_sync___redArg___closed__7),
                            core::ptr::addr_of_mut!(l_Lake_Job_sync___redArg___closed__7_once),
                            _init_l_Lake_Job_sync___redArg___closed__7,
                        );
                        v___x_5264_ = l_panic___at___00Lake_Job_sync_spec__0(v___x_5263_);
                        v___y_5237_ = v___x_5264_;
                        state = 5;
                        continue;
                    } else {
                        v___x_5265_ = lean_string_from_utf8_unchecked(v_data_5235_);
                        v___y_5237_ = v___x_5265_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_5208_);
                    crate::leanh::lean_dec(v_prio_5186_);
                    crate::leanh::lean_dec_ref(v_a_5181_);
                    v_a_5266_ = crate::leanh::lean_ctor_get(v___x_5223_, 0);
                    crate::leanh::lean_inc(v_a_5266_);
                    v_a_5267_ = crate::leanh::lean_ctor_get(v___x_5223_, 1);
                    crate::leanh::lean_inc(v_a_5267_);
                    crate::leanh::lean_dec_ref_known(v___x_5223_, 2);
                    v___x_5268_ = crate::leanh::lean_box(0);
                    v___x_5269_ = l_Lake_Job_bindM___redArg___lam__0(
                        v___x_5210_,
                        v___x_5211_,
                        v___x_5268_,
                        v_a_5267_,
                    );
                    v_a_5270_ = crate::leanh::lean_ctor_get(v___x_5269_, 1);
                    crate::leanh::lean_inc(v_a_5270_);
                    crate::leanh::lean_dec_ref(v___x_5269_);
                    v_a_5190_ = v_a_5266_;
                    v_a_5191_ = v_a_5270_;
                    state = 1;
                    continue;
                }
            }
            5 => {
                v___x_5238_ = lean_string_utf8_byte_size(v___y_5237_);
                v___x_5239_ = lean_nat_dec_eq(v___x_5238_, v___x_5206_);
                if v___x_5239_ == 0 {
                    crate::leanh::lean_inc(v_buildTime_5234_);
                    crate::leanh::lean_inc_ref(v_trace_5233_);
                    crate::leanh::lean_inc_ref(v_log_5230_);
                    v_isSharedCheck_5256_ = (!crate::leanh::lean_is_exclusive(v_a_5228_)) as u8;
                    if v_isSharedCheck_5256_ == 0 {
                        v_unused_5257_ = crate::leanh::lean_ctor_get(v_a_5228_, 2);
                        crate::leanh::lean_dec(v_unused_5257_);
                        v_unused_5258_ = crate::leanh::lean_ctor_get(v_a_5228_, 1);
                        crate::leanh::lean_dec(v_unused_5258_);
                        v_unused_5259_ = crate::leanh::lean_ctor_get(v_a_5228_, 0);
                        crate::leanh::lean_dec(v_unused_5259_);
                        v___x_5241_ = v_a_5228_;
                        v_isShared_5242_ = v_isSharedCheck_5256_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_a_5228_);
                        v___x_5241_ = crate::leanh::lean_box(0);
                        v_isShared_5242_ = v_isSharedCheck_5256_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_5237_);
                    v___x_5260_ = crate::leanh::lean_box(0);
                    v___x_5261_ = l_Lake_Job_bindM___redArg___lam__2(
                        v_a_5224_,
                        v___x_5260_,
                        v_a_5181_,
                        v_a_5182_,
                        v_a_5183_,
                        v_a_5184_,
                        v_a_5185_,
                        v_a_5228_,
                    );
                    crate::leanh::lean_dec_ref(v_a_5181_);
                    v___y_5195_ = v___x_5261_;
                    state = 2;
                    continue;
                }
            }
            6 => {
                v___x_5243_ = l_Lake_Job_sync___redArg___closed__3;
                v___x_5244_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5244_, 0, v___y_5237_);
                crate::leanh::lean_ctor_set(v___x_5244_, 1, v___x_5206_);
                crate::leanh::lean_ctor_set(v___x_5244_, 2, v___x_5238_);
                v___x_5245_ = l_String_Slice_trimAscii(v___x_5244_);
                v___x_5246_ = l_String_Slice_toString(v___x_5245_);
                crate::leanh::lean_dec_ref(v___x_5245_);
                v___x_5247_ = lean_string_append(v___x_5243_, v___x_5246_);
                crate::leanh::lean_dec_ref(v___x_5246_);
                v___x_5248_ = 1;
                v___x_5249_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_5249_, 0, v___x_5247_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5249_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_5248_,
                );
                v___x_5250_ = crate::leanh::lean_box(0);
                v___x_5251_ = lean_array_push(v_log_5230_, v___x_5249_);
                if v_isShared_5242_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5241_, 0, v___x_5251_);
                    v___x_5253_ = v___x_5241_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5255_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5255_, 0, v___x_5251_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5255_, 1, v_trace_5233_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5255_, 2, v_buildTime_5234_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5255_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_action_5231_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5255_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_5232_,
                    );
                    v___x_5253_ = v_reuseFailAlloc_5255_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_5254_ = l_Lake_Job_bindM___redArg___lam__2(
                    v_a_5224_,
                    v___x_5250_,
                    v_a_5181_,
                    v_a_5182_,
                    v_a_5183_,
                    v_a_5184_,
                    v_a_5185_,
                    v___x_5253_,
                );
                crate::leanh::lean_dec_ref(v_a_5181_);
                v___y_5195_ = v___x_5254_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_5277_ == 0 {
                    v___x_5279_ = v___x_5276_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5281_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5281_, 0, v_a_5273_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5281_, 1, v_a_5274_);
                    v___x_5279_ = v_reuseFailAlloc_5281_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_5280_ = lean_task_pure(v___x_5279_);
                return v___x_5280_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Job_bindM___redArg___lam__3___boxed(
    mut v_a_5283_: *mut crate::leanh::LeanObject,
    mut v_f_5284_: *mut crate::leanh::LeanObject,
    mut v_a_5285_: *mut crate::leanh::LeanObject,
    mut v_a_5286_: *mut crate::leanh::LeanObject,
    mut v_a_5287_: *mut crate::leanh::LeanObject,
    mut v_a_5288_: *mut crate::leanh::LeanObject,
    mut v_a_5289_: *mut crate::leanh::LeanObject,
    mut v_prio_5290_: *mut crate::leanh::LeanObject,
    mut v_x_5291_: *mut crate::leanh::LeanObject,
    mut v___y_5292_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5293_ = l_Lake_Job_bindM___redArg___lam__3(
        v_a_5283_,
        v_f_5284_,
        v_a_5285_,
        v_a_5286_,
        v_a_5287_,
        v_a_5288_,
        v_a_5289_,
        v_prio_5290_,
        v_x_5291_,
    );
    crate::leanh::lean_dec_ref(v_a_5289_);
    crate::leanh::lean_dec(v_a_5288_);
    crate::leanh::lean_dec(v_a_5287_);
    crate::leanh::lean_dec(v_a_5286_);
    crate::leanh::lean_dec_ref(v_a_5283_);
    return v_res_5293_;
}
pub unsafe fn l_Lake_Job_bindM___redArg(
    mut v_kind_5294_: *mut crate::leanh::LeanObject,
    mut v_self_5295_: *mut crate::leanh::LeanObject,
    mut v_f_5296_: *mut crate::leanh::LeanObject,
    mut v_prio_5297_: *mut crate::leanh::LeanObject,
    mut v_sync_5298_: u8,
    mut v_a_5299_: *mut crate::leanh::LeanObject,
    mut v_a_5300_: *mut crate::leanh::LeanObject,
    mut v_a_5301_: *mut crate::leanh::LeanObject,
    mut v_a_5302_: *mut crate::leanh::LeanObject,
    mut v_a_5303_: *mut crate::leanh::LeanObject,
    mut v_a_5304_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_task_5306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_caption_5307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_optional_5308_: u8 = 0;
    let mut v___x_5310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5311_: u8 = 0;
    let mut v___f_5312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5317_: u8 = 0;
    let mut v_unused_5318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_task_5306_ = crate::leanh::lean_ctor_get(v_self_5295_, 0);
                v_caption_5307_ = crate::leanh::lean_ctor_get(v_self_5295_, 2);
                v_optional_5308_ = crate::leanh::lean_ctor_get_uint8(
                    v_self_5295_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_isSharedCheck_5317_ = (!crate::leanh::lean_is_exclusive(v_self_5295_)) as u8;
                if v_isSharedCheck_5317_ == 0 {
                    v_unused_5318_ = crate::leanh::lean_ctor_get(v_self_5295_, 1);
                    crate::leanh::lean_dec(v_unused_5318_);
                    v___x_5310_ = v_self_5295_;
                    v_isShared_5311_ = v_isSharedCheck_5317_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_caption_5307_);
                    crate::leanh::lean_inc(v_task_5306_);
                    crate::leanh::lean_dec(v_self_5295_);
                    v___x_5310_ = crate::leanh::lean_box(0);
                    v_isShared_5311_ = v_isSharedCheck_5317_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_prio_5297_);
                crate::leanh::lean_inc_ref(v_a_5303_);
                crate::leanh::lean_inc(v_a_5302_);
                crate::leanh::lean_inc(v_a_5301_);
                crate::leanh::lean_inc(v_a_5300_);
                crate::leanh::lean_inc_ref(v_a_5304_);
                v___f_5312_ = crate::leanh::lean_alloc_closure(
                    l_Lake_Job_bindM___redArg___lam__3___boxed as *mut core::ffi::c_void,
                    10,
                    8,
                );
                crate::leanh::lean_closure_set(v___f_5312_, 0, v_a_5304_);
                crate::leanh::lean_closure_set(v___f_5312_, 1, v_f_5296_);
                crate::leanh::lean_closure_set(v___f_5312_, 2, v_a_5299_);
                crate::leanh::lean_closure_set(v___f_5312_, 3, v_a_5300_);
                crate::leanh::lean_closure_set(v___f_5312_, 4, v_a_5301_);
                crate::leanh::lean_closure_set(v___f_5312_, 5, v_a_5302_);
                crate::leanh::lean_closure_set(v___f_5312_, 6, v_a_5303_);
                crate::leanh::lean_closure_set(v___f_5312_, 7, v_prio_5297_);
                v___x_5313_ =
                    lean_io_bind_task(v_task_5306_, v___f_5312_, v_prio_5297_, v_sync_5298_);
                if v_isShared_5311_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5310_, 1, v_kind_5294_);
                    crate::leanh::lean_ctor_set(v___x_5310_, 0, v___x_5313_);
                    v___x_5315_ = v___x_5310_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5316_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5316_, 0, v___x_5313_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5316_, 1, v_kind_5294_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5316_, 2, v_caption_5307_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5316_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_optional_5308_,
                    );
                    v___x_5315_ = v_reuseFailAlloc_5316_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5315_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Job_bindM___redArg___boxed(
    mut v_kind_5319_: *mut crate::leanh::LeanObject,
    mut v_self_5320_: *mut crate::leanh::LeanObject,
    mut v_f_5321_: *mut crate::leanh::LeanObject,
    mut v_prio_5322_: *mut crate::leanh::LeanObject,
    mut v_sync_5323_: *mut crate::leanh::LeanObject,
    mut v_a_5324_: *mut crate::leanh::LeanObject,
    mut v_a_5325_: *mut crate::leanh::LeanObject,
    mut v_a_5326_: *mut crate::leanh::LeanObject,
    mut v_a_5327_: *mut crate::leanh::LeanObject,
    mut v_a_5328_: *mut crate::leanh::LeanObject,
    mut v_a_5329_: *mut crate::leanh::LeanObject,
    mut v_a_5330_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sync_boxed_5331_: u8 = 0;
    let mut v_res_5332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sync_boxed_5331_ = (crate::leanh::lean_unbox(v_sync_5323_) as u8);
    v_res_5332_ = l_Lake_Job_bindM___redArg(
        v_kind_5319_,
        v_self_5320_,
        v_f_5321_,
        v_prio_5322_,
        v_sync_boxed_5331_,
        v_a_5324_,
        v_a_5325_,
        v_a_5326_,
        v_a_5327_,
        v_a_5328_,
        v_a_5329_,
    );
    crate::leanh::lean_dec_ref(v_a_5329_);
    crate::leanh::lean_dec_ref(v_a_5328_);
    crate::leanh::lean_dec(v_a_5327_);
    crate::leanh::lean_dec(v_a_5326_);
    crate::leanh::lean_dec(v_a_5325_);
    return v_res_5332_;
}
pub unsafe fn l_Lake_Job_bindM(
    mut v_00_u03b2_5333_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_5334_: *mut crate::leanh::LeanObject,
    mut v_kind_5335_: *mut crate::leanh::LeanObject,
    mut v_self_5336_: *mut crate::leanh::LeanObject,
    mut v_f_5337_: *mut crate::leanh::LeanObject,
    mut v_prio_5338_: *mut crate::leanh::LeanObject,
    mut v_sync_5339_: u8,
    mut v_a_5340_: *mut crate::leanh::LeanObject,
    mut v_a_5341_: *mut crate::leanh::LeanObject,
    mut v_a_5342_: *mut crate::leanh::LeanObject,
    mut v_a_5343_: *mut crate::leanh::LeanObject,
    mut v_a_5344_: *mut crate::leanh::LeanObject,
    mut v_a_5345_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5347_ = l_Lake_Job_bindM___redArg(
        v_kind_5335_,
        v_self_5336_,
        v_f_5337_,
        v_prio_5338_,
        v_sync_5339_,
        v_a_5340_,
        v_a_5341_,
        v_a_5342_,
        v_a_5343_,
        v_a_5344_,
        v_a_5345_,
    );
    return v___x_5347_;
}
pub unsafe fn l_Lake_Job_bindM___boxed(
    mut v_00_u03b2_5348_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_5349_: *mut crate::leanh::LeanObject,
    mut v_kind_5350_: *mut crate::leanh::LeanObject,
    mut v_self_5351_: *mut crate::leanh::LeanObject,
    mut v_f_5352_: *mut crate::leanh::LeanObject,
    mut v_prio_5353_: *mut crate::leanh::LeanObject,
    mut v_sync_5354_: *mut crate::leanh::LeanObject,
    mut v_a_5355_: *mut crate::leanh::LeanObject,
    mut v_a_5356_: *mut crate::leanh::LeanObject,
    mut v_a_5357_: *mut crate::leanh::LeanObject,
    mut v_a_5358_: *mut crate::leanh::LeanObject,
    mut v_a_5359_: *mut crate::leanh::LeanObject,
    mut v_a_5360_: *mut crate::leanh::LeanObject,
    mut v_a_5361_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sync_boxed_5362_: u8 = 0;
    let mut v_res_5363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sync_boxed_5362_ = (crate::leanh::lean_unbox(v_sync_5354_) as u8);
    v_res_5363_ = l_Lake_Job_bindM(
        v_00_u03b2_5348_,
        v_00_u03b1_5349_,
        v_kind_5350_,
        v_self_5351_,
        v_f_5352_,
        v_prio_5353_,
        v_sync_boxed_5362_,
        v_a_5355_,
        v_a_5356_,
        v_a_5357_,
        v_a_5358_,
        v_a_5359_,
        v_a_5360_,
    );
    crate::leanh::lean_dec_ref(v_a_5360_);
    crate::leanh::lean_dec_ref(v_a_5359_);
    crate::leanh::lean_dec(v_a_5358_);
    crate::leanh::lean_dec(v_a_5357_);
    crate::leanh::lean_dec(v_a_5356_);
    return v_res_5363_;
}
pub unsafe fn l_Lake_Job_zipResultWith___redArg___lam__0(
    mut v_f_5364_: *mut crate::leanh::LeanObject,
    mut v_rx_5365_: *mut crate::leanh::LeanObject,
    mut v_ry_5366_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5367_ = crate::leanh::lean_apply_2(v_f_5364_, v_rx_5365_, v_ry_5366_);
    return v___x_5367_;
}
pub unsafe fn l_Lake_Job_zipResultWith___redArg___lam__1(
    mut v_other_5368_: *mut crate::leanh::LeanObject,
    mut v_f_5369_: *mut crate::leanh::LeanObject,
    mut v_prio_5370_: *mut crate::leanh::LeanObject,
    mut v_sync_5371_: u8,
    mut v_rx_5372_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_task_5373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_task_5373_ = crate::leanh::lean_ctor_get(v_other_5368_, 0);
    crate::leanh::lean_inc_ref(v_task_5373_);
    crate::leanh::lean_dec_ref(v_other_5368_);
    v___f_5374_ = crate::leanh::lean_alloc_closure(
        l_Lake_Job_zipResultWith___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_5374_, 0, v_f_5369_);
    crate::leanh::lean_closure_set(v___f_5374_, 1, v_rx_5372_);
    v___x_5375_ = lean_task_map(v___f_5374_, v_task_5373_, v_prio_5370_, v_sync_5371_);
    return v___x_5375_;
}
pub unsafe fn l_Lake_Job_zipResultWith___redArg___lam__1___boxed(
    mut v_other_5376_: *mut crate::leanh::LeanObject,
    mut v_f_5377_: *mut crate::leanh::LeanObject,
    mut v_prio_5378_: *mut crate::leanh::LeanObject,
    mut v_sync_5379_: *mut crate::leanh::LeanObject,
    mut v_rx_5380_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sync_boxed_5381_: u8 = 0;
    let mut v_res_5382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sync_boxed_5381_ = (crate::leanh::lean_unbox(v_sync_5379_) as u8);
    v_res_5382_ = l_Lake_Job_zipResultWith___redArg___lam__1(
        v_other_5376_,
        v_f_5377_,
        v_prio_5378_,
        v_sync_boxed_5381_,
        v_rx_5380_,
    );
    return v_res_5382_;
}
pub unsafe fn l_Lake_Job_zipResultWith___redArg(
    mut v_inst_5383_: *mut crate::leanh::LeanObject,
    mut v_f_5384_: *mut crate::leanh::LeanObject,
    mut v_self_5385_: *mut crate::leanh::LeanObject,
    mut v_other_5386_: *mut crate::leanh::LeanObject,
    mut v_prio_5387_: *mut crate::leanh::LeanObject,
    mut v_sync_5388_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v_task_5389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5392_: u8 = 0;
    let mut v___x_5393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5395_: u8 = 0;
    let mut v___x_5396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5398_: u8 = 0;
    let mut v___x_5400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5402_: u8 = 0;
    let mut v_unused_5403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_task_5389_ = crate::leanh::lean_ctor_get(v_self_5385_, 0);
                v_isSharedCheck_5402_ = (!crate::leanh::lean_is_exclusive(v_self_5385_)) as u8;
                if v_isSharedCheck_5402_ == 0 {
                    v_unused_5403_ = crate::leanh::lean_ctor_get(v_self_5385_, 2);
                    crate::leanh::lean_dec(v_unused_5403_);
                    v_unused_5404_ = crate::leanh::lean_ctor_get(v_self_5385_, 1);
                    crate::leanh::lean_dec(v_unused_5404_);
                    v___x_5391_ = v_self_5385_;
                    v_isShared_5392_ = v_isSharedCheck_5402_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_task_5389_);
                    crate::leanh::lean_dec(v_self_5385_);
                    v___x_5391_ = crate::leanh::lean_box(0);
                    v_isShared_5392_ = v_isSharedCheck_5402_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5393_ = crate::leanh::lean_box((v_sync_5388_) as usize);
                crate::leanh::lean_inc(v_prio_5387_);
                v___f_5394_ = crate::leanh::lean_alloc_closure(
                    l_Lake_Job_zipResultWith___redArg___lam__1___boxed as *mut core::ffi::c_void,
                    5,
                    4,
                );
                crate::leanh::lean_closure_set(v___f_5394_, 0, v_other_5386_);
                crate::leanh::lean_closure_set(v___f_5394_, 1, v_f_5384_);
                crate::leanh::lean_closure_set(v___f_5394_, 2, v_prio_5387_);
                crate::leanh::lean_closure_set(v___f_5394_, 3, v___x_5393_);
                v___x_5395_ = 1;
                v___x_5396_ = lean_task_bind(v_task_5389_, v___f_5394_, v_prio_5387_, v___x_5395_);
                v___x_5397_ = l_panic___at___00Lake_Job_sync_spec__0___closed__0;
                v___x_5398_ = 0;
                if v_isShared_5392_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5391_, 2, v___x_5397_);
                    crate::leanh::lean_ctor_set(v___x_5391_, 1, v_inst_5383_);
                    crate::leanh::lean_ctor_set(v___x_5391_, 0, v___x_5396_);
                    v___x_5400_ = v___x_5391_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5401_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5401_, 0, v___x_5396_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5401_, 1, v_inst_5383_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5401_, 2, v___x_5397_);
                    v___x_5400_ = v_reuseFailAlloc_5401_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5400_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_5398_,
                );
                return v___x_5400_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Job_zipResultWith___redArg___boxed(
    mut v_inst_5405_: *mut crate::leanh::LeanObject,
    mut v_f_5406_: *mut crate::leanh::LeanObject,
    mut v_self_5407_: *mut crate::leanh::LeanObject,
    mut v_other_5408_: *mut crate::leanh::LeanObject,
    mut v_prio_5409_: *mut crate::leanh::LeanObject,
    mut v_sync_5410_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sync_boxed_5411_: u8 = 0;
    let mut v_res_5412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sync_boxed_5411_ = (crate::leanh::lean_unbox(v_sync_5410_) as u8);
    v_res_5412_ = l_Lake_Job_zipResultWith___redArg(
        v_inst_5405_,
        v_f_5406_,
        v_self_5407_,
        v_other_5408_,
        v_prio_5409_,
        v_sync_boxed_5411_,
    );
    return v_res_5412_;
}
pub unsafe fn l_Lake_Job_zipResultWith(
    mut v_00_u03b3_5413_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_5414_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5415_: *mut crate::leanh::LeanObject,
    mut v_inst_5416_: *mut crate::leanh::LeanObject,
    mut v_f_5417_: *mut crate::leanh::LeanObject,
    mut v_self_5418_: *mut crate::leanh::LeanObject,
    mut v_other_5419_: *mut crate::leanh::LeanObject,
    mut v_prio_5420_: *mut crate::leanh::LeanObject,
    mut v_sync_5421_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v_task_5422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5425_: u8 = 0;
    let mut v___x_5426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5428_: u8 = 0;
    let mut v___x_5429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5431_: u8 = 0;
    let mut v___x_5433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5435_: u8 = 0;
    let mut v_unused_5436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_task_5422_ = crate::leanh::lean_ctor_get(v_self_5418_, 0);
                v_isSharedCheck_5435_ = (!crate::leanh::lean_is_exclusive(v_self_5418_)) as u8;
                if v_isSharedCheck_5435_ == 0 {
                    v_unused_5436_ = crate::leanh::lean_ctor_get(v_self_5418_, 2);
                    crate::leanh::lean_dec(v_unused_5436_);
                    v_unused_5437_ = crate::leanh::lean_ctor_get(v_self_5418_, 1);
                    crate::leanh::lean_dec(v_unused_5437_);
                    v___x_5424_ = v_self_5418_;
                    v_isShared_5425_ = v_isSharedCheck_5435_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_task_5422_);
                    crate::leanh::lean_dec(v_self_5418_);
                    v___x_5424_ = crate::leanh::lean_box(0);
                    v_isShared_5425_ = v_isSharedCheck_5435_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5426_ = crate::leanh::lean_box((v_sync_5421_) as usize);
                crate::leanh::lean_inc(v_prio_5420_);
                v___f_5427_ = crate::leanh::lean_alloc_closure(
                    l_Lake_Job_zipResultWith___redArg___lam__1___boxed as *mut core::ffi::c_void,
                    5,
                    4,
                );
                crate::leanh::lean_closure_set(v___f_5427_, 0, v_other_5419_);
                crate::leanh::lean_closure_set(v___f_5427_, 1, v_f_5417_);
                crate::leanh::lean_closure_set(v___f_5427_, 2, v_prio_5420_);
                crate::leanh::lean_closure_set(v___f_5427_, 3, v___x_5426_);
                v___x_5428_ = 1;
                v___x_5429_ = lean_task_bind(v_task_5422_, v___f_5427_, v_prio_5420_, v___x_5428_);
                v___x_5430_ = l_panic___at___00Lake_Job_sync_spec__0___closed__0;
                v___x_5431_ = 0;
                if v_isShared_5425_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5424_, 2, v___x_5430_);
                    crate::leanh::lean_ctor_set(v___x_5424_, 1, v_inst_5416_);
                    crate::leanh::lean_ctor_set(v___x_5424_, 0, v___x_5429_);
                    v___x_5433_ = v___x_5424_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5434_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5434_, 0, v___x_5429_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5434_, 1, v_inst_5416_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5434_, 2, v___x_5430_);
                    v___x_5433_ = v_reuseFailAlloc_5434_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5433_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_5431_,
                );
                return v___x_5433_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Job_zipResultWith___boxed(
    mut v_00_u03b3_5438_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_5439_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5440_: *mut crate::leanh::LeanObject,
    mut v_inst_5441_: *mut crate::leanh::LeanObject,
    mut v_f_5442_: *mut crate::leanh::LeanObject,
    mut v_self_5443_: *mut crate::leanh::LeanObject,
    mut v_other_5444_: *mut crate::leanh::LeanObject,
    mut v_prio_5445_: *mut crate::leanh::LeanObject,
    mut v_sync_5446_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sync_boxed_5447_: u8 = 0;
    let mut v_res_5448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sync_boxed_5447_ = (crate::leanh::lean_unbox(v_sync_5446_) as u8);
    v_res_5448_ = l_Lake_Job_zipResultWith(
        v_00_u03b3_5438_,
        v_00_u03b1_5439_,
        v_00_u03b2_5440_,
        v_inst_5441_,
        v_f_5442_,
        v_self_5443_,
        v_other_5444_,
        v_prio_5445_,
        v_sync_boxed_5447_,
    );
    return v_res_5448_;
}
pub unsafe fn l_Lake_Job_zipWith___redArg___lam__0(
    mut v_rx_5449_: *mut crate::leanh::LeanObject,
    mut v_f_5450_: *mut crate::leanh::LeanObject,
    mut v_ry_5451_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_5453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5472_: u8 = 0;
    let mut v___x_5473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5478_: u8 = 0;
    let mut v_a_5479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_rx_5449_) == 0 {
                    if crate::leanh::lean_obj_tag(v_ry_5451_) == 0 {
                        v_a_5466_ = crate::leanh::lean_ctor_get(v_rx_5449_, 0);
                        crate::leanh::lean_inc(v_a_5466_);
                        v_a_5467_ = crate::leanh::lean_ctor_get(v_rx_5449_, 1);
                        crate::leanh::lean_inc(v_a_5467_);
                        crate::leanh::lean_dec_ref_known(v_rx_5449_, 2);
                        v_a_5468_ = crate::leanh::lean_ctor_get(v_ry_5451_, 0);
                        v_a_5469_ = crate::leanh::lean_ctor_get(v_ry_5451_, 1);
                        v_isSharedCheck_5478_ =
                            (!crate::leanh::lean_is_exclusive(v_ry_5451_)) as u8;
                        if v_isSharedCheck_5478_ == 0 {
                            v___x_5471_ = v_ry_5451_;
                            v_isShared_5472_ = v_isSharedCheck_5478_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5469_);
                            crate::leanh::lean_inc(v_a_5468_);
                            crate::leanh::lean_dec(v_ry_5451_);
                            v___x_5471_ = crate::leanh::lean_box(0);
                            v_isShared_5472_ = v_isSharedCheck_5478_;
                            state = 4;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_f_5450_);
                        v_a_5479_ = crate::leanh::lean_ctor_get(v_rx_5449_, 1);
                        crate::leanh::lean_inc(v_a_5479_);
                        crate::leanh::lean_dec_ref_known(v_rx_5449_, 2);
                        v_a_5464_ = v_a_5479_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_f_5450_);
                    if crate::leanh::lean_obj_tag(v_rx_5449_) == 0 {
                        v_a_5480_ = crate::leanh::lean_ctor_get(v_rx_5449_, 1);
                        crate::leanh::lean_inc(v_a_5480_);
                        crate::leanh::lean_dec_ref_known(v_rx_5449_, 2);
                        v_a_5464_ = v_a_5480_;
                        state = 3;
                        continue;
                    } else {
                        v_a_5481_ = crate::leanh::lean_ctor_get(v_rx_5449_, 1);
                        crate::leanh::lean_inc(v_a_5481_);
                        crate::leanh::lean_dec_ref_known(v_rx_5449_, 2);
                        v___x_5482_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___y_5459_ = v_ry_5451_;
                        v___y_5460_ = v___x_5482_;
                        v___y_5461_ = v_a_5481_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5456_ = l_Lake_JobState_merge(v___y_5454_, v___y_5455_);
                v___x_5457_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5457_, 0, v___y_5453_);
                crate::leanh::lean_ctor_set(v___x_5457_, 1, v___x_5456_);
                return v___x_5457_;
            }
            2 => {
                v_a_5462_ = crate::leanh::lean_ctor_get(v___y_5459_, 1);
                crate::leanh::lean_inc(v_a_5462_);
                crate::leanh::lean_dec_ref(v___y_5459_);
                v___y_5453_ = v___y_5460_;
                v___y_5454_ = v___y_5461_;
                v___y_5455_ = v_a_5462_;
                state = 1;
                continue;
            }
            3 => {
                v___x_5465_ = crate::leanh::lean_unsigned_to_nat(0);
                v___y_5459_ = v_ry_5451_;
                v___y_5460_ = v___x_5465_;
                v___y_5461_ = v_a_5464_;
                state = 2;
                continue;
            }
            4 => {
                v___x_5473_ = crate::leanh::lean_apply_2(v_f_5450_, v_a_5466_, v_a_5468_);
                v___x_5474_ = l_Lake_JobState_merge(v_a_5467_, v_a_5469_);
                if v_isShared_5472_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5471_, 1, v___x_5474_);
                    crate::leanh::lean_ctor_set(v___x_5471_, 0, v___x_5473_);
                    v___x_5476_ = v___x_5471_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5477_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5477_, 0, v___x_5473_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5477_, 1, v___x_5474_);
                    v___x_5476_ = v_reuseFailAlloc_5477_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5476_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Job_zipWith___redArg___lam__1(
    mut v_other_5483_: *mut crate::leanh::LeanObject,
    mut v_f_5484_: *mut crate::leanh::LeanObject,
    mut v_prio_5485_: *mut crate::leanh::LeanObject,
    mut v_sync_5486_: u8,
    mut v_rx_5487_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_task_5488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_task_5488_ = crate::leanh::lean_ctor_get(v_other_5483_, 0);
    crate::leanh::lean_inc_ref(v_task_5488_);
    crate::leanh::lean_dec_ref(v_other_5483_);
    v___f_5489_ = crate::leanh::lean_alloc_closure(
        l_Lake_Job_zipWith___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_5489_, 0, v_rx_5487_);
    crate::leanh::lean_closure_set(v___f_5489_, 1, v_f_5484_);
    v___x_5490_ = lean_task_map(v___f_5489_, v_task_5488_, v_prio_5485_, v_sync_5486_);
    return v___x_5490_;
}
pub unsafe fn l_Lake_Job_zipWith___redArg___lam__1___boxed(
    mut v_other_5491_: *mut crate::leanh::LeanObject,
    mut v_f_5492_: *mut crate::leanh::LeanObject,
    mut v_prio_5493_: *mut crate::leanh::LeanObject,
    mut v_sync_5494_: *mut crate::leanh::LeanObject,
    mut v_rx_5495_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sync_boxed_5496_: u8 = 0;
    let mut v_res_5497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sync_boxed_5496_ = (crate::leanh::lean_unbox(v_sync_5494_) as u8);
    v_res_5497_ = l_Lake_Job_zipWith___redArg___lam__1(
        v_other_5491_,
        v_f_5492_,
        v_prio_5493_,
        v_sync_boxed_5496_,
        v_rx_5495_,
    );
    return v_res_5497_;
}
pub unsafe fn l_Lake_Job_zipWith___redArg(
    mut v_inst_5498_: *mut crate::leanh::LeanObject,
    mut v_f_5499_: *mut crate::leanh::LeanObject,
    mut v_self_5500_: *mut crate::leanh::LeanObject,
    mut v_other_5501_: *mut crate::leanh::LeanObject,
    mut v_prio_5502_: *mut crate::leanh::LeanObject,
    mut v_sync_5503_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v_task_5504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5507_: u8 = 0;
    let mut v___x_5508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5510_: u8 = 0;
    let mut v___x_5511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5513_: u8 = 0;
    let mut v___x_5515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5517_: u8 = 0;
    let mut v_unused_5518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_task_5504_ = crate::leanh::lean_ctor_get(v_self_5500_, 0);
                v_isSharedCheck_5517_ = (!crate::leanh::lean_is_exclusive(v_self_5500_)) as u8;
                if v_isSharedCheck_5517_ == 0 {
                    v_unused_5518_ = crate::leanh::lean_ctor_get(v_self_5500_, 2);
                    crate::leanh::lean_dec(v_unused_5518_);
                    v_unused_5519_ = crate::leanh::lean_ctor_get(v_self_5500_, 1);
                    crate::leanh::lean_dec(v_unused_5519_);
                    v___x_5506_ = v_self_5500_;
                    v_isShared_5507_ = v_isSharedCheck_5517_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_task_5504_);
                    crate::leanh::lean_dec(v_self_5500_);
                    v___x_5506_ = crate::leanh::lean_box(0);
                    v_isShared_5507_ = v_isSharedCheck_5517_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5508_ = crate::leanh::lean_box((v_sync_5503_) as usize);
                crate::leanh::lean_inc(v_prio_5502_);
                v___f_5509_ = crate::leanh::lean_alloc_closure(
                    l_Lake_Job_zipWith___redArg___lam__1___boxed as *mut core::ffi::c_void,
                    5,
                    4,
                );
                crate::leanh::lean_closure_set(v___f_5509_, 0, v_other_5501_);
                crate::leanh::lean_closure_set(v___f_5509_, 1, v_f_5499_);
                crate::leanh::lean_closure_set(v___f_5509_, 2, v_prio_5502_);
                crate::leanh::lean_closure_set(v___f_5509_, 3, v___x_5508_);
                v___x_5510_ = 1;
                v___x_5511_ = lean_task_bind(v_task_5504_, v___f_5509_, v_prio_5502_, v___x_5510_);
                v___x_5512_ = l_panic___at___00Lake_Job_sync_spec__0___closed__0;
                v___x_5513_ = 0;
                if v_isShared_5507_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5506_, 2, v___x_5512_);
                    crate::leanh::lean_ctor_set(v___x_5506_, 1, v_inst_5498_);
                    crate::leanh::lean_ctor_set(v___x_5506_, 0, v___x_5511_);
                    v___x_5515_ = v___x_5506_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5516_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5516_, 0, v___x_5511_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5516_, 1, v_inst_5498_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5516_, 2, v___x_5512_);
                    v___x_5515_ = v_reuseFailAlloc_5516_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5515_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_5513_,
                );
                return v___x_5515_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Job_zipWith___redArg___boxed(
    mut v_inst_5520_: *mut crate::leanh::LeanObject,
    mut v_f_5521_: *mut crate::leanh::LeanObject,
    mut v_self_5522_: *mut crate::leanh::LeanObject,
    mut v_other_5523_: *mut crate::leanh::LeanObject,
    mut v_prio_5524_: *mut crate::leanh::LeanObject,
    mut v_sync_5525_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sync_boxed_5526_: u8 = 0;
    let mut v_res_5527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sync_boxed_5526_ = (crate::leanh::lean_unbox(v_sync_5525_) as u8);
    v_res_5527_ = l_Lake_Job_zipWith___redArg(
        v_inst_5520_,
        v_f_5521_,
        v_self_5522_,
        v_other_5523_,
        v_prio_5524_,
        v_sync_boxed_5526_,
    );
    return v_res_5527_;
}
pub unsafe fn l_Lake_Job_zipWith___lam__0(
    mut v_rx_5528_: *mut crate::leanh::LeanObject,
    mut v_f_5529_: *mut crate::leanh::LeanObject,
    mut v_ry_5530_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_5532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rb_5544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5552_: u8 = 0;
    let mut v___x_5553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5558_: u8 = 0;
    let mut v_a_5559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_rx_5528_) == 0 {
                    if crate::leanh::lean_obj_tag(v_ry_5530_) == 0 {
                        v_a_5546_ = crate::leanh::lean_ctor_get(v_rx_5528_, 0);
                        crate::leanh::lean_inc(v_a_5546_);
                        v_a_5547_ = crate::leanh::lean_ctor_get(v_rx_5528_, 1);
                        crate::leanh::lean_inc(v_a_5547_);
                        crate::leanh::lean_dec_ref_known(v_rx_5528_, 2);
                        v_a_5548_ = crate::leanh::lean_ctor_get(v_ry_5530_, 0);
                        v_a_5549_ = crate::leanh::lean_ctor_get(v_ry_5530_, 1);
                        v_isSharedCheck_5558_ =
                            (!crate::leanh::lean_is_exclusive(v_ry_5530_)) as u8;
                        if v_isSharedCheck_5558_ == 0 {
                            v___x_5551_ = v_ry_5530_;
                            v_isShared_5552_ = v_isSharedCheck_5558_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5549_);
                            crate::leanh::lean_inc(v_a_5548_);
                            crate::leanh::lean_dec(v_ry_5530_);
                            v___x_5551_ = crate::leanh::lean_box(0);
                            v_isShared_5552_ = v_isSharedCheck_5558_;
                            state = 4;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_f_5529_);
                        v_a_5559_ = crate::leanh::lean_ctor_get(v_rx_5528_, 1);
                        crate::leanh::lean_inc(v_a_5559_);
                        crate::leanh::lean_dec_ref_known(v_rx_5528_, 2);
                        v_a_5543_ = v_a_5559_;
                        v_rb_5544_ = v_ry_5530_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_f_5529_);
                    if crate::leanh::lean_obj_tag(v_rx_5528_) == 0 {
                        v_a_5560_ = crate::leanh::lean_ctor_get(v_rx_5528_, 1);
                        crate::leanh::lean_inc(v_a_5560_);
                        crate::leanh::lean_dec_ref_known(v_rx_5528_, 2);
                        v_a_5543_ = v_a_5560_;
                        v_rb_5544_ = v_ry_5530_;
                        state = 3;
                        continue;
                    } else {
                        v_a_5561_ = crate::leanh::lean_ctor_get(v_rx_5528_, 1);
                        crate::leanh::lean_inc(v_a_5561_);
                        crate::leanh::lean_dec_ref_known(v_rx_5528_, 2);
                        v___x_5562_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___y_5538_ = v_ry_5530_;
                        v___y_5539_ = v___x_5562_;
                        v___y_5540_ = v_a_5561_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5535_ = l_Lake_JobState_merge(v___y_5533_, v___y_5534_);
                v___x_5536_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5536_, 0, v___y_5532_);
                crate::leanh::lean_ctor_set(v___x_5536_, 1, v___x_5535_);
                return v___x_5536_;
            }
            2 => {
                v_a_5541_ = crate::leanh::lean_ctor_get(v___y_5538_, 1);
                crate::leanh::lean_inc(v_a_5541_);
                crate::leanh::lean_dec_ref(v___y_5538_);
                v___y_5532_ = v___y_5539_;
                v___y_5533_ = v___y_5540_;
                v___y_5534_ = v_a_5541_;
                state = 1;
                continue;
            }
            3 => {
                v___x_5545_ = crate::leanh::lean_unsigned_to_nat(0);
                v___y_5538_ = v_rb_5544_;
                v___y_5539_ = v___x_5545_;
                v___y_5540_ = v_a_5543_;
                state = 2;
                continue;
            }
            4 => {
                v___x_5553_ = crate::leanh::lean_apply_2(v_f_5529_, v_a_5546_, v_a_5548_);
                v___x_5554_ = l_Lake_JobState_merge(v_a_5547_, v_a_5549_);
                if v_isShared_5552_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5551_, 1, v___x_5554_);
                    crate::leanh::lean_ctor_set(v___x_5551_, 0, v___x_5553_);
                    v___x_5556_ = v___x_5551_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5557_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5557_, 0, v___x_5553_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5557_, 1, v___x_5554_);
                    v___x_5556_ = v_reuseFailAlloc_5557_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5556_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Job_zipWith___lam__1(
    mut v_other_5563_: *mut crate::leanh::LeanObject,
    mut v_f_5564_: *mut crate::leanh::LeanObject,
    mut v_prio_5565_: *mut crate::leanh::LeanObject,
    mut v_sync_5566_: u8,
    mut v_rx_5567_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_task_5568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_task_5568_ = crate::leanh::lean_ctor_get(v_other_5563_, 0);
    crate::leanh::lean_inc_ref(v_task_5568_);
    crate::leanh::lean_dec_ref(v_other_5563_);
    v___f_5569_ = crate::leanh::lean_alloc_closure(
        l_Lake_Job_zipWith___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_5569_, 0, v_rx_5567_);
    crate::leanh::lean_closure_set(v___f_5569_, 1, v_f_5564_);
    v___x_5570_ = lean_task_map(v___f_5569_, v_task_5568_, v_prio_5565_, v_sync_5566_);
    return v___x_5570_;
}
pub unsafe fn l_Lake_Job_zipWith___lam__1___boxed(
    mut v_other_5571_: *mut crate::leanh::LeanObject,
    mut v_f_5572_: *mut crate::leanh::LeanObject,
    mut v_prio_5573_: *mut crate::leanh::LeanObject,
    mut v_sync_5574_: *mut crate::leanh::LeanObject,
    mut v_rx_5575_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sync_boxed_5576_: u8 = 0;
    let mut v_res_5577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sync_boxed_5576_ = (crate::leanh::lean_unbox(v_sync_5574_) as u8);
    v_res_5577_ = l_Lake_Job_zipWith___lam__1(
        v_other_5571_,
        v_f_5572_,
        v_prio_5573_,
        v_sync_boxed_5576_,
        v_rx_5575_,
    );
    return v_res_5577_;
}
pub unsafe fn l_Lake_Job_zipWith(
    mut v_00_u03b3_5578_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_5579_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5580_: *mut crate::leanh::LeanObject,
    mut v_inst_5581_: *mut crate::leanh::LeanObject,
    mut v_f_5582_: *mut crate::leanh::LeanObject,
    mut v_self_5583_: *mut crate::leanh::LeanObject,
    mut v_other_5584_: *mut crate::leanh::LeanObject,
    mut v_prio_5585_: *mut crate::leanh::LeanObject,
    mut v_sync_5586_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v_task_5587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5590_: u8 = 0;
    let mut v___x_5591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5593_: u8 = 0;
    let mut v___x_5594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5596_: u8 = 0;
    let mut v___x_5598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5600_: u8 = 0;
    let mut v_unused_5601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_task_5587_ = crate::leanh::lean_ctor_get(v_self_5583_, 0);
                v_isSharedCheck_5600_ = (!crate::leanh::lean_is_exclusive(v_self_5583_)) as u8;
                if v_isSharedCheck_5600_ == 0 {
                    v_unused_5601_ = crate::leanh::lean_ctor_get(v_self_5583_, 2);
                    crate::leanh::lean_dec(v_unused_5601_);
                    v_unused_5602_ = crate::leanh::lean_ctor_get(v_self_5583_, 1);
                    crate::leanh::lean_dec(v_unused_5602_);
                    v___x_5589_ = v_self_5583_;
                    v_isShared_5590_ = v_isSharedCheck_5600_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_task_5587_);
                    crate::leanh::lean_dec(v_self_5583_);
                    v___x_5589_ = crate::leanh::lean_box(0);
                    v_isShared_5590_ = v_isSharedCheck_5600_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5591_ = crate::leanh::lean_box((v_sync_5586_) as usize);
                crate::leanh::lean_inc(v_prio_5585_);
                v___f_5592_ = crate::leanh::lean_alloc_closure(
                    l_Lake_Job_zipWith___lam__1___boxed as *mut core::ffi::c_void,
                    5,
                    4,
                );
                crate::leanh::lean_closure_set(v___f_5592_, 0, v_other_5584_);
                crate::leanh::lean_closure_set(v___f_5592_, 1, v_f_5582_);
                crate::leanh::lean_closure_set(v___f_5592_, 2, v_prio_5585_);
                crate::leanh::lean_closure_set(v___f_5592_, 3, v___x_5591_);
                v___x_5593_ = 1;
                v___x_5594_ = lean_task_bind(v_task_5587_, v___f_5592_, v_prio_5585_, v___x_5593_);
                v___x_5595_ = l_panic___at___00Lake_Job_sync_spec__0___closed__0;
                v___x_5596_ = 0;
                if v_isShared_5590_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5589_, 2, v___x_5595_);
                    crate::leanh::lean_ctor_set(v___x_5589_, 1, v_inst_5581_);
                    crate::leanh::lean_ctor_set(v___x_5589_, 0, v___x_5594_);
                    v___x_5598_ = v___x_5589_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5599_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5599_, 0, v___x_5594_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5599_, 1, v_inst_5581_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5599_, 2, v___x_5595_);
                    v___x_5598_ = v_reuseFailAlloc_5599_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5598_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_5596_,
                );
                return v___x_5598_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Job_zipWith___boxed(
    mut v_00_u03b3_5603_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_5604_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5605_: *mut crate::leanh::LeanObject,
    mut v_inst_5606_: *mut crate::leanh::LeanObject,
    mut v_f_5607_: *mut crate::leanh::LeanObject,
    mut v_self_5608_: *mut crate::leanh::LeanObject,
    mut v_other_5609_: *mut crate::leanh::LeanObject,
    mut v_prio_5610_: *mut crate::leanh::LeanObject,
    mut v_sync_5611_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sync_boxed_5612_: u8 = 0;
    let mut v_res_5613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sync_boxed_5612_ = (crate::leanh::lean_unbox(v_sync_5611_) as u8);
    v_res_5613_ = l_Lake_Job_zipWith(
        v_00_u03b3_5603_,
        v_00_u03b1_5604_,
        v_00_u03b2_5605_,
        v_inst_5606_,
        v_f_5607_,
        v_self_5608_,
        v_other_5609_,
        v_prio_5610_,
        v_sync_boxed_5612_,
    );
    return v_res_5613_;
}
pub unsafe fn l_Lake_Job_add___redArg___lam__0(
    mut v___x_5614_: *mut crate::leanh::LeanObject,
    mut v_rx_5615_: *mut crate::leanh::LeanObject,
    mut v_ry_5616_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_5618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_log_5621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_action_5622_: u8 = 0;
    let mut v_wantsRebuild_5623_: u8 = 0;
    let mut v_buildTime_5624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trace_5625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5628_: u8 = 0;
    let mut v___x_5630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5633_: u8 = 0;
    let mut v_unused_5634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5645_: u8 = 0;
    let mut v___x_5646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_log_5647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_action_5648_: u8 = 0;
    let mut v_wantsRebuild_5649_: u8 = 0;
    let mut v_buildTime_5650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trace_5651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5654_: u8 = 0;
    let mut v___x_5656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5661_: u8 = 0;
    let mut v_unused_5662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5664_: u8 = 0;
    let mut v_unused_5665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_rx_5615_) == 0 {
                    if crate::leanh::lean_obj_tag(v_ry_5616_) == 0 {
                        crate::leanh::lean_dec(v___x_5614_);
                        v_a_5640_ = crate::leanh::lean_ctor_get(v_rx_5615_, 0);
                        crate::leanh::lean_inc(v_a_5640_);
                        v_a_5641_ = crate::leanh::lean_ctor_get(v_rx_5615_, 1);
                        crate::leanh::lean_inc(v_a_5641_);
                        crate::leanh::lean_dec_ref_known(v_rx_5615_, 2);
                        v_a_5642_ = crate::leanh::lean_ctor_get(v_ry_5616_, 1);
                        v_isSharedCheck_5664_ =
                            (!crate::leanh::lean_is_exclusive(v_ry_5616_)) as u8;
                        if v_isSharedCheck_5664_ == 0 {
                            v_unused_5665_ = crate::leanh::lean_ctor_get(v_ry_5616_, 0);
                            crate::leanh::lean_dec(v_unused_5665_);
                            v___x_5644_ = v_ry_5616_;
                            v_isShared_5645_ = v_isSharedCheck_5664_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5642_);
                            crate::leanh::lean_dec(v_ry_5616_);
                            v___x_5644_ = crate::leanh::lean_box(0);
                            v_isShared_5645_ = v_isSharedCheck_5664_;
                            state = 5;
                            continue;
                        }
                    } else {
                        v_a_5666_ = crate::leanh::lean_ctor_get(v_rx_5615_, 1);
                        crate::leanh::lean_inc(v_a_5666_);
                        crate::leanh::lean_dec_ref_known(v_rx_5615_, 2);
                        v___y_5637_ = v_ry_5616_;
                        v___y_5638_ = v_a_5666_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_a_5667_ = crate::leanh::lean_ctor_get(v_rx_5615_, 1);
                    crate::leanh::lean_inc(v_a_5667_);
                    crate::leanh::lean_dec_ref(v_rx_5615_);
                    v___y_5637_ = v_ry_5616_;
                    v___y_5638_ = v_a_5667_;
                    state = 4;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v___y_5618_);
                v___x_5620_ = l_Lake_JobState_merge(v___y_5618_, v___y_5619_);
                v_log_5621_ = crate::leanh::lean_ctor_get(v___x_5620_, 0);
                crate::leanh::lean_inc_ref(v_log_5621_);
                v_action_5622_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_5620_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_wantsRebuild_5623_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_5620_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                );
                v_buildTime_5624_ = crate::leanh::lean_ctor_get(v___x_5620_, 2);
                crate::leanh::lean_inc(v_buildTime_5624_);
                crate::leanh::lean_dec_ref(v___x_5620_);
                v_trace_5625_ = crate::leanh::lean_ctor_get(v___y_5618_, 1);
                v_isSharedCheck_5633_ = (!crate::leanh::lean_is_exclusive(v___y_5618_)) as u8;
                if v_isSharedCheck_5633_ == 0 {
                    v_unused_5634_ = crate::leanh::lean_ctor_get(v___y_5618_, 2);
                    crate::leanh::lean_dec(v_unused_5634_);
                    v_unused_5635_ = crate::leanh::lean_ctor_get(v___y_5618_, 0);
                    crate::leanh::lean_dec(v_unused_5635_);
                    v___x_5627_ = v___y_5618_;
                    v_isShared_5628_ = v_isSharedCheck_5633_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_trace_5625_);
                    crate::leanh::lean_dec(v___y_5618_);
                    v___x_5627_ = crate::leanh::lean_box(0);
                    v_isShared_5628_ = v_isSharedCheck_5633_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_5628_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5627_, 2, v_buildTime_5624_);
                    crate::leanh::lean_ctor_set(v___x_5627_, 0, v_log_5621_);
                    v___x_5630_ = v___x_5627_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5632_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5632_, 0, v_log_5621_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5632_, 1, v_trace_5625_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5632_, 2, v_buildTime_5624_);
                    v___x_5630_ = v_reuseFailAlloc_5632_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5630_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v_action_5622_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5630_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                    v_wantsRebuild_5623_,
                );
                v___x_5631_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5631_, 0, v___x_5614_);
                crate::leanh::lean_ctor_set(v___x_5631_, 1, v___x_5630_);
                return v___x_5631_;
            }
            4 => {
                v_a_5639_ = crate::leanh::lean_ctor_get(v___y_5637_, 1);
                crate::leanh::lean_inc(v_a_5639_);
                crate::leanh::lean_dec_ref(v___y_5637_);
                v___y_5618_ = v___y_5638_;
                v___y_5619_ = v_a_5639_;
                state = 1;
                continue;
            }
            5 => {
                crate::leanh::lean_inc(v_a_5641_);
                v___x_5646_ = l_Lake_JobState_merge(v_a_5641_, v_a_5642_);
                v_log_5647_ = crate::leanh::lean_ctor_get(v___x_5646_, 0);
                crate::leanh::lean_inc_ref(v_log_5647_);
                v_action_5648_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_5646_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_wantsRebuild_5649_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_5646_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                );
                v_buildTime_5650_ = crate::leanh::lean_ctor_get(v___x_5646_, 2);
                crate::leanh::lean_inc(v_buildTime_5650_);
                crate::leanh::lean_dec_ref(v___x_5646_);
                v_trace_5651_ = crate::leanh::lean_ctor_get(v_a_5641_, 1);
                v_isSharedCheck_5661_ = (!crate::leanh::lean_is_exclusive(v_a_5641_)) as u8;
                if v_isSharedCheck_5661_ == 0 {
                    v_unused_5662_ = crate::leanh::lean_ctor_get(v_a_5641_, 2);
                    crate::leanh::lean_dec(v_unused_5662_);
                    v_unused_5663_ = crate::leanh::lean_ctor_get(v_a_5641_, 0);
                    crate::leanh::lean_dec(v_unused_5663_);
                    v___x_5653_ = v_a_5641_;
                    v_isShared_5654_ = v_isSharedCheck_5661_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_trace_5651_);
                    crate::leanh::lean_dec(v_a_5641_);
                    v___x_5653_ = crate::leanh::lean_box(0);
                    v_isShared_5654_ = v_isSharedCheck_5661_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_5654_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5653_, 2, v_buildTime_5650_);
                    crate::leanh::lean_ctor_set(v___x_5653_, 0, v_log_5647_);
                    v___x_5656_ = v___x_5653_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5660_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5660_, 0, v_log_5647_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5660_, 1, v_trace_5651_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5660_, 2, v_buildTime_5650_);
                    v___x_5656_ = v_reuseFailAlloc_5660_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5656_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v_action_5648_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5656_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                    v_wantsRebuild_5649_,
                );
                if v_isShared_5645_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5644_, 1, v___x_5656_);
                    crate::leanh::lean_ctor_set(v___x_5644_, 0, v_a_5640_);
                    v___x_5658_ = v___x_5644_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5659_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5659_, 0, v_a_5640_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5659_, 1, v___x_5656_);
                    v___x_5658_ = v_reuseFailAlloc_5659_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5658_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Job_add___redArg___lam__1(
    mut v_other_5668_: *mut crate::leanh::LeanObject,
    mut v___x_5669_: *mut crate::leanh::LeanObject,
    mut v___x_5670_: u8,
    mut v_rx_5671_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_task_5672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_task_5672_ = crate::leanh::lean_ctor_get(v_other_5668_, 0);
    crate::leanh::lean_inc_ref(v_task_5672_);
    crate::leanh::lean_dec_ref(v_other_5668_);
    crate::leanh::lean_inc(v___x_5669_);
    v___f_5673_ = crate::leanh::lean_alloc_closure(
        l_Lake_Job_add___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_5673_, 0, v___x_5669_);
    crate::leanh::lean_closure_set(v___f_5673_, 1, v_rx_5671_);
    v___x_5674_ = lean_task_map(v___f_5673_, v_task_5672_, v___x_5669_, v___x_5670_);
    return v___x_5674_;
}
pub unsafe fn l_Lake_Job_add___redArg___lam__1___boxed(
    mut v_other_5675_: *mut crate::leanh::LeanObject,
    mut v___x_5676_: *mut crate::leanh::LeanObject,
    mut v___x_5677_: *mut crate::leanh::LeanObject,
    mut v_rx_5678_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_262__boxed_5679_: u8 = 0;
    let mut v_res_5680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_262__boxed_5679_ = (crate::leanh::lean_unbox(v___x_5677_) as u8);
    v_res_5680_ = l_Lake_Job_add___redArg___lam__1(
        v_other_5675_,
        v___x_5676_,
        v___x_262__boxed_5679_,
        v_rx_5678_,
    );
    return v_res_5680_;
}
pub unsafe fn l_Lake_Job_add___redArg(
    mut v_self_5681_: *mut crate::leanh::LeanObject,
    mut v_other_5682_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_task_5683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_5684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5687_: u8 = 0;
    let mut v___x_5688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5689_: u8 = 0;
    let mut v___x_5690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5692_: u8 = 0;
    let mut v___x_5693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5698_: u8 = 0;
    let mut v_unused_5699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_task_5683_ = crate::leanh::lean_ctor_get(v_self_5681_, 0);
                v_kind_5684_ = crate::leanh::lean_ctor_get(v_self_5681_, 1);
                v_isSharedCheck_5698_ = (!crate::leanh::lean_is_exclusive(v_self_5681_)) as u8;
                if v_isSharedCheck_5698_ == 0 {
                    v_unused_5699_ = crate::leanh::lean_ctor_get(v_self_5681_, 2);
                    crate::leanh::lean_dec(v_unused_5699_);
                    v___x_5686_ = v_self_5681_;
                    v_isShared_5687_ = v_isSharedCheck_5698_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_kind_5684_);
                    crate::leanh::lean_inc(v_task_5683_);
                    crate::leanh::lean_dec(v_self_5681_);
                    v___x_5686_ = crate::leanh::lean_box(0);
                    v_isShared_5687_ = v_isSharedCheck_5698_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5688_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5689_ = 0;
                v___x_5690_ = crate::leanh::lean_box((v___x_5689_) as usize);
                v___f_5691_ = crate::leanh::lean_alloc_closure(
                    l_Lake_Job_add___redArg___lam__1___boxed as *mut core::ffi::c_void,
                    4,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_5691_, 0, v_other_5682_);
                crate::leanh::lean_closure_set(v___f_5691_, 1, v___x_5688_);
                crate::leanh::lean_closure_set(v___f_5691_, 2, v___x_5690_);
                v___x_5692_ = 1;
                v___x_5693_ = lean_task_bind(v_task_5683_, v___f_5691_, v___x_5688_, v___x_5692_);
                v___x_5694_ = l_panic___at___00Lake_Job_sync_spec__0___closed__0;
                if v_isShared_5687_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5686_, 2, v___x_5694_);
                    crate::leanh::lean_ctor_set(v___x_5686_, 0, v___x_5693_);
                    v___x_5696_ = v___x_5686_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5697_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5697_, 0, v___x_5693_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5697_, 1, v_kind_5684_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5697_, 2, v___x_5694_);
                    v___x_5696_ = v_reuseFailAlloc_5697_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5696_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_5689_,
                );
                return v___x_5696_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Job_add(
    mut v_00_u03b1_5700_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5701_: *mut crate::leanh::LeanObject,
    mut v_self_5702_: *mut crate::leanh::LeanObject,
    mut v_other_5703_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5704_ = l_Lake_Job_add___redArg(v_self_5702_, v_other_5703_);
    return v___x_5704_;
}
pub unsafe fn l_Lake_Job_mix___redArg___lam__0(
    mut v___x_5705_: *mut crate::leanh::LeanObject,
    mut v_rx_5706_: *mut crate::leanh::LeanObject,
    mut v_ry_5707_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_5709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5721_: u8 = 0;
    let mut v___x_5722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5727_: u8 = 0;
    let mut v_unused_5728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_rx_5706_) == 0 {
                    if crate::leanh::lean_obj_tag(v_ry_5707_) == 0 {
                        crate::leanh::lean_dec(v___x_5705_);
                        v_a_5717_ = crate::leanh::lean_ctor_get(v_rx_5706_, 1);
                        crate::leanh::lean_inc(v_a_5717_);
                        crate::leanh::lean_dec_ref_known(v_rx_5706_, 2);
                        v_a_5718_ = crate::leanh::lean_ctor_get(v_ry_5707_, 1);
                        v_isSharedCheck_5727_ =
                            (!crate::leanh::lean_is_exclusive(v_ry_5707_)) as u8;
                        if v_isSharedCheck_5727_ == 0 {
                            v_unused_5728_ = crate::leanh::lean_ctor_get(v_ry_5707_, 0);
                            crate::leanh::lean_dec(v_unused_5728_);
                            v___x_5720_ = v_ry_5707_;
                            v_isShared_5721_ = v_isSharedCheck_5727_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5718_);
                            crate::leanh::lean_dec(v_ry_5707_);
                            v___x_5720_ = crate::leanh::lean_box(0);
                            v_isShared_5721_ = v_isSharedCheck_5727_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_5729_ = crate::leanh::lean_ctor_get(v_rx_5706_, 1);
                        crate::leanh::lean_inc(v_a_5729_);
                        crate::leanh::lean_dec_ref_known(v_rx_5706_, 2);
                        v___y_5714_ = v_ry_5707_;
                        v___y_5715_ = v_a_5729_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_5730_ = crate::leanh::lean_ctor_get(v_rx_5706_, 1);
                    crate::leanh::lean_inc(v_a_5730_);
                    crate::leanh::lean_dec_ref(v_rx_5706_);
                    v___y_5714_ = v_ry_5707_;
                    v___y_5715_ = v_a_5730_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_5711_ = l_Lake_JobState_merge(v___y_5709_, v___y_5710_);
                v___x_5712_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5712_, 0, v___x_5705_);
                crate::leanh::lean_ctor_set(v___x_5712_, 1, v___x_5711_);
                return v___x_5712_;
            }
            2 => {
                v_a_5716_ = crate::leanh::lean_ctor_get(v___y_5714_, 1);
                crate::leanh::lean_inc(v_a_5716_);
                crate::leanh::lean_dec_ref(v___y_5714_);
                v___y_5709_ = v___y_5715_;
                v___y_5710_ = v_a_5716_;
                state = 1;
                continue;
            }
            3 => {
                v___x_5722_ = crate::leanh::lean_box(0);
                v___x_5723_ = l_Lake_JobState_merge(v_a_5717_, v_a_5718_);
                if v_isShared_5721_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5720_, 1, v___x_5723_);
                    crate::leanh::lean_ctor_set(v___x_5720_, 0, v___x_5722_);
                    v___x_5725_ = v___x_5720_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5726_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5726_, 0, v___x_5722_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5726_, 1, v___x_5723_);
                    v___x_5725_ = v_reuseFailAlloc_5726_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5725_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Job_mix___redArg___lam__1(
    mut v_other_5731_: *mut crate::leanh::LeanObject,
    mut v___x_5732_: *mut crate::leanh::LeanObject,
    mut v___x_5733_: u8,
    mut v_rx_5734_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_task_5735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_task_5735_ = crate::leanh::lean_ctor_get(v_other_5731_, 0);
    crate::leanh::lean_inc_ref(v_task_5735_);
    crate::leanh::lean_dec_ref(v_other_5731_);
    crate::leanh::lean_inc(v___x_5732_);
    v___f_5736_ = crate::leanh::lean_alloc_closure(
        l_Lake_Job_mix___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_5736_, 0, v___x_5732_);
    crate::leanh::lean_closure_set(v___f_5736_, 1, v_rx_5734_);
    v___x_5737_ = lean_task_map(v___f_5736_, v_task_5735_, v___x_5732_, v___x_5733_);
    return v___x_5737_;
}
pub unsafe fn l_Lake_Job_mix___redArg___lam__1___boxed(
    mut v_other_5738_: *mut crate::leanh::LeanObject,
    mut v___x_5739_: *mut crate::leanh::LeanObject,
    mut v___x_5740_: *mut crate::leanh::LeanObject,
    mut v_rx_5741_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_142__boxed_5742_: u8 = 0;
    let mut v_res_5743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_142__boxed_5742_ = (crate::leanh::lean_unbox(v___x_5740_) as u8);
    v_res_5743_ = l_Lake_Job_mix___redArg___lam__1(
        v_other_5738_,
        v___x_5739_,
        v___x_142__boxed_5742_,
        v_rx_5741_,
    );
    return v_res_5743_;
}
pub unsafe fn l_Lake_Job_mix___redArg(
    mut v_self_5744_: *mut crate::leanh::LeanObject,
    mut v_other_5745_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_task_5746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5749_: u8 = 0;
    let mut v___x_5750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5752_: u8 = 0;
    let mut v___x_5753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5757_: u8 = 0;
    let mut v___x_5759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5761_: u8 = 0;
    let mut v_unused_5762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_task_5746_ = crate::leanh::lean_ctor_get(v_self_5744_, 0);
                v_isSharedCheck_5761_ = (!crate::leanh::lean_is_exclusive(v_self_5744_)) as u8;
                if v_isSharedCheck_5761_ == 0 {
                    v_unused_5762_ = crate::leanh::lean_ctor_get(v_self_5744_, 2);
                    crate::leanh::lean_dec(v_unused_5762_);
                    v_unused_5763_ = crate::leanh::lean_ctor_get(v_self_5744_, 1);
                    crate::leanh::lean_dec(v_unused_5763_);
                    v___x_5748_ = v_self_5744_;
                    v_isShared_5749_ = v_isSharedCheck_5761_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_task_5746_);
                    crate::leanh::lean_dec(v_self_5744_);
                    v___x_5748_ = crate::leanh::lean_box(0);
                    v_isShared_5749_ = v_isSharedCheck_5761_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5750_ = l_Lake_instDataKindUnit;
                v___x_5751_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5752_ = 1;
                v___x_5753_ = crate::leanh::lean_box((v___x_5752_) as usize);
                v___f_5754_ = crate::leanh::lean_alloc_closure(
                    l_Lake_Job_mix___redArg___lam__1___boxed as *mut core::ffi::c_void,
                    4,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_5754_, 0, v_other_5745_);
                crate::leanh::lean_closure_set(v___f_5754_, 1, v___x_5751_);
                crate::leanh::lean_closure_set(v___f_5754_, 2, v___x_5753_);
                v___x_5755_ = lean_task_bind(v_task_5746_, v___f_5754_, v___x_5751_, v___x_5752_);
                v___x_5756_ = l_panic___at___00Lake_Job_sync_spec__0___closed__0;
                v___x_5757_ = 0;
                if v_isShared_5749_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5748_, 2, v___x_5756_);
                    crate::leanh::lean_ctor_set(v___x_5748_, 1, v___x_5750_);
                    crate::leanh::lean_ctor_set(v___x_5748_, 0, v___x_5755_);
                    v___x_5759_ = v___x_5748_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5760_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5760_, 0, v___x_5755_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5760_, 1, v___x_5750_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5760_, 2, v___x_5756_);
                    v___x_5759_ = v_reuseFailAlloc_5760_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5759_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_5757_,
                );
                return v___x_5759_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Job_mix(
    mut v_00_u03b1_5764_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5765_: *mut crate::leanh::LeanObject,
    mut v_self_5766_: *mut crate::leanh::LeanObject,
    mut v_other_5767_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5768_ = l_Lake_Job_mix___redArg(v_self_5766_, v_other_5767_);
    return v___x_5768_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_mixList_spec__0_spec__0___redArg(
    mut v_as_5769_: *mut crate::leanh::LeanObject,
    mut v_i_5770_: usize,
    mut v_stop_5771_: usize,
    mut v_b_5772_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5773_: u8 = 0;
    let mut v___x_5774_: usize = 0;
    let mut v___x_5775_: usize = 0;
    let mut v___x_5776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5773_ = lean_usize_dec_eq(v_i_5770_, v_stop_5771_);
                if v___x_5773_ == 0 {
                    v___x_5774_ = 1usize;
                    v___x_5775_ = lean_usize_sub(v_i_5770_, v___x_5774_);
                    v___x_5776_ = lean_array_uget_borrowed(v_as_5769_, v___x_5775_);
                    crate::leanh::lean_inc(v___x_5776_);
                    v___x_5777_ = l_Lake_Job_mix___redArg(v___x_5776_, v_b_5772_);
                    v_i_5770_ = v___x_5775_;
                    v_b_5772_ = v___x_5777_;
                    state = 0;
                    continue;
                } else {
                    return v_b_5772_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_mixList_spec__0_spec__0___redArg___boxed(
    mut v_as_5779_: *mut crate::leanh::LeanObject,
    mut v_i_5780_: *mut crate::leanh::LeanObject,
    mut v_stop_5781_: *mut crate::leanh::LeanObject,
    mut v_b_5782_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_5783_: usize = 0;
    let mut v_stop_boxed_5784_: usize = 0;
    let mut v_res_5785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5783_ = crate::leanh::lean_unbox_usize(v_i_5780_);
    crate::leanh::lean_dec(v_i_5780_);
    v_stop_boxed_5784_ = crate::leanh::lean_unbox_usize(v_stop_5781_);
    crate::leanh::lean_dec(v_stop_5781_);
    v_res_5785_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_mixList_spec__0_spec__0___redArg(v_as_5779_, v_i_boxed_5783_, v_stop_boxed_5784_, v_b_5782_);
    crate::leanh::lean_dec_ref(v_as_5779_);
    return v_res_5785_;
}
pub unsafe fn l_List_foldrTR___at___00Lake_Job_mixList_spec__0___redArg(
    mut v_init_5786_: *mut crate::leanh::LeanObject,
    mut v_l_5787_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5791_: u8 = 0;
    v___x_5788_ = lean_array_mk(v_l_5787_);
    v___x_5789_ = lean_array_get_size(v___x_5788_);
    v___x_5790_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5791_ = lean_nat_dec_lt(v___x_5790_, v___x_5789_);
    if v___x_5791_ == 0 {
        crate::leanh::lean_dec_ref(v___x_5788_);
        return v_init_5786_;
    } else {
        let mut v___x_5792_: usize = 0;
        let mut v___x_5793_: usize = 0;
        let mut v___x_5794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5792_ = lean_usize_of_nat(v___x_5789_);
        v___x_5793_ = 0usize;
        v___x_5794_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_mixList_spec__0_spec__0___redArg(v___x_5788_, v___x_5792_, v___x_5793_, v_init_5786_);
        crate::leanh::lean_dec_ref(v___x_5788_);
        return v___x_5794_;
    }
}
pub unsafe fn l_Lake_Job_mixList___redArg(
    mut v_jobs_5795_: *mut crate::leanh::LeanObject,
    mut v_traceCaption_5796_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5801_: u8 = 0;
    let mut v___x_5802_: u8 = 0;
    let mut v___x_5803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5797_ = crate::leanh::lean_box(0);
    v___x_5798_ = crate::leanh::lean_box(0);
    v___x_5799_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5800_ = l_Lake_Job_sync___redArg___closed__1;
    v___x_5801_ = 0;
    v___x_5802_ = 0;
    v___x_5803_ = l_Lake_BuildTrace_nil(v_traceCaption_5796_);
    v___x_5804_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_5804_, 0, v___x_5800_);
    crate::leanh::lean_ctor_set(v___x_5804_, 1, v___x_5803_);
    crate::leanh::lean_ctor_set(v___x_5804_, 2, v___x_5799_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_5804_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v___x_5801_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_5804_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
        v___x_5802_,
    );
    v___x_5805_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5805_, 0, v___x_5797_);
    crate::leanh::lean_ctor_set(v___x_5805_, 1, v___x_5804_);
    v___x_5806_ = lean_task_pure(v___x_5805_);
    v___x_5807_ = l_panic___at___00Lake_Job_sync_spec__0___closed__0;
    v___x_5808_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_5808_, 0, v___x_5806_);
    crate::leanh::lean_ctor_set(v___x_5808_, 1, v___x_5798_);
    crate::leanh::lean_ctor_set(v___x_5808_, 2, v___x_5807_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_5808_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v___x_5802_,
    );
    v___x_5809_ =
        l_List_foldrTR___at___00Lake_Job_mixList_spec__0___redArg(v___x_5808_, v_jobs_5795_);
    return v___x_5809_;
}
pub unsafe fn l_Lake_Job_mixList(
    mut v_00_u03b1_5810_: *mut crate::leanh::LeanObject,
    mut v_jobs_5811_: *mut crate::leanh::LeanObject,
    mut v_traceCaption_5812_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5813_ = l_Lake_Job_mixList___redArg(v_jobs_5811_, v_traceCaption_5812_);
    return v___x_5813_;
}
pub unsafe fn l_List_foldrTR___at___00Lake_Job_mixList_spec__0(
    mut v_00_u03b1_5814_: *mut crate::leanh::LeanObject,
    mut v_init_5815_: *mut crate::leanh::LeanObject,
    mut v_l_5816_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5817_ =
        l_List_foldrTR___at___00Lake_Job_mixList_spec__0___redArg(v_init_5815_, v_l_5816_);
    return v___x_5817_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_mixList_spec__0_spec__0(
    mut v_00_u03b1_5818_: *mut crate::leanh::LeanObject,
    mut v_as_5819_: *mut crate::leanh::LeanObject,
    mut v_i_5820_: usize,
    mut v_stop_5821_: usize,
    mut v_b_5822_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5823_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_mixList_spec__0_spec__0___redArg(v_as_5819_, v_i_5820_, v_stop_5821_, v_b_5822_);
    return v___x_5823_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_mixList_spec__0_spec__0___boxed(
    mut v_00_u03b1_5824_: *mut crate::leanh::LeanObject,
    mut v_as_5825_: *mut crate::leanh::LeanObject,
    mut v_i_5826_: *mut crate::leanh::LeanObject,
    mut v_stop_5827_: *mut crate::leanh::LeanObject,
    mut v_b_5828_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_5829_: usize = 0;
    let mut v_stop_boxed_5830_: usize = 0;
    let mut v_res_5831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5829_ = crate::leanh::lean_unbox_usize(v_i_5826_);
    crate::leanh::lean_dec(v_i_5826_);
    v_stop_boxed_5830_ = crate::leanh::lean_unbox_usize(v_stop_5827_);
    crate::leanh::lean_dec(v_stop_5827_);
    v_res_5831_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_mixList_spec__0_spec__0(v_00_u03b1_5824_, v_as_5825_, v_i_boxed_5829_, v_stop_boxed_5830_, v_b_5828_);
    crate::leanh::lean_dec_ref(v_as_5825_);
    return v_res_5831_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0___redArg(
    mut v_as_5832_: *mut crate::leanh::LeanObject,
    mut v_i_5833_: usize,
    mut v_stop_5834_: usize,
    mut v_b_5835_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5836_: u8 = 0;
    let mut v___x_5837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5839_: usize = 0;
    let mut v___x_5840_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5836_ = lean_usize_dec_eq(v_i_5833_, v_stop_5834_);
                if v___x_5836_ == 0 {
                    v___x_5837_ = lean_array_uget_borrowed(v_as_5832_, v_i_5833_);
                    crate::leanh::lean_inc(v___x_5837_);
                    v___x_5838_ = l_Lake_Job_mix___redArg(v_b_5835_, v___x_5837_);
                    v___x_5839_ = 1usize;
                    v___x_5840_ = lean_usize_add(v_i_5833_, v___x_5839_);
                    v_i_5833_ = v___x_5840_;
                    v_b_5835_ = v___x_5838_;
                    state = 0;
                    continue;
                } else {
                    return v_b_5835_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0___redArg___boxed(
    mut v_as_5842_: *mut crate::leanh::LeanObject,
    mut v_i_5843_: *mut crate::leanh::LeanObject,
    mut v_stop_5844_: *mut crate::leanh::LeanObject,
    mut v_b_5845_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_5846_: usize = 0;
    let mut v_stop_boxed_5847_: usize = 0;
    let mut v_res_5848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5846_ = crate::leanh::lean_unbox_usize(v_i_5843_);
    crate::leanh::lean_dec(v_i_5843_);
    v_stop_boxed_5847_ = crate::leanh::lean_unbox_usize(v_stop_5844_);
    crate::leanh::lean_dec(v_stop_5844_);
    v_res_5848_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0___redArg(v_as_5842_, v_i_boxed_5846_, v_stop_boxed_5847_, v_b_5845_);
    crate::leanh::lean_dec_ref(v_as_5842_);
    return v_res_5848_;
}
pub unsafe fn l_Lake_Job_mixArray___redArg(
    mut v_jobs_5849_: *mut crate::leanh::LeanObject,
    mut v_traceCaption_5850_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5855_: u8 = 0;
    let mut v___x_5856_: u8 = 0;
    let mut v___x_5857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5864_: u8 = 0;
    v___x_5851_ = crate::leanh::lean_box(0);
    v___x_5852_ = crate::leanh::lean_box(0);
    v___x_5853_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5854_ = l_Lake_Job_sync___redArg___closed__1;
    v___x_5855_ = 0;
    v___x_5856_ = 0;
    v___x_5857_ = l_Lake_BuildTrace_nil(v_traceCaption_5850_);
    v___x_5858_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_5858_, 0, v___x_5854_);
    crate::leanh::lean_ctor_set(v___x_5858_, 1, v___x_5857_);
    crate::leanh::lean_ctor_set(v___x_5858_, 2, v___x_5853_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_5858_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v___x_5855_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_5858_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
        v___x_5856_,
    );
    v___x_5859_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5859_, 0, v___x_5851_);
    crate::leanh::lean_ctor_set(v___x_5859_, 1, v___x_5858_);
    v___x_5860_ = lean_task_pure(v___x_5859_);
    v___x_5861_ = l_panic___at___00Lake_Job_sync_spec__0___closed__0;
    v___x_5862_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_5862_, 0, v___x_5860_);
    crate::leanh::lean_ctor_set(v___x_5862_, 1, v___x_5852_);
    crate::leanh::lean_ctor_set(v___x_5862_, 2, v___x_5861_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_5862_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v___x_5856_,
    );
    v___x_5863_ = lean_array_get_size(v_jobs_5849_);
    v___x_5864_ = lean_nat_dec_lt(v___x_5853_, v___x_5863_);
    if v___x_5864_ == 0 {
        return v___x_5862_;
    } else {
        let mut v___x_5865_: u8 = 0;
        v___x_5865_ = lean_nat_dec_le(v___x_5863_, v___x_5863_);
        if v___x_5865_ == 0 {
            if v___x_5864_ == 0 {
                return v___x_5862_;
            } else {
                let mut v___x_5866_: usize = 0;
                let mut v___x_5867_: usize = 0;
                let mut v___x_5868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_5866_ = 0usize;
                v___x_5867_ = lean_usize_of_nat(v___x_5863_);
                v___x_5868_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0___redArg(v_jobs_5849_, v___x_5866_, v___x_5867_, v___x_5862_);
                return v___x_5868_;
            }
        } else {
            let mut v___x_5869_: usize = 0;
            let mut v___x_5870_: usize = 0;
            let mut v___x_5871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_5869_ = 0usize;
            v___x_5870_ = lean_usize_of_nat(v___x_5863_);
            v___x_5871_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0___redArg(v_jobs_5849_, v___x_5869_, v___x_5870_, v___x_5862_);
            return v___x_5871_;
        }
    }
}
pub unsafe fn l_Lake_Job_mixArray___redArg___boxed(
    mut v_jobs_5872_: *mut crate::leanh::LeanObject,
    mut v_traceCaption_5873_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5874_ = l_Lake_Job_mixArray___redArg(v_jobs_5872_, v_traceCaption_5873_);
    crate::leanh::lean_dec_ref(v_jobs_5872_);
    return v_res_5874_;
}
pub unsafe fn l_Lake_Job_mixArray(
    mut v_00_u03b1_5875_: *mut crate::leanh::LeanObject,
    mut v_jobs_5876_: *mut crate::leanh::LeanObject,
    mut v_traceCaption_5877_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5878_ = l_Lake_Job_mixArray___redArg(v_jobs_5876_, v_traceCaption_5877_);
    return v___x_5878_;
}
pub unsafe fn l_Lake_Job_mixArray___boxed(
    mut v_00_u03b1_5879_: *mut crate::leanh::LeanObject,
    mut v_jobs_5880_: *mut crate::leanh::LeanObject,
    mut v_traceCaption_5881_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5882_ = l_Lake_Job_mixArray(v_00_u03b1_5879_, v_jobs_5880_, v_traceCaption_5881_);
    crate::leanh::lean_dec_ref(v_jobs_5880_);
    return v_res_5882_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0(
    mut v_00_u03b1_5883_: *mut crate::leanh::LeanObject,
    mut v_as_5884_: *mut crate::leanh::LeanObject,
    mut v_i_5885_: usize,
    mut v_stop_5886_: usize,
    mut v_b_5887_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5888_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0___redArg(v_as_5884_, v_i_5885_, v_stop_5886_, v_b_5887_);
    return v___x_5888_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0___boxed(
    mut v_00_u03b1_5889_: *mut crate::leanh::LeanObject,
    mut v_as_5890_: *mut crate::leanh::LeanObject,
    mut v_i_5891_: *mut crate::leanh::LeanObject,
    mut v_stop_5892_: *mut crate::leanh::LeanObject,
    mut v_b_5893_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_5894_: usize = 0;
    let mut v_stop_boxed_5895_: usize = 0;
    let mut v_res_5896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5894_ = crate::leanh::lean_unbox_usize(v_i_5891_);
    crate::leanh::lean_dec(v_i_5891_);
    v_stop_boxed_5895_ = crate::leanh::lean_unbox_usize(v_stop_5892_);
    crate::leanh::lean_dec(v_stop_5892_);
    v_res_5896_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0(v_00_u03b1_5889_, v_as_5890_, v_i_boxed_5894_, v_stop_boxed_5895_, v_b_5893_);
    crate::leanh::lean_dec_ref(v_as_5890_);
    return v_res_5896_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg___lam__0(
    mut v___x_5897_: *mut crate::leanh::LeanObject,
    mut v_rx_5898_: *mut crate::leanh::LeanObject,
    mut v_ry_5899_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_5901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5913_: u8 = 0;
    let mut v_a_5914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5918_: u8 = 0;
    let mut v___x_5920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5926_: u8 = 0;
    let mut v_isSharedCheck_5927_: u8 = 0;
    let mut v_a_5928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_rx_5898_) == 0 {
                    if crate::leanh::lean_obj_tag(v_ry_5899_) == 0 {
                        crate::leanh::lean_dec(v___x_5897_);
                        v_a_5909_ = crate::leanh::lean_ctor_get(v_rx_5898_, 0);
                        v_a_5910_ = crate::leanh::lean_ctor_get(v_rx_5898_, 1);
                        v_isSharedCheck_5927_ =
                            (!crate::leanh::lean_is_exclusive(v_rx_5898_)) as u8;
                        if v_isSharedCheck_5927_ == 0 {
                            v___x_5912_ = v_rx_5898_;
                            v_isShared_5913_ = v_isSharedCheck_5927_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5910_);
                            crate::leanh::lean_inc(v_a_5909_);
                            crate::leanh::lean_dec(v_rx_5898_);
                            v___x_5912_ = crate::leanh::lean_box(0);
                            v_isShared_5913_ = v_isSharedCheck_5927_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_5928_ = crate::leanh::lean_ctor_get(v_rx_5898_, 1);
                        crate::leanh::lean_inc(v_a_5928_);
                        crate::leanh::lean_dec_ref_known(v_rx_5898_, 2);
                        v___y_5906_ = v_ry_5899_;
                        v___y_5907_ = v_a_5928_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_5929_ = crate::leanh::lean_ctor_get(v_rx_5898_, 1);
                    crate::leanh::lean_inc(v_a_5929_);
                    crate::leanh::lean_dec_ref(v_rx_5898_);
                    v___y_5906_ = v_ry_5899_;
                    v___y_5907_ = v_a_5929_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_5903_ = l_Lake_JobState_merge(v___y_5901_, v___y_5902_);
                v___x_5904_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5904_, 0, v___x_5897_);
                crate::leanh::lean_ctor_set(v___x_5904_, 1, v___x_5903_);
                return v___x_5904_;
            }
            2 => {
                v_a_5908_ = crate::leanh::lean_ctor_get(v___y_5906_, 1);
                crate::leanh::lean_inc(v_a_5908_);
                crate::leanh::lean_dec_ref(v___y_5906_);
                v___y_5901_ = v___y_5907_;
                v___y_5902_ = v_a_5908_;
                state = 1;
                continue;
            }
            3 => {
                v_a_5914_ = crate::leanh::lean_ctor_get(v_ry_5899_, 0);
                v_a_5915_ = crate::leanh::lean_ctor_get(v_ry_5899_, 1);
                v_isSharedCheck_5926_ = (!crate::leanh::lean_is_exclusive(v_ry_5899_)) as u8;
                if v_isSharedCheck_5926_ == 0 {
                    v___x_5917_ = v_ry_5899_;
                    v_isShared_5918_ = v_isSharedCheck_5926_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_5915_);
                    crate::leanh::lean_inc(v_a_5914_);
                    crate::leanh::lean_dec(v_ry_5899_);
                    v___x_5917_ = crate::leanh::lean_box(0);
                    v_isShared_5918_ = v_isSharedCheck_5926_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_5913_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5912_, 1);
                    crate::leanh::lean_ctor_set(v___x_5912_, 1, v_a_5914_);
                    v___x_5920_ = v___x_5912_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5925_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5925_, 0, v_a_5909_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5925_, 1, v_a_5914_);
                    v___x_5920_ = v_reuseFailAlloc_5925_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5921_ = l_Lake_JobState_merge(v_a_5910_, v_a_5915_);
                if v_isShared_5918_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5917_, 1, v___x_5921_);
                    crate::leanh::lean_ctor_set(v___x_5917_, 0, v___x_5920_);
                    v___x_5923_ = v___x_5917_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5924_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5924_, 0, v___x_5920_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5924_, 1, v___x_5921_);
                    v___x_5923_ = v_reuseFailAlloc_5924_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5923_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg___lam__1(
    mut v_b_5930_: *mut crate::leanh::LeanObject,
    mut v___x_5931_: *mut crate::leanh::LeanObject,
    mut v___x_5932_: u8,
    mut v_rx_5933_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_task_5934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_task_5934_ = crate::leanh::lean_ctor_get(v_b_5930_, 0);
    crate::leanh::lean_inc_ref(v_task_5934_);
    crate::leanh::lean_dec_ref(v_b_5930_);
    crate::leanh::lean_inc(v___x_5931_);
    v___f_5935_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg___lam__0 as *mut core::ffi::c_void, 3, 2);
    crate::leanh::lean_closure_set(v___f_5935_, 0, v___x_5931_);
    crate::leanh::lean_closure_set(v___f_5935_, 1, v_rx_5933_);
    v___x_5936_ = lean_task_map(v___f_5935_, v_task_5934_, v___x_5931_, v___x_5932_);
    return v___x_5936_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg___lam__1___boxed(
    mut v_b_5937_: *mut crate::leanh::LeanObject,
    mut v___x_5938_: *mut crate::leanh::LeanObject,
    mut v___x_5939_: *mut crate::leanh::LeanObject,
    mut v_rx_5940_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_480__boxed_5941_: u8 = 0;
    let mut v_res_5942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_480__boxed_5941_ = (crate::leanh::lean_unbox(v___x_5939_) as u8);
    v_res_5942_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg___lam__1(v_b_5937_, v___x_5938_, v___x_480__boxed_5941_, v_rx_5940_);
    return v_res_5942_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg(
    mut v_as_5943_: *mut crate::leanh::LeanObject,
    mut v_i_5944_: usize,
    mut v_stop_5945_: usize,
    mut v_b_5946_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5947_: u8 = 0;
    let mut v___x_5948_: usize = 0;
    let mut v___x_5949_: usize = 0;
    let mut v___x_5950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_task_5951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5954_: u8 = 0;
    let mut v___x_5955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5957_: u8 = 0;
    let mut v___x_5958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5966_: u8 = 0;
    let mut v_unused_5967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5947_ = lean_usize_dec_eq(v_i_5944_, v_stop_5945_);
                if v___x_5947_ == 0 {
                    v___x_5948_ = 1usize;
                    v___x_5949_ = lean_usize_sub(v_i_5944_, v___x_5948_);
                    v___x_5950_ = lean_array_uget(v_as_5943_, v___x_5949_);
                    v_task_5951_ = crate::leanh::lean_ctor_get(v___x_5950_, 0);
                    v_isSharedCheck_5966_ = (!crate::leanh::lean_is_exclusive(v___x_5950_)) as u8;
                    if v_isSharedCheck_5966_ == 0 {
                        v_unused_5967_ = crate::leanh::lean_ctor_get(v___x_5950_, 2);
                        crate::leanh::lean_dec(v_unused_5967_);
                        v_unused_5968_ = crate::leanh::lean_ctor_get(v___x_5950_, 1);
                        crate::leanh::lean_dec(v_unused_5968_);
                        v___x_5953_ = v___x_5950_;
                        v_isShared_5954_ = v_isSharedCheck_5966_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_task_5951_);
                        crate::leanh::lean_dec(v___x_5950_);
                        v___x_5953_ = crate::leanh::lean_box(0);
                        v_isShared_5954_ = v_isSharedCheck_5966_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_5946_;
                }
            }
            1 => {
                v___x_5955_ = crate::leanh::lean_box(0);
                v___x_5956_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5957_ = 1;
                v___x_5958_ = crate::leanh::lean_box((v___x_5957_) as usize);
                v___f_5959_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg___lam__1___boxed as *mut core::ffi::c_void, 4, 3);
                crate::leanh::lean_closure_set(v___f_5959_, 0, v_b_5946_);
                crate::leanh::lean_closure_set(v___f_5959_, 1, v___x_5956_);
                crate::leanh::lean_closure_set(v___f_5959_, 2, v___x_5958_);
                v___x_5960_ = lean_task_bind(v_task_5951_, v___f_5959_, v___x_5956_, v___x_5957_);
                v___x_5961_ = l_panic___at___00Lake_Job_sync_spec__0___closed__0;
                if v_isShared_5954_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5953_, 2, v___x_5961_);
                    crate::leanh::lean_ctor_set(v___x_5953_, 1, v___x_5955_);
                    crate::leanh::lean_ctor_set(v___x_5953_, 0, v___x_5960_);
                    v___x_5963_ = v___x_5953_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5965_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5965_, 0, v___x_5960_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5965_, 1, v___x_5955_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5965_, 2, v___x_5961_);
                    v___x_5963_ = v_reuseFailAlloc_5965_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5963_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_5947_,
                );
                v_i_5944_ = v___x_5949_;
                v_b_5946_ = v___x_5963_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg___boxed(
    mut v_as_5969_: *mut crate::leanh::LeanObject,
    mut v_i_5970_: *mut crate::leanh::LeanObject,
    mut v_stop_5971_: *mut crate::leanh::LeanObject,
    mut v_b_5972_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_5973_: usize = 0;
    let mut v_stop_boxed_5974_: usize = 0;
    let mut v_res_5975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5973_ = crate::leanh::lean_unbox_usize(v_i_5970_);
    crate::leanh::lean_dec(v_i_5970_);
    v_stop_boxed_5974_ = crate::leanh::lean_unbox_usize(v_stop_5971_);
    crate::leanh::lean_dec(v_stop_5971_);
    v_res_5975_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg(v_as_5969_, v_i_boxed_5973_, v_stop_boxed_5974_, v_b_5972_);
    crate::leanh::lean_dec_ref(v_as_5969_);
    return v_res_5975_;
}
pub unsafe fn l_List_foldrTR___at___00Lake_Job_collectList_spec__0___redArg(
    mut v_init_5976_: *mut crate::leanh::LeanObject,
    mut v_l_5977_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5981_: u8 = 0;
    v___x_5978_ = lean_array_mk(v_l_5977_);
    v___x_5979_ = lean_array_get_size(v___x_5978_);
    v___x_5980_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5981_ = lean_nat_dec_lt(v___x_5980_, v___x_5979_);
    if v___x_5981_ == 0 {
        crate::leanh::lean_dec_ref(v___x_5978_);
        return v_init_5976_;
    } else {
        let mut v___x_5982_: usize = 0;
        let mut v___x_5983_: usize = 0;
        let mut v___x_5984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5982_ = lean_usize_of_nat(v___x_5979_);
        v___x_5983_ = 0usize;
        v___x_5984_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg(v___x_5978_, v___x_5982_, v___x_5983_, v_init_5976_);
        crate::leanh::lean_dec_ref(v___x_5978_);
        return v___x_5984_;
    }
}
pub unsafe fn l_Lake_Job_collectList___redArg(
    mut v_jobs_5985_: *mut crate::leanh::LeanObject,
    mut v_traceCaption_5986_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5991_: u8 = 0;
    let mut v___x_5992_: u8 = 0;
    let mut v___x_5993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5987_ = crate::leanh::lean_box(0);
    v___x_5988_ = crate::leanh::lean_box(0);
    v___x_5989_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5990_ = l_Lake_Job_sync___redArg___closed__1;
    v___x_5991_ = 0;
    v___x_5992_ = 0;
    v___x_5993_ = l_Lake_BuildTrace_nil(v_traceCaption_5986_);
    v___x_5994_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_5994_, 0, v___x_5990_);
    crate::leanh::lean_ctor_set(v___x_5994_, 1, v___x_5993_);
    crate::leanh::lean_ctor_set(v___x_5994_, 2, v___x_5989_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_5994_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v___x_5991_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_5994_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
        v___x_5992_,
    );
    v___x_5995_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5995_, 0, v___x_5987_);
    crate::leanh::lean_ctor_set(v___x_5995_, 1, v___x_5994_);
    v___x_5996_ = lean_task_pure(v___x_5995_);
    v___x_5997_ = l_panic___at___00Lake_Job_sync_spec__0___closed__0;
    v___x_5998_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_5998_, 0, v___x_5996_);
    crate::leanh::lean_ctor_set(v___x_5998_, 1, v___x_5988_);
    crate::leanh::lean_ctor_set(v___x_5998_, 2, v___x_5997_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_5998_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v___x_5992_,
    );
    v___x_5999_ =
        l_List_foldrTR___at___00Lake_Job_collectList_spec__0___redArg(v___x_5998_, v_jobs_5985_);
    return v___x_5999_;
}
pub unsafe fn l_Lake_Job_collectList(
    mut v_00_u03b1_6000_: *mut crate::leanh::LeanObject,
    mut v_jobs_6001_: *mut crate::leanh::LeanObject,
    mut v_traceCaption_6002_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6003_ = l_Lake_Job_collectList___redArg(v_jobs_6001_, v_traceCaption_6002_);
    return v___x_6003_;
}
pub unsafe fn l_List_foldrTR___at___00Lake_Job_collectList_spec__0(
    mut v_00_u03b1_6004_: *mut crate::leanh::LeanObject,
    mut v_init_6005_: *mut crate::leanh::LeanObject,
    mut v_l_6006_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6007_ =
        l_List_foldrTR___at___00Lake_Job_collectList_spec__0___redArg(v_init_6005_, v_l_6006_);
    return v___x_6007_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0(
    mut v_00_u03b1_6008_: *mut crate::leanh::LeanObject,
    mut v_as_6009_: *mut crate::leanh::LeanObject,
    mut v_i_6010_: usize,
    mut v_stop_6011_: usize,
    mut v_b_6012_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6013_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg(v_as_6009_, v_i_6010_, v_stop_6011_, v_b_6012_);
    return v___x_6013_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___boxed(
    mut v_00_u03b1_6014_: *mut crate::leanh::LeanObject,
    mut v_as_6015_: *mut crate::leanh::LeanObject,
    mut v_i_6016_: *mut crate::leanh::LeanObject,
    mut v_stop_6017_: *mut crate::leanh::LeanObject,
    mut v_b_6018_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_6019_: usize = 0;
    let mut v_stop_boxed_6020_: usize = 0;
    let mut v_res_6021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_6019_ = crate::leanh::lean_unbox_usize(v_i_6016_);
    crate::leanh::lean_dec(v_i_6016_);
    v_stop_boxed_6020_ = crate::leanh::lean_unbox_usize(v_stop_6017_);
    crate::leanh::lean_dec(v_stop_6017_);
    v_res_6021_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0(v_00_u03b1_6014_, v_as_6015_, v_i_boxed_6019_, v_stop_boxed_6020_, v_b_6018_);
    crate::leanh::lean_dec_ref(v_as_6015_);
    return v_res_6021_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg___lam__0(
    mut v___x_6022_: *mut crate::leanh::LeanObject,
    mut v_rx_6023_: *mut crate::leanh::LeanObject,
    mut v_ry_6024_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_6026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6040_: u8 = 0;
    let mut v___x_6041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6046_: u8 = 0;
    let mut v_a_6047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_rx_6023_) == 0 {
                    if crate::leanh::lean_obj_tag(v_ry_6024_) == 0 {
                        crate::leanh::lean_dec(v___x_6022_);
                        v_a_6034_ = crate::leanh::lean_ctor_get(v_rx_6023_, 0);
                        crate::leanh::lean_inc(v_a_6034_);
                        v_a_6035_ = crate::leanh::lean_ctor_get(v_rx_6023_, 1);
                        crate::leanh::lean_inc(v_a_6035_);
                        crate::leanh::lean_dec_ref_known(v_rx_6023_, 2);
                        v_a_6036_ = crate::leanh::lean_ctor_get(v_ry_6024_, 0);
                        v_a_6037_ = crate::leanh::lean_ctor_get(v_ry_6024_, 1);
                        v_isSharedCheck_6046_ =
                            (!crate::leanh::lean_is_exclusive(v_ry_6024_)) as u8;
                        if v_isSharedCheck_6046_ == 0 {
                            v___x_6039_ = v_ry_6024_;
                            v_isShared_6040_ = v_isSharedCheck_6046_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6037_);
                            crate::leanh::lean_inc(v_a_6036_);
                            crate::leanh::lean_dec(v_ry_6024_);
                            v___x_6039_ = crate::leanh::lean_box(0);
                            v_isShared_6040_ = v_isSharedCheck_6046_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_6047_ = crate::leanh::lean_ctor_get(v_rx_6023_, 1);
                        crate::leanh::lean_inc(v_a_6047_);
                        crate::leanh::lean_dec_ref_known(v_rx_6023_, 2);
                        v___y_6031_ = v_ry_6024_;
                        v___y_6032_ = v_a_6047_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_6048_ = crate::leanh::lean_ctor_get(v_rx_6023_, 1);
                    crate::leanh::lean_inc(v_a_6048_);
                    crate::leanh::lean_dec_ref(v_rx_6023_);
                    v___y_6031_ = v_ry_6024_;
                    v___y_6032_ = v_a_6048_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_6028_ = l_Lake_JobState_merge(v___y_6026_, v___y_6027_);
                v___x_6029_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6029_, 0, v___x_6022_);
                crate::leanh::lean_ctor_set(v___x_6029_, 1, v___x_6028_);
                return v___x_6029_;
            }
            2 => {
                v_a_6033_ = crate::leanh::lean_ctor_get(v___y_6031_, 1);
                crate::leanh::lean_inc(v_a_6033_);
                crate::leanh::lean_dec_ref(v___y_6031_);
                v___y_6026_ = v___y_6032_;
                v___y_6027_ = v_a_6033_;
                state = 1;
                continue;
            }
            3 => {
                v___x_6041_ = lean_array_push(v_a_6034_, v_a_6036_);
                v___x_6042_ = l_Lake_JobState_merge(v_a_6035_, v_a_6037_);
                if v_isShared_6040_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6039_, 1, v___x_6042_);
                    crate::leanh::lean_ctor_set(v___x_6039_, 0, v___x_6041_);
                    v___x_6044_ = v___x_6039_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6045_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6045_, 0, v___x_6041_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6045_, 1, v___x_6042_);
                    v___x_6044_ = v_reuseFailAlloc_6045_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6044_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg___lam__1(
    mut v___x_6049_: *mut crate::leanh::LeanObject,
    mut v___x_6050_: *mut crate::leanh::LeanObject,
    mut v___x_6051_: u8,
    mut v_rx_6052_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_task_6053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_task_6053_ = crate::leanh::lean_ctor_get(v___x_6049_, 0);
    crate::leanh::lean_inc_ref(v_task_6053_);
    crate::leanh::lean_dec_ref(v___x_6049_);
    crate::leanh::lean_inc(v___x_6050_);
    v___f_6054_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg___lam__0 as *mut core::ffi::c_void, 3, 2);
    crate::leanh::lean_closure_set(v___f_6054_, 0, v___x_6050_);
    crate::leanh::lean_closure_set(v___f_6054_, 1, v_rx_6052_);
    v___x_6055_ = lean_task_map(v___f_6054_, v_task_6053_, v___x_6050_, v___x_6051_);
    return v___x_6055_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg___lam__1___boxed(
    mut v___x_6056_: *mut crate::leanh::LeanObject,
    mut v___x_6057_: *mut crate::leanh::LeanObject,
    mut v___x_6058_: *mut crate::leanh::LeanObject,
    mut v_rx_6059_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_411__boxed_6060_: u8 = 0;
    let mut v_res_6061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_411__boxed_6060_ = (crate::leanh::lean_unbox(v___x_6058_) as u8);
    v_res_6061_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg___lam__1(v___x_6056_, v___x_6057_, v___x_411__boxed_6060_, v_rx_6059_);
    return v_res_6061_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg(
    mut v_as_6062_: *mut crate::leanh::LeanObject,
    mut v_i_6063_: usize,
    mut v_stop_6064_: usize,
    mut v_b_6065_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6066_: u8 = 0;
    let mut v_task_6067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6070_: u8 = 0;
    let mut v___x_6071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6074_: u8 = 0;
    let mut v___x_6075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6081_: usize = 0;
    let mut v___x_6082_: usize = 0;
    let mut v_reuseFailAlloc_6084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6085_: u8 = 0;
    let mut v_unused_6086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6066_ = lean_usize_dec_eq(v_i_6063_, v_stop_6064_);
                if v___x_6066_ == 0 {
                    v_task_6067_ = crate::leanh::lean_ctor_get(v_b_6065_, 0);
                    v_isSharedCheck_6085_ = (!crate::leanh::lean_is_exclusive(v_b_6065_)) as u8;
                    if v_isSharedCheck_6085_ == 0 {
                        v_unused_6086_ = crate::leanh::lean_ctor_get(v_b_6065_, 2);
                        crate::leanh::lean_dec(v_unused_6086_);
                        v_unused_6087_ = crate::leanh::lean_ctor_get(v_b_6065_, 1);
                        crate::leanh::lean_dec(v_unused_6087_);
                        v___x_6069_ = v_b_6065_;
                        v_isShared_6070_ = v_isSharedCheck_6085_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_task_6067_);
                        crate::leanh::lean_dec(v_b_6065_);
                        v___x_6069_ = crate::leanh::lean_box(0);
                        v_isShared_6070_ = v_isSharedCheck_6085_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_6065_;
                }
            }
            1 => {
                v___x_6071_ = crate::leanh::lean_box(0);
                v___x_6072_ = lean_array_uget_borrowed(v_as_6062_, v_i_6063_);
                v___x_6073_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_6074_ = 1;
                v___x_6075_ = crate::leanh::lean_box((v___x_6074_) as usize);
                crate::leanh::lean_inc(v___x_6072_);
                v___f_6076_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg___lam__1___boxed as *mut core::ffi::c_void, 4, 3);
                crate::leanh::lean_closure_set(v___f_6076_, 0, v___x_6072_);
                crate::leanh::lean_closure_set(v___f_6076_, 1, v___x_6073_);
                crate::leanh::lean_closure_set(v___f_6076_, 2, v___x_6075_);
                v___x_6077_ = lean_task_bind(v_task_6067_, v___f_6076_, v___x_6073_, v___x_6074_);
                v___x_6078_ = l_panic___at___00Lake_Job_sync_spec__0___closed__0;
                if v_isShared_6070_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6069_, 2, v___x_6078_);
                    crate::leanh::lean_ctor_set(v___x_6069_, 1, v___x_6071_);
                    crate::leanh::lean_ctor_set(v___x_6069_, 0, v___x_6077_);
                    v___x_6080_ = v___x_6069_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6084_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6084_, 0, v___x_6077_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6084_, 1, v___x_6071_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6084_, 2, v___x_6078_);
                    v___x_6080_ = v_reuseFailAlloc_6084_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_6080_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_6066_,
                );
                v___x_6081_ = 1usize;
                v___x_6082_ = lean_usize_add(v_i_6063_, v___x_6081_);
                v_i_6063_ = v___x_6082_;
                v_b_6065_ = v___x_6080_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg___boxed(
    mut v_as_6088_: *mut crate::leanh::LeanObject,
    mut v_i_6089_: *mut crate::leanh::LeanObject,
    mut v_stop_6090_: *mut crate::leanh::LeanObject,
    mut v_b_6091_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_6092_: usize = 0;
    let mut v_stop_boxed_6093_: usize = 0;
    let mut v_res_6094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_6092_ = crate::leanh::lean_unbox_usize(v_i_6089_);
    crate::leanh::lean_dec(v_i_6089_);
    v_stop_boxed_6093_ = crate::leanh::lean_unbox_usize(v_stop_6090_);
    crate::leanh::lean_dec(v_stop_6090_);
    v_res_6094_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg(v_as_6088_, v_i_boxed_6092_, v_stop_boxed_6093_, v_b_6091_);
    crate::leanh::lean_dec_ref(v_as_6088_);
    return v_res_6094_;
}
pub unsafe fn l_Lake_Job_collectArray___redArg(
    mut v_jobs_6095_: *mut crate::leanh::LeanObject,
    mut v_traceCaption_6096_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6102_: u8 = 0;
    let mut v___x_6103_: u8 = 0;
    let mut v___x_6104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6110_: u8 = 0;
    v___x_6097_ = lean_array_get_size(v_jobs_6095_);
    v___x_6098_ = lean_mk_empty_array_with_capacity(v___x_6097_);
    v___x_6099_ = crate::leanh::lean_box(0);
    v___x_6100_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_6101_ = l_Lake_Job_sync___redArg___closed__1;
    v___x_6102_ = 0;
    v___x_6103_ = 0;
    v___x_6104_ = l_Lake_BuildTrace_nil(v_traceCaption_6096_);
    v___x_6105_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_6105_, 0, v___x_6101_);
    crate::leanh::lean_ctor_set(v___x_6105_, 1, v___x_6104_);
    crate::leanh::lean_ctor_set(v___x_6105_, 2, v___x_6100_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_6105_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v___x_6102_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_6105_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
        v___x_6103_,
    );
    v___x_6106_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6106_, 0, v___x_6098_);
    crate::leanh::lean_ctor_set(v___x_6106_, 1, v___x_6105_);
    v___x_6107_ = lean_task_pure(v___x_6106_);
    v___x_6108_ = l_panic___at___00Lake_Job_sync_spec__0___closed__0;
    v___x_6109_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_6109_, 0, v___x_6107_);
    crate::leanh::lean_ctor_set(v___x_6109_, 1, v___x_6099_);
    crate::leanh::lean_ctor_set(v___x_6109_, 2, v___x_6108_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_6109_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v___x_6103_,
    );
    v___x_6110_ = lean_nat_dec_lt(v___x_6100_, v___x_6097_);
    if v___x_6110_ == 0 {
        return v___x_6109_;
    } else {
        let mut v___x_6111_: u8 = 0;
        v___x_6111_ = lean_nat_dec_le(v___x_6097_, v___x_6097_);
        if v___x_6111_ == 0 {
            if v___x_6110_ == 0 {
                return v___x_6109_;
            } else {
                let mut v___x_6112_: usize = 0;
                let mut v___x_6113_: usize = 0;
                let mut v___x_6114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_6112_ = 0usize;
                v___x_6113_ = lean_usize_of_nat(v___x_6097_);
                v___x_6114_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg(v_jobs_6095_, v___x_6112_, v___x_6113_, v___x_6109_);
                return v___x_6114_;
            }
        } else {
            let mut v___x_6115_: usize = 0;
            let mut v___x_6116_: usize = 0;
            let mut v___x_6117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_6115_ = 0usize;
            v___x_6116_ = lean_usize_of_nat(v___x_6097_);
            v___x_6117_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg(v_jobs_6095_, v___x_6115_, v___x_6116_, v___x_6109_);
            return v___x_6117_;
        }
    }
}
pub unsafe fn l_Lake_Job_collectArray___redArg___boxed(
    mut v_jobs_6118_: *mut crate::leanh::LeanObject,
    mut v_traceCaption_6119_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6120_ = l_Lake_Job_collectArray___redArg(v_jobs_6118_, v_traceCaption_6119_);
    crate::leanh::lean_dec_ref(v_jobs_6118_);
    return v_res_6120_;
}
pub unsafe fn l_Lake_Job_collectArray(
    mut v_00_u03b1_6121_: *mut crate::leanh::LeanObject,
    mut v_jobs_6122_: *mut crate::leanh::LeanObject,
    mut v_traceCaption_6123_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6124_ = l_Lake_Job_collectArray___redArg(v_jobs_6122_, v_traceCaption_6123_);
    return v___x_6124_;
}
pub unsafe fn l_Lake_Job_collectArray___boxed(
    mut v_00_u03b1_6125_: *mut crate::leanh::LeanObject,
    mut v_jobs_6126_: *mut crate::leanh::LeanObject,
    mut v_traceCaption_6127_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6128_ = l_Lake_Job_collectArray(v_00_u03b1_6125_, v_jobs_6126_, v_traceCaption_6127_);
    crate::leanh::lean_dec_ref(v_jobs_6126_);
    return v_res_6128_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0(
    mut v_00_u03b1_6129_: *mut crate::leanh::LeanObject,
    mut v_as_6130_: *mut crate::leanh::LeanObject,
    mut v_i_6131_: usize,
    mut v_stop_6132_: usize,
    mut v_b_6133_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6134_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg(v_as_6130_, v_i_6131_, v_stop_6132_, v_b_6133_);
    return v___x_6134_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___boxed(
    mut v_00_u03b1_6135_: *mut crate::leanh::LeanObject,
    mut v_as_6136_: *mut crate::leanh::LeanObject,
    mut v_i_6137_: *mut crate::leanh::LeanObject,
    mut v_stop_6138_: *mut crate::leanh::LeanObject,
    mut v_b_6139_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_6140_: usize = 0;
    let mut v_stop_boxed_6141_: usize = 0;
    let mut v_res_6142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_6140_ = crate::leanh::lean_unbox_usize(v_i_6137_);
    crate::leanh::lean_dec(v_i_6137_);
    v_stop_boxed_6141_ = crate::leanh::lean_unbox_usize(v_stop_6138_);
    crate::leanh::lean_dec(v_stop_6138_);
    v_res_6142_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0(v_00_u03b1_6135_, v_as_6136_, v_i_boxed_6140_, v_stop_boxed_6141_, v_b_6139_);
    crate::leanh::lean_dec_ref(v_as_6136_);
    return v_res_6142_;
}
pub unsafe fn l___private_Lake_Build_Job_Monad_0__Lake_Job_collectVector_unsafe__1(
    mut v_00_u03b1_6143_: *mut crate::leanh::LeanObject,
    mut v_inst_6144_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6145_ = crate::leanh::lean_box(0);
    return v___x_6145_;
}
pub unsafe fn l_Lake_Job_collectVector___redArg___lam__0(
    mut v___x_6146_: *mut crate::leanh::LeanObject,
    mut v_rx_6147_: *mut crate::leanh::LeanObject,
    mut v_i_6148_: *mut crate::leanh::LeanObject,
    mut v_ry_6149_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_6151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6165_: u8 = 0;
    let mut v___x_6166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6171_: u8 = 0;
    let mut v_a_6172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_rx_6147_) == 0 {
                    if crate::leanh::lean_obj_tag(v_ry_6149_) == 0 {
                        crate::leanh::lean_dec(v___x_6146_);
                        v_a_6159_ = crate::leanh::lean_ctor_get(v_rx_6147_, 0);
                        crate::leanh::lean_inc(v_a_6159_);
                        v_a_6160_ = crate::leanh::lean_ctor_get(v_rx_6147_, 1);
                        crate::leanh::lean_inc(v_a_6160_);
                        crate::leanh::lean_dec_ref_known(v_rx_6147_, 2);
                        v_a_6161_ = crate::leanh::lean_ctor_get(v_ry_6149_, 0);
                        v_a_6162_ = crate::leanh::lean_ctor_get(v_ry_6149_, 1);
                        v_isSharedCheck_6171_ =
                            (!crate::leanh::lean_is_exclusive(v_ry_6149_)) as u8;
                        if v_isSharedCheck_6171_ == 0 {
                            v___x_6164_ = v_ry_6149_;
                            v_isShared_6165_ = v_isSharedCheck_6171_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6162_);
                            crate::leanh::lean_inc(v_a_6161_);
                            crate::leanh::lean_dec(v_ry_6149_);
                            v___x_6164_ = crate::leanh::lean_box(0);
                            v_isShared_6165_ = v_isSharedCheck_6171_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_6172_ = crate::leanh::lean_ctor_get(v_rx_6147_, 1);
                        crate::leanh::lean_inc(v_a_6172_);
                        crate::leanh::lean_dec_ref_known(v_rx_6147_, 2);
                        v___y_6156_ = v_ry_6149_;
                        v___y_6157_ = v_a_6172_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_6173_ = crate::leanh::lean_ctor_get(v_rx_6147_, 1);
                    crate::leanh::lean_inc(v_a_6173_);
                    crate::leanh::lean_dec_ref(v_rx_6147_);
                    v___y_6156_ = v_ry_6149_;
                    v___y_6157_ = v_a_6173_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_6153_ = l_Lake_JobState_merge(v___y_6151_, v___y_6152_);
                v___x_6154_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6154_, 0, v___x_6146_);
                crate::leanh::lean_ctor_set(v___x_6154_, 1, v___x_6153_);
                return v___x_6154_;
            }
            2 => {
                v_a_6158_ = crate::leanh::lean_ctor_get(v___y_6156_, 1);
                crate::leanh::lean_inc(v_a_6158_);
                crate::leanh::lean_dec_ref(v___y_6156_);
                v___y_6151_ = v___y_6157_;
                v___y_6152_ = v_a_6158_;
                state = 1;
                continue;
            }
            3 => {
                v___x_6166_ = lean_array_fset(v_a_6159_, v_i_6148_, v_a_6161_);
                v___x_6167_ = l_Lake_JobState_merge(v_a_6160_, v_a_6162_);
                if v_isShared_6165_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6164_, 1, v___x_6167_);
                    crate::leanh::lean_ctor_set(v___x_6164_, 0, v___x_6166_);
                    v___x_6169_ = v___x_6164_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6170_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6170_, 0, v___x_6166_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6170_, 1, v___x_6167_);
                    v___x_6169_ = v_reuseFailAlloc_6170_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6169_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Job_collectVector___redArg___lam__0___boxed(
    mut v___x_6174_: *mut crate::leanh::LeanObject,
    mut v_rx_6175_: *mut crate::leanh::LeanObject,
    mut v_i_6176_: *mut crate::leanh::LeanObject,
    mut v_ry_6177_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6178_ =
        l_Lake_Job_collectVector___redArg___lam__0(v___x_6174_, v_rx_6175_, v_i_6176_, v_ry_6177_);
    crate::leanh::lean_dec(v_i_6176_);
    return v_res_6178_;
}
pub unsafe fn l_Lake_Job_collectVector___redArg___lam__1(
    mut v___x_6179_: *mut crate::leanh::LeanObject,
    mut v___x_6180_: *mut crate::leanh::LeanObject,
    mut v_i_6181_: *mut crate::leanh::LeanObject,
    mut v___x_6182_: u8,
    mut v_rx_6183_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_task_6184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_task_6184_ = crate::leanh::lean_ctor_get(v___x_6179_, 0);
    crate::leanh::lean_inc_ref(v_task_6184_);
    crate::leanh::lean_dec_ref(v___x_6179_);
    crate::leanh::lean_inc(v___x_6180_);
    v___f_6185_ = crate::leanh::lean_alloc_closure(
        l_Lake_Job_collectVector___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_6185_, 0, v___x_6180_);
    crate::leanh::lean_closure_set(v___f_6185_, 1, v_rx_6183_);
    crate::leanh::lean_closure_set(v___f_6185_, 2, v_i_6181_);
    v___x_6186_ = lean_task_map(v___f_6185_, v_task_6184_, v___x_6180_, v___x_6182_);
    return v___x_6186_;
}
pub unsafe fn l_Lake_Job_collectVector___redArg___lam__1___boxed(
    mut v___x_6187_: *mut crate::leanh::LeanObject,
    mut v___x_6188_: *mut crate::leanh::LeanObject,
    mut v_i_6189_: *mut crate::leanh::LeanObject,
    mut v___x_6190_: *mut crate::leanh::LeanObject,
    mut v_rx_6191_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_191__boxed_6192_: u8 = 0;
    let mut v_res_6193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_191__boxed_6192_ = (crate::leanh::lean_unbox(v___x_6190_) as u8);
    v_res_6193_ = l_Lake_Job_collectVector___redArg___lam__1(
        v___x_6187_,
        v___x_6188_,
        v_i_6189_,
        v___x_191__boxed_6192_,
        v_rx_6191_,
    );
    return v_res_6193_;
}
pub unsafe fn l_Lake_Job_collectVector___redArg___lam__2(
    mut v_jobs_6194_: *mut crate::leanh::LeanObject,
    mut v___x_6195_: *mut crate::leanh::LeanObject,
    mut v_i_6196_: *mut crate::leanh::LeanObject,
    mut v_h_6197_: *mut crate::leanh::LeanObject,
    mut v_job_6198_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_task_6199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6202_: u8 = 0;
    let mut v___x_6203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6205_: u8 = 0;
    let mut v___x_6206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6210_: u8 = 0;
    let mut v___x_6212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6214_: u8 = 0;
    let mut v_unused_6215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_task_6199_ = crate::leanh::lean_ctor_get(v_job_6198_, 0);
                v_isSharedCheck_6214_ = (!crate::leanh::lean_is_exclusive(v_job_6198_)) as u8;
                if v_isSharedCheck_6214_ == 0 {
                    v_unused_6215_ = crate::leanh::lean_ctor_get(v_job_6198_, 2);
                    crate::leanh::lean_dec(v_unused_6215_);
                    v_unused_6216_ = crate::leanh::lean_ctor_get(v_job_6198_, 1);
                    crate::leanh::lean_dec(v_unused_6216_);
                    v___x_6201_ = v_job_6198_;
                    v_isShared_6202_ = v_isSharedCheck_6214_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_task_6199_);
                    crate::leanh::lean_dec(v_job_6198_);
                    v___x_6201_ = crate::leanh::lean_box(0);
                    v_isShared_6202_ = v_isSharedCheck_6214_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6203_ = lean_array_fget_borrowed(v_jobs_6194_, v_i_6196_);
                v___x_6204_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_6205_ = 1;
                v___x_6206_ = crate::leanh::lean_box((v___x_6205_) as usize);
                crate::leanh::lean_inc(v___x_6203_);
                v___f_6207_ = crate::leanh::lean_alloc_closure(
                    l_Lake_Job_collectVector___redArg___lam__1___boxed as *mut core::ffi::c_void,
                    5,
                    4,
                );
                crate::leanh::lean_closure_set(v___f_6207_, 0, v___x_6203_);
                crate::leanh::lean_closure_set(v___f_6207_, 1, v___x_6204_);
                crate::leanh::lean_closure_set(v___f_6207_, 2, v_i_6196_);
                crate::leanh::lean_closure_set(v___f_6207_, 3, v___x_6206_);
                v___x_6208_ = lean_task_bind(v_task_6199_, v___f_6207_, v___x_6204_, v___x_6205_);
                v___x_6209_ = l_panic___at___00Lake_Job_sync_spec__0___closed__0;
                v___x_6210_ = 0;
                if v_isShared_6202_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6201_, 2, v___x_6209_);
                    crate::leanh::lean_ctor_set(v___x_6201_, 1, v___x_6195_);
                    crate::leanh::lean_ctor_set(v___x_6201_, 0, v___x_6208_);
                    v___x_6212_ = v___x_6201_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6213_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6213_, 0, v___x_6208_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6213_, 1, v___x_6195_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6213_, 2, v___x_6209_);
                    v___x_6212_ = v_reuseFailAlloc_6213_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_6212_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_6210_,
                );
                return v___x_6212_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Job_collectVector___redArg___lam__2___boxed(
    mut v_jobs_6217_: *mut crate::leanh::LeanObject,
    mut v___x_6218_: *mut crate::leanh::LeanObject,
    mut v_i_6219_: *mut crate::leanh::LeanObject,
    mut v_h_6220_: *mut crate::leanh::LeanObject,
    mut v_job_6221_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6222_ = l_Lake_Job_collectVector___redArg___lam__2(
        v_jobs_6217_,
        v___x_6218_,
        v_i_6219_,
        v_h_6220_,
        v_job_6221_,
    );
    crate::leanh::lean_dec_ref(v_jobs_6217_);
    return v_res_6222_;
}
pub unsafe fn l_Lake_Job_collectVector___redArg(
    mut v_n_6223_: *mut crate::leanh::LeanObject,
    mut v_jobs_6224_: *mut crate::leanh::LeanObject,
    mut v_traceCaption_6225_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_placeholder_6226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6232_: u8 = 0;
    let mut v___x_6233_: u8 = 0;
    let mut v___x_6234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_placeholder_6226_ = crate::leanh::lean_box(0);
    v___x_6227_ = crate::leanh::lean_box(0);
    v___f_6228_ = crate::leanh::lean_alloc_closure(
        l_Lake_Job_collectVector___redArg___lam__2___boxed as *mut core::ffi::c_void,
        5,
        2,
    );
    crate::leanh::lean_closure_set(v___f_6228_, 0, v_jobs_6224_);
    crate::leanh::lean_closure_set(v___f_6228_, 1, v___x_6227_);
    crate::leanh::lean_inc_n(v_n_6223_, 2);
    v___x_6229_ = lean_mk_array(v_n_6223_, v_placeholder_6226_);
    v___x_6230_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_6231_ = l_Lake_Job_sync___redArg___closed__1;
    v___x_6232_ = 0;
    v___x_6233_ = 0;
    v___x_6234_ = l_Lake_BuildTrace_nil(v_traceCaption_6225_);
    v___x_6235_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_6235_, 0, v___x_6231_);
    crate::leanh::lean_ctor_set(v___x_6235_, 1, v___x_6234_);
    crate::leanh::lean_ctor_set(v___x_6235_, 2, v___x_6230_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_6235_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v___x_6232_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_6235_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
        v___x_6233_,
    );
    v___x_6236_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6236_, 0, v___x_6229_);
    crate::leanh::lean_ctor_set(v___x_6236_, 1, v___x_6235_);
    v___x_6237_ = lean_task_pure(v___x_6236_);
    v___x_6238_ = l_panic___at___00Lake_Job_sync_spec__0___closed__0;
    v___x_6239_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_6239_, 0, v___x_6237_);
    crate::leanh::lean_ctor_set(v___x_6239_, 1, v___x_6227_);
    crate::leanh::lean_ctor_set(v___x_6239_, 2, v___x_6238_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_6239_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v___x_6233_,
    );
    v___x_6240_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop(
        crate::leanh::lean_box(0),
        v_n_6223_,
        v___f_6228_,
        v_n_6223_,
        crate::leanh::lean_box(0),
        v___x_6239_,
    );
    crate::leanh::lean_dec(v_n_6223_);
    return v___x_6240_;
}
pub unsafe fn l_Lake_Job_collectVector(
    mut v_n_6241_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_6242_: *mut crate::leanh::LeanObject,
    mut v_inst_6243_: *mut crate::leanh::LeanObject,
    mut v_jobs_6244_: *mut crate::leanh::LeanObject,
    mut v_traceCaption_6245_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6246_ = l_Lake_Job_collectVector___redArg(v_n_6241_, v_jobs_6244_, v_traceCaption_6245_);
    return v___x_6246_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Build_Job_Monad(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Build_Fetch(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lake_instMonadStateOfJobStateJobM = _init_l_Lake_instMonadStateOfJobStateJobM();
    crate::leanh::lean_mark_persistent(l_Lake_instMonadStateOfJobStateJobM);
    l_Lake_instAlternativeJobM = _init_l_Lake_instAlternativeJobM();
    crate::leanh::lean_mark_persistent(l_Lake_instAlternativeJobM);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Build_Job_Monad(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Build_Job_Monad(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Build_Fetch(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Job_Monad(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Build_Job_Monad(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_Build_Job_Monad(builtin);
}
