// Lean compiler output
// Module: Std.Async.Timer
// Imports: Std.Time Std.Internal.UV.Timer Std.Async.Select
use crate::r#gen::Init::Data::Int::Basic::l_Int_toNat;
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr4, l_Lean_mkAtom};
use crate::r#gen::Init::System::IO::l_BaseIO_chainTask___redArg;
use crate::r#gen::Init::System::IOError::lean_mk_io_user_error;
use crate::r#gen::Init::System::Promise::l_IO_Promise_isResolved___redArg;
use crate::r#gen::Std::Async::Basic::l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask;
use crate::r#gen::Std::Async::Select::{
    initialize_Std_Async_Select, runtime_initialize_Std_Async_Select,
};
use crate::r#gen::Std::Internal::UV::Timer::{
    initialize_Std_Internal_UV_Timer, runtime_initialize_Std_Internal_UV_Timer,
};
use crate::r#gen::Std::Time::{initialize_Std_Time, runtime_initialize_Std_Time};
use crate::lean_imports_rs::Init::Core::lean_task_map;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::lean_uint64_of_nat;
use crate::lean_imports_rs::Init::Prelude::{lean_array_push, lean_mk_empty_array_with_capacity};
use crate::lean_imports_rs::Init::System::Promise::{
    lean_io_promise_resolve, lean_io_promise_result_opt,
};
use crate::lean_imports_rs::Init::System::ST::{lean_st_ref_set, lean_st_ref_take};
use crate::lean_imports_rs::Std::Internal::UV::Timer::{
    lean_uv_timer_cancel, lean_uv_timer_mk, lean_uv_timer_next, lean_uv_timer_reset,
    lean_uv_timer_stop,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_set, lean_ctor_set_tag, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent, lean_obj_once, lean_obj_tag,
    lean_unbox, lean_unsigned_to_nat,
};
pub static l_Std_Async_Sleep_mk___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Async_Sleep_mk___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Async_Sleep_mk___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_Sleep_mk___closed__0_value) as *mut LeanObject;
pub static l_Std_Async_Sleep_wait___closed__0_value: LeanStringObject<44> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Std_Async_Sleep_wait___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_Sleep_wait___closed__0_value) as *mut LeanObject;
pub static l_Std_Async_Sleep_wait___closed__1_value: LeanClosureObject<1> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Async_Sleep_wait___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(l_Std_Async_Sleep_wait___closed__0_value) as *mut LeanObject],
};
static mut l_Std_Async_Sleep_wait___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_Sleep_wait___closed__1_value) as *mut LeanObject;
pub static l_Std_Async_Waiter_race___at___00Std_Async_Sleep_selector_spec__0___closed__0_value:
    LeanCtorObject<1> = LeanCtorObject {
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
static mut l_Std_Async_Waiter_race___at___00Std_Async_Sleep_selector_spec__0___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Async_Waiter_race___at___00Std_Async_Sleep_selector_spec__0___closed__0_value
) as *mut LeanObject;
pub static l_Std_Async_Sleep_selector___lam__0___closed__0_value: LeanCtorObject<1> =
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
static mut l_Std_Async_Sleep_selector___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_Sleep_selector___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Std_Async_Sleep_selector___lam__0___closed__1_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_Async_Sleep_selector___lam__0___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Async_Sleep_selector___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_Sleep_selector___lam__0___closed__1_value) as *mut LeanObject;
pub static l_Std_Async_Sleep_selector___lam__3___closed__0_value: LeanClosureObject<1> =
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
        m_fun: l_Std_Async_Sleep_selector___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Std_Async_Sleep_selector___lam__3___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_Sleep_selector___lam__3___closed__0_value) as *mut LeanObject;
pub static l_Std_Async_Sleep_selector___lam__6___closed__0_value: LeanCtorObject<1> =
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
static mut l_Std_Async_Sleep_selector___lam__6___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_Sleep_selector___lam__6___closed__0_value) as *mut LeanObject;
pub static l_Std_Async_Sleep_selector___lam__6___closed__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_Sleep_selector___lam__6___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Async_Sleep_selector___lam__6___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_Sleep_selector___lam__6___closed__1_value) as *mut LeanObject;
pub static l_Std_Async_Sleep_selector___lam__6___closed__2_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_Async_Sleep_selector___lam__6___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Async_Sleep_selector___lam__6___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_Sleep_selector___lam__6___closed__2_value) as *mut LeanObject;
pub static l_Std_Async_Sleep_selector___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Async_Sleep_selector___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Async_Sleep_selector___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_Sleep_selector___closed__0_value) as *mut LeanObject;
pub static l_Std_Async_sleep___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Async_sleep___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Async_sleep___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_sleep___closed__0_value) as *mut LeanObject;
pub static l_Std_Async_Selector_sleep___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Async_Selector_sleep___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Async_Selector_sleep___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_Selector_sleep___closed__0_value) as *mut LeanObject;
pub static l_Std_Async_Interval_mk___auto__1___closed__0_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Std_Async_Interval_mk___auto__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_Interval_mk___auto__1___closed__0_value) as *mut LeanObject;
pub static l_Std_Async_Interval_mk___auto__1___closed__1_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Std_Async_Interval_mk___auto__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_Interval_mk___auto__1___closed__1_value) as *mut LeanObject;
pub static l_Std_Async_Interval_mk___auto__1___closed__2_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Std_Async_Interval_mk___auto__1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_Interval_mk___auto__1___closed__2_value) as *mut LeanObject;
pub static l_Std_Async_Interval_mk___auto__1___closed__3_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Std_Async_Interval_mk___auto__1___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_Interval_mk___auto__1___closed__3_value) as *mut LeanObject;
static l_Std_Async_Interval_mk___auto__1___closed__4_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Async_Interval_mk___auto__1___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Std_Async_Interval_mk___auto__1___closed__4_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_Interval_mk___auto__1___closed__4_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Async_Interval_mk___auto__1___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Std_Async_Interval_mk___auto__1___closed__4_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_Interval_mk___auto__1___closed__4_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Async_Interval_mk___auto__1___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Std_Async_Interval_mk___auto__1___closed__4_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_Interval_mk___auto__1___closed__4_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Async_Interval_mk___auto__1___closed__3_value)
                as *mut LeanObject,
            8504843326314613972 as *mut LeanObject,
        ],
    };
static mut l_Std_Async_Interval_mk___auto__1___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_Interval_mk___auto__1___closed__4_value) as *mut LeanObject;
pub static l_Std_Async_Interval_mk___auto__1___closed__5_value: LeanArrayObject<0> =
    LeanArrayObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Std_Async_Interval_mk___auto__1___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_Interval_mk___auto__1___closed__5_value) as *mut LeanObject;
pub static l_Std_Async_Interval_mk___auto__1___closed__6_value: LeanStringObject<19> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Std_Async_Interval_mk___auto__1___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_Interval_mk___auto__1___closed__6_value) as *mut LeanObject;
static l_Std_Async_Interval_mk___auto__1___closed__7_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Async_Interval_mk___auto__1___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Std_Async_Interval_mk___auto__1___closed__7_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_Interval_mk___auto__1___closed__7_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Async_Interval_mk___auto__1___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Std_Async_Interval_mk___auto__1___closed__7_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_Interval_mk___auto__1___closed__7_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Async_Interval_mk___auto__1___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Std_Async_Interval_mk___auto__1___closed__7_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_Interval_mk___auto__1___closed__7_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Async_Interval_mk___auto__1___closed__6_value)
                as *mut LeanObject,
            17228437386856258271 as *mut LeanObject,
        ],
    };
static mut l_Std_Async_Interval_mk___auto__1___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_Interval_mk___auto__1___closed__7_value) as *mut LeanObject;
pub static l_Std_Async_Interval_mk___auto__1___closed__8_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Std_Async_Interval_mk___auto__1___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_Interval_mk___auto__1___closed__8_value) as *mut LeanObject;
pub static l_Std_Async_Interval_mk___auto__1___closed__9_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Async_Interval_mk___auto__1___closed__8_value)
                as *mut LeanObject,
            9855511589286918680 as *mut LeanObject,
        ],
    };
static mut l_Std_Async_Interval_mk___auto__1___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_Interval_mk___auto__1___closed__9_value) as *mut LeanObject;
pub static l_Std_Async_Interval_mk___auto__1___closed__10_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Std_Async_Interval_mk___auto__1___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_Interval_mk___auto__1___closed__10_value) as *mut LeanObject;
static l_Std_Async_Interval_mk___auto__1___closed__11_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Async_Interval_mk___auto__1___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Std_Async_Interval_mk___auto__1___closed__11_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_Interval_mk___auto__1___closed__11_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Async_Interval_mk___auto__1___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Std_Async_Interval_mk___auto__1___closed__11_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_Interval_mk___auto__1___closed__11_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Async_Interval_mk___auto__1___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Std_Async_Interval_mk___auto__1___closed__11_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_Interval_mk___auto__1___closed__11_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Async_Interval_mk___auto__1___closed__10_value)
                as *mut LeanObject,
            14249328086033210933 as *mut LeanObject,
        ],
    };
static mut l_Std_Async_Interval_mk___auto__1___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_Interval_mk___auto__1___closed__11_value) as *mut LeanObject;
static mut l_Std_Async_Interval_mk___auto__1___closed__12_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Async_Interval_mk___auto__1___closed__12: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Async_Interval_mk___auto__1___closed__13_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Async_Interval_mk___auto__1___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Async_Interval_mk___auto__1___closed__14_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Std_Async_Interval_mk___auto__1___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_Interval_mk___auto__1___closed__14_value) as *mut LeanObject;
static l_Std_Async_Interval_mk___auto__1___closed__15_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Async_Interval_mk___auto__1___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Std_Async_Interval_mk___auto__1___closed__15_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_Interval_mk___auto__1___closed__15_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Async_Interval_mk___auto__1___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Std_Async_Interval_mk___auto__1___closed__15_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_Interval_mk___auto__1___closed__15_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Async_Interval_mk___auto__1___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Std_Async_Interval_mk___auto__1___closed__15_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_Interval_mk___auto__1___closed__15_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Async_Interval_mk___auto__1___closed__14_value)
                as *mut LeanObject,
            3488656302031949961 as *mut LeanObject,
        ],
    };
static mut l_Std_Async_Interval_mk___auto__1___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_Interval_mk___auto__1___closed__15_value) as *mut LeanObject;
pub static l_Std_Async_Interval_mk___auto__1___closed__16_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 1,
        },
        m_objs: [
            (((2 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Async_Interval_mk___auto__1___closed__9_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Async_Interval_mk___auto__1___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Async_Interval_mk___auto__1___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Async_Interval_mk___auto__1___closed__16_value) as *mut LeanObject;
static mut l_Std_Async_Interval_mk___auto__1___closed__17_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Async_Interval_mk___auto__1___closed__17: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Async_Interval_mk___auto__1___closed__18_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Async_Interval_mk___auto__1___closed__18: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Async_Interval_mk___auto__1___closed__19_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Async_Interval_mk___auto__1___closed__19: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Async_Interval_mk___auto__1___closed__20_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Async_Interval_mk___auto__1___closed__20: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Async_Interval_mk___auto__1___closed__21_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Async_Interval_mk___auto__1___closed__21: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Async_Interval_mk___auto__1___closed__22_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Async_Interval_mk___auto__1___closed__22: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Async_Interval_mk___auto__1___closed__23_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Async_Interval_mk___auto__1___closed__23: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Async_Interval_mk___auto__1___closed__24_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Async_Interval_mk___auto__1___closed__24: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Async_Interval_mk___auto__1___closed__25_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Async_Interval_mk___auto__1___closed__25: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Async_Interval_mk___auto__1___closed__26_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Async_Interval_mk___auto__1___closed__26: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_Async_Interval_mk___auto__1: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Std_Async_Sleep_mk___lam__0(mut v_x_698_: *mut LeanObject) -> *mut LeanObject {
    let mut v_a_700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_703_: u8 = 0;
    let mut v___x_705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_708_: u8 = 0;
    let mut v_a_709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_712_: u8 = 0;
    let mut v___x_714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_717_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_698_) == 0 {
                    v_a_700_ = lean_ctor_get(v_x_698_, 0);
                    v_isSharedCheck_708_ = (!lean_is_exclusive(v_x_698_)) as u8;
                    if v_isSharedCheck_708_ == 0 {
                        v___x_702_ = v_x_698_;
                        v_isShared_703_ = v_isSharedCheck_708_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_700_);
                        lean_dec(v_x_698_);
                        v___x_702_ = lean_box(0);
                        v_isShared_703_ = v_isSharedCheck_708_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_709_ = lean_ctor_get(v_x_698_, 0);
                    v_isSharedCheck_717_ = (!lean_is_exclusive(v_x_698_)) as u8;
                    if v_isSharedCheck_717_ == 0 {
                        v___x_711_ = v_x_698_;
                        v_isShared_712_ = v_isSharedCheck_717_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_709_);
                        lean_dec(v_x_698_);
                        v___x_711_ = lean_box(0);
                        v_isShared_712_ = v_isSharedCheck_717_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_703_ == 0 {
                    v___x_705_ = v___x_702_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_707_, 0, v_a_700_);
                    v___x_705_ = v_reuseFailAlloc_707_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_706_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_706_, 0, v___x_705_);
                return v___x_706_;
            }
            3 => {
                if v_isShared_712_ == 0 {
                    v___x_714_ = v___x_711_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_716_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_716_, 0, v_a_709_);
                    v___x_714_ = v_reuseFailAlloc_716_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_715_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_715_, 0, v___x_714_);
                return v___x_715_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Sleep_mk___lam__0___boxed(
    mut v_x_718_: *mut LeanObject,
    mut v___y_719_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_720_: *mut LeanObject = core::ptr::null_mut();
    v_res_720_ = l_Std_Async_Sleep_mk___lam__0(v_x_718_);
    return v_res_720_;
}
pub unsafe fn l_Std_Async_Sleep_mk(mut v_duration_722_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_729_: u8 = 0;
    let mut v___x_730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_732_: u64 = 0;
    let mut v___x_733_: u8 = 0;
    let mut v___x_734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_738_: u8 = 0;
    let mut v___x_740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_742_: u8 = 0;
    let mut v_a_743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_746_: u8 = 0;
    let mut v___x_748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_750_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_724_ = l_Std_Async_Sleep_mk___closed__0;
                v___x_731_ = l_Int_toNat(v_duration_722_);
                v___x_732_ = lean_uint64_of_nat(v___x_731_);
                lean_dec(v___x_731_);
                v___x_733_ = 0;
                v___x_734_ = lean_uv_timer_mk(v___x_732_, v___x_733_);
                if lean_obj_tag(v___x_734_) == 0 {
                    v_a_735_ = lean_ctor_get(v___x_734_, 0);
                    v_isSharedCheck_742_ = (!lean_is_exclusive(v___x_734_)) as u8;
                    if v_isSharedCheck_742_ == 0 {
                        v___x_737_ = v___x_734_;
                        v_isShared_738_ = v_isSharedCheck_742_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_735_);
                        lean_dec(v___x_734_);
                        v___x_737_ = lean_box(0);
                        v_isShared_738_ = v_isSharedCheck_742_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_743_ = lean_ctor_get(v___x_734_, 0);
                    v_isSharedCheck_750_ = (!lean_is_exclusive(v___x_734_)) as u8;
                    if v_isSharedCheck_750_ == 0 {
                        v___x_745_ = v___x_734_;
                        v_isShared_746_ = v_isSharedCheck_750_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_743_);
                        lean_dec(v___x_734_);
                        v___x_745_ = lean_box(0);
                        v_isShared_746_ = v_isSharedCheck_750_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_727_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_727_, 0, v_val_726_);
                v___x_728_ = lean_unsigned_to_nat(0);
                v___x_729_ = 0;
                v___x_730_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
                    v___x_728_,
                    v___x_729_,
                    v___x_727_,
                    v___f_724_,
                );
                return v___x_730_;
            }
            2 => {
                if v_isShared_738_ == 0 {
                    lean_ctor_set_tag(v___x_737_, 1);
                    v___x_740_ = v___x_737_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_741_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_741_, 0, v_a_735_);
                    v___x_740_ = v_reuseFailAlloc_741_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_val_726_ = v___x_740_;
                state = 1;
                continue;
            }
            4 => {
                if v_isShared_746_ == 0 {
                    lean_ctor_set_tag(v___x_745_, 0);
                    v___x_748_ = v___x_745_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_749_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_749_, 0, v_a_743_);
                    v___x_748_ = v_reuseFailAlloc_749_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_val_726_ = v___x_748_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Sleep_mk___boxed(
    mut v_duration_751_: *mut LeanObject,
    mut v_a_752_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_753_: *mut LeanObject = core::ptr::null_mut();
    v_res_753_ = l_Std_Async_Sleep_mk(v_duration_751_);
    lean_dec(v_duration_751_);
    return v_res_753_;
}
pub unsafe fn l_Std_Async_Sleep_wait___lam__0(
    mut v___x_754_: *mut LeanObject,
    mut v_x_755_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_761_: u8 = 0;
    let mut v___x_763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_765_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_755_) == 0 {
                    v___x_756_ = lean_mk_io_user_error(v___x_754_);
                    v___x_757_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_757_, 0, v___x_756_);
                    return v___x_757_;
                } else {
                    lean_dec_ref(v___x_754_);
                    v_val_758_ = lean_ctor_get(v_x_755_, 0);
                    v_isSharedCheck_765_ = (!lean_is_exclusive(v_x_755_)) as u8;
                    if v_isSharedCheck_765_ == 0 {
                        v___x_760_ = v_x_755_;
                        v_isShared_761_ = v_isSharedCheck_765_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_758_);
                        lean_dec(v_x_755_);
                        v___x_760_ = lean_box(0);
                        v_isShared_761_ = v_isSharedCheck_765_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_761_ == 0 {
                    v___x_763_ = v___x_760_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_764_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_764_, 0, v_val_758_);
                    v___x_763_ = v_reuseFailAlloc_764_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_763_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Sleep_wait(mut v_s_769_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_775_: u8 = 0;
    let mut v___f_776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_779_: u8 = 0;
    let mut v___x_780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_784_: u8 = 0;
    let mut v_a_785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_788_: u8 = 0;
    let mut v___x_790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_793_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_771_ = lean_uv_timer_next(v_s_769_);
                if lean_obj_tag(v___x_771_) == 0 {
                    v_a_772_ = lean_ctor_get(v___x_771_, 0);
                    v_isSharedCheck_784_ = (!lean_is_exclusive(v___x_771_)) as u8;
                    if v_isSharedCheck_784_ == 0 {
                        v___x_774_ = v___x_771_;
                        v_isShared_775_ = v_isSharedCheck_784_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_772_);
                        lean_dec(v___x_771_);
                        v___x_774_ = lean_box(0);
                        v_isShared_775_ = v_isSharedCheck_784_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_785_ = lean_ctor_get(v___x_771_, 0);
                    v_isSharedCheck_793_ = (!lean_is_exclusive(v___x_771_)) as u8;
                    if v_isSharedCheck_793_ == 0 {
                        v___x_787_ = v___x_771_;
                        v_isShared_788_ = v_isSharedCheck_793_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_785_);
                        lean_dec(v___x_771_);
                        v___x_787_ = lean_box(0);
                        v_isShared_788_ = v_isSharedCheck_793_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___f_776_ = l_Std_Async_Sleep_wait___closed__1;
                v___x_777_ = lean_io_promise_result_opt(v_a_772_);
                lean_dec(v_a_772_);
                v___x_778_ = lean_unsigned_to_nat(0);
                v___x_779_ = 0;
                v___x_780_ = lean_task_map(v___f_776_, v___x_777_, v___x_778_, v___x_779_);
                if v_isShared_775_ == 0 {
                    lean_ctor_set_tag(v___x_774_, 1);
                    lean_ctor_set(v___x_774_, 0, v___x_780_);
                    v___x_782_ = v___x_774_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_783_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_783_, 0, v___x_780_);
                    v___x_782_ = v_reuseFailAlloc_783_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_782_;
            }
            3 => {
                if v_isShared_788_ == 0 {
                    lean_ctor_set_tag(v___x_787_, 0);
                    v___x_790_ = v___x_787_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_792_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_792_, 0, v_a_785_);
                    v___x_790_ = v_reuseFailAlloc_792_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_791_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_791_, 0, v___x_790_);
                return v___x_791_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Sleep_wait___boxed(
    mut v_s_794_: *mut LeanObject,
    mut v_a_795_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_796_: *mut LeanObject = core::ptr::null_mut();
    v_res_796_ = l_Std_Async_Sleep_wait(v_s_794_);
    lean_dec(v_s_794_);
    return v_res_796_;
}
pub unsafe fn l_Std_Async_Sleep_reset(mut v_s_797_: *mut LeanObject) -> *mut LeanObject {
    let mut v_val_800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_806_: u8 = 0;
    let mut v___x_808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_810_: u8 = 0;
    let mut v_a_811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_814_: u8 = 0;
    let mut v___x_816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_818_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_802_ = lean_uv_timer_reset(v_s_797_);
                if lean_obj_tag(v___x_802_) == 0 {
                    v_a_803_ = lean_ctor_get(v___x_802_, 0);
                    v_isSharedCheck_810_ = (!lean_is_exclusive(v___x_802_)) as u8;
                    if v_isSharedCheck_810_ == 0 {
                        v___x_805_ = v___x_802_;
                        v_isShared_806_ = v_isSharedCheck_810_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_803_);
                        lean_dec(v___x_802_);
                        v___x_805_ = lean_box(0);
                        v_isShared_806_ = v_isSharedCheck_810_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_811_ = lean_ctor_get(v___x_802_, 0);
                    v_isSharedCheck_818_ = (!lean_is_exclusive(v___x_802_)) as u8;
                    if v_isSharedCheck_818_ == 0 {
                        v___x_813_ = v___x_802_;
                        v_isShared_814_ = v_isSharedCheck_818_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_811_);
                        lean_dec(v___x_802_);
                        v___x_813_ = lean_box(0);
                        v_isShared_814_ = v_isSharedCheck_818_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_801_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_801_, 0, v_val_800_);
                return v___x_801_;
            }
            2 => {
                if v_isShared_806_ == 0 {
                    lean_ctor_set_tag(v___x_805_, 1);
                    v___x_808_ = v___x_805_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_809_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_809_, 0, v_a_803_);
                    v___x_808_ = v_reuseFailAlloc_809_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_val_800_ = v___x_808_;
                state = 1;
                continue;
            }
            4 => {
                if v_isShared_814_ == 0 {
                    lean_ctor_set_tag(v___x_813_, 0);
                    v___x_816_ = v___x_813_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_817_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_817_, 0, v_a_811_);
                    v___x_816_ = v_reuseFailAlloc_817_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_val_800_ = v___x_816_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Sleep_reset___boxed(
    mut v_s_819_: *mut LeanObject,
    mut v_a_820_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_821_: *mut LeanObject = core::ptr::null_mut();
    v_res_821_ = l_Std_Async_Sleep_reset(v_s_819_);
    lean_dec(v_s_819_);
    return v_res_821_;
}
pub unsafe fn l_Std_Async_Sleep_stop(mut v_s_822_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_824_: *mut LeanObject = core::ptr::null_mut();
    v___x_824_ = lean_uv_timer_stop(v_s_822_);
    return v___x_824_;
}
pub unsafe fn l_Std_Async_Sleep_stop___boxed(
    mut v_s_825_: *mut LeanObject,
    mut v_a_826_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_827_: *mut LeanObject = core::ptr::null_mut();
    v_res_827_ = l_Std_Async_Sleep_stop(v_s_825_);
    lean_dec(v_s_825_);
    return v_res_827_;
}
pub unsafe fn l_Std_Async_Waiter_race___at___00Std_Async_Sleep_selector_spec__0(
    mut v_w_830_: *mut LeanObject,
    mut v_lose_831_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_finished_833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_promise_834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_837_: u8 = 0;
    let mut v___x_838_: u8 = 0;
    let mut v___x_839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_844_: u8 = 0;
    let mut v___x_845_: u8 = 0;
    let mut v___x_846_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_finished_833_ = lean_ctor_get(v_w_830_, 0);
                v_promise_834_ = lean_ctor_get(v_w_830_, 1);
                v___x_835_ = lean_st_ref_take(v_finished_833_);
                v___x_844_ = (lean_unbox(v___x_835_) as u8);
                lean_dec(v___x_835_);
                if v___x_844_ == 0 {
                    v___x_845_ = 1;
                    v___y_837_ = v___x_845_;
                    state = 1;
                    continue;
                } else {
                    v___x_846_ = 0;
                    v___y_837_ = v___x_846_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_838_ = 1;
                v___x_839_ = lean_box((v___x_838_) as usize);
                v___x_840_ = lean_st_ref_set(v_finished_833_, v___x_839_);
                if v___y_837_ == 0 {
                    v___x_841_ = lean_apply_1(v_lose_831_, lean_box(0));
                    return v___x_841_;
                } else {
                    lean_dec_ref(v_lose_831_);
                    v___x_842_ = l_Std_Async_Waiter_race___at___00Std_Async_Sleep_selector_spec__0___closed__0;
                    v___x_843_ = lean_io_promise_resolve(v___x_842_, v_promise_834_);
                    return v___x_843_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Waiter_race___at___00Std_Async_Sleep_selector_spec__0___boxed(
    mut v_w_847_: *mut LeanObject,
    mut v_lose_848_: *mut LeanObject,
    mut v___y_849_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_850_: *mut LeanObject = core::ptr::null_mut();
    v_res_850_ =
        l_Std_Async_Waiter_race___at___00Std_Async_Sleep_selector_spec__0(v_w_847_, v_lose_848_);
    lean_dec_ref(v_w_847_);
    return v_res_850_;
}
pub unsafe fn l_Std_Async_Sleep_selector___lam__0(
    mut v_x_855_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_860_: u8 = 0;
    let mut v___x_862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_865_: u8 = 0;
    let mut v___x_866_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_855_) == 0 {
                    v_a_857_ = lean_ctor_get(v_x_855_, 0);
                    v_isSharedCheck_865_ = (!lean_is_exclusive(v_x_855_)) as u8;
                    if v_isSharedCheck_865_ == 0 {
                        v___x_859_ = v_x_855_;
                        v_isShared_860_ = v_isSharedCheck_865_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_857_);
                        lean_dec(v_x_855_);
                        v___x_859_ = lean_box(0);
                        v_isShared_860_ = v_isSharedCheck_865_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v_x_855_, 1);
                    v___x_866_ = l_Std_Async_Sleep_selector___lam__0___closed__1;
                    return v___x_866_;
                }
            }
            1 => {
                if v_isShared_860_ == 0 {
                    v___x_862_ = v___x_859_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_864_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_864_, 0, v_a_857_);
                    v___x_862_ = v_reuseFailAlloc_864_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_863_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_863_, 0, v___x_862_);
                return v___x_863_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Sleep_selector___lam__0___boxed(
    mut v_x_867_: *mut LeanObject,
    mut v___y_868_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_869_: *mut LeanObject = core::ptr::null_mut();
    v_res_869_ = l_Std_Async_Sleep_selector___lam__0(v_x_867_);
    return v_res_869_;
}
pub unsafe fn l_Std_Async_Sleep_selector___lam__1(
    mut v_s_870_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_val_873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_879_: u8 = 0;
    let mut v___x_881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_883_: u8 = 0;
    let mut v_a_884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_887_: u8 = 0;
    let mut v___x_889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_891_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_875_ = lean_uv_timer_cancel(v_s_870_);
                if lean_obj_tag(v___x_875_) == 0 {
                    v_a_876_ = lean_ctor_get(v___x_875_, 0);
                    v_isSharedCheck_883_ = (!lean_is_exclusive(v___x_875_)) as u8;
                    if v_isSharedCheck_883_ == 0 {
                        v___x_878_ = v___x_875_;
                        v_isShared_879_ = v_isSharedCheck_883_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_876_);
                        lean_dec(v___x_875_);
                        v___x_878_ = lean_box(0);
                        v_isShared_879_ = v_isSharedCheck_883_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_884_ = lean_ctor_get(v___x_875_, 0);
                    v_isSharedCheck_891_ = (!lean_is_exclusive(v___x_875_)) as u8;
                    if v_isSharedCheck_891_ == 0 {
                        v___x_886_ = v___x_875_;
                        v_isShared_887_ = v_isSharedCheck_891_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_884_);
                        lean_dec(v___x_875_);
                        v___x_886_ = lean_box(0);
                        v_isShared_887_ = v_isSharedCheck_891_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_874_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_874_, 0, v_val_873_);
                return v___x_874_;
            }
            2 => {
                if v_isShared_879_ == 0 {
                    lean_ctor_set_tag(v___x_878_, 1);
                    v___x_881_ = v___x_878_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_882_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_882_, 0, v_a_876_);
                    v___x_881_ = v_reuseFailAlloc_882_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_val_873_ = v___x_881_;
                state = 1;
                continue;
            }
            4 => {
                if v_isShared_887_ == 0 {
                    lean_ctor_set_tag(v___x_886_, 0);
                    v___x_889_ = v___x_886_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_890_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_890_, 0, v_a_884_);
                    v___x_889_ = v_reuseFailAlloc_890_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_val_873_ = v___x_889_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Sleep_selector___lam__1___boxed(
    mut v_s_892_: *mut LeanObject,
    mut v___y_893_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_894_: *mut LeanObject = core::ptr::null_mut();
    v_res_894_ = l_Std_Async_Sleep_selector___lam__1(v_s_892_);
    lean_dec(v_s_892_);
    return v_res_894_;
}
pub unsafe fn l_Std_Async_Sleep_selector___lam__2(
    mut v___x_895_: *mut LeanObject,
) -> *mut LeanObject {
    return v___x_895_;
}
pub unsafe fn l_Std_Async_Sleep_selector___lam__2___boxed(
    mut v___x_897_: *mut LeanObject,
    mut v___y_898_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_899_: *mut LeanObject = core::ptr::null_mut();
    v_res_899_ = l_Std_Async_Sleep_selector___lam__2(v___x_897_);
    return v_res_899_;
}
pub unsafe fn l_Std_Async_Sleep_selector___lam__3(
    mut v_waiter_902_: *mut LeanObject,
    mut v_x_903_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_903_) == 0 {
        let mut v___x_905_: *mut LeanObject = core::ptr::null_mut();
        v___x_905_ = lean_box(0);
        return v___x_905_;
    } else {
        let mut v___f_906_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_907_: *mut LeanObject = core::ptr::null_mut();
        v___f_906_ = l_Std_Async_Sleep_selector___lam__3___closed__0;
        v___x_907_ = l_Std_Async_Waiter_race___at___00Std_Async_Sleep_selector_spec__0(
            v_waiter_902_,
            v___f_906_,
        );
        return v___x_907_;
    }
}
pub unsafe fn l_Std_Async_Sleep_selector___lam__3___boxed(
    mut v_waiter_908_: *mut LeanObject,
    mut v_x_909_: *mut LeanObject,
    mut v___y_910_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_911_: *mut LeanObject = core::ptr::null_mut();
    v_res_911_ = l_Std_Async_Sleep_selector___lam__3(v_waiter_908_, v_x_909_);
    lean_dec(v_x_909_);
    lean_dec_ref(v_waiter_908_);
    return v_res_911_;
}
pub unsafe fn l_Std_Async_Sleep_selector___lam__4(
    mut v___f_912_: *mut LeanObject,
    mut v_x_913_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_918_: u8 = 0;
    let mut v___x_920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_923_: u8 = 0;
    let mut v_a_924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_927_: u8 = 0;
    let mut v___x_928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_930_: u8 = 0;
    let mut v___x_931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_936_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_913_) == 0 {
                    lean_dec_ref(v___f_912_);
                    v_a_915_ = lean_ctor_get(v_x_913_, 0);
                    v_isSharedCheck_923_ = (!lean_is_exclusive(v_x_913_)) as u8;
                    if v_isSharedCheck_923_ == 0 {
                        v___x_917_ = v_x_913_;
                        v_isShared_918_ = v_isSharedCheck_923_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_915_);
                        lean_dec(v_x_913_);
                        v___x_917_ = lean_box(0);
                        v_isShared_918_ = v_isSharedCheck_923_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_924_ = lean_ctor_get(v_x_913_, 0);
                    v_isSharedCheck_936_ = (!lean_is_exclusive(v_x_913_)) as u8;
                    if v_isSharedCheck_936_ == 0 {
                        v___x_926_ = v_x_913_;
                        v_isShared_927_ = v_isSharedCheck_936_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_924_);
                        lean_dec(v_x_913_);
                        v___x_926_ = lean_box(0);
                        v_isShared_927_ = v_isSharedCheck_936_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_918_ == 0 {
                    v___x_920_ = v___x_917_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_922_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_922_, 0, v_a_915_);
                    v___x_920_ = v_reuseFailAlloc_922_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_921_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_921_, 0, v___x_920_);
                return v___x_921_;
            }
            3 => {
                v___x_928_ = lean_io_promise_result_opt(v_a_924_);
                lean_dec(v_a_924_);
                v___x_929_ = lean_unsigned_to_nat(0);
                v___x_930_ = 0;
                v___x_931_ =
                    l_BaseIO_chainTask___redArg(v___x_928_, v___f_912_, v___x_929_, v___x_930_);
                if v_isShared_927_ == 0 {
                    lean_ctor_set(v___x_926_, 0, v___x_931_);
                    v___x_933_ = v___x_926_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_935_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_935_, 0, v___x_931_);
                    v___x_933_ = v_reuseFailAlloc_935_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_934_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_934_, 0, v___x_933_);
                return v___x_934_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Sleep_selector___lam__4___boxed(
    mut v___f_937_: *mut LeanObject,
    mut v_x_938_: *mut LeanObject,
    mut v___y_939_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_940_: *mut LeanObject = core::ptr::null_mut();
    v_res_940_ = l_Std_Async_Sleep_selector___lam__4(v___f_937_, v_x_938_);
    return v_res_940_;
}
pub unsafe fn l_Std_Async_Sleep_selector___lam__5(
    mut v_s_941_: *mut LeanObject,
    mut v_waiter_942_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_950_: u8 = 0;
    let mut v___x_951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_956_: u8 = 0;
    let mut v___x_958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_960_: u8 = 0;
    let mut v_a_961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_964_: u8 = 0;
    let mut v___x_966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_968_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_944_ = lean_alloc_closure(
                    l_Std_Async_Sleep_selector___lam__3___boxed as *mut core::ffi::c_void,
                    3,
                    1,
                );
                lean_closure_set(v___f_944_, 0, v_waiter_942_);
                v___f_945_ = lean_alloc_closure(
                    l_Std_Async_Sleep_selector___lam__4___boxed as *mut core::ffi::c_void,
                    3,
                    1,
                );
                lean_closure_set(v___f_945_, 0, v___f_944_);
                v___x_952_ = lean_uv_timer_next(v_s_941_);
                if lean_obj_tag(v___x_952_) == 0 {
                    v_a_953_ = lean_ctor_get(v___x_952_, 0);
                    v_isSharedCheck_960_ = (!lean_is_exclusive(v___x_952_)) as u8;
                    if v_isSharedCheck_960_ == 0 {
                        v___x_955_ = v___x_952_;
                        v_isShared_956_ = v_isSharedCheck_960_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_953_);
                        lean_dec(v___x_952_);
                        v___x_955_ = lean_box(0);
                        v_isShared_956_ = v_isSharedCheck_960_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_961_ = lean_ctor_get(v___x_952_, 0);
                    v_isSharedCheck_968_ = (!lean_is_exclusive(v___x_952_)) as u8;
                    if v_isSharedCheck_968_ == 0 {
                        v___x_963_ = v___x_952_;
                        v_isShared_964_ = v_isSharedCheck_968_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_961_);
                        lean_dec(v___x_952_);
                        v___x_963_ = lean_box(0);
                        v_isShared_964_ = v_isSharedCheck_968_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_948_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_948_, 0, v_val_947_);
                v___x_949_ = lean_unsigned_to_nat(0);
                v___x_950_ = 0;
                v___x_951_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
                    v___x_949_,
                    v___x_950_,
                    v___x_948_,
                    v___f_945_,
                );
                return v___x_951_;
            }
            2 => {
                if v_isShared_956_ == 0 {
                    lean_ctor_set_tag(v___x_955_, 1);
                    v___x_958_ = v___x_955_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_959_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_959_, 0, v_a_953_);
                    v___x_958_ = v_reuseFailAlloc_959_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_val_947_ = v___x_958_;
                state = 1;
                continue;
            }
            4 => {
                if v_isShared_964_ == 0 {
                    lean_ctor_set_tag(v___x_963_, 0);
                    v___x_966_ = v___x_963_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_967_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_967_, 0, v_a_961_);
                    v___x_966_ = v_reuseFailAlloc_967_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_val_947_ = v___x_966_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Sleep_selector___lam__5___boxed(
    mut v_s_969_: *mut LeanObject,
    mut v_waiter_970_: *mut LeanObject,
    mut v___y_971_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_972_: *mut LeanObject = core::ptr::null_mut();
    v_res_972_ = l_Std_Async_Sleep_selector___lam__5(v_s_969_, v_waiter_970_);
    lean_dec(v_s_969_);
    return v_res_972_;
}
pub unsafe fn l_Std_Async_Sleep_selector___lam__6(
    mut v___f_979_: *mut LeanObject,
    mut v_s_980_: *mut LeanObject,
    mut v_x_981_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_986_: u8 = 0;
    let mut v___x_988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_991_: u8 = 0;
    let mut v_a_992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_995_: u8 = 0;
    let mut v_val_997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1000_: u8 = 0;
    let mut v___x_1001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: u8 = 0;
    let mut v___x_1003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1013_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_981_) == 0 {
                    lean_dec_ref(v___f_979_);
                    v_a_983_ = lean_ctor_get(v_x_981_, 0);
                    v_isSharedCheck_991_ = (!lean_is_exclusive(v_x_981_)) as u8;
                    if v_isSharedCheck_991_ == 0 {
                        v___x_985_ = v_x_981_;
                        v_isShared_986_ = v_isSharedCheck_991_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_983_);
                        lean_dec(v_x_981_);
                        v___x_985_ = lean_box(0);
                        v_isShared_986_ = v_isSharedCheck_991_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_992_ = lean_ctor_get(v_x_981_, 0);
                    v_isSharedCheck_1013_ = (!lean_is_exclusive(v_x_981_)) as u8;
                    if v_isSharedCheck_1013_ == 0 {
                        v___x_994_ = v_x_981_;
                        v_isShared_995_ = v_isSharedCheck_1013_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_992_);
                        lean_dec(v_x_981_);
                        v___x_994_ = lean_box(0);
                        v_isShared_995_ = v_isSharedCheck_1013_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_986_ == 0 {
                    v___x_988_ = v___x_985_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_990_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_990_, 0, v_a_983_);
                    v___x_988_ = v_reuseFailAlloc_990_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_989_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_989_, 0, v___x_988_);
                return v___x_989_;
            }
            3 => {
                v___x_1002_ = (lean_unbox(v_a_992_) as u8);
                if v___x_1002_ == 0 {
                    v___x_1003_ = lean_uv_timer_cancel(v_s_980_);
                    if lean_obj_tag(v___x_1003_) == 0 {
                        v_a_1004_ = lean_ctor_get(v___x_1003_, 0);
                        lean_inc(v_a_1004_);
                        lean_dec_ref_known(v___x_1003_, 1);
                        if v_isShared_995_ == 0 {
                            lean_ctor_set(v___x_994_, 0, v_a_1004_);
                            v___x_1006_ = v___x_994_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_1007_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1007_, 0, v_a_1004_);
                            v___x_1006_ = v_reuseFailAlloc_1007_;
                            state = 5;
                            continue;
                        }
                    } else {
                        v_a_1008_ = lean_ctor_get(v___x_1003_, 0);
                        lean_inc(v_a_1008_);
                        lean_dec_ref_known(v___x_1003_, 1);
                        if v_isShared_995_ == 0 {
                            lean_ctor_set_tag(v___x_994_, 0);
                            lean_ctor_set(v___x_994_, 0, v_a_1008_);
                            v___x_1010_ = v___x_994_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_1011_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1011_, 0, v_a_1008_);
                            v___x_1010_ = v_reuseFailAlloc_1011_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_994_);
                    lean_dec(v_a_992_);
                    lean_dec_ref(v___f_979_);
                    v___x_1012_ = l_Std_Async_Sleep_selector___lam__6___closed__2;
                    return v___x_1012_;
                }
            }
            4 => {
                v___x_998_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_998_, 0, v_val_997_);
                v___x_999_ = lean_unsigned_to_nat(0);
                v___x_1000_ = (lean_unbox(v_a_992_) as u8);
                lean_dec(v_a_992_);
                v___x_1001_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
                    v___x_999_,
                    v___x_1000_,
                    v___x_998_,
                    v___f_979_,
                );
                return v___x_1001_;
            }
            5 => {
                v_val_997_ = v___x_1006_;
                state = 4;
                continue;
            }
            6 => {
                v_val_997_ = v___x_1010_;
                state = 4;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Sleep_selector___lam__6___boxed(
    mut v___f_1014_: *mut LeanObject,
    mut v_s_1015_: *mut LeanObject,
    mut v_x_1016_: *mut LeanObject,
    mut v___y_1017_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1018_: *mut LeanObject = core::ptr::null_mut();
    v_res_1018_ = l_Std_Async_Sleep_selector___lam__6(v___f_1014_, v_s_1015_, v_x_1016_);
    lean_dec(v_s_1015_);
    return v_res_1018_;
}
pub unsafe fn l_Std_Async_Sleep_selector___lam__7(
    mut v___f_1019_: *mut LeanObject,
    mut v_x_1020_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1025_: u8 = 0;
    let mut v___x_1027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1030_: u8 = 0;
    let mut v_a_1031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1034_: u8 = 0;
    let mut v___x_1035_: u8 = 0;
    let mut v___x_1036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1041_: u8 = 0;
    let mut v___x_1042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1044_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1020_) == 0 {
                    lean_dec_ref(v___f_1019_);
                    v_a_1022_ = lean_ctor_get(v_x_1020_, 0);
                    v_isSharedCheck_1030_ = (!lean_is_exclusive(v_x_1020_)) as u8;
                    if v_isSharedCheck_1030_ == 0 {
                        v___x_1024_ = v_x_1020_;
                        v_isShared_1025_ = v_isSharedCheck_1030_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1022_);
                        lean_dec(v_x_1020_);
                        v___x_1024_ = lean_box(0);
                        v_isShared_1025_ = v_isSharedCheck_1030_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1031_ = lean_ctor_get(v_x_1020_, 0);
                    v_isSharedCheck_1044_ = (!lean_is_exclusive(v_x_1020_)) as u8;
                    if v_isSharedCheck_1044_ == 0 {
                        v___x_1033_ = v_x_1020_;
                        v_isShared_1034_ = v_isSharedCheck_1044_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1031_);
                        lean_dec(v_x_1020_);
                        v___x_1033_ = lean_box(0);
                        v_isShared_1034_ = v_isSharedCheck_1044_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1025_ == 0 {
                    v___x_1027_ = v___x_1024_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1029_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_a_1022_);
                    v___x_1027_ = v_reuseFailAlloc_1029_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1028_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1028_, 0, v___x_1027_);
                return v___x_1028_;
            }
            3 => {
                v___x_1035_ = l_IO_Promise_isResolved___redArg(v_a_1031_);
                lean_dec(v_a_1031_);
                v___x_1036_ = lean_box((v___x_1035_) as usize);
                if v_isShared_1034_ == 0 {
                    lean_ctor_set(v___x_1033_, 0, v___x_1036_);
                    v___x_1038_ = v___x_1033_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1043_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1043_, 0, v___x_1036_);
                    v___x_1038_ = v_reuseFailAlloc_1043_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1039_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1039_, 0, v___x_1038_);
                v___x_1040_ = lean_unsigned_to_nat(0);
                v___x_1041_ = 0;
                v___x_1042_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
                    v___x_1040_,
                    v___x_1041_,
                    v___x_1039_,
                    v___f_1019_,
                );
                return v___x_1042_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Sleep_selector___lam__7___boxed(
    mut v___f_1045_: *mut LeanObject,
    mut v_x_1046_: *mut LeanObject,
    mut v___y_1047_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1048_: *mut LeanObject = core::ptr::null_mut();
    v_res_1048_ = l_Std_Async_Sleep_selector___lam__7(v___f_1045_, v_x_1046_);
    return v_res_1048_;
}
pub unsafe fn l_Std_Async_Sleep_selector___lam__8(
    mut v___f_1049_: *mut LeanObject,
    mut v_s_1050_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_val_1053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1056_: u8 = 0;
    let mut v___x_1057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1062_: u8 = 0;
    let mut v___x_1064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1066_: u8 = 0;
    let mut v_a_1067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1070_: u8 = 0;
    let mut v___x_1072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1074_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1058_ = lean_uv_timer_next(v_s_1050_);
                if lean_obj_tag(v___x_1058_) == 0 {
                    v_a_1059_ = lean_ctor_get(v___x_1058_, 0);
                    v_isSharedCheck_1066_ = (!lean_is_exclusive(v___x_1058_)) as u8;
                    if v_isSharedCheck_1066_ == 0 {
                        v___x_1061_ = v___x_1058_;
                        v_isShared_1062_ = v_isSharedCheck_1066_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_1059_);
                        lean_dec(v___x_1058_);
                        v___x_1061_ = lean_box(0);
                        v_isShared_1062_ = v_isSharedCheck_1066_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_1067_ = lean_ctor_get(v___x_1058_, 0);
                    v_isSharedCheck_1074_ = (!lean_is_exclusive(v___x_1058_)) as u8;
                    if v_isSharedCheck_1074_ == 0 {
                        v___x_1069_ = v___x_1058_;
                        v_isShared_1070_ = v_isSharedCheck_1074_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_1067_);
                        lean_dec(v___x_1058_);
                        v___x_1069_ = lean_box(0);
                        v_isShared_1070_ = v_isSharedCheck_1074_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1054_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1054_, 0, v_val_1053_);
                v___x_1055_ = lean_unsigned_to_nat(0);
                v___x_1056_ = 0;
                v___x_1057_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
                    v___x_1055_,
                    v___x_1056_,
                    v___x_1054_,
                    v___f_1049_,
                );
                return v___x_1057_;
            }
            2 => {
                if v_isShared_1062_ == 0 {
                    lean_ctor_set_tag(v___x_1061_, 1);
                    v___x_1064_ = v___x_1061_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1065_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1065_, 0, v_a_1059_);
                    v___x_1064_ = v_reuseFailAlloc_1065_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_val_1053_ = v___x_1064_;
                state = 1;
                continue;
            }
            4 => {
                if v_isShared_1070_ == 0 {
                    lean_ctor_set_tag(v___x_1069_, 0);
                    v___x_1072_ = v___x_1069_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1073_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1073_, 0, v_a_1067_);
                    v___x_1072_ = v_reuseFailAlloc_1073_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_val_1053_ = v___x_1072_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Sleep_selector___lam__8___boxed(
    mut v___f_1075_: *mut LeanObject,
    mut v_s_1076_: *mut LeanObject,
    mut v___y_1077_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1078_: *mut LeanObject = core::ptr::null_mut();
    v_res_1078_ = l_Std_Async_Sleep_selector___lam__8(v___f_1075_, v_s_1076_);
    lean_dec(v_s_1076_);
    return v_res_1078_;
}
pub unsafe fn l_Std_Async_Sleep_selector(mut v_s_1080_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_1081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1087_: *mut LeanObject = core::ptr::null_mut();
    v___f_1081_ = l_Std_Async_Sleep_selector___closed__0;
    lean_inc_n(v_s_1080_, 3);
    v___f_1082_ = lean_alloc_closure(
        l_Std_Async_Sleep_selector___lam__1___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1082_, 0, v_s_1080_);
    v___f_1083_ = lean_alloc_closure(
        l_Std_Async_Sleep_selector___lam__5___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_1083_, 0, v_s_1080_);
    v___f_1084_ = lean_alloc_closure(
        l_Std_Async_Sleep_selector___lam__6___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_1084_, 0, v___f_1081_);
    lean_closure_set(v___f_1084_, 1, v_s_1080_);
    v___f_1085_ = lean_alloc_closure(
        l_Std_Async_Sleep_selector___lam__7___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_1085_, 0, v___f_1084_);
    v___f_1086_ = lean_alloc_closure(
        l_Std_Async_Sleep_selector___lam__8___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_1086_, 0, v___f_1085_);
    lean_closure_set(v___f_1086_, 1, v_s_1080_);
    v___x_1087_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1087_, 0, v___f_1086_);
    lean_ctor_set(v___x_1087_, 1, v___f_1083_);
    lean_ctor_set(v___x_1087_, 2, v___f_1082_);
    return v___x_1087_;
}
pub unsafe fn l_Std_Async_sleep___lam__1(mut v_x_1088_: *mut LeanObject) -> *mut LeanObject {
    let mut v_a_1090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1093_: u8 = 0;
    let mut v___x_1095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1098_: u8 = 0;
    let mut v_a_1099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1102_: u8 = 0;
    let mut v___x_1103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1107_: u8 = 0;
    let mut v___f_1108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1111_: u8 = 0;
    let mut v___x_1112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1116_: u8 = 0;
    let mut v_a_1117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1120_: u8 = 0;
    let mut v___x_1122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1127_: u8 = 0;
    let mut v_isSharedCheck_1128_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1088_) == 0 {
                    v_a_1090_ = lean_ctor_get(v_x_1088_, 0);
                    v_isSharedCheck_1098_ = (!lean_is_exclusive(v_x_1088_)) as u8;
                    if v_isSharedCheck_1098_ == 0 {
                        v___x_1092_ = v_x_1088_;
                        v_isShared_1093_ = v_isSharedCheck_1098_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1090_);
                        lean_dec(v_x_1088_);
                        v___x_1092_ = lean_box(0);
                        v_isShared_1093_ = v_isSharedCheck_1098_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1099_ = lean_ctor_get(v_x_1088_, 0);
                    v_isSharedCheck_1128_ = (!lean_is_exclusive(v_x_1088_)) as u8;
                    if v_isSharedCheck_1128_ == 0 {
                        v___x_1101_ = v_x_1088_;
                        v_isShared_1102_ = v_isSharedCheck_1128_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1099_);
                        lean_dec(v_x_1088_);
                        v___x_1101_ = lean_box(0);
                        v_isShared_1102_ = v_isSharedCheck_1128_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1093_ == 0 {
                    v___x_1095_ = v___x_1092_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1097_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1097_, 0, v_a_1090_);
                    v___x_1095_ = v_reuseFailAlloc_1097_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1096_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1096_, 0, v___x_1095_);
                return v___x_1096_;
            }
            3 => {
                v___x_1103_ = lean_uv_timer_next(v_a_1099_);
                lean_dec(v_a_1099_);
                if lean_obj_tag(v___x_1103_) == 0 {
                    lean_del_object(v___x_1101_);
                    v_a_1104_ = lean_ctor_get(v___x_1103_, 0);
                    v_isSharedCheck_1116_ = (!lean_is_exclusive(v___x_1103_)) as u8;
                    if v_isSharedCheck_1116_ == 0 {
                        v___x_1106_ = v___x_1103_;
                        v_isShared_1107_ = v_isSharedCheck_1116_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_1104_);
                        lean_dec(v___x_1103_);
                        v___x_1106_ = lean_box(0);
                        v_isShared_1107_ = v_isSharedCheck_1116_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_a_1117_ = lean_ctor_get(v___x_1103_, 0);
                    v_isSharedCheck_1127_ = (!lean_is_exclusive(v___x_1103_)) as u8;
                    if v_isSharedCheck_1127_ == 0 {
                        v___x_1119_ = v___x_1103_;
                        v_isShared_1120_ = v_isSharedCheck_1127_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_1117_);
                        lean_dec(v___x_1103_);
                        v___x_1119_ = lean_box(0);
                        v_isShared_1120_ = v_isSharedCheck_1127_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                v___f_1108_ = l_Std_Async_Sleep_wait___closed__1;
                v___x_1109_ = lean_io_promise_result_opt(v_a_1104_);
                lean_dec(v_a_1104_);
                v___x_1110_ = lean_unsigned_to_nat(0);
                v___x_1111_ = 0;
                v___x_1112_ = lean_task_map(v___f_1108_, v___x_1109_, v___x_1110_, v___x_1111_);
                if v_isShared_1107_ == 0 {
                    lean_ctor_set_tag(v___x_1106_, 1);
                    lean_ctor_set(v___x_1106_, 0, v___x_1112_);
                    v___x_1114_ = v___x_1106_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1115_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1115_, 0, v___x_1112_);
                    v___x_1114_ = v_reuseFailAlloc_1115_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1114_;
            }
            6 => {
                if v_isShared_1102_ == 0 {
                    lean_ctor_set_tag(v___x_1101_, 0);
                    lean_ctor_set(v___x_1101_, 0, v_a_1117_);
                    v___x_1122_ = v___x_1101_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1126_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1126_, 0, v_a_1117_);
                    v___x_1122_ = v_reuseFailAlloc_1126_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_1120_ == 0 {
                    lean_ctor_set_tag(v___x_1119_, 0);
                    lean_ctor_set(v___x_1119_, 0, v___x_1122_);
                    v___x_1124_ = v___x_1119_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1125_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1125_, 0, v___x_1122_);
                    v___x_1124_ = v_reuseFailAlloc_1125_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1124_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_sleep___lam__1___boxed(
    mut v_x_1129_: *mut LeanObject,
    mut v___y_1130_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1131_: *mut LeanObject = core::ptr::null_mut();
    v_res_1131_ = l_Std_Async_sleep___lam__1(v_x_1129_);
    return v_res_1131_;
}
pub unsafe fn l_Std_Async_sleep(mut v_duration_1133_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_1135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1141_: u8 = 0;
    let mut v___x_1142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: u64 = 0;
    let mut v___x_1146_: u8 = 0;
    let mut v___x_1147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1151_: u8 = 0;
    let mut v___x_1153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1155_: u8 = 0;
    let mut v_a_1156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1159_: u8 = 0;
    let mut v___x_1161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1163_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1135_ = l_Std_Async_sleep___closed__0;
                v___f_1136_ = l_Std_Async_Sleep_mk___closed__0;
                v___x_1144_ = l_Int_toNat(v_duration_1133_);
                v___x_1145_ = lean_uint64_of_nat(v___x_1144_);
                lean_dec(v___x_1144_);
                v___x_1146_ = 0;
                v___x_1147_ = lean_uv_timer_mk(v___x_1145_, v___x_1146_);
                if lean_obj_tag(v___x_1147_) == 0 {
                    v_a_1148_ = lean_ctor_get(v___x_1147_, 0);
                    v_isSharedCheck_1155_ = (!lean_is_exclusive(v___x_1147_)) as u8;
                    if v_isSharedCheck_1155_ == 0 {
                        v___x_1150_ = v___x_1147_;
                        v_isShared_1151_ = v_isSharedCheck_1155_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_1148_);
                        lean_dec(v___x_1147_);
                        v___x_1150_ = lean_box(0);
                        v_isShared_1151_ = v_isSharedCheck_1155_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_1156_ = lean_ctor_get(v___x_1147_, 0);
                    v_isSharedCheck_1163_ = (!lean_is_exclusive(v___x_1147_)) as u8;
                    if v_isSharedCheck_1163_ == 0 {
                        v___x_1158_ = v___x_1147_;
                        v_isShared_1159_ = v_isSharedCheck_1163_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_1156_);
                        lean_dec(v___x_1147_);
                        v___x_1158_ = lean_box(0);
                        v_isShared_1159_ = v_isSharedCheck_1163_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1139_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1139_, 0, v_val_1138_);
                v___x_1140_ = lean_unsigned_to_nat(0);
                v___x_1141_ = 0;
                v___x_1142_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
                    v___x_1140_,
                    v___x_1141_,
                    v___x_1139_,
                    v___f_1136_,
                );
                v___x_1143_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
                    v___x_1140_,
                    v___x_1141_,
                    v___x_1142_,
                    v___f_1135_,
                );
                return v___x_1143_;
            }
            2 => {
                if v_isShared_1151_ == 0 {
                    lean_ctor_set_tag(v___x_1150_, 1);
                    v___x_1153_ = v___x_1150_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1154_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1154_, 0, v_a_1148_);
                    v___x_1153_ = v_reuseFailAlloc_1154_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_val_1138_ = v___x_1153_;
                state = 1;
                continue;
            }
            4 => {
                if v_isShared_1159_ == 0 {
                    lean_ctor_set_tag(v___x_1158_, 0);
                    v___x_1161_ = v___x_1158_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1162_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_a_1156_);
                    v___x_1161_ = v_reuseFailAlloc_1162_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_val_1138_ = v___x_1161_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_sleep___boxed(
    mut v_duration_1164_: *mut LeanObject,
    mut v_a_1165_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1166_: *mut LeanObject = core::ptr::null_mut();
    v_res_1166_ = l_Std_Async_sleep(v_duration_1164_);
    lean_dec(v_duration_1164_);
    return v_res_1166_;
}
pub unsafe fn l_Std_Async_Selector_sleep___lam__0(
    mut v_x_1167_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1172_: u8 = 0;
    let mut v___x_1174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1177_: u8 = 0;
    let mut v_a_1178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1181_: u8 = 0;
    let mut v___x_1182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1187_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1167_) == 0 {
                    v_a_1169_ = lean_ctor_get(v_x_1167_, 0);
                    v_isSharedCheck_1177_ = (!lean_is_exclusive(v_x_1167_)) as u8;
                    if v_isSharedCheck_1177_ == 0 {
                        v___x_1171_ = v_x_1167_;
                        v_isShared_1172_ = v_isSharedCheck_1177_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1169_);
                        lean_dec(v_x_1167_);
                        v___x_1171_ = lean_box(0);
                        v_isShared_1172_ = v_isSharedCheck_1177_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1178_ = lean_ctor_get(v_x_1167_, 0);
                    v_isSharedCheck_1187_ = (!lean_is_exclusive(v_x_1167_)) as u8;
                    if v_isSharedCheck_1187_ == 0 {
                        v___x_1180_ = v_x_1167_;
                        v_isShared_1181_ = v_isSharedCheck_1187_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1178_);
                        lean_dec(v_x_1167_);
                        v___x_1180_ = lean_box(0);
                        v_isShared_1181_ = v_isSharedCheck_1187_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1172_ == 0 {
                    v___x_1174_ = v___x_1171_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1176_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1176_, 0, v_a_1169_);
                    v___x_1174_ = v_reuseFailAlloc_1176_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1175_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1175_, 0, v___x_1174_);
                return v___x_1175_;
            }
            3 => {
                v___x_1182_ = l_Std_Async_Sleep_selector(v_a_1178_);
                if v_isShared_1181_ == 0 {
                    lean_ctor_set(v___x_1180_, 0, v___x_1182_);
                    v___x_1184_ = v___x_1180_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1186_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1186_, 0, v___x_1182_);
                    v___x_1184_ = v_reuseFailAlloc_1186_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1185_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1185_, 0, v___x_1184_);
                return v___x_1185_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Selector_sleep___lam__0___boxed(
    mut v_x_1188_: *mut LeanObject,
    mut v___y_1189_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1190_: *mut LeanObject = core::ptr::null_mut();
    v_res_1190_ = l_Std_Async_Selector_sleep___lam__0(v_x_1188_);
    return v_res_1190_;
}
pub unsafe fn l_Std_Async_Selector_sleep(mut v_duration_1192_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_1194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: u8 = 0;
    let mut v___x_1201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: u64 = 0;
    let mut v___x_1205_: u8 = 0;
    let mut v___x_1206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1210_: u8 = 0;
    let mut v___x_1212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1214_: u8 = 0;
    let mut v_a_1215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1218_: u8 = 0;
    let mut v___x_1220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1222_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1194_ = l_Std_Async_Selector_sleep___closed__0;
                v___f_1195_ = l_Std_Async_Sleep_mk___closed__0;
                v___x_1203_ = l_Int_toNat(v_duration_1192_);
                v___x_1204_ = lean_uint64_of_nat(v___x_1203_);
                lean_dec(v___x_1203_);
                v___x_1205_ = 0;
                v___x_1206_ = lean_uv_timer_mk(v___x_1204_, v___x_1205_);
                if lean_obj_tag(v___x_1206_) == 0 {
                    v_a_1207_ = lean_ctor_get(v___x_1206_, 0);
                    v_isSharedCheck_1214_ = (!lean_is_exclusive(v___x_1206_)) as u8;
                    if v_isSharedCheck_1214_ == 0 {
                        v___x_1209_ = v___x_1206_;
                        v_isShared_1210_ = v_isSharedCheck_1214_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_1207_);
                        lean_dec(v___x_1206_);
                        v___x_1209_ = lean_box(0);
                        v_isShared_1210_ = v_isSharedCheck_1214_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_1215_ = lean_ctor_get(v___x_1206_, 0);
                    v_isSharedCheck_1222_ = (!lean_is_exclusive(v___x_1206_)) as u8;
                    if v_isSharedCheck_1222_ == 0 {
                        v___x_1217_ = v___x_1206_;
                        v_isShared_1218_ = v_isSharedCheck_1222_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_1215_);
                        lean_dec(v___x_1206_);
                        v___x_1217_ = lean_box(0);
                        v_isShared_1218_ = v_isSharedCheck_1222_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1198_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1198_, 0, v_val_1197_);
                v___x_1199_ = lean_unsigned_to_nat(0);
                v___x_1200_ = 0;
                v___x_1201_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
                    v___x_1199_,
                    v___x_1200_,
                    v___x_1198_,
                    v___f_1195_,
                );
                v___x_1202_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
                    v___x_1199_,
                    v___x_1200_,
                    v___x_1201_,
                    v___f_1194_,
                );
                return v___x_1202_;
            }
            2 => {
                if v_isShared_1210_ == 0 {
                    lean_ctor_set_tag(v___x_1209_, 1);
                    v___x_1212_ = v___x_1209_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1213_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1213_, 0, v_a_1207_);
                    v___x_1212_ = v_reuseFailAlloc_1213_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_val_1197_ = v___x_1212_;
                state = 1;
                continue;
            }
            4 => {
                if v_isShared_1218_ == 0 {
                    lean_ctor_set_tag(v___x_1217_, 0);
                    v___x_1220_ = v___x_1217_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1221_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1221_, 0, v_a_1215_);
                    v___x_1220_ = v_reuseFailAlloc_1221_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_val_1197_ = v___x_1220_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Selector_sleep___boxed(
    mut v_duration_1223_: *mut LeanObject,
    mut v_a_1224_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1225_: *mut LeanObject = core::ptr::null_mut();
    v_res_1225_ = l_Std_Async_Selector_sleep(v_duration_1223_);
    lean_dec(v_duration_1223_);
    return v_res_1225_;
}
pub unsafe fn _init_l_Std_Async_Interval_mk___auto__1___closed__12() -> *mut LeanObject {
    let mut v___x_1252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1253_: *mut LeanObject = core::ptr::null_mut();
    v___x_1252_ = l_Std_Async_Interval_mk___auto__1___closed__10;
    v___x_1253_ = l_Lean_mkAtom(v___x_1252_);
    return v___x_1253_;
}
pub unsafe fn _init_l_Std_Async_Interval_mk___auto__1___closed__13() -> *mut LeanObject {
    let mut v___x_1254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut LeanObject = core::ptr::null_mut();
    v___x_1254_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_Interval_mk___auto__1___closed__12),
        core::ptr::addr_of_mut!(l_Std_Async_Interval_mk___auto__1___closed__12_once),
        _init_l_Std_Async_Interval_mk___auto__1___closed__12,
    );
    v___x_1255_ = l_Std_Async_Interval_mk___auto__1___closed__5;
    v___x_1256_ = lean_array_push(v___x_1255_, v___x_1254_);
    return v___x_1256_;
}
pub unsafe fn _init_l_Std_Async_Interval_mk___auto__1___closed__17() -> *mut LeanObject {
    let mut v___x_1267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1269_: *mut LeanObject = core::ptr::null_mut();
    v___x_1267_ = l_Std_Async_Interval_mk___auto__1___closed__16;
    v___x_1268_ = l_Std_Async_Interval_mk___auto__1___closed__5;
    v___x_1269_ = lean_array_push(v___x_1268_, v___x_1267_);
    return v___x_1269_;
}
pub unsafe fn _init_l_Std_Async_Interval_mk___auto__1___closed__18() -> *mut LeanObject {
    let mut v___x_1270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: *mut LeanObject = core::ptr::null_mut();
    v___x_1270_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_Interval_mk___auto__1___closed__17),
        core::ptr::addr_of_mut!(l_Std_Async_Interval_mk___auto__1___closed__17_once),
        _init_l_Std_Async_Interval_mk___auto__1___closed__17,
    );
    v___x_1271_ = l_Std_Async_Interval_mk___auto__1___closed__15;
    v___x_1272_ = lean_box(2);
    v___x_1273_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_1273_, 0, v___x_1272_);
    lean_ctor_set(v___x_1273_, 1, v___x_1271_);
    lean_ctor_set(v___x_1273_, 2, v___x_1270_);
    return v___x_1273_;
}
pub unsafe fn _init_l_Std_Async_Interval_mk___auto__1___closed__19() -> *mut LeanObject {
    let mut v___x_1274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: *mut LeanObject = core::ptr::null_mut();
    v___x_1274_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_Interval_mk___auto__1___closed__18),
        core::ptr::addr_of_mut!(l_Std_Async_Interval_mk___auto__1___closed__18_once),
        _init_l_Std_Async_Interval_mk___auto__1___closed__18,
    );
    v___x_1275_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_Interval_mk___auto__1___closed__13),
        core::ptr::addr_of_mut!(l_Std_Async_Interval_mk___auto__1___closed__13_once),
        _init_l_Std_Async_Interval_mk___auto__1___closed__13,
    );
    v___x_1276_ = lean_array_push(v___x_1275_, v___x_1274_);
    return v___x_1276_;
}
pub unsafe fn _init_l_Std_Async_Interval_mk___auto__1___closed__20() -> *mut LeanObject {
    let mut v___x_1277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1280_: *mut LeanObject = core::ptr::null_mut();
    v___x_1277_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_Interval_mk___auto__1___closed__19),
        core::ptr::addr_of_mut!(l_Std_Async_Interval_mk___auto__1___closed__19_once),
        _init_l_Std_Async_Interval_mk___auto__1___closed__19,
    );
    v___x_1278_ = l_Std_Async_Interval_mk___auto__1___closed__11;
    v___x_1279_ = lean_box(2);
    v___x_1280_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_1280_, 0, v___x_1279_);
    lean_ctor_set(v___x_1280_, 1, v___x_1278_);
    lean_ctor_set(v___x_1280_, 2, v___x_1277_);
    return v___x_1280_;
}
pub unsafe fn _init_l_Std_Async_Interval_mk___auto__1___closed__21() -> *mut LeanObject {
    let mut v___x_1281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1283_: *mut LeanObject = core::ptr::null_mut();
    v___x_1281_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_Interval_mk___auto__1___closed__20),
        core::ptr::addr_of_mut!(l_Std_Async_Interval_mk___auto__1___closed__20_once),
        _init_l_Std_Async_Interval_mk___auto__1___closed__20,
    );
    v___x_1282_ = l_Std_Async_Interval_mk___auto__1___closed__5;
    v___x_1283_ = lean_array_push(v___x_1282_, v___x_1281_);
    return v___x_1283_;
}
pub unsafe fn _init_l_Std_Async_Interval_mk___auto__1___closed__22() -> *mut LeanObject {
    let mut v___x_1284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1287_: *mut LeanObject = core::ptr::null_mut();
    v___x_1284_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_Interval_mk___auto__1___closed__21),
        core::ptr::addr_of_mut!(l_Std_Async_Interval_mk___auto__1___closed__21_once),
        _init_l_Std_Async_Interval_mk___auto__1___closed__21,
    );
    v___x_1285_ = l_Std_Async_Interval_mk___auto__1___closed__9;
    v___x_1286_ = lean_box(2);
    v___x_1287_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_1287_, 0, v___x_1286_);
    lean_ctor_set(v___x_1287_, 1, v___x_1285_);
    lean_ctor_set(v___x_1287_, 2, v___x_1284_);
    return v___x_1287_;
}
pub unsafe fn _init_l_Std_Async_Interval_mk___auto__1___closed__23() -> *mut LeanObject {
    let mut v___x_1288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1290_: *mut LeanObject = core::ptr::null_mut();
    v___x_1288_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_Interval_mk___auto__1___closed__22),
        core::ptr::addr_of_mut!(l_Std_Async_Interval_mk___auto__1___closed__22_once),
        _init_l_Std_Async_Interval_mk___auto__1___closed__22,
    );
    v___x_1289_ = l_Std_Async_Interval_mk___auto__1___closed__5;
    v___x_1290_ = lean_array_push(v___x_1289_, v___x_1288_);
    return v___x_1290_;
}
pub unsafe fn _init_l_Std_Async_Interval_mk___auto__1___closed__24() -> *mut LeanObject {
    let mut v___x_1291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: *mut LeanObject = core::ptr::null_mut();
    v___x_1291_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_Interval_mk___auto__1___closed__23),
        core::ptr::addr_of_mut!(l_Std_Async_Interval_mk___auto__1___closed__23_once),
        _init_l_Std_Async_Interval_mk___auto__1___closed__23,
    );
    v___x_1292_ = l_Std_Async_Interval_mk___auto__1___closed__7;
    v___x_1293_ = lean_box(2);
    v___x_1294_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_1294_, 0, v___x_1293_);
    lean_ctor_set(v___x_1294_, 1, v___x_1292_);
    lean_ctor_set(v___x_1294_, 2, v___x_1291_);
    return v___x_1294_;
}
pub unsafe fn _init_l_Std_Async_Interval_mk___auto__1___closed__25() -> *mut LeanObject {
    let mut v___x_1295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1297_: *mut LeanObject = core::ptr::null_mut();
    v___x_1295_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_Interval_mk___auto__1___closed__24),
        core::ptr::addr_of_mut!(l_Std_Async_Interval_mk___auto__1___closed__24_once),
        _init_l_Std_Async_Interval_mk___auto__1___closed__24,
    );
    v___x_1296_ = l_Std_Async_Interval_mk___auto__1___closed__5;
    v___x_1297_ = lean_array_push(v___x_1296_, v___x_1295_);
    return v___x_1297_;
}
pub unsafe fn _init_l_Std_Async_Interval_mk___auto__1___closed__26() -> *mut LeanObject {
    let mut v___x_1298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut LeanObject = core::ptr::null_mut();
    v___x_1298_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_Interval_mk___auto__1___closed__25),
        core::ptr::addr_of_mut!(l_Std_Async_Interval_mk___auto__1___closed__25_once),
        _init_l_Std_Async_Interval_mk___auto__1___closed__25,
    );
    v___x_1299_ = l_Std_Async_Interval_mk___auto__1___closed__4;
    v___x_1300_ = lean_box(2);
    v___x_1301_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_1301_, 0, v___x_1300_);
    lean_ctor_set(v___x_1301_, 1, v___x_1299_);
    lean_ctor_set(v___x_1301_, 2, v___x_1298_);
    return v___x_1301_;
}
pub unsafe fn _init_l_Std_Async_Interval_mk___auto__1() -> *mut LeanObject {
    let mut v___x_1302_: *mut LeanObject = core::ptr::null_mut();
    v___x_1302_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Async_Interval_mk___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Std_Async_Interval_mk___auto__1___closed__26_once),
        _init_l_Std_Async_Interval_mk___auto__1___closed__26,
    );
    return v___x_1302_;
}
pub unsafe fn l_Std_Async_Interval_mk___redArg(
    mut v_duration_1303_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: u64 = 0;
    let mut v___x_1307_: u8 = 0;
    let mut v___x_1308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1312_: u8 = 0;
    let mut v___x_1314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1316_: u8 = 0;
    let mut v_a_1317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1320_: u8 = 0;
    let mut v___x_1322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1324_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1305_ = l_Int_toNat(v_duration_1303_);
                v___x_1306_ = lean_uint64_of_nat(v___x_1305_);
                lean_dec(v___x_1305_);
                v___x_1307_ = 1;
                v___x_1308_ = lean_uv_timer_mk(v___x_1306_, v___x_1307_);
                if lean_obj_tag(v___x_1308_) == 0 {
                    v_a_1309_ = lean_ctor_get(v___x_1308_, 0);
                    v_isSharedCheck_1316_ = (!lean_is_exclusive(v___x_1308_)) as u8;
                    if v_isSharedCheck_1316_ == 0 {
                        v___x_1311_ = v___x_1308_;
                        v_isShared_1312_ = v_isSharedCheck_1316_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1309_);
                        lean_dec(v___x_1308_);
                        v___x_1311_ = lean_box(0);
                        v_isShared_1312_ = v_isSharedCheck_1316_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1317_ = lean_ctor_get(v___x_1308_, 0);
                    v_isSharedCheck_1324_ = (!lean_is_exclusive(v___x_1308_)) as u8;
                    if v_isSharedCheck_1324_ == 0 {
                        v___x_1319_ = v___x_1308_;
                        v_isShared_1320_ = v_isSharedCheck_1324_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1317_);
                        lean_dec(v___x_1308_);
                        v___x_1319_ = lean_box(0);
                        v_isShared_1320_ = v_isSharedCheck_1324_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1312_ == 0 {
                    v___x_1314_ = v___x_1311_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1315_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1315_, 0, v_a_1309_);
                    v___x_1314_ = v_reuseFailAlloc_1315_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1314_;
            }
            3 => {
                if v_isShared_1320_ == 0 {
                    v___x_1322_ = v___x_1319_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1323_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1323_, 0, v_a_1317_);
                    v___x_1322_ = v_reuseFailAlloc_1323_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1322_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Interval_mk___redArg___boxed(
    mut v_duration_1325_: *mut LeanObject,
    mut v_a_1326_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1327_: *mut LeanObject = core::ptr::null_mut();
    v_res_1327_ = l_Std_Async_Interval_mk___redArg(v_duration_1325_);
    lean_dec(v_duration_1325_);
    return v_res_1327_;
}
pub unsafe fn l_Std_Async_Interval_mk(
    mut v_duration_1328_: *mut LeanObject,
    mut v_x_1329_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: u64 = 0;
    let mut v___x_1333_: u8 = 0;
    let mut v___x_1334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1338_: u8 = 0;
    let mut v___x_1340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1342_: u8 = 0;
    let mut v_a_1343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1346_: u8 = 0;
    let mut v___x_1348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1350_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1331_ = l_Int_toNat(v_duration_1328_);
                v___x_1332_ = lean_uint64_of_nat(v___x_1331_);
                lean_dec(v___x_1331_);
                v___x_1333_ = 1;
                v___x_1334_ = lean_uv_timer_mk(v___x_1332_, v___x_1333_);
                if lean_obj_tag(v___x_1334_) == 0 {
                    v_a_1335_ = lean_ctor_get(v___x_1334_, 0);
                    v_isSharedCheck_1342_ = (!lean_is_exclusive(v___x_1334_)) as u8;
                    if v_isSharedCheck_1342_ == 0 {
                        v___x_1337_ = v___x_1334_;
                        v_isShared_1338_ = v_isSharedCheck_1342_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1335_);
                        lean_dec(v___x_1334_);
                        v___x_1337_ = lean_box(0);
                        v_isShared_1338_ = v_isSharedCheck_1342_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1343_ = lean_ctor_get(v___x_1334_, 0);
                    v_isSharedCheck_1350_ = (!lean_is_exclusive(v___x_1334_)) as u8;
                    if v_isSharedCheck_1350_ == 0 {
                        v___x_1345_ = v___x_1334_;
                        v_isShared_1346_ = v_isSharedCheck_1350_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1343_);
                        lean_dec(v___x_1334_);
                        v___x_1345_ = lean_box(0);
                        v_isShared_1346_ = v_isSharedCheck_1350_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1338_ == 0 {
                    v___x_1340_ = v___x_1337_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1341_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1341_, 0, v_a_1335_);
                    v___x_1340_ = v_reuseFailAlloc_1341_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1340_;
            }
            3 => {
                if v_isShared_1346_ == 0 {
                    v___x_1348_ = v___x_1345_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1349_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1349_, 0, v_a_1343_);
                    v___x_1348_ = v_reuseFailAlloc_1349_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1348_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Interval_mk___boxed(
    mut v_duration_1351_: *mut LeanObject,
    mut v_x_1352_: *mut LeanObject,
    mut v_a_1353_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1354_: *mut LeanObject = core::ptr::null_mut();
    v_res_1354_ = l_Std_Async_Interval_mk(v_duration_1351_, v_x_1352_);
    lean_dec(v_duration_1351_);
    return v_res_1354_;
}
pub unsafe fn l_Std_Async_Interval_tick(mut v_i_1355_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1361_: u8 = 0;
    let mut v___f_1362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: u8 = 0;
    let mut v___x_1366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1370_: u8 = 0;
    let mut v_a_1371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1374_: u8 = 0;
    let mut v___x_1376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1379_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1357_ = lean_uv_timer_next(v_i_1355_);
                if lean_obj_tag(v___x_1357_) == 0 {
                    v_a_1358_ = lean_ctor_get(v___x_1357_, 0);
                    v_isSharedCheck_1370_ = (!lean_is_exclusive(v___x_1357_)) as u8;
                    if v_isSharedCheck_1370_ == 0 {
                        v___x_1360_ = v___x_1357_;
                        v_isShared_1361_ = v_isSharedCheck_1370_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1358_);
                        lean_dec(v___x_1357_);
                        v___x_1360_ = lean_box(0);
                        v_isShared_1361_ = v_isSharedCheck_1370_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1371_ = lean_ctor_get(v___x_1357_, 0);
                    v_isSharedCheck_1379_ = (!lean_is_exclusive(v___x_1357_)) as u8;
                    if v_isSharedCheck_1379_ == 0 {
                        v___x_1373_ = v___x_1357_;
                        v_isShared_1374_ = v_isSharedCheck_1379_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1371_);
                        lean_dec(v___x_1357_);
                        v___x_1373_ = lean_box(0);
                        v_isShared_1374_ = v_isSharedCheck_1379_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___f_1362_ = l_Std_Async_Sleep_wait___closed__1;
                v___x_1363_ = lean_io_promise_result_opt(v_a_1358_);
                lean_dec(v_a_1358_);
                v___x_1364_ = lean_unsigned_to_nat(0);
                v___x_1365_ = 0;
                v___x_1366_ = lean_task_map(v___f_1362_, v___x_1363_, v___x_1364_, v___x_1365_);
                if v_isShared_1361_ == 0 {
                    lean_ctor_set_tag(v___x_1360_, 1);
                    lean_ctor_set(v___x_1360_, 0, v___x_1366_);
                    v___x_1368_ = v___x_1360_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1369_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1369_, 0, v___x_1366_);
                    v___x_1368_ = v_reuseFailAlloc_1369_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1368_;
            }
            3 => {
                if v_isShared_1374_ == 0 {
                    lean_ctor_set_tag(v___x_1373_, 0);
                    v___x_1376_ = v___x_1373_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1378_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1378_, 0, v_a_1371_);
                    v___x_1376_ = v_reuseFailAlloc_1378_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1377_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1377_, 0, v___x_1376_);
                return v___x_1377_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Interval_tick___boxed(
    mut v_i_1380_: *mut LeanObject,
    mut v_a_1381_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1382_: *mut LeanObject = core::ptr::null_mut();
    v_res_1382_ = l_Std_Async_Interval_tick(v_i_1380_);
    lean_dec(v_i_1380_);
    return v_res_1382_;
}
pub unsafe fn l_Std_Async_Interval_reset(mut v_i_1383_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1385_: *mut LeanObject = core::ptr::null_mut();
    v___x_1385_ = lean_uv_timer_reset(v_i_1383_);
    return v___x_1385_;
}
pub unsafe fn l_Std_Async_Interval_reset___boxed(
    mut v_i_1386_: *mut LeanObject,
    mut v_a_1387_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1388_: *mut LeanObject = core::ptr::null_mut();
    v_res_1388_ = l_Std_Async_Interval_reset(v_i_1386_);
    lean_dec(v_i_1386_);
    return v_res_1388_;
}
pub unsafe fn l_Std_Async_Interval_stop(mut v_i_1389_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1391_: *mut LeanObject = core::ptr::null_mut();
    v___x_1391_ = lean_uv_timer_stop(v_i_1389_);
    return v___x_1391_;
}
pub unsafe fn l_Std_Async_Interval_stop___boxed(
    mut v_i_1392_: *mut LeanObject,
    mut v_a_1393_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1394_: *mut LeanObject = core::ptr::null_mut();
    v_res_1394_ = l_Std_Async_Interval_stop(v_i_1392_);
    lean_dec(v_i_1392_);
    return v_res_1394_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Async_Timer(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Time(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Internal_UV_Timer(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Async_Select(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Async_Timer(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    l_Std_Async_Interval_mk___auto__1 = _init_l_Std_Async_Interval_mk___auto__1();
    lean_mark_persistent(l_Std_Async_Interval_mk___auto__1);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Async_Timer(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Time(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Internal_UV_Timer(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Async_Select(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Async_Timer(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Async_Timer(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Async_Timer(builtin);
}
