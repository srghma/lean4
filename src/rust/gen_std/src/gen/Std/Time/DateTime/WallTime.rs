// Lean compiler output
// Module: Std.Time.DateTime.WallTime
// Imports: Init.System.IO Std.Time.Duration
use crate::r#gen::Init::Data::Int::Repr::l_Int_repr;
use crate::r#gen::Init::Data::Ord::Basic::l_compareOn___boxed;
use crate::r#gen::Init::Data::Rat::Basic::l_Rat_ofInt;
use crate::r#gen::Init::Data::Repr::{l_Repr_addAppParen, l_String_quote};
use crate::r#gen::Init::System::IO::{
    initialize_Init_System_IO, runtime_initialize_Init_System_IO,
};
use crate::r#gen::Std::Time::Duration::{
    initialize_Std_Time_Duration, l_Std_Time_Duration_instDecidableLe,
    l_Std_Time_Duration_instDecidableLt, l_Std_Time_Duration_ofNanoseconds,
    l_Std_Time_instDecidableEqDuration_decEq, l_Std_Time_instOrdDuration,
    l_Std_Time_instToStringDuration_leftPad, runtime_initialize_Std_Time_Duration,
};
use crate::r#gen::Std::Time::Time::Unit::Nanosecond::l_Std_Time_Nanosecond_instReprOrdinal___lam__0;
use crate::ffi::{
    lean_int_add, lean_int_dec_eq, lean_int_dec_lt, lean_int_mul, lean_int_neg, lean_nat_to_int,
};
use crate::ffi::lean_int_div;
use crate::ffi::lean_string_length;
use crate::ffi::lean_string_append;
pub static l_Std_Time_instReprWallTime_repr___redArg___closed__0_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [123, 32, 0],
};
static mut l_Std_Time_instReprWallTime_repr___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprWallTime_repr___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprWallTime_repr___redArg___closed__1_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [118, 97, 108, 0],
};
static mut l_Std_Time_instReprWallTime_repr___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprWallTime_repr___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprWallTime_repr___redArg___closed__2_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_instReprWallTime_repr___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_instReprWallTime_repr___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprWallTime_repr___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprWallTime_repr___redArg___closed__3_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_instReprWallTime_repr___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_instReprWallTime_repr___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprWallTime_repr___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprWallTime_repr___redArg___closed__4_value:
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
    m_data: [32, 58, 61, 32, 0],
};
static mut l_Std_Time_instReprWallTime_repr___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprWallTime_repr___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprWallTime_repr___redArg___closed__5_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_instReprWallTime_repr___redArg___closed__4_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_instReprWallTime_repr___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprWallTime_repr___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprWallTime_repr___redArg___closed__6_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_instReprWallTime_repr___redArg___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_instReprWallTime_repr___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_instReprWallTime_repr___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprWallTime_repr___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_instReprWallTime_repr___redArg___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instReprWallTime_repr___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_instReprWallTime_repr___redArg___closed__8_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [115, 0],
};
static mut l_Std_Time_instReprWallTime_repr___redArg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprWallTime_repr___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprWallTime_repr___redArg___closed__9_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [32, 125, 0],
};
static mut l_Std_Time_instReprWallTime_repr___redArg___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprWallTime_repr___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_instReprWallTime_repr___redArg___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instReprWallTime_repr___redArg___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instReprWallTime_repr___redArg___closed__11_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instReprWallTime_repr___redArg___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_instReprWallTime_repr___redArg___closed__12_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_instReprWallTime_repr___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_instReprWallTime_repr___redArg___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprWallTime_repr___redArg___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprWallTime_repr___redArg___closed__13_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_instReprWallTime_repr___redArg___closed__9_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_instReprWallTime_repr___redArg___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprWallTime_repr___redArg___closed__13_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_instReprWallTime_repr___redArg___closed__14_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instReprWallTime_repr___redArg___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_instReprWallTime_repr___redArg___closed__15_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [46, 0],
};
static mut l_Std_Time_instReprWallTime_repr___redArg___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprWallTime_repr___redArg___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprWallTime_repr___redArg___closed__16_value:
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
static mut l_Std_Time_instReprWallTime_repr___redArg___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprWallTime_repr___redArg___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprWallTime_repr___redArg___closed__17_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [45, 0],
};
static mut l_Std_Time_instReprWallTime_repr___redArg___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprWallTime_repr___redArg___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprWallTime___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instReprWallTime_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instReprWallTime___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprWallTime___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_instReprWallTime: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprWallTime___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_instInhabitedWallTime_default___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedWallTime_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_instInhabitedWallTime_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_instInhabitedWallTime: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_instLEWallTime: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Std_Time_instLTWallTime: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Time_instOrdWallTime___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instOrdWallTime___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instOrdWallTime___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdWallTime___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_instOrdWallTime___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instOrdWallTime___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_instOrdWallTime: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Time_instToStringWallTime___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instToStringWallTime___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instToStringWallTime___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instToStringWallTime___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_instToStringWallTime: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instToStringWallTime___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprWallTime__1___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        87, 97, 108, 108, 84, 105, 109, 101, 46, 111, 102, 78, 97, 110, 111, 115, 101, 99, 111,
        110, 100, 115, 32, 0,
    ],
};
static mut l_Std_Time_instReprWallTime__1___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprWallTime__1___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprWallTime__1___lam__0___closed__1_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_instReprWallTime__1___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_instReprWallTime__1___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprWallTime__1___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_instReprWallTime__1___lam__0___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instReprWallTime__1___lam__0___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_instReprWallTime__1___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instReprWallTime__1___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instReprWallTime__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprWallTime__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_instReprWallTime__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprWallTime__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_WallTime_toMinutes___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_WallTime_toMinutes___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_WallTime_toDays___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_WallTime_toDays___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_WallTime_ofMilliseconds___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_WallTime_ofMilliseconds___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_WallTime_subSeconds___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_WallTime_subSeconds___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_WallTime_addHours___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_WallTime_addHours___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_WallTime_instHAddDuration___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_WallTime_addDuration___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_WallTime_instHAddDuration___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_WallTime_instHAddDuration___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_WallTime_instHAddDuration: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_WallTime_instHAddDuration___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_WallTime_instHSubDuration___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_WallTime_subDuration___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_WallTime_instHSubDuration___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_WallTime_instHSubDuration___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_WallTime_instHSubDuration: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_WallTime_instHSubDuration___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_WallTime_instHAddOffset___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_WallTime_addDays___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_WallTime_instHAddOffset___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_WallTime_instHAddOffset___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_WallTime_instHAddOffset: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_WallTime_instHAddOffset___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_WallTime_instHSubOffset___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_WallTime_subDays___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_WallTime_instHSubOffset___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_WallTime_instHSubOffset___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_WallTime_instHSubOffset: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_WallTime_instHSubOffset___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_WallTime_instHAddOffset__1___closed__0_value:
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
    m_fun: l_Std_Time_WallTime_addWeeks___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_WallTime_instHAddOffset__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_WallTime_instHAddOffset__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_WallTime_instHAddOffset__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_WallTime_instHAddOffset__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_WallTime_instHSubOffset__1___closed__0_value:
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
    m_fun: l_Std_Time_WallTime_subWeeks___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_WallTime_instHSubOffset__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_WallTime_instHSubOffset__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_WallTime_instHSubOffset__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_WallTime_instHSubOffset__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_WallTime_instHAddOffset__2___closed__0_value:
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
    m_fun: l_Std_Time_WallTime_addHours___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_WallTime_instHAddOffset__2___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_WallTime_instHAddOffset__2___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_WallTime_instHAddOffset__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_WallTime_instHAddOffset__2___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_WallTime_instHSubOffset__2___closed__0_value:
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
    m_fun: l_Std_Time_WallTime_subHours___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_WallTime_instHSubOffset__2___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_WallTime_instHSubOffset__2___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_WallTime_instHSubOffset__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_WallTime_instHSubOffset__2___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_WallTime_instHAddOffset__3___closed__0_value:
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
    m_fun: l_Std_Time_WallTime_addMinutes___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_WallTime_instHAddOffset__3___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_WallTime_instHAddOffset__3___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_WallTime_instHAddOffset__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_WallTime_instHAddOffset__3___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_WallTime_instHSubOffset__3___closed__0_value:
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
    m_fun: l_Std_Time_WallTime_subMinutes___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_WallTime_instHSubOffset__3___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_WallTime_instHSubOffset__3___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_WallTime_instHSubOffset__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_WallTime_instHSubOffset__3___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_WallTime_instHAddOffset__4___closed__0_value:
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
    m_fun: l_Std_Time_WallTime_addSeconds___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_WallTime_instHAddOffset__4___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_WallTime_instHAddOffset__4___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_WallTime_instHAddOffset__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_WallTime_instHAddOffset__4___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_WallTime_instHSubOffset__4___closed__0_value:
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
    m_fun: l_Std_Time_WallTime_subSeconds___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_WallTime_instHSubOffset__4___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_WallTime_instHSubOffset__4___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_WallTime_instHSubOffset__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_WallTime_instHSubOffset__4___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_WallTime_instHAddOffset__5___closed__0_value:
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
    m_fun: l_Std_Time_WallTime_addMilliseconds___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_WallTime_instHAddOffset__5___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_WallTime_instHAddOffset__5___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_WallTime_instHAddOffset__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_WallTime_instHAddOffset__5___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_WallTime_instHSubOffset__5___closed__0_value:
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
    m_fun: l_Std_Time_WallTime_subMilliseconds___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_WallTime_instHSubOffset__5___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_WallTime_instHSubOffset__5___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_WallTime_instHSubOffset__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_WallTime_instHSubOffset__5___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_WallTime_instHAddOffset__6___closed__0_value:
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
    m_fun: l_Std_Time_WallTime_addNanoseconds___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_WallTime_instHAddOffset__6___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_WallTime_instHAddOffset__6___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_WallTime_instHAddOffset__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_WallTime_instHAddOffset__6___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_WallTime_instHSubOffset__6___closed__0_value:
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
    m_fun: l_Std_Time_WallTime_subNanoseconds___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_WallTime_instHSubOffset__6___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_WallTime_instHSubOffset__6___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_WallTime_instHSubOffset__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_WallTime_instHSubOffset__6___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_WallTime_instHSubDuration__1___closed__0_value:
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
    m_fun: l_Std_Time_WallTime_instHSubDuration__1___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_WallTime_instHSubDuration__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_WallTime_instHSubDuration__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_WallTime_instHSubDuration__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_WallTime_instHSubDuration__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Nat_cast___at___00Std_Time_instReprWallTime_repr_spec__0(
    mut v_a_581_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_582_ = lean_nat_to_int(v_a_581_);
    return v___x_582_;
}
pub unsafe fn _init_l_Std_Time_instReprWallTime_repr___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_596_ = crate::leanh::lean_unsigned_to_nat(7);
    v___x_597_ = lean_nat_to_int(v___x_596_);
    return v___x_597_;
}
pub unsafe fn _init_l_Std_Time_instReprWallTime_repr___redArg___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_600_ = l_Std_Time_instReprWallTime_repr___redArg___closed__0;
    v___x_601_ = lean_string_length(v___x_600_);
    return v___x_601_;
}
pub unsafe fn _init_l_Std_Time_instReprWallTime_repr___redArg___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_602_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime_repr___redArg___closed__10),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime_repr___redArg___closed__10_once),
        _init_l_Std_Time_instReprWallTime_repr___redArg___closed__10,
    );
    v___x_603_ = lean_nat_to_int(v___x_602_);
    return v___x_603_;
}
pub unsafe fn _init_l_Std_Time_instReprWallTime_repr___redArg___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_608_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_609_ = lean_nat_to_int(v___x_608_);
    return v___x_609_;
}
pub unsafe fn l_Std_Time_instReprWallTime_repr___redArg(
    mut v_x_613_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_second_614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_618_: u8 = 0;
    let mut v___x_619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_631_: u8 = 0;
    let mut v___x_632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_649_: u8 = 0;
    let mut v___x_650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_657_: u8 = 0;
    let mut v___x_658_: u8 = 0;
    let mut v___x_659_: u8 = 0;
    let mut v___x_660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_668_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_second_614_ = crate::leanh::lean_ctor_get(v_x_613_, 0);
                v_nano_615_ = crate::leanh::lean_ctor_get(v_x_613_, 1);
                v_isSharedCheck_668_ = (!crate::leanh::lean_is_exclusive(v_x_613_)) as u8;
                if v_isSharedCheck_668_ == 0 {
                    v___x_617_ = v_x_613_;
                    v_isShared_618_ = v_isSharedCheck_668_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nano_615_);
                    crate::leanh::lean_inc(v_second_614_);
                    crate::leanh::lean_dec(v_x_613_);
                    v___x_617_ = crate::leanh::lean_box(0);
                    v_isShared_618_ = v_isSharedCheck_668_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_619_ = l_Std_Time_instReprWallTime_repr___redArg___closed__6;
                v___x_620_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime_repr___redArg___closed__7),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprWallTime_repr___redArg___closed__7_once
                    ),
                    _init_l_Std_Time_instReprWallTime_repr___redArg___closed__7,
                );
                v___x_656_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime_repr___redArg___closed__14),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprWallTime_repr___redArg___closed__14_once
                    ),
                    _init_l_Std_Time_instReprWallTime_repr___redArg___closed__14,
                );
                v___x_657_ = lean_int_dec_lt(v___x_656_, v_second_614_);
                if v___x_657_ == 0 {
                    v___x_658_ = lean_int_dec_lt(v_second_614_, v___x_656_);
                    if v___x_658_ == 0 {
                        v___x_659_ = lean_int_dec_lt(v_nano_615_, v___x_656_);
                        if v___x_659_ == 0 {
                            v___x_660_ = l_Std_Time_instReprWallTime_repr___redArg___closed__16;
                            crate::leanh::lean_inc(v_nano_615_);
                            v_fst_643_ = v___x_660_;
                            v_fst_644_ = v_second_614_;
                            v_snd_645_ = v_nano_615_;
                            state = 4;
                            continue;
                        } else {
                            v___x_661_ = l_Std_Time_instReprWallTime_repr___redArg___closed__17;
                            v___x_662_ = lean_int_neg(v_second_614_);
                            crate::leanh::lean_dec(v_second_614_);
                            v___x_663_ = lean_int_neg(v_nano_615_);
                            v_fst_643_ = v___x_661_;
                            v_fst_644_ = v___x_662_;
                            v_snd_645_ = v___x_663_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v___x_664_ = l_Std_Time_instReprWallTime_repr___redArg___closed__17;
                        v___x_665_ = lean_int_neg(v_second_614_);
                        crate::leanh::lean_dec(v_second_614_);
                        v___x_666_ = lean_int_neg(v_nano_615_);
                        v_fst_643_ = v___x_664_;
                        v_fst_644_ = v___x_665_;
                        v_snd_645_ = v___x_666_;
                        state = 4;
                        continue;
                    }
                } else {
                    v___x_667_ = l_Std_Time_instReprWallTime_repr___redArg___closed__16;
                    crate::leanh::lean_inc(v_nano_615_);
                    v_fst_643_ = v___x_667_;
                    v_fst_644_ = v_second_614_;
                    v_snd_645_ = v_nano_615_;
                    state = 4;
                    continue;
                }
            }
            2 => {
                v___x_624_ = lean_string_append(v___y_622_, v___y_623_);
                crate::leanh::lean_dec_ref(v___y_623_);
                v___x_625_ = l_Std_Time_instReprWallTime_repr___redArg___closed__8;
                v___x_626_ = lean_string_append(v___x_624_, v___x_625_);
                v___x_627_ = l_String_quote(v___x_626_);
                v___x_628_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_628_, 0, v___x_627_);
                if v_isShared_618_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_617_, 4);
                    crate::leanh::lean_ctor_set(v___x_617_, 1, v___x_628_);
                    crate::leanh::lean_ctor_set(v___x_617_, 0, v___x_620_);
                    v___x_630_ = v___x_617_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_641_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_641_, 0, v___x_620_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_641_, 1, v___x_628_);
                    v___x_630_ = v_reuseFailAlloc_641_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_631_ = 0;
                v___x_632_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_632_, 0, v___x_630_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_632_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_631_,
                );
                v___x_633_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_633_, 0, v___x_619_);
                crate::leanh::lean_ctor_set(v___x_633_, 1, v___x_632_);
                v___x_634_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime_repr___redArg___closed__11),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprWallTime_repr___redArg___closed__11_once
                    ),
                    _init_l_Std_Time_instReprWallTime_repr___redArg___closed__11,
                );
                v___x_635_ = l_Std_Time_instReprWallTime_repr___redArg___closed__12;
                v___x_636_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_636_, 0, v___x_635_);
                crate::leanh::lean_ctor_set(v___x_636_, 1, v___x_633_);
                v___x_637_ = l_Std_Time_instReprWallTime_repr___redArg___closed__13;
                v___x_638_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_638_, 0, v___x_636_);
                crate::leanh::lean_ctor_set(v___x_638_, 1, v___x_637_);
                v___x_639_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_639_, 0, v___x_634_);
                crate::leanh::lean_ctor_set(v___x_639_, 1, v___x_638_);
                v___x_640_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_640_, 0, v___x_639_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_640_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_631_,
                );
                return v___x_640_;
            }
            4 => {
                v___x_646_ = l_Int_repr(v_fst_644_);
                crate::leanh::lean_dec(v_fst_644_);
                crate::leanh::lean_inc_ref(v_fst_643_);
                v___x_647_ = lean_string_append(v_fst_643_, v___x_646_);
                crate::leanh::lean_dec_ref(v___x_646_);
                v___x_648_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime_repr___redArg___closed__14),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprWallTime_repr___redArg___closed__14_once
                    ),
                    _init_l_Std_Time_instReprWallTime_repr___redArg___closed__14,
                );
                v___x_649_ = lean_int_dec_eq(v_nano_615_, v___x_648_);
                crate::leanh::lean_dec(v_nano_615_);
                if v___x_649_ == 0 {
                    v___x_650_ = l_Std_Time_instReprWallTime_repr___redArg___closed__15;
                    v___x_651_ = crate::leanh::lean_unsigned_to_nat(9);
                    v___x_652_ = l_Int_repr(v_snd_645_);
                    crate::leanh::lean_dec(v_snd_645_);
                    v___x_653_ = l_Std_Time_instToStringDuration_leftPad(v___x_651_, v___x_652_);
                    crate::leanh::lean_dec_ref(v___x_652_);
                    v___x_654_ = lean_string_append(v___x_650_, v___x_653_);
                    crate::leanh::lean_dec_ref(v___x_653_);
                    v___y_622_ = v___x_647_;
                    v___y_623_ = v___x_654_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_snd_645_);
                    v___x_655_ = l_Std_Time_instReprWallTime_repr___redArg___closed__16;
                    v___y_622_ = v___x_647_;
                    v___y_623_ = v___x_655_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_instReprWallTime_repr(
    mut v_x_669_: *mut crate::leanh::LeanObject,
    mut v_prec_670_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_671_ = l_Std_Time_instReprWallTime_repr___redArg(v_x_669_);
    return v___x_671_;
}
pub unsafe fn l_Std_Time_instReprWallTime_repr___boxed(
    mut v_x_672_: *mut crate::leanh::LeanObject,
    mut v_prec_673_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_674_ = l_Std_Time_instReprWallTime_repr(v_x_672_, v_prec_673_);
    crate::leanh::lean_dec(v_prec_673_);
    return v_res_674_;
}
pub unsafe fn l_Std_Time_instDecidableEqWallTime_decEq(
    mut v_x_677_: *mut crate::leanh::LeanObject,
    mut v_x_678_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_679_: u8 = 0;
    v___x_679_ = l_Std_Time_instDecidableEqDuration_decEq(v_x_677_, v_x_678_);
    return v___x_679_;
}
pub unsafe fn l_Std_Time_instDecidableEqWallTime_decEq___boxed(
    mut v_x_680_: *mut crate::leanh::LeanObject,
    mut v_x_681_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_682_: u8 = 0;
    let mut v_r_683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_682_ = l_Std_Time_instDecidableEqWallTime_decEq(v_x_680_, v_x_681_);
    crate::leanh::lean_dec_ref(v_x_681_);
    crate::leanh::lean_dec_ref(v_x_680_);
    v_r_683_ = crate::leanh::lean_box((v_res_682_) as usize);
    return v_r_683_;
}
pub unsafe fn l_Std_Time_instDecidableEqWallTime(
    mut v_x_684_: *mut crate::leanh::LeanObject,
    mut v_x_685_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_686_: u8 = 0;
    v___x_686_ = l_Std_Time_instDecidableEqDuration_decEq(v_x_684_, v_x_685_);
    return v___x_686_;
}
pub unsafe fn l_Std_Time_instDecidableEqWallTime___boxed(
    mut v_x_687_: *mut crate::leanh::LeanObject,
    mut v_x_688_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_689_: u8 = 0;
    let mut v_r_690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_689_ = l_Std_Time_instDecidableEqWallTime(v_x_687_, v_x_688_);
    crate::leanh::lean_dec_ref(v_x_688_);
    crate::leanh::lean_dec_ref(v_x_687_);
    v_r_690_ = crate::leanh::lean_box((v_res_689_) as usize);
    return v_r_690_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedWallTime_default___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_691_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime_repr___redArg___closed__14),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime_repr___redArg___closed__14_once),
        _init_l_Std_Time_instReprWallTime_repr___redArg___closed__14,
    );
    v___x_692_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_692_, 0, v___x_691_);
    crate::leanh::lean_ctor_set(v___x_692_, 1, v___x_691_);
    return v___x_692_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedWallTime_default() -> *mut crate::leanh::LeanObject {
    let mut v___x_693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_693_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedWallTime_default___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedWallTime_default___closed__0_once),
        _init_l_Std_Time_instInhabitedWallTime_default___closed__0,
    );
    return v___x_693_;
}
pub unsafe fn l_Nat_cast___at___00Std_Time_instInhabitedWallTime_default_spec__0(
    mut v_a_694_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_695_ = lean_nat_to_int(v_a_694_);
    v___x_696_ = l_Rat_ofInt(v___x_695_);
    return v___x_696_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedWallTime() -> *mut crate::leanh::LeanObject {
    let mut v___x_697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_697_ = l_Std_Time_instInhabitedWallTime_default;
    return v___x_697_;
}
pub unsafe fn _init_l_Std_Time_instLEWallTime() -> *mut crate::leanh::LeanObject {
    let mut v___x_698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_698_ = crate::leanh::lean_box(0);
    return v___x_698_;
}
pub unsafe fn l_Std_Time_instDecidableLeWallTime(
    mut v_x_699_: *mut crate::leanh::LeanObject,
    mut v_y_700_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_701_: u8 = 0;
    v___x_701_ = l_Std_Time_Duration_instDecidableLe(v_x_699_, v_y_700_);
    return v___x_701_;
}
pub unsafe fn l_Std_Time_instDecidableLeWallTime___boxed(
    mut v_x_702_: *mut crate::leanh::LeanObject,
    mut v_y_703_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_704_: u8 = 0;
    let mut v_r_705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_704_ = l_Std_Time_instDecidableLeWallTime(v_x_702_, v_y_703_);
    crate::leanh::lean_dec_ref(v_y_703_);
    crate::leanh::lean_dec_ref(v_x_702_);
    v_r_705_ = crate::leanh::lean_box((v_res_704_) as usize);
    return v_r_705_;
}
pub unsafe fn _init_l_Std_Time_instLTWallTime() -> *mut crate::leanh::LeanObject {
    let mut v___x_706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_706_ = crate::leanh::lean_box(0);
    return v___x_706_;
}
pub unsafe fn l_Std_Time_instDecidableLtWallTime(
    mut v_x_707_: *mut crate::leanh::LeanObject,
    mut v_y_708_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_709_: u8 = 0;
    v___x_709_ = l_Std_Time_Duration_instDecidableLt(v_x_707_, v_y_708_);
    return v___x_709_;
}
pub unsafe fn l_Std_Time_instDecidableLtWallTime___boxed(
    mut v_x_710_: *mut crate::leanh::LeanObject,
    mut v_y_711_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_712_: u8 = 0;
    let mut v_r_713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_712_ = l_Std_Time_instDecidableLtWallTime(v_x_710_, v_y_711_);
    crate::leanh::lean_dec_ref(v_y_711_);
    crate::leanh::lean_dec_ref(v_x_710_);
    v_r_713_ = crate::leanh::lean_box((v_res_712_) as usize);
    return v_r_713_;
}
pub unsafe fn l_Std_Time_instOrdWallTime___lam__0(
    mut v_x_714_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_x_714_);
    return v_x_714_;
}
pub unsafe fn l_Std_Time_instOrdWallTime___lam__0___boxed(
    mut v_x_715_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_716_ = l_Std_Time_instOrdWallTime___lam__0(v_x_715_);
    crate::leanh::lean_dec_ref(v_x_715_);
    return v_res_716_;
}
pub unsafe fn _init_l_Std_Time_instOrdWallTime___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___f_718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_718_ = l_Std_Time_instOrdWallTime___closed__0;
    v___x_719_ = l_Std_Time_instOrdDuration;
    v___x_720_ =
        crate::leanh::lean_alloc_closure(l_compareOn___boxed as *mut core::ffi::c_void, 6, 4);
    crate::leanh::lean_closure_set(v___x_720_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_720_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_720_, 2, v___x_719_);
    crate::leanh::lean_closure_set(v___x_720_, 3, v___f_718_);
    return v___x_720_;
}
pub unsafe fn _init_l_Std_Time_instOrdWallTime() -> *mut crate::leanh::LeanObject {
    let mut v___x_721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_721_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instOrdWallTime___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_instOrdWallTime___closed__1_once),
        _init_l_Std_Time_instOrdWallTime___closed__1,
    );
    return v___x_721_;
}
pub unsafe fn l_Std_Time_instToStringWallTime___lam__0(
    mut v_s_722_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_second_723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_second_723_ = crate::leanh::lean_ctor_get(v_s_722_, 0);
    v___x_724_ = l_Int_repr(v_second_723_);
    return v___x_724_;
}
pub unsafe fn l_Std_Time_instToStringWallTime___lam__0___boxed(
    mut v_s_725_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_726_ = l_Std_Time_instToStringWallTime___lam__0(v_s_725_);
    crate::leanh::lean_dec_ref(v_s_725_);
    return v_res_726_;
}
pub unsafe fn _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_732_ = crate::leanh::lean_unsigned_to_nat(1000000000);
    v___x_733_ = lean_nat_to_int(v___x_732_);
    return v___x_733_;
}
pub unsafe fn l_Std_Time_instReprWallTime__1___lam__0(
    mut v_s_734_: *mut crate::leanh::LeanObject,
    mut v___y_735_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_second_736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_740_: u8 = 0;
    let mut v___x_741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nanos_744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_751_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_second_736_ = crate::leanh::lean_ctor_get(v_s_734_, 0);
                v_nano_737_ = crate::leanh::lean_ctor_get(v_s_734_, 1);
                v_isSharedCheck_751_ = (!crate::leanh::lean_is_exclusive(v_s_734_)) as u8;
                if v_isSharedCheck_751_ == 0 {
                    v___x_739_ = v_s_734_;
                    v_isShared_740_ = v_isSharedCheck_751_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nano_737_);
                    crate::leanh::lean_inc(v_second_736_);
                    crate::leanh::lean_dec(v_s_734_);
                    v___x_739_ = crate::leanh::lean_box(0);
                    v_isShared_740_ = v_isSharedCheck_751_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_741_ = l_Std_Time_instReprWallTime__1___lam__0___closed__1;
                v___x_742_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime__1___lam__0___closed__2),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprWallTime__1___lam__0___closed__2_once
                    ),
                    _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2,
                );
                v___x_743_ = lean_int_mul(v_second_736_, v___x_742_);
                crate::leanh::lean_dec(v_second_736_);
                v_nanos_744_ = lean_int_add(v___x_743_, v_nano_737_);
                crate::leanh::lean_dec(v_nano_737_);
                crate::leanh::lean_dec(v___x_743_);
                v___x_745_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_746_ =
                    l_Std_Time_Nanosecond_instReprOrdinal___lam__0(v_nanos_744_, v___x_745_);
                crate::leanh::lean_dec(v_nanos_744_);
                if v_isShared_740_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_739_, 5);
                    crate::leanh::lean_ctor_set(v___x_739_, 1, v___x_746_);
                    crate::leanh::lean_ctor_set(v___x_739_, 0, v___x_741_);
                    v___x_748_ = v___x_739_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_750_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_750_, 0, v___x_741_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_750_, 1, v___x_746_);
                    v___x_748_ = v_reuseFailAlloc_750_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_749_ = l_Repr_addAppParen(v___x_748_, v___y_735_);
                return v___x_749_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_instReprWallTime__1___lam__0___boxed(
    mut v_s_752_: *mut crate::leanh::LeanObject,
    mut v___y_753_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_754_ = l_Std_Time_instReprWallTime__1___lam__0(v_s_752_, v___y_753_);
    crate::leanh::lean_dec(v___y_753_);
    return v_res_754_;
}
pub unsafe fn l_Std_Time_WallTime_ofDuration(
    mut v_duration_757_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_duration_757_);
    return v_duration_757_;
}
pub unsafe fn l_Std_Time_WallTime_ofDuration___boxed(
    mut v_duration_758_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_759_ = l_Std_Time_WallTime_ofDuration(v_duration_758_);
    crate::leanh::lean_dec_ref(v_duration_758_);
    return v_res_759_;
}
pub unsafe fn l_Std_Time_WallTime_ofSeconds(
    mut v_secs_760_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_761_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime_repr___redArg___closed__14),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime_repr___redArg___closed__14_once),
        _init_l_Std_Time_instReprWallTime_repr___redArg___closed__14,
    );
    v___x_762_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_762_, 0, v_secs_760_);
    crate::leanh::lean_ctor_set(v___x_762_, 1, v___x_761_);
    return v___x_762_;
}
pub unsafe fn l_Std_Time_WallTime_ofNanoseconds(
    mut v_nanos_763_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_764_ = l_Std_Time_Duration_ofNanoseconds(v_nanos_763_);
    return v___x_764_;
}
pub unsafe fn l_Std_Time_WallTime_ofNanoseconds___boxed(
    mut v_nanos_765_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_766_ = l_Std_Time_WallTime_ofNanoseconds(v_nanos_765_);
    crate::leanh::lean_dec(v_nanos_765_);
    return v_res_766_;
}
pub unsafe fn l_Std_Time_WallTime_toSeconds(
    mut v_wt_767_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_second_768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_second_768_ = crate::leanh::lean_ctor_get(v_wt_767_, 0);
    crate::leanh::lean_inc(v_second_768_);
    return v_second_768_;
}
pub unsafe fn l_Std_Time_WallTime_toSeconds___boxed(
    mut v_wt_769_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_770_ = l_Std_Time_WallTime_toSeconds(v_wt_769_);
    crate::leanh::lean_dec_ref(v_wt_769_);
    return v_res_770_;
}
pub unsafe fn l_Std_Time_WallTime_toNanoseconds(
    mut v_wt_771_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_second_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nanos_776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_second_772_ = crate::leanh::lean_ctor_get(v_wt_771_, 0);
    v_nano_773_ = crate::leanh::lean_ctor_get(v_wt_771_, 1);
    v___x_774_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime__1___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime__1___lam__0___closed__2_once),
        _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2,
    );
    v___x_775_ = lean_int_mul(v_second_772_, v___x_774_);
    v_nanos_776_ = lean_int_add(v___x_775_, v_nano_773_);
    crate::leanh::lean_dec(v___x_775_);
    return v_nanos_776_;
}
pub unsafe fn l_Std_Time_WallTime_toNanoseconds___boxed(
    mut v_wt_777_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_778_ = l_Std_Time_WallTime_toNanoseconds(v_wt_777_);
    crate::leanh::lean_dec_ref(v_wt_777_);
    return v_res_778_;
}
pub unsafe fn _init_l_Std_Time_WallTime_toMinutes___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_779_ = crate::leanh::lean_unsigned_to_nat(60);
    v___x_780_ = lean_nat_to_int(v___x_779_);
    return v___x_780_;
}
pub unsafe fn l_Std_Time_WallTime_toMinutes(
    mut v_tm_781_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_second_782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_second_782_ = crate::leanh::lean_ctor_get(v_tm_781_, 0);
    v___x_783_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_WallTime_toMinutes___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_WallTime_toMinutes___closed__0_once),
        _init_l_Std_Time_WallTime_toMinutes___closed__0,
    );
    v___x_784_ = lean_int_div(v_second_782_, v___x_783_);
    return v___x_784_;
}
pub unsafe fn l_Std_Time_WallTime_toMinutes___boxed(
    mut v_tm_785_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_786_ = l_Std_Time_WallTime_toMinutes(v_tm_785_);
    crate::leanh::lean_dec_ref(v_tm_785_);
    return v_res_786_;
}
pub unsafe fn _init_l_Std_Time_WallTime_toDays___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_787_ = crate::leanh::lean_unsigned_to_nat(86400);
    v___x_788_ = lean_nat_to_int(v___x_787_);
    return v___x_788_;
}
pub unsafe fn l_Std_Time_WallTime_toDays(
    mut v_tm_789_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_second_790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_second_790_ = crate::leanh::lean_ctor_get(v_tm_789_, 0);
    v___x_791_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_WallTime_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_WallTime_toDays___closed__0_once),
        _init_l_Std_Time_WallTime_toDays___closed__0,
    );
    v___x_792_ = lean_int_div(v_second_790_, v___x_791_);
    return v___x_792_;
}
pub unsafe fn l_Std_Time_WallTime_toDays___boxed(
    mut v_tm_793_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_794_ = l_Std_Time_WallTime_toDays(v_tm_793_);
    crate::leanh::lean_dec_ref(v_tm_793_);
    return v_res_794_;
}
pub unsafe fn _init_l_Std_Time_WallTime_ofMilliseconds___closed__0() -> *mut crate::leanh::LeanObject
{
    let mut v___x_795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_795_ = crate::leanh::lean_unsigned_to_nat(1000000);
    v___x_796_ = lean_nat_to_int(v___x_795_);
    return v___x_796_;
}
pub unsafe fn l_Std_Time_WallTime_ofMilliseconds(
    mut v_milli_797_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_798_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_WallTime_ofMilliseconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_WallTime_ofMilliseconds___closed__0_once),
        _init_l_Std_Time_WallTime_ofMilliseconds___closed__0,
    );
    v___x_799_ = lean_int_mul(v_milli_797_, v___x_798_);
    v___x_800_ = l_Std_Time_Duration_ofNanoseconds(v___x_799_);
    crate::leanh::lean_dec(v___x_799_);
    return v___x_800_;
}
pub unsafe fn l_Std_Time_WallTime_ofMilliseconds___boxed(
    mut v_milli_801_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_802_ = l_Std_Time_WallTime_ofMilliseconds(v_milli_801_);
    crate::leanh::lean_dec(v_milli_801_);
    return v_res_802_;
}
pub unsafe fn l_Std_Time_WallTime_toMilliseconds(
    mut v_tm_803_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_second_804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_second_804_ = crate::leanh::lean_ctor_get(v_tm_803_, 0);
    v_nano_805_ = crate::leanh::lean_ctor_get(v_tm_803_, 1);
    v___x_806_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime__1___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime__1___lam__0___closed__2_once),
        _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2,
    );
    v___x_807_ = lean_int_mul(v_second_804_, v___x_806_);
    v___x_808_ = lean_int_add(v___x_807_, v_nano_805_);
    crate::leanh::lean_dec(v___x_807_);
    v___x_809_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_WallTime_ofMilliseconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_WallTime_ofMilliseconds___closed__0_once),
        _init_l_Std_Time_WallTime_ofMilliseconds___closed__0,
    );
    v___x_810_ = lean_int_div(v___x_808_, v___x_809_);
    crate::leanh::lean_dec(v___x_808_);
    return v___x_810_;
}
pub unsafe fn l_Std_Time_WallTime_toMilliseconds___boxed(
    mut v_tm_811_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_812_ = l_Std_Time_WallTime_toMilliseconds(v_tm_811_);
    crate::leanh::lean_dec_ref(v_tm_811_);
    return v_res_812_;
}
pub unsafe fn l_Std_Time_WallTime_addMilliseconds(
    mut v_t_813_: *mut crate::leanh::LeanObject,
    mut v_s_814_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_second_815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_second_815_ = crate::leanh::lean_ctor_get(v_t_813_, 0);
    v_nano_816_ = crate::leanh::lean_ctor_get(v_t_813_, 1);
    v___x_817_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_WallTime_ofMilliseconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_WallTime_ofMilliseconds___closed__0_once),
        _init_l_Std_Time_WallTime_ofMilliseconds___closed__0,
    );
    v___x_818_ = lean_int_mul(v_s_814_, v___x_817_);
    v___x_819_ = l_Std_Time_Duration_ofNanoseconds(v___x_818_);
    crate::leanh::lean_dec(v___x_818_);
    v_second_820_ = crate::leanh::lean_ctor_get(v___x_819_, 0);
    crate::leanh::lean_inc(v_second_820_);
    v_nano_821_ = crate::leanh::lean_ctor_get(v___x_819_, 1);
    crate::leanh::lean_inc(v_nano_821_);
    crate::leanh::lean_dec_ref(v___x_819_);
    v___x_822_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime__1___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime__1___lam__0___closed__2_once),
        _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2,
    );
    v___x_823_ = lean_int_mul(v_second_815_, v___x_822_);
    v___x_824_ = lean_int_add(v___x_823_, v_nano_816_);
    crate::leanh::lean_dec(v___x_823_);
    v___x_825_ = lean_int_mul(v_second_820_, v___x_822_);
    crate::leanh::lean_dec(v_second_820_);
    v___x_826_ = lean_int_add(v___x_825_, v_nano_821_);
    crate::leanh::lean_dec(v_nano_821_);
    crate::leanh::lean_dec(v___x_825_);
    v___x_827_ = lean_int_add(v___x_824_, v___x_826_);
    crate::leanh::lean_dec(v___x_826_);
    crate::leanh::lean_dec(v___x_824_);
    v___x_828_ = l_Std_Time_Duration_ofNanoseconds(v___x_827_);
    crate::leanh::lean_dec(v___x_827_);
    return v___x_828_;
}
pub unsafe fn l_Std_Time_WallTime_addMilliseconds___boxed(
    mut v_t_829_: *mut crate::leanh::LeanObject,
    mut v_s_830_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_831_ = l_Std_Time_WallTime_addMilliseconds(v_t_829_, v_s_830_);
    crate::leanh::lean_dec(v_s_830_);
    crate::leanh::lean_dec_ref(v_t_829_);
    return v_res_831_;
}
pub unsafe fn l_Std_Time_WallTime_subMilliseconds(
    mut v_t_832_: *mut crate::leanh::LeanObject,
    mut v_s_833_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_834_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_WallTime_ofMilliseconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_WallTime_ofMilliseconds___closed__0_once),
        _init_l_Std_Time_WallTime_ofMilliseconds___closed__0,
    );
    v___x_835_ = lean_int_mul(v_s_833_, v___x_834_);
    v___x_836_ = l_Std_Time_Duration_ofNanoseconds(v___x_835_);
    crate::leanh::lean_dec(v___x_835_);
    v_second_837_ = crate::leanh::lean_ctor_get(v___x_836_, 0);
    crate::leanh::lean_inc(v_second_837_);
    v_nano_838_ = crate::leanh::lean_ctor_get(v___x_836_, 1);
    crate::leanh::lean_inc(v_nano_838_);
    crate::leanh::lean_dec_ref(v___x_836_);
    v_second_839_ = crate::leanh::lean_ctor_get(v_t_832_, 0);
    v_nano_840_ = crate::leanh::lean_ctor_get(v_t_832_, 1);
    v___x_841_ = lean_int_neg(v_second_837_);
    crate::leanh::lean_dec(v_second_837_);
    v___x_842_ = lean_int_neg(v_nano_838_);
    crate::leanh::lean_dec(v_nano_838_);
    v___x_843_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime__1___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime__1___lam__0___closed__2_once),
        _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2,
    );
    v___x_844_ = lean_int_mul(v_second_839_, v___x_843_);
    v___x_845_ = lean_int_add(v___x_844_, v_nano_840_);
    crate::leanh::lean_dec(v___x_844_);
    v___x_846_ = lean_int_mul(v___x_841_, v___x_843_);
    crate::leanh::lean_dec(v___x_841_);
    v___x_847_ = lean_int_add(v___x_846_, v___x_842_);
    crate::leanh::lean_dec(v___x_842_);
    crate::leanh::lean_dec(v___x_846_);
    v___x_848_ = lean_int_add(v___x_845_, v___x_847_);
    crate::leanh::lean_dec(v___x_847_);
    crate::leanh::lean_dec(v___x_845_);
    v___x_849_ = l_Std_Time_Duration_ofNanoseconds(v___x_848_);
    crate::leanh::lean_dec(v___x_848_);
    return v___x_849_;
}
pub unsafe fn l_Std_Time_WallTime_subMilliseconds___boxed(
    mut v_t_850_: *mut crate::leanh::LeanObject,
    mut v_s_851_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_852_ = l_Std_Time_WallTime_subMilliseconds(v_t_850_, v_s_851_);
    crate::leanh::lean_dec(v_s_851_);
    crate::leanh::lean_dec_ref(v_t_850_);
    return v_res_852_;
}
pub unsafe fn l_Std_Time_WallTime_addNanoseconds(
    mut v_t_853_: *mut crate::leanh::LeanObject,
    mut v_s_854_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_second_855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_second_855_ = crate::leanh::lean_ctor_get(v_t_853_, 0);
    v_nano_856_ = crate::leanh::lean_ctor_get(v_t_853_, 1);
    v___x_857_ = l_Std_Time_Duration_ofNanoseconds(v_s_854_);
    v_second_858_ = crate::leanh::lean_ctor_get(v___x_857_, 0);
    crate::leanh::lean_inc(v_second_858_);
    v_nano_859_ = crate::leanh::lean_ctor_get(v___x_857_, 1);
    crate::leanh::lean_inc(v_nano_859_);
    crate::leanh::lean_dec_ref(v___x_857_);
    v___x_860_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime__1___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime__1___lam__0___closed__2_once),
        _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2,
    );
    v___x_861_ = lean_int_mul(v_second_855_, v___x_860_);
    v___x_862_ = lean_int_add(v___x_861_, v_nano_856_);
    crate::leanh::lean_dec(v___x_861_);
    v___x_863_ = lean_int_mul(v_second_858_, v___x_860_);
    crate::leanh::lean_dec(v_second_858_);
    v___x_864_ = lean_int_add(v___x_863_, v_nano_859_);
    crate::leanh::lean_dec(v_nano_859_);
    crate::leanh::lean_dec(v___x_863_);
    v___x_865_ = lean_int_add(v___x_862_, v___x_864_);
    crate::leanh::lean_dec(v___x_864_);
    crate::leanh::lean_dec(v___x_862_);
    v___x_866_ = l_Std_Time_Duration_ofNanoseconds(v___x_865_);
    crate::leanh::lean_dec(v___x_865_);
    return v___x_866_;
}
pub unsafe fn l_Std_Time_WallTime_addNanoseconds___boxed(
    mut v_t_867_: *mut crate::leanh::LeanObject,
    mut v_s_868_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_869_ = l_Std_Time_WallTime_addNanoseconds(v_t_867_, v_s_868_);
    crate::leanh::lean_dec(v_s_868_);
    crate::leanh::lean_dec_ref(v_t_867_);
    return v_res_869_;
}
pub unsafe fn l_Std_Time_WallTime_subNanoseconds(
    mut v_t_870_: *mut crate::leanh::LeanObject,
    mut v_s_871_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_872_ = l_Std_Time_Duration_ofNanoseconds(v_s_871_);
    v_second_873_ = crate::leanh::lean_ctor_get(v___x_872_, 0);
    crate::leanh::lean_inc(v_second_873_);
    v_nano_874_ = crate::leanh::lean_ctor_get(v___x_872_, 1);
    crate::leanh::lean_inc(v_nano_874_);
    crate::leanh::lean_dec_ref(v___x_872_);
    v_second_875_ = crate::leanh::lean_ctor_get(v_t_870_, 0);
    v_nano_876_ = crate::leanh::lean_ctor_get(v_t_870_, 1);
    v___x_877_ = lean_int_neg(v_second_873_);
    crate::leanh::lean_dec(v_second_873_);
    v___x_878_ = lean_int_neg(v_nano_874_);
    crate::leanh::lean_dec(v_nano_874_);
    v___x_879_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime__1___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime__1___lam__0___closed__2_once),
        _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2,
    );
    v___x_880_ = lean_int_mul(v_second_875_, v___x_879_);
    v___x_881_ = lean_int_add(v___x_880_, v_nano_876_);
    crate::leanh::lean_dec(v___x_880_);
    v___x_882_ = lean_int_mul(v___x_877_, v___x_879_);
    crate::leanh::lean_dec(v___x_877_);
    v___x_883_ = lean_int_add(v___x_882_, v___x_878_);
    crate::leanh::lean_dec(v___x_878_);
    crate::leanh::lean_dec(v___x_882_);
    v___x_884_ = lean_int_add(v___x_881_, v___x_883_);
    crate::leanh::lean_dec(v___x_883_);
    crate::leanh::lean_dec(v___x_881_);
    v___x_885_ = l_Std_Time_Duration_ofNanoseconds(v___x_884_);
    crate::leanh::lean_dec(v___x_884_);
    return v___x_885_;
}
pub unsafe fn l_Std_Time_WallTime_subNanoseconds___boxed(
    mut v_t_886_: *mut crate::leanh::LeanObject,
    mut v_s_887_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_888_ = l_Std_Time_WallTime_subNanoseconds(v_t_886_, v_s_887_);
    crate::leanh::lean_dec(v_s_887_);
    crate::leanh::lean_dec_ref(v_t_886_);
    return v_res_888_;
}
pub unsafe fn l_Std_Time_WallTime_addSeconds(
    mut v_t_889_: *mut crate::leanh::LeanObject,
    mut v_s_890_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_second_891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_second_891_ = crate::leanh::lean_ctor_get(v_t_889_, 0);
    v_nano_892_ = crate::leanh::lean_ctor_get(v_t_889_, 1);
    v___x_893_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime_repr___redArg___closed__14),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime_repr___redArg___closed__14_once),
        _init_l_Std_Time_instReprWallTime_repr___redArg___closed__14,
    );
    v___x_894_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime__1___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime__1___lam__0___closed__2_once),
        _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2,
    );
    v___x_895_ = lean_int_mul(v_second_891_, v___x_894_);
    v___x_896_ = lean_int_add(v___x_895_, v_nano_892_);
    crate::leanh::lean_dec(v___x_895_);
    v___x_897_ = lean_int_mul(v_s_890_, v___x_894_);
    v___x_898_ = lean_int_add(v___x_897_, v___x_893_);
    crate::leanh::lean_dec(v___x_897_);
    v___x_899_ = lean_int_add(v___x_896_, v___x_898_);
    crate::leanh::lean_dec(v___x_898_);
    crate::leanh::lean_dec(v___x_896_);
    v___x_900_ = l_Std_Time_Duration_ofNanoseconds(v___x_899_);
    crate::leanh::lean_dec(v___x_899_);
    return v___x_900_;
}
pub unsafe fn l_Std_Time_WallTime_addSeconds___boxed(
    mut v_t_901_: *mut crate::leanh::LeanObject,
    mut v_s_902_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_903_ = l_Std_Time_WallTime_addSeconds(v_t_901_, v_s_902_);
    crate::leanh::lean_dec(v_s_902_);
    crate::leanh::lean_dec_ref(v_t_901_);
    return v_res_903_;
}
pub unsafe fn _init_l_Std_Time_WallTime_subSeconds___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_904_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime_repr___redArg___closed__14),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime_repr___redArg___closed__14_once),
        _init_l_Std_Time_instReprWallTime_repr___redArg___closed__14,
    );
    v___x_905_ = lean_int_neg(v___x_904_);
    return v___x_905_;
}
pub unsafe fn l_Std_Time_WallTime_subSeconds(
    mut v_t_906_: *mut crate::leanh::LeanObject,
    mut v_s_907_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_second_908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_second_908_ = crate::leanh::lean_ctor_get(v_t_906_, 0);
    v_nano_909_ = crate::leanh::lean_ctor_get(v_t_906_, 1);
    v___x_910_ = lean_int_neg(v_s_907_);
    v___x_911_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_WallTime_subSeconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_WallTime_subSeconds___closed__0_once),
        _init_l_Std_Time_WallTime_subSeconds___closed__0,
    );
    v___x_912_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime__1___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime__1___lam__0___closed__2_once),
        _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2,
    );
    v___x_913_ = lean_int_mul(v_second_908_, v___x_912_);
    v___x_914_ = lean_int_add(v___x_913_, v_nano_909_);
    crate::leanh::lean_dec(v___x_913_);
    v___x_915_ = lean_int_mul(v___x_910_, v___x_912_);
    crate::leanh::lean_dec(v___x_910_);
    v___x_916_ = lean_int_add(v___x_915_, v___x_911_);
    crate::leanh::lean_dec(v___x_915_);
    v___x_917_ = lean_int_add(v___x_914_, v___x_916_);
    crate::leanh::lean_dec(v___x_916_);
    crate::leanh::lean_dec(v___x_914_);
    v___x_918_ = l_Std_Time_Duration_ofNanoseconds(v___x_917_);
    crate::leanh::lean_dec(v___x_917_);
    return v___x_918_;
}
pub unsafe fn l_Std_Time_WallTime_subSeconds___boxed(
    mut v_t_919_: *mut crate::leanh::LeanObject,
    mut v_s_920_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_921_ = l_Std_Time_WallTime_subSeconds(v_t_919_, v_s_920_);
    crate::leanh::lean_dec(v_s_920_);
    crate::leanh::lean_dec_ref(v_t_919_);
    return v_res_921_;
}
pub unsafe fn l_Std_Time_WallTime_addMinutes(
    mut v_t_922_: *mut crate::leanh::LeanObject,
    mut v_m_923_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_second_924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_second_924_ = crate::leanh::lean_ctor_get(v_t_922_, 0);
    v_nano_925_ = crate::leanh::lean_ctor_get(v_t_922_, 1);
    v___x_926_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_WallTime_toMinutes___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_WallTime_toMinutes___closed__0_once),
        _init_l_Std_Time_WallTime_toMinutes___closed__0,
    );
    v___x_927_ = lean_int_mul(v_m_923_, v___x_926_);
    v___x_928_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime_repr___redArg___closed__14),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime_repr___redArg___closed__14_once),
        _init_l_Std_Time_instReprWallTime_repr___redArg___closed__14,
    );
    v___x_929_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime__1___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime__1___lam__0___closed__2_once),
        _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2,
    );
    v___x_930_ = lean_int_mul(v_second_924_, v___x_929_);
    v___x_931_ = lean_int_add(v___x_930_, v_nano_925_);
    crate::leanh::lean_dec(v___x_930_);
    v___x_932_ = lean_int_mul(v___x_927_, v___x_929_);
    crate::leanh::lean_dec(v___x_927_);
    v___x_933_ = lean_int_add(v___x_932_, v___x_928_);
    crate::leanh::lean_dec(v___x_932_);
    v___x_934_ = lean_int_add(v___x_931_, v___x_933_);
    crate::leanh::lean_dec(v___x_933_);
    crate::leanh::lean_dec(v___x_931_);
    v___x_935_ = l_Std_Time_Duration_ofNanoseconds(v___x_934_);
    crate::leanh::lean_dec(v___x_934_);
    return v___x_935_;
}
pub unsafe fn l_Std_Time_WallTime_addMinutes___boxed(
    mut v_t_936_: *mut crate::leanh::LeanObject,
    mut v_m_937_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_938_ = l_Std_Time_WallTime_addMinutes(v_t_936_, v_m_937_);
    crate::leanh::lean_dec(v_m_937_);
    crate::leanh::lean_dec_ref(v_t_936_);
    return v_res_938_;
}
pub unsafe fn l_Std_Time_WallTime_subMinutes(
    mut v_t_939_: *mut crate::leanh::LeanObject,
    mut v_m_940_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_second_941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_second_941_ = crate::leanh::lean_ctor_get(v_t_939_, 0);
    v_nano_942_ = crate::leanh::lean_ctor_get(v_t_939_, 1);
    v___x_943_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_WallTime_toMinutes___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_WallTime_toMinutes___closed__0_once),
        _init_l_Std_Time_WallTime_toMinutes___closed__0,
    );
    v___x_944_ = lean_int_mul(v_m_940_, v___x_943_);
    v___x_945_ = lean_int_neg(v___x_944_);
    crate::leanh::lean_dec(v___x_944_);
    v___x_946_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_WallTime_subSeconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_WallTime_subSeconds___closed__0_once),
        _init_l_Std_Time_WallTime_subSeconds___closed__0,
    );
    v___x_947_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime__1___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime__1___lam__0___closed__2_once),
        _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2,
    );
    v___x_948_ = lean_int_mul(v_second_941_, v___x_947_);
    v___x_949_ = lean_int_add(v___x_948_, v_nano_942_);
    crate::leanh::lean_dec(v___x_948_);
    v___x_950_ = lean_int_mul(v___x_945_, v___x_947_);
    crate::leanh::lean_dec(v___x_945_);
    v___x_951_ = lean_int_add(v___x_950_, v___x_946_);
    crate::leanh::lean_dec(v___x_950_);
    v___x_952_ = lean_int_add(v___x_949_, v___x_951_);
    crate::leanh::lean_dec(v___x_951_);
    crate::leanh::lean_dec(v___x_949_);
    v___x_953_ = l_Std_Time_Duration_ofNanoseconds(v___x_952_);
    crate::leanh::lean_dec(v___x_952_);
    return v___x_953_;
}
pub unsafe fn l_Std_Time_WallTime_subMinutes___boxed(
    mut v_t_954_: *mut crate::leanh::LeanObject,
    mut v_m_955_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_956_ = l_Std_Time_WallTime_subMinutes(v_t_954_, v_m_955_);
    crate::leanh::lean_dec(v_m_955_);
    crate::leanh::lean_dec_ref(v_t_954_);
    return v_res_956_;
}
pub unsafe fn _init_l_Std_Time_WallTime_addHours___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_957_ = crate::leanh::lean_unsigned_to_nat(3600);
    v___x_958_ = lean_nat_to_int(v___x_957_);
    return v___x_958_;
}
pub unsafe fn l_Std_Time_WallTime_addHours(
    mut v_t_959_: *mut crate::leanh::LeanObject,
    mut v_h_960_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_second_961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_second_961_ = crate::leanh::lean_ctor_get(v_t_959_, 0);
    v_nano_962_ = crate::leanh::lean_ctor_get(v_t_959_, 1);
    v___x_963_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_WallTime_addHours___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_WallTime_addHours___closed__0_once),
        _init_l_Std_Time_WallTime_addHours___closed__0,
    );
    v___x_964_ = lean_int_mul(v_h_960_, v___x_963_);
    v___x_965_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime_repr___redArg___closed__14),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime_repr___redArg___closed__14_once),
        _init_l_Std_Time_instReprWallTime_repr___redArg___closed__14,
    );
    v___x_966_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime__1___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime__1___lam__0___closed__2_once),
        _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2,
    );
    v___x_967_ = lean_int_mul(v_second_961_, v___x_966_);
    v___x_968_ = lean_int_add(v___x_967_, v_nano_962_);
    crate::leanh::lean_dec(v___x_967_);
    v___x_969_ = lean_int_mul(v___x_964_, v___x_966_);
    crate::leanh::lean_dec(v___x_964_);
    v___x_970_ = lean_int_add(v___x_969_, v___x_965_);
    crate::leanh::lean_dec(v___x_969_);
    v___x_971_ = lean_int_add(v___x_968_, v___x_970_);
    crate::leanh::lean_dec(v___x_970_);
    crate::leanh::lean_dec(v___x_968_);
    v___x_972_ = l_Std_Time_Duration_ofNanoseconds(v___x_971_);
    crate::leanh::lean_dec(v___x_971_);
    return v___x_972_;
}
pub unsafe fn l_Std_Time_WallTime_addHours___boxed(
    mut v_t_973_: *mut crate::leanh::LeanObject,
    mut v_h_974_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_975_ = l_Std_Time_WallTime_addHours(v_t_973_, v_h_974_);
    crate::leanh::lean_dec(v_h_974_);
    crate::leanh::lean_dec_ref(v_t_973_);
    return v_res_975_;
}
pub unsafe fn l_Std_Time_WallTime_subHours(
    mut v_t_976_: *mut crate::leanh::LeanObject,
    mut v_h_977_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_second_978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_second_978_ = crate::leanh::lean_ctor_get(v_t_976_, 0);
    v_nano_979_ = crate::leanh::lean_ctor_get(v_t_976_, 1);
    v___x_980_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_WallTime_addHours___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_WallTime_addHours___closed__0_once),
        _init_l_Std_Time_WallTime_addHours___closed__0,
    );
    v___x_981_ = lean_int_mul(v_h_977_, v___x_980_);
    v___x_982_ = lean_int_neg(v___x_981_);
    crate::leanh::lean_dec(v___x_981_);
    v___x_983_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_WallTime_subSeconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_WallTime_subSeconds___closed__0_once),
        _init_l_Std_Time_WallTime_subSeconds___closed__0,
    );
    v___x_984_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime__1___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime__1___lam__0___closed__2_once),
        _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2,
    );
    v___x_985_ = lean_int_mul(v_second_978_, v___x_984_);
    v___x_986_ = lean_int_add(v___x_985_, v_nano_979_);
    crate::leanh::lean_dec(v___x_985_);
    v___x_987_ = lean_int_mul(v___x_982_, v___x_984_);
    crate::leanh::lean_dec(v___x_982_);
    v___x_988_ = lean_int_add(v___x_987_, v___x_983_);
    crate::leanh::lean_dec(v___x_987_);
    v___x_989_ = lean_int_add(v___x_986_, v___x_988_);
    crate::leanh::lean_dec(v___x_988_);
    crate::leanh::lean_dec(v___x_986_);
    v___x_990_ = l_Std_Time_Duration_ofNanoseconds(v___x_989_);
    crate::leanh::lean_dec(v___x_989_);
    return v___x_990_;
}
pub unsafe fn l_Std_Time_WallTime_subHours___boxed(
    mut v_t_991_: *mut crate::leanh::LeanObject,
    mut v_h_992_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_993_ = l_Std_Time_WallTime_subHours(v_t_991_, v_h_992_);
    crate::leanh::lean_dec(v_h_992_);
    crate::leanh::lean_dec_ref(v_t_991_);
    return v_res_993_;
}
pub unsafe fn l_Std_Time_WallTime_addDays(
    mut v_t_994_: *mut crate::leanh::LeanObject,
    mut v_d_995_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_second_996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_second_996_ = crate::leanh::lean_ctor_get(v_t_994_, 0);
    v_nano_997_ = crate::leanh::lean_ctor_get(v_t_994_, 1);
    v___x_998_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_WallTime_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_WallTime_toDays___closed__0_once),
        _init_l_Std_Time_WallTime_toDays___closed__0,
    );
    v___x_999_ = lean_int_mul(v_d_995_, v___x_998_);
    v___x_1000_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime_repr___redArg___closed__14),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime_repr___redArg___closed__14_once),
        _init_l_Std_Time_instReprWallTime_repr___redArg___closed__14,
    );
    v___x_1001_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime__1___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime__1___lam__0___closed__2_once),
        _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2,
    );
    v___x_1002_ = lean_int_mul(v_second_996_, v___x_1001_);
    v___x_1003_ = lean_int_add(v___x_1002_, v_nano_997_);
    crate::leanh::lean_dec(v___x_1002_);
    v___x_1004_ = lean_int_mul(v___x_999_, v___x_1001_);
    crate::leanh::lean_dec(v___x_999_);
    v___x_1005_ = lean_int_add(v___x_1004_, v___x_1000_);
    crate::leanh::lean_dec(v___x_1004_);
    v___x_1006_ = lean_int_add(v___x_1003_, v___x_1005_);
    crate::leanh::lean_dec(v___x_1005_);
    crate::leanh::lean_dec(v___x_1003_);
    v___x_1007_ = l_Std_Time_Duration_ofNanoseconds(v___x_1006_);
    crate::leanh::lean_dec(v___x_1006_);
    return v___x_1007_;
}
pub unsafe fn l_Std_Time_WallTime_addDays___boxed(
    mut v_t_1008_: *mut crate::leanh::LeanObject,
    mut v_d_1009_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1010_ = l_Std_Time_WallTime_addDays(v_t_1008_, v_d_1009_);
    crate::leanh::lean_dec(v_d_1009_);
    crate::leanh::lean_dec_ref(v_t_1008_);
    return v_res_1010_;
}
pub unsafe fn l_Std_Time_WallTime_subDays(
    mut v_t_1011_: *mut crate::leanh::LeanObject,
    mut v_d_1012_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_second_1013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_second_1013_ = crate::leanh::lean_ctor_get(v_t_1011_, 0);
    v_nano_1014_ = crate::leanh::lean_ctor_get(v_t_1011_, 1);
    v___x_1015_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_WallTime_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_WallTime_toDays___closed__0_once),
        _init_l_Std_Time_WallTime_toDays___closed__0,
    );
    v___x_1016_ = lean_int_mul(v_d_1012_, v___x_1015_);
    v___x_1017_ = lean_int_neg(v___x_1016_);
    crate::leanh::lean_dec(v___x_1016_);
    v___x_1018_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_WallTime_subSeconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_WallTime_subSeconds___closed__0_once),
        _init_l_Std_Time_WallTime_subSeconds___closed__0,
    );
    v___x_1019_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime__1___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime__1___lam__0___closed__2_once),
        _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2,
    );
    v___x_1020_ = lean_int_mul(v_second_1013_, v___x_1019_);
    v___x_1021_ = lean_int_add(v___x_1020_, v_nano_1014_);
    crate::leanh::lean_dec(v___x_1020_);
    v___x_1022_ = lean_int_mul(v___x_1017_, v___x_1019_);
    crate::leanh::lean_dec(v___x_1017_);
    v___x_1023_ = lean_int_add(v___x_1022_, v___x_1018_);
    crate::leanh::lean_dec(v___x_1022_);
    v___x_1024_ = lean_int_add(v___x_1021_, v___x_1023_);
    crate::leanh::lean_dec(v___x_1023_);
    crate::leanh::lean_dec(v___x_1021_);
    v___x_1025_ = l_Std_Time_Duration_ofNanoseconds(v___x_1024_);
    crate::leanh::lean_dec(v___x_1024_);
    return v___x_1025_;
}
pub unsafe fn l_Std_Time_WallTime_subDays___boxed(
    mut v_t_1026_: *mut crate::leanh::LeanObject,
    mut v_d_1027_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1028_ = l_Std_Time_WallTime_subDays(v_t_1026_, v_d_1027_);
    crate::leanh::lean_dec(v_d_1027_);
    crate::leanh::lean_dec_ref(v_t_1026_);
    return v_res_1028_;
}
pub unsafe fn l_Std_Time_WallTime_addWeeks(
    mut v_t_1029_: *mut crate::leanh::LeanObject,
    mut v_d_1030_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_second_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_second_1031_ = crate::leanh::lean_ctor_get(v_t_1029_, 0);
    v_nano_1032_ = crate::leanh::lean_ctor_get(v_t_1029_, 1);
    v___x_1033_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime_repr___redArg___closed__7_once),
        _init_l_Std_Time_instReprWallTime_repr___redArg___closed__7,
    );
    v___x_1034_ = lean_int_mul(v_d_1030_, v___x_1033_);
    v___x_1035_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_WallTime_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_WallTime_toDays___closed__0_once),
        _init_l_Std_Time_WallTime_toDays___closed__0,
    );
    v___x_1036_ = lean_int_mul(v___x_1034_, v___x_1035_);
    crate::leanh::lean_dec(v___x_1034_);
    v___x_1037_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime_repr___redArg___closed__14),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime_repr___redArg___closed__14_once),
        _init_l_Std_Time_instReprWallTime_repr___redArg___closed__14,
    );
    v___x_1038_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime__1___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime__1___lam__0___closed__2_once),
        _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2,
    );
    v___x_1039_ = lean_int_mul(v_second_1031_, v___x_1038_);
    v___x_1040_ = lean_int_add(v___x_1039_, v_nano_1032_);
    crate::leanh::lean_dec(v___x_1039_);
    v___x_1041_ = lean_int_mul(v___x_1036_, v___x_1038_);
    crate::leanh::lean_dec(v___x_1036_);
    v___x_1042_ = lean_int_add(v___x_1041_, v___x_1037_);
    crate::leanh::lean_dec(v___x_1041_);
    v___x_1043_ = lean_int_add(v___x_1040_, v___x_1042_);
    crate::leanh::lean_dec(v___x_1042_);
    crate::leanh::lean_dec(v___x_1040_);
    v___x_1044_ = l_Std_Time_Duration_ofNanoseconds(v___x_1043_);
    crate::leanh::lean_dec(v___x_1043_);
    return v___x_1044_;
}
pub unsafe fn l_Std_Time_WallTime_addWeeks___boxed(
    mut v_t_1045_: *mut crate::leanh::LeanObject,
    mut v_d_1046_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1047_ = l_Std_Time_WallTime_addWeeks(v_t_1045_, v_d_1046_);
    crate::leanh::lean_dec(v_d_1046_);
    crate::leanh::lean_dec_ref(v_t_1045_);
    return v_res_1047_;
}
pub unsafe fn l_Std_Time_WallTime_subWeeks(
    mut v_t_1048_: *mut crate::leanh::LeanObject,
    mut v_d_1049_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_second_1050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_second_1050_ = crate::leanh::lean_ctor_get(v_t_1048_, 0);
    v_nano_1051_ = crate::leanh::lean_ctor_get(v_t_1048_, 1);
    v___x_1052_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime_repr___redArg___closed__7_once),
        _init_l_Std_Time_instReprWallTime_repr___redArg___closed__7,
    );
    v___x_1053_ = lean_int_mul(v_d_1049_, v___x_1052_);
    v___x_1054_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_WallTime_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_WallTime_toDays___closed__0_once),
        _init_l_Std_Time_WallTime_toDays___closed__0,
    );
    v___x_1055_ = lean_int_mul(v___x_1053_, v___x_1054_);
    crate::leanh::lean_dec(v___x_1053_);
    v___x_1056_ = lean_int_neg(v___x_1055_);
    crate::leanh::lean_dec(v___x_1055_);
    v___x_1057_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_WallTime_subSeconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_WallTime_subSeconds___closed__0_once),
        _init_l_Std_Time_WallTime_subSeconds___closed__0,
    );
    v___x_1058_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime__1___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime__1___lam__0___closed__2_once),
        _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2,
    );
    v___x_1059_ = lean_int_mul(v_second_1050_, v___x_1058_);
    v___x_1060_ = lean_int_add(v___x_1059_, v_nano_1051_);
    crate::leanh::lean_dec(v___x_1059_);
    v___x_1061_ = lean_int_mul(v___x_1056_, v___x_1058_);
    crate::leanh::lean_dec(v___x_1056_);
    v___x_1062_ = lean_int_add(v___x_1061_, v___x_1057_);
    crate::leanh::lean_dec(v___x_1061_);
    v___x_1063_ = lean_int_add(v___x_1060_, v___x_1062_);
    crate::leanh::lean_dec(v___x_1062_);
    crate::leanh::lean_dec(v___x_1060_);
    v___x_1064_ = l_Std_Time_Duration_ofNanoseconds(v___x_1063_);
    crate::leanh::lean_dec(v___x_1063_);
    return v___x_1064_;
}
pub unsafe fn l_Std_Time_WallTime_subWeeks___boxed(
    mut v_t_1065_: *mut crate::leanh::LeanObject,
    mut v_d_1066_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1067_ = l_Std_Time_WallTime_subWeeks(v_t_1065_, v_d_1066_);
    crate::leanh::lean_dec(v_d_1066_);
    crate::leanh::lean_dec_ref(v_t_1065_);
    return v_res_1067_;
}
pub unsafe fn l_Std_Time_WallTime_addDuration(
    mut v_t_1068_: *mut crate::leanh::LeanObject,
    mut v_d_1069_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_second_1070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_1072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_second_1070_ = crate::leanh::lean_ctor_get(v_t_1068_, 0);
    v_nano_1071_ = crate::leanh::lean_ctor_get(v_t_1068_, 1);
    v_second_1072_ = crate::leanh::lean_ctor_get(v_d_1069_, 0);
    v_nano_1073_ = crate::leanh::lean_ctor_get(v_d_1069_, 1);
    v___x_1074_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime__1___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime__1___lam__0___closed__2_once),
        _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2,
    );
    v___x_1075_ = lean_int_mul(v_second_1070_, v___x_1074_);
    v___x_1076_ = lean_int_add(v___x_1075_, v_nano_1071_);
    crate::leanh::lean_dec(v___x_1075_);
    v___x_1077_ = lean_int_mul(v_second_1072_, v___x_1074_);
    v___x_1078_ = lean_int_add(v___x_1077_, v_nano_1073_);
    crate::leanh::lean_dec(v___x_1077_);
    v___x_1079_ = lean_int_add(v___x_1076_, v___x_1078_);
    crate::leanh::lean_dec(v___x_1078_);
    crate::leanh::lean_dec(v___x_1076_);
    v___x_1080_ = l_Std_Time_Duration_ofNanoseconds(v___x_1079_);
    crate::leanh::lean_dec(v___x_1079_);
    return v___x_1080_;
}
pub unsafe fn l_Std_Time_WallTime_addDuration___boxed(
    mut v_t_1081_: *mut crate::leanh::LeanObject,
    mut v_d_1082_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1083_ = l_Std_Time_WallTime_addDuration(v_t_1081_, v_d_1082_);
    crate::leanh::lean_dec_ref(v_d_1082_);
    crate::leanh::lean_dec_ref(v_t_1081_);
    return v_res_1083_;
}
pub unsafe fn l_Std_Time_WallTime_subDuration(
    mut v_t_1084_: *mut crate::leanh::LeanObject,
    mut v_d_1085_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_second_1086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_second_1086_ = crate::leanh::lean_ctor_get(v_d_1085_, 0);
    v_nano_1087_ = crate::leanh::lean_ctor_get(v_d_1085_, 1);
    v_second_1088_ = crate::leanh::lean_ctor_get(v_t_1084_, 0);
    v_nano_1089_ = crate::leanh::lean_ctor_get(v_t_1084_, 1);
    v___x_1090_ = lean_int_neg(v_second_1086_);
    v___x_1091_ = lean_int_neg(v_nano_1087_);
    v___x_1092_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime__1___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime__1___lam__0___closed__2_once),
        _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2,
    );
    v___x_1093_ = lean_int_mul(v_second_1088_, v___x_1092_);
    v___x_1094_ = lean_int_add(v___x_1093_, v_nano_1089_);
    crate::leanh::lean_dec(v___x_1093_);
    v___x_1095_ = lean_int_mul(v___x_1090_, v___x_1092_);
    crate::leanh::lean_dec(v___x_1090_);
    v___x_1096_ = lean_int_add(v___x_1095_, v___x_1091_);
    crate::leanh::lean_dec(v___x_1091_);
    crate::leanh::lean_dec(v___x_1095_);
    v___x_1097_ = lean_int_add(v___x_1094_, v___x_1096_);
    crate::leanh::lean_dec(v___x_1096_);
    crate::leanh::lean_dec(v___x_1094_);
    v___x_1098_ = l_Std_Time_Duration_ofNanoseconds(v___x_1097_);
    crate::leanh::lean_dec(v___x_1097_);
    return v___x_1098_;
}
pub unsafe fn l_Std_Time_WallTime_subDuration___boxed(
    mut v_t_1099_: *mut crate::leanh::LeanObject,
    mut v_d_1100_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1101_ = l_Std_Time_WallTime_subDuration(v_t_1099_, v_d_1100_);
    crate::leanh::lean_dec_ref(v_d_1100_);
    crate::leanh::lean_dec_ref(v_t_1099_);
    return v_res_1101_;
}
pub unsafe fn l_Std_Time_WallTime_toDuration(
    mut v_wt_1102_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_wt_1102_);
    return v_wt_1102_;
}
pub unsafe fn l_Std_Time_WallTime_toDuration___boxed(
    mut v_wt_1103_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1104_ = l_Std_Time_WallTime_toDuration(v_wt_1103_);
    crate::leanh::lean_dec_ref(v_wt_1103_);
    return v_res_1104_;
}
pub unsafe fn l_Std_Time_WallTime_instHSubDuration__1___lam__0(
    mut v_x_1137_: *mut crate::leanh::LeanObject,
    mut v_y_1138_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_second_1139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_1141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_second_1139_ = crate::leanh::lean_ctor_get(v_y_1138_, 0);
    v_nano_1140_ = crate::leanh::lean_ctor_get(v_y_1138_, 1);
    v_second_1141_ = crate::leanh::lean_ctor_get(v_x_1137_, 0);
    v_nano_1142_ = crate::leanh::lean_ctor_get(v_x_1137_, 1);
    v___x_1143_ = lean_int_neg(v_second_1139_);
    v___x_1144_ = lean_int_neg(v_nano_1140_);
    v___x_1145_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime__1___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime__1___lam__0___closed__2_once),
        _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2,
    );
    v___x_1146_ = lean_int_mul(v_second_1141_, v___x_1145_);
    v___x_1147_ = lean_int_add(v___x_1146_, v_nano_1142_);
    crate::leanh::lean_dec(v___x_1146_);
    v___x_1148_ = lean_int_mul(v___x_1143_, v___x_1145_);
    crate::leanh::lean_dec(v___x_1143_);
    v___x_1149_ = lean_int_add(v___x_1148_, v___x_1144_);
    crate::leanh::lean_dec(v___x_1144_);
    crate::leanh::lean_dec(v___x_1148_);
    v___x_1150_ = lean_int_add(v___x_1147_, v___x_1149_);
    crate::leanh::lean_dec(v___x_1149_);
    crate::leanh::lean_dec(v___x_1147_);
    v___x_1151_ = l_Std_Time_Duration_ofNanoseconds(v___x_1150_);
    crate::leanh::lean_dec(v___x_1150_);
    return v___x_1151_;
}
pub unsafe fn l_Std_Time_WallTime_instHSubDuration__1___lam__0___boxed(
    mut v_x_1152_: *mut crate::leanh::LeanObject,
    mut v_y_1153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1154_ = l_Std_Time_WallTime_instHSubDuration__1___lam__0(v_x_1152_, v_y_1153_);
    crate::leanh::lean_dec_ref(v_y_1153_);
    crate::leanh::lean_dec_ref(v_x_1152_);
    return v_res_1154_;
}
pub unsafe fn l_Std_Time_WallTime_instOfNat(
    mut v_n_1157_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1158_ = lean_nat_to_int(v_n_1157_);
    v___x_1159_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime_repr___redArg___closed__14),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime_repr___redArg___closed__14_once),
        _init_l_Std_Time_instReprWallTime_repr___redArg___closed__14,
    );
    v___x_1160_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1160_, 0, v___x_1158_);
    crate::leanh::lean_ctor_set(v___x_1160_, 1, v___x_1159_);
    return v___x_1160_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Time_DateTime_WallTime(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_System_IO(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Duration(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Std_Time_instInhabitedWallTime_default = _init_l_Std_Time_instInhabitedWallTime_default();
    crate::leanh::lean_mark_persistent(l_Std_Time_instInhabitedWallTime_default);
    l_Std_Time_instInhabitedWallTime = _init_l_Std_Time_instInhabitedWallTime();
    crate::leanh::lean_mark_persistent(l_Std_Time_instInhabitedWallTime);
    l_Std_Time_instLEWallTime = _init_l_Std_Time_instLEWallTime();
    crate::leanh::lean_mark_persistent(l_Std_Time_instLEWallTime);
    l_Std_Time_instLTWallTime = _init_l_Std_Time_instLTWallTime();
    crate::leanh::lean_mark_persistent(l_Std_Time_instLTWallTime);
    l_Std_Time_instOrdWallTime = _init_l_Std_Time_instOrdWallTime();
    crate::leanh::lean_mark_persistent(l_Std_Time_instOrdWallTime);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Time_DateTime_WallTime(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Time_DateTime_WallTime(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_System_IO(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Time_Duration(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Time_DateTime_WallTime(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Time_DateTime_WallTime(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Time_DateTime_WallTime(builtin);
}
