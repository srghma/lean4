// Lean compiler output
// Module: Std.Time.DateTime.WallTime
// Imports: Init.System.IO Std.Time.Duration
use crate::ffi::{
    lean_int_add, lean_int_dec_eq, lean_int_dec_lt, lean_int_div, lean_int_mul, lean_int_neg,
    lean_nat_to_int, lean_string_append, lean_string_length,
};
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
pub static l_Std_Time_instReprWallTime_repr___redArg___closed__0_value:
    leanh::LeanStringObject<3> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Time_instReprWallTime_repr___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprWallTime_repr___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instReprWallTime_repr___redArg___closed__1_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Time_instReprWallTime_repr___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprWallTime_repr___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instReprWallTime_repr___redArg___closed__2_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_instReprWallTime_repr___redArg___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_instReprWallTime_repr___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprWallTime_repr___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instReprWallTime_repr___redArg___closed__3_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_instReprWallTime_repr___redArg___closed__2_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_instReprWallTime_repr___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprWallTime_repr___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instReprWallTime_repr___redArg___closed__4_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Time_instReprWallTime_repr___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprWallTime_repr___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instReprWallTime_repr___redArg___closed__5_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_instReprWallTime_repr___redArg___closed__4_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_instReprWallTime_repr___redArg___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprWallTime_repr___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instReprWallTime_repr___redArg___closed__6_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_instReprWallTime_repr___redArg___closed__3_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_instReprWallTime_repr___redArg___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_instReprWallTime_repr___redArg___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprWallTime_repr___redArg___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_instReprWallTime_repr___redArg___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instReprWallTime_repr___redArg___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_instReprWallTime_repr___redArg___closed__8_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Time_instReprWallTime_repr___redArg___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprWallTime_repr___redArg___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instReprWallTime_repr___redArg___closed__9_value:
    leanh::LeanStringObject<3> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Time_instReprWallTime_repr___redArg___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprWallTime_repr___redArg___closed__9_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_instReprWallTime_repr___redArg___closed__10_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instReprWallTime_repr___redArg___closed__10: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instReprWallTime_repr___redArg___closed__11_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instReprWallTime_repr___redArg___closed__11: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_instReprWallTime_repr___redArg___closed__12_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_instReprWallTime_repr___redArg___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_instReprWallTime_repr___redArg___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprWallTime_repr___redArg___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instReprWallTime_repr___redArg___closed__13_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_instReprWallTime_repr___redArg___closed__9_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_instReprWallTime_repr___redArg___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprWallTime_repr___redArg___closed__13_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_instReprWallTime_repr___redArg___closed__14_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instReprWallTime_repr___redArg___closed__14: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_instReprWallTime_repr___redArg___closed__15_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Time_instReprWallTime_repr___redArg___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprWallTime_repr___redArg___closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instReprWallTime_repr___redArg___closed__16_value:
    leanh::LeanStringObject<1> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Time_instReprWallTime_repr___redArg___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprWallTime_repr___redArg___closed__16_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instReprWallTime_repr___redArg___closed__17_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Time_instReprWallTime_repr___redArg___closed__17: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprWallTime_repr___redArg___closed__17_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instReprWallTime___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instReprWallTime_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instReprWallTime___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprWallTime___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instReprWallTime: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprWallTime___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_instInhabitedWallTime_default___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedWallTime_default___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_instInhabitedWallTime_default: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_instInhabitedWallTime: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_instLEWallTime: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Std_Time_instLTWallTime: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Time_instOrdWallTime___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instOrdWallTime___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instOrdWallTime___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdWallTime___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_instOrdWallTime___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instOrdWallTime___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_instOrdWallTime: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Time_instToStringWallTime___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instToStringWallTime___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instToStringWallTime___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instToStringWallTime___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instToStringWallTime: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instToStringWallTime___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instReprWallTime__1___lam__0___closed__0_value:
    leanh::LeanStringObject<24> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Time_instReprWallTime__1___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprWallTime__1___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instReprWallTime__1___lam__0___closed__1_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_instReprWallTime__1___lam__0___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_instReprWallTime__1___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprWallTime__1___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_instReprWallTime__1___lam__0___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instReprWallTime__1___lam__0___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_instReprWallTime__1___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instReprWallTime__1___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instReprWallTime__1___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprWallTime__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instReprWallTime__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprWallTime__1___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_WallTime_toMinutes___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_WallTime_toMinutes___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_WallTime_toDays___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_WallTime_toDays___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_WallTime_ofMilliseconds___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_WallTime_ofMilliseconds___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_WallTime_subSeconds___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_WallTime_subSeconds___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_WallTime_addHours___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_WallTime_addHours___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_WallTime_instHAddDuration___closed__0_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Time_WallTime_addDuration___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_WallTime_instHAddDuration___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_WallTime_instHAddDuration___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_WallTime_instHAddDuration: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_WallTime_instHAddDuration___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_WallTime_instHSubDuration___closed__0_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Time_WallTime_subDuration___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_WallTime_instHSubDuration___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_WallTime_instHSubDuration___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_WallTime_instHSubDuration: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_WallTime_instHSubDuration___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_WallTime_instHAddOffset___closed__0_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Time_WallTime_addDays___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_WallTime_instHAddOffset___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_WallTime_instHAddOffset___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_WallTime_instHAddOffset: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_WallTime_instHAddOffset___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_WallTime_instHSubOffset___closed__0_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Time_WallTime_subDays___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_WallTime_instHSubOffset___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_WallTime_instHSubOffset___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_WallTime_instHSubOffset: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_WallTime_instHSubOffset___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_WallTime_instHAddOffset__1___closed__0_value:
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
    m_fun: l_Std_Time_WallTime_addWeeks___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_WallTime_instHAddOffset__1___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_WallTime_instHAddOffset__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_WallTime_instHAddOffset__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_WallTime_instHAddOffset__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_WallTime_instHSubOffset__1___closed__0_value:
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
    m_fun: l_Std_Time_WallTime_subWeeks___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_WallTime_instHSubOffset__1___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_WallTime_instHSubOffset__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_WallTime_instHSubOffset__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_WallTime_instHSubOffset__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_WallTime_instHAddOffset__2___closed__0_value:
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
    m_fun: l_Std_Time_WallTime_addHours___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_WallTime_instHAddOffset__2___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_WallTime_instHAddOffset__2___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_WallTime_instHAddOffset__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_WallTime_instHAddOffset__2___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_WallTime_instHSubOffset__2___closed__0_value:
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
    m_fun: l_Std_Time_WallTime_subHours___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_WallTime_instHSubOffset__2___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_WallTime_instHSubOffset__2___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_WallTime_instHSubOffset__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_WallTime_instHSubOffset__2___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_WallTime_instHAddOffset__3___closed__0_value:
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
    m_fun: l_Std_Time_WallTime_addMinutes___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_WallTime_instHAddOffset__3___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_WallTime_instHAddOffset__3___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_WallTime_instHAddOffset__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_WallTime_instHAddOffset__3___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_WallTime_instHSubOffset__3___closed__0_value:
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
    m_fun: l_Std_Time_WallTime_subMinutes___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_WallTime_instHSubOffset__3___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_WallTime_instHSubOffset__3___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_WallTime_instHSubOffset__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_WallTime_instHSubOffset__3___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_WallTime_instHAddOffset__4___closed__0_value:
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
    m_fun: l_Std_Time_WallTime_addSeconds___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_WallTime_instHAddOffset__4___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_WallTime_instHAddOffset__4___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_WallTime_instHAddOffset__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_WallTime_instHAddOffset__4___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_WallTime_instHSubOffset__4___closed__0_value:
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
    m_fun: l_Std_Time_WallTime_subSeconds___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_WallTime_instHSubOffset__4___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_WallTime_instHSubOffset__4___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_WallTime_instHSubOffset__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_WallTime_instHSubOffset__4___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_WallTime_instHAddOffset__5___closed__0_value:
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
    m_fun: l_Std_Time_WallTime_addMilliseconds___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_WallTime_instHAddOffset__5___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_WallTime_instHAddOffset__5___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_WallTime_instHAddOffset__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_WallTime_instHAddOffset__5___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_WallTime_instHSubOffset__5___closed__0_value:
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
    m_fun: l_Std_Time_WallTime_subMilliseconds___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_WallTime_instHSubOffset__5___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_WallTime_instHSubOffset__5___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_WallTime_instHSubOffset__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_WallTime_instHSubOffset__5___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_WallTime_instHAddOffset__6___closed__0_value:
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
    m_fun: l_Std_Time_WallTime_addNanoseconds___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_WallTime_instHAddOffset__6___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_WallTime_instHAddOffset__6___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_WallTime_instHAddOffset__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_WallTime_instHAddOffset__6___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_WallTime_instHSubOffset__6___closed__0_value:
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
    m_fun: l_Std_Time_WallTime_subNanoseconds___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_WallTime_instHSubOffset__6___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_WallTime_instHSubOffset__6___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_WallTime_instHSubOffset__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_WallTime_instHSubOffset__6___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_WallTime_instHSubDuration__1___closed__0_value:
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
    m_fun: l_Std_Time_WallTime_instHSubDuration__1___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_WallTime_instHSubDuration__1___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_WallTime_instHSubDuration__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_WallTime_instHSubDuration__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_WallTime_instHSubDuration__1___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Nat_cast___at___00Std_Time_instReprWallTime_repr_spec__0(
    mut v_a_581_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_582_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_582_ = lean_nat_to_int(v_a_581_);
    return v___x_582_;
}
pub unsafe fn _init_l_Std_Time_instReprWallTime_repr___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_597_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_596_ = leanh::lean_unsigned_to_nat(7);
    v___x_597_ = lean_nat_to_int(v___x_596_);
    return v___x_597_;
}
pub unsafe fn _init_l_Std_Time_instReprWallTime_repr___redArg___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_601_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_600_ = l_Std_Time_instReprWallTime_repr___redArg___closed__0;
    v___x_601_ = lean_string_length(v___x_600_);
    return v___x_601_;
}
pub unsafe fn _init_l_Std_Time_instReprWallTime_repr___redArg___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_603_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_602_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime_repr___redArg___closed__10),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime_repr___redArg___closed__10_once),
        _init_l_Std_Time_instReprWallTime_repr___redArg___closed__10,
    );
    v___x_603_ = lean_nat_to_int(v___x_602_);
    return v___x_603_;
}
pub unsafe fn _init_l_Std_Time_instReprWallTime_repr___redArg___closed__14()
-> *mut leanh::LeanObject {
    let mut v___x_608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_609_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_608_ = leanh::lean_unsigned_to_nat(0);
    v___x_609_ = lean_nat_to_int(v___x_608_);
    return v___x_609_;
}
pub unsafe fn l_Std_Time_instReprWallTime_repr___redArg(
    mut v_x_613_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_second_614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_618_: u8 = 0;
    let mut v___x_619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_631_: u8 = 0;
    let mut v___x_632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_649_: u8 = 0;
    let mut v___x_650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_657_: u8 = 0;
    let mut v___x_658_: u8 = 0;
    let mut v___x_659_: u8 = 0;
    let mut v___x_660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_668_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_second_614_ = leanh::lean_ctor_get(v_x_613_, 0);
                v_nano_615_ = leanh::lean_ctor_get(v_x_613_, 1);
                v_isSharedCheck_668_ = (!leanh::lean_is_exclusive(v_x_613_)) as u8;
                if v_isSharedCheck_668_ == 0 {
                    v___x_617_ = v_x_613_;
                    v_isShared_618_ = v_isSharedCheck_668_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_nano_615_);
                    leanh::lean_inc(v_second_614_);
                    leanh::lean_dec(v_x_613_);
                    v___x_617_ = leanh::lean_box(0);
                    v_isShared_618_ = v_isSharedCheck_668_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_619_ = l_Std_Time_instReprWallTime_repr___redArg___closed__6;
                v___x_620_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime_repr___redArg___closed__7),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprWallTime_repr___redArg___closed__7_once
                    ),
                    _init_l_Std_Time_instReprWallTime_repr___redArg___closed__7,
                );
                v___x_656_ = leanh::lean_obj_once(
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
                            leanh::lean_inc(v_nano_615_);
                            v_fst_643_ = v___x_660_;
                            v_fst_644_ = v_second_614_;
                            v_snd_645_ = v_nano_615_;
                            state = 4;
                            continue;
                        } else {
                            v___x_661_ = l_Std_Time_instReprWallTime_repr___redArg___closed__17;
                            v___x_662_ = lean_int_neg(v_second_614_);
                            leanh::lean_dec(v_second_614_);
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
                        leanh::lean_dec(v_second_614_);
                        v___x_666_ = lean_int_neg(v_nano_615_);
                        v_fst_643_ = v___x_664_;
                        v_fst_644_ = v___x_665_;
                        v_snd_645_ = v___x_666_;
                        state = 4;
                        continue;
                    }
                } else {
                    v___x_667_ = l_Std_Time_instReprWallTime_repr___redArg___closed__16;
                    leanh::lean_inc(v_nano_615_);
                    v_fst_643_ = v___x_667_;
                    v_fst_644_ = v_second_614_;
                    v_snd_645_ = v_nano_615_;
                    state = 4;
                    continue;
                }
            }
            2 => {
                v___x_624_ = lean_string_append(v___y_622_, v___y_623_);
                leanh::lean_dec_ref(v___y_623_);
                v___x_625_ = l_Std_Time_instReprWallTime_repr___redArg___closed__8;
                v___x_626_ = lean_string_append(v___x_624_, v___x_625_);
                v___x_627_ = l_String_quote(v___x_626_);
                v___x_628_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_628_, 0, v___x_627_);
                if v_isShared_618_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_617_, 4);
                    leanh::lean_ctor_set(v___x_617_, 1, v___x_628_);
                    leanh::lean_ctor_set(v___x_617_, 0, v___x_620_);
                    v___x_630_ = v___x_617_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_641_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_641_, 0, v___x_620_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_641_, 1, v___x_628_);
                    v___x_630_ = v_reuseFailAlloc_641_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_631_ = 0;
                v___x_632_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_632_, 0, v___x_630_);
                leanh::lean_ctor_set_uint8(
                    v___x_632_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_631_,
                );
                v___x_633_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_633_, 0, v___x_619_);
                leanh::lean_ctor_set(v___x_633_, 1, v___x_632_);
                v___x_634_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime_repr___redArg___closed__11),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprWallTime_repr___redArg___closed__11_once
                    ),
                    _init_l_Std_Time_instReprWallTime_repr___redArg___closed__11,
                );
                v___x_635_ = l_Std_Time_instReprWallTime_repr___redArg___closed__12;
                v___x_636_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_636_, 0, v___x_635_);
                leanh::lean_ctor_set(v___x_636_, 1, v___x_633_);
                v___x_637_ = l_Std_Time_instReprWallTime_repr___redArg___closed__13;
                v___x_638_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_638_, 0, v___x_636_);
                leanh::lean_ctor_set(v___x_638_, 1, v___x_637_);
                v___x_639_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_639_, 0, v___x_634_);
                leanh::lean_ctor_set(v___x_639_, 1, v___x_638_);
                v___x_640_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_640_, 0, v___x_639_);
                leanh::lean_ctor_set_uint8(
                    v___x_640_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_631_,
                );
                return v___x_640_;
            }
            4 => {
                v___x_646_ = l_Int_repr(v_fst_644_);
                leanh::lean_dec(v_fst_644_);
                leanh::lean_inc_ref(v_fst_643_);
                v___x_647_ = lean_string_append(v_fst_643_, v___x_646_);
                leanh::lean_dec_ref(v___x_646_);
                v___x_648_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime_repr___redArg___closed__14),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprWallTime_repr___redArg___closed__14_once
                    ),
                    _init_l_Std_Time_instReprWallTime_repr___redArg___closed__14,
                );
                v___x_649_ = lean_int_dec_eq(v_nano_615_, v___x_648_);
                leanh::lean_dec(v_nano_615_);
                if v___x_649_ == 0 {
                    v___x_650_ = l_Std_Time_instReprWallTime_repr___redArg___closed__15;
                    v___x_651_ = leanh::lean_unsigned_to_nat(9);
                    v___x_652_ = l_Int_repr(v_snd_645_);
                    leanh::lean_dec(v_snd_645_);
                    v___x_653_ = l_Std_Time_instToStringDuration_leftPad(v___x_651_, v___x_652_);
                    leanh::lean_dec_ref(v___x_652_);
                    v___x_654_ = lean_string_append(v___x_650_, v___x_653_);
                    leanh::lean_dec_ref(v___x_653_);
                    v___y_622_ = v___x_647_;
                    v___y_623_ = v___x_654_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_snd_645_);
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
    mut v_x_669_: *mut leanh::LeanObject,
    mut v_prec_670_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_671_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_671_ = l_Std_Time_instReprWallTime_repr___redArg(v_x_669_);
    return v___x_671_;
}
pub unsafe fn l_Std_Time_instReprWallTime_repr___boxed(
    mut v_x_672_: *mut leanh::LeanObject,
    mut v_prec_673_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_674_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_674_ = l_Std_Time_instReprWallTime_repr(v_x_672_, v_prec_673_);
    leanh::lean_dec(v_prec_673_);
    return v_res_674_;
}
pub unsafe fn l_Std_Time_instDecidableEqWallTime_decEq(
    mut v_x_677_: *mut leanh::LeanObject,
    mut v_x_678_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_679_: u8 = 0;
    v___x_679_ = l_Std_Time_instDecidableEqDuration_decEq(v_x_677_, v_x_678_);
    return v___x_679_;
}
pub unsafe fn l_Std_Time_instDecidableEqWallTime_decEq___boxed(
    mut v_x_680_: *mut leanh::LeanObject,
    mut v_x_681_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_682_: u8 = 0;
    let mut v_r_683_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_682_ = l_Std_Time_instDecidableEqWallTime_decEq(v_x_680_, v_x_681_);
    leanh::lean_dec_ref(v_x_681_);
    leanh::lean_dec_ref(v_x_680_);
    v_r_683_ = leanh::lean_box((v_res_682_) as usize);
    return v_r_683_;
}
pub unsafe fn l_Std_Time_instDecidableEqWallTime(
    mut v_x_684_: *mut leanh::LeanObject,
    mut v_x_685_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_686_: u8 = 0;
    v___x_686_ = l_Std_Time_instDecidableEqDuration_decEq(v_x_684_, v_x_685_);
    return v___x_686_;
}
pub unsafe fn l_Std_Time_instDecidableEqWallTime___boxed(
    mut v_x_687_: *mut leanh::LeanObject,
    mut v_x_688_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_689_: u8 = 0;
    let mut v_r_690_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_689_ = l_Std_Time_instDecidableEqWallTime(v_x_687_, v_x_688_);
    leanh::lean_dec_ref(v_x_688_);
    leanh::lean_dec_ref(v_x_687_);
    v_r_690_ = leanh::lean_box((v_res_689_) as usize);
    return v_r_690_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedWallTime_default___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_692_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_691_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime_repr___redArg___closed__14),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime_repr___redArg___closed__14_once),
        _init_l_Std_Time_instReprWallTime_repr___redArg___closed__14,
    );
    v___x_692_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_692_, 0, v___x_691_);
    leanh::lean_ctor_set(v___x_692_, 1, v___x_691_);
    return v___x_692_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedWallTime_default() -> *mut leanh::LeanObject {
    let mut v___x_693_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_693_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedWallTime_default___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedWallTime_default___closed__0_once),
        _init_l_Std_Time_instInhabitedWallTime_default___closed__0,
    );
    return v___x_693_;
}
pub unsafe fn l_Nat_cast___at___00Std_Time_instInhabitedWallTime_default_spec__0(
    mut v_a_694_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_696_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_695_ = lean_nat_to_int(v_a_694_);
    v___x_696_ = l_Rat_ofInt(v___x_695_);
    return v___x_696_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedWallTime() -> *mut leanh::LeanObject {
    let mut v___x_697_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_697_ = l_Std_Time_instInhabitedWallTime_default;
    return v___x_697_;
}
pub unsafe fn _init_l_Std_Time_instLEWallTime() -> *mut leanh::LeanObject {
    let mut v___x_698_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_698_ = leanh::lean_box(0);
    return v___x_698_;
}
pub unsafe fn l_Std_Time_instDecidableLeWallTime(
    mut v_x_699_: *mut leanh::LeanObject,
    mut v_y_700_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_701_: u8 = 0;
    v___x_701_ = l_Std_Time_Duration_instDecidableLe(v_x_699_, v_y_700_);
    return v___x_701_;
}
pub unsafe fn l_Std_Time_instDecidableLeWallTime___boxed(
    mut v_x_702_: *mut leanh::LeanObject,
    mut v_y_703_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_704_: u8 = 0;
    let mut v_r_705_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_704_ = l_Std_Time_instDecidableLeWallTime(v_x_702_, v_y_703_);
    leanh::lean_dec_ref(v_y_703_);
    leanh::lean_dec_ref(v_x_702_);
    v_r_705_ = leanh::lean_box((v_res_704_) as usize);
    return v_r_705_;
}
pub unsafe fn _init_l_Std_Time_instLTWallTime() -> *mut leanh::LeanObject {
    let mut v___x_706_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_706_ = leanh::lean_box(0);
    return v___x_706_;
}
pub unsafe fn l_Std_Time_instDecidableLtWallTime(
    mut v_x_707_: *mut leanh::LeanObject,
    mut v_y_708_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_709_: u8 = 0;
    v___x_709_ = l_Std_Time_Duration_instDecidableLt(v_x_707_, v_y_708_);
    return v___x_709_;
}
pub unsafe fn l_Std_Time_instDecidableLtWallTime___boxed(
    mut v_x_710_: *mut leanh::LeanObject,
    mut v_y_711_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_712_: u8 = 0;
    let mut v_r_713_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_712_ = l_Std_Time_instDecidableLtWallTime(v_x_710_, v_y_711_);
    leanh::lean_dec_ref(v_y_711_);
    leanh::lean_dec_ref(v_x_710_);
    v_r_713_ = leanh::lean_box((v_res_712_) as usize);
    return v_r_713_;
}
pub unsafe fn l_Std_Time_instOrdWallTime___lam__0(
    mut v_x_714_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v_x_714_);
    return v_x_714_;
}
pub unsafe fn l_Std_Time_instOrdWallTime___lam__0___boxed(
    mut v_x_715_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_716_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_716_ = l_Std_Time_instOrdWallTime___lam__0(v_x_715_);
    leanh::lean_dec_ref(v_x_715_);
    return v_res_716_;
}
pub unsafe fn _init_l_Std_Time_instOrdWallTime___closed__1() -> *mut leanh::LeanObject {
    let mut v___f_718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_720_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_718_ = l_Std_Time_instOrdWallTime___closed__0;
    v___x_719_ = l_Std_Time_instOrdDuration;
    v___x_720_ =
        leanh::lean_alloc_closure(l_compareOn___boxed as *mut core::ffi::c_void, 6, 4);
    leanh::lean_closure_set(v___x_720_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_720_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_720_, 2, v___x_719_);
    leanh::lean_closure_set(v___x_720_, 3, v___f_718_);
    return v___x_720_;
}
pub unsafe fn _init_l_Std_Time_instOrdWallTime() -> *mut leanh::LeanObject {
    let mut v___x_721_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_721_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instOrdWallTime___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_instOrdWallTime___closed__1_once),
        _init_l_Std_Time_instOrdWallTime___closed__1,
    );
    return v___x_721_;
}
pub unsafe fn l_Std_Time_instToStringWallTime___lam__0(
    mut v_s_722_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_second_723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_724_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_second_723_ = leanh::lean_ctor_get(v_s_722_, 0);
    v___x_724_ = l_Int_repr(v_second_723_);
    return v___x_724_;
}
pub unsafe fn l_Std_Time_instToStringWallTime___lam__0___boxed(
    mut v_s_725_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_726_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_726_ = l_Std_Time_instToStringWallTime___lam__0(v_s_725_);
    leanh::lean_dec_ref(v_s_725_);
    return v_res_726_;
}
pub unsafe fn _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_733_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_732_ = leanh::lean_unsigned_to_nat(1000000000);
    v___x_733_ = lean_nat_to_int(v___x_732_);
    return v___x_733_;
}
pub unsafe fn l_Std_Time_instReprWallTime__1___lam__0(
    mut v_s_734_: *mut leanh::LeanObject,
    mut v___y_735_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_second_736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_740_: u8 = 0;
    let mut v___x_741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nanos_744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_751_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_second_736_ = leanh::lean_ctor_get(v_s_734_, 0);
                v_nano_737_ = leanh::lean_ctor_get(v_s_734_, 1);
                v_isSharedCheck_751_ = (!leanh::lean_is_exclusive(v_s_734_)) as u8;
                if v_isSharedCheck_751_ == 0 {
                    v___x_739_ = v_s_734_;
                    v_isShared_740_ = v_isSharedCheck_751_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_nano_737_);
                    leanh::lean_inc(v_second_736_);
                    leanh::lean_dec(v_s_734_);
                    v___x_739_ = leanh::lean_box(0);
                    v_isShared_740_ = v_isSharedCheck_751_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_741_ = l_Std_Time_instReprWallTime__1___lam__0___closed__1;
                v___x_742_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime__1___lam__0___closed__2),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprWallTime__1___lam__0___closed__2_once
                    ),
                    _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2,
                );
                v___x_743_ = lean_int_mul(v_second_736_, v___x_742_);
                leanh::lean_dec(v_second_736_);
                v_nanos_744_ = lean_int_add(v___x_743_, v_nano_737_);
                leanh::lean_dec(v_nano_737_);
                leanh::lean_dec(v___x_743_);
                v___x_745_ = leanh::lean_unsigned_to_nat(0);
                v___x_746_ =
                    l_Std_Time_Nanosecond_instReprOrdinal___lam__0(v_nanos_744_, v___x_745_);
                leanh::lean_dec(v_nanos_744_);
                if v_isShared_740_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_739_, 5);
                    leanh::lean_ctor_set(v___x_739_, 1, v___x_746_);
                    leanh::lean_ctor_set(v___x_739_, 0, v___x_741_);
                    v___x_748_ = v___x_739_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_750_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_750_, 0, v___x_741_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_750_, 1, v___x_746_);
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
    mut v_s_752_: *mut leanh::LeanObject,
    mut v___y_753_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_754_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_754_ = l_Std_Time_instReprWallTime__1___lam__0(v_s_752_, v___y_753_);
    leanh::lean_dec(v___y_753_);
    return v_res_754_;
}
pub unsafe fn l_Std_Time_WallTime_ofDuration(
    mut v_duration_757_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v_duration_757_);
    return v_duration_757_;
}
pub unsafe fn l_Std_Time_WallTime_ofDuration___boxed(
    mut v_duration_758_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_759_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_759_ = l_Std_Time_WallTime_ofDuration(v_duration_758_);
    leanh::lean_dec_ref(v_duration_758_);
    return v_res_759_;
}
pub unsafe fn l_Std_Time_WallTime_ofSeconds(
    mut v_secs_760_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_762_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_761_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime_repr___redArg___closed__14),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime_repr___redArg___closed__14_once),
        _init_l_Std_Time_instReprWallTime_repr___redArg___closed__14,
    );
    v___x_762_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_762_, 0, v_secs_760_);
    leanh::lean_ctor_set(v___x_762_, 1, v___x_761_);
    return v___x_762_;
}
pub unsafe fn l_Std_Time_WallTime_ofNanoseconds(
    mut v_nanos_763_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_764_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_764_ = l_Std_Time_Duration_ofNanoseconds(v_nanos_763_);
    return v___x_764_;
}
pub unsafe fn l_Std_Time_WallTime_ofNanoseconds___boxed(
    mut v_nanos_765_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_766_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_766_ = l_Std_Time_WallTime_ofNanoseconds(v_nanos_765_);
    leanh::lean_dec(v_nanos_765_);
    return v_res_766_;
}
pub unsafe fn l_Std_Time_WallTime_toSeconds(
    mut v_wt_767_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_second_768_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_second_768_ = leanh::lean_ctor_get(v_wt_767_, 0);
    leanh::lean_inc(v_second_768_);
    return v_second_768_;
}
pub unsafe fn l_Std_Time_WallTime_toSeconds___boxed(
    mut v_wt_769_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_770_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_770_ = l_Std_Time_WallTime_toSeconds(v_wt_769_);
    leanh::lean_dec_ref(v_wt_769_);
    return v_res_770_;
}
pub unsafe fn l_Std_Time_WallTime_toNanoseconds(
    mut v_wt_771_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_second_772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nanos_776_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_second_772_ = leanh::lean_ctor_get(v_wt_771_, 0);
    v_nano_773_ = leanh::lean_ctor_get(v_wt_771_, 1);
    v___x_774_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime__1___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime__1___lam__0___closed__2_once),
        _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2,
    );
    v___x_775_ = lean_int_mul(v_second_772_, v___x_774_);
    v_nanos_776_ = lean_int_add(v___x_775_, v_nano_773_);
    leanh::lean_dec(v___x_775_);
    return v_nanos_776_;
}
pub unsafe fn l_Std_Time_WallTime_toNanoseconds___boxed(
    mut v_wt_777_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_778_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_778_ = l_Std_Time_WallTime_toNanoseconds(v_wt_777_);
    leanh::lean_dec_ref(v_wt_777_);
    return v_res_778_;
}
pub unsafe fn _init_l_Std_Time_WallTime_toMinutes___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_780_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_779_ = leanh::lean_unsigned_to_nat(60);
    v___x_780_ = lean_nat_to_int(v___x_779_);
    return v___x_780_;
}
pub unsafe fn l_Std_Time_WallTime_toMinutes(
    mut v_tm_781_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_second_782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_784_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_second_782_ = leanh::lean_ctor_get(v_tm_781_, 0);
    v___x_783_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_WallTime_toMinutes___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_WallTime_toMinutes___closed__0_once),
        _init_l_Std_Time_WallTime_toMinutes___closed__0,
    );
    v___x_784_ = lean_int_div(v_second_782_, v___x_783_);
    return v___x_784_;
}
pub unsafe fn l_Std_Time_WallTime_toMinutes___boxed(
    mut v_tm_785_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_786_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_786_ = l_Std_Time_WallTime_toMinutes(v_tm_785_);
    leanh::lean_dec_ref(v_tm_785_);
    return v_res_786_;
}
pub unsafe fn _init_l_Std_Time_WallTime_toDays___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_788_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_787_ = leanh::lean_unsigned_to_nat(86400);
    v___x_788_ = lean_nat_to_int(v___x_787_);
    return v___x_788_;
}
pub unsafe fn l_Std_Time_WallTime_toDays(
    mut v_tm_789_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_second_790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_792_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_second_790_ = leanh::lean_ctor_get(v_tm_789_, 0);
    v___x_791_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_WallTime_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_WallTime_toDays___closed__0_once),
        _init_l_Std_Time_WallTime_toDays___closed__0,
    );
    v___x_792_ = lean_int_div(v_second_790_, v___x_791_);
    return v___x_792_;
}
pub unsafe fn l_Std_Time_WallTime_toDays___boxed(
    mut v_tm_793_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_794_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_794_ = l_Std_Time_WallTime_toDays(v_tm_793_);
    leanh::lean_dec_ref(v_tm_793_);
    return v_res_794_;
}
pub unsafe fn _init_l_Std_Time_WallTime_ofMilliseconds___closed__0() -> *mut leanh::LeanObject
{
    let mut v___x_795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_796_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_795_ = leanh::lean_unsigned_to_nat(1000000);
    v___x_796_ = lean_nat_to_int(v___x_795_);
    return v___x_796_;
}
pub unsafe fn l_Std_Time_WallTime_ofMilliseconds(
    mut v_milli_797_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_800_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_798_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_WallTime_ofMilliseconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_WallTime_ofMilliseconds___closed__0_once),
        _init_l_Std_Time_WallTime_ofMilliseconds___closed__0,
    );
    v___x_799_ = lean_int_mul(v_milli_797_, v___x_798_);
    v___x_800_ = l_Std_Time_Duration_ofNanoseconds(v___x_799_);
    leanh::lean_dec(v___x_799_);
    return v___x_800_;
}
pub unsafe fn l_Std_Time_WallTime_ofMilliseconds___boxed(
    mut v_milli_801_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_802_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_802_ = l_Std_Time_WallTime_ofMilliseconds(v_milli_801_);
    leanh::lean_dec(v_milli_801_);
    return v_res_802_;
}
pub unsafe fn l_Std_Time_WallTime_toMilliseconds(
    mut v_tm_803_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_second_804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_810_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_second_804_ = leanh::lean_ctor_get(v_tm_803_, 0);
    v_nano_805_ = leanh::lean_ctor_get(v_tm_803_, 1);
    v___x_806_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime__1___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime__1___lam__0___closed__2_once),
        _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2,
    );
    v___x_807_ = lean_int_mul(v_second_804_, v___x_806_);
    v___x_808_ = lean_int_add(v___x_807_, v_nano_805_);
    leanh::lean_dec(v___x_807_);
    v___x_809_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_WallTime_ofMilliseconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_WallTime_ofMilliseconds___closed__0_once),
        _init_l_Std_Time_WallTime_ofMilliseconds___closed__0,
    );
    v___x_810_ = lean_int_div(v___x_808_, v___x_809_);
    leanh::lean_dec(v___x_808_);
    return v___x_810_;
}
pub unsafe fn l_Std_Time_WallTime_toMilliseconds___boxed(
    mut v_tm_811_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_812_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_812_ = l_Std_Time_WallTime_toMilliseconds(v_tm_811_);
    leanh::lean_dec_ref(v_tm_811_);
    return v_res_812_;
}
pub unsafe fn l_Std_Time_WallTime_addMilliseconds(
    mut v_t_813_: *mut leanh::LeanObject,
    mut v_s_814_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_second_815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_828_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_second_815_ = leanh::lean_ctor_get(v_t_813_, 0);
    v_nano_816_ = leanh::lean_ctor_get(v_t_813_, 1);
    v___x_817_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_WallTime_ofMilliseconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_WallTime_ofMilliseconds___closed__0_once),
        _init_l_Std_Time_WallTime_ofMilliseconds___closed__0,
    );
    v___x_818_ = lean_int_mul(v_s_814_, v___x_817_);
    v___x_819_ = l_Std_Time_Duration_ofNanoseconds(v___x_818_);
    leanh::lean_dec(v___x_818_);
    v_second_820_ = leanh::lean_ctor_get(v___x_819_, 0);
    leanh::lean_inc(v_second_820_);
    v_nano_821_ = leanh::lean_ctor_get(v___x_819_, 1);
    leanh::lean_inc(v_nano_821_);
    leanh::lean_dec_ref(v___x_819_);
    v___x_822_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime__1___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime__1___lam__0___closed__2_once),
        _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2,
    );
    v___x_823_ = lean_int_mul(v_second_815_, v___x_822_);
    v___x_824_ = lean_int_add(v___x_823_, v_nano_816_);
    leanh::lean_dec(v___x_823_);
    v___x_825_ = lean_int_mul(v_second_820_, v___x_822_);
    leanh::lean_dec(v_second_820_);
    v___x_826_ = lean_int_add(v___x_825_, v_nano_821_);
    leanh::lean_dec(v_nano_821_);
    leanh::lean_dec(v___x_825_);
    v___x_827_ = lean_int_add(v___x_824_, v___x_826_);
    leanh::lean_dec(v___x_826_);
    leanh::lean_dec(v___x_824_);
    v___x_828_ = l_Std_Time_Duration_ofNanoseconds(v___x_827_);
    leanh::lean_dec(v___x_827_);
    return v___x_828_;
}
pub unsafe fn l_Std_Time_WallTime_addMilliseconds___boxed(
    mut v_t_829_: *mut leanh::LeanObject,
    mut v_s_830_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_831_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_831_ = l_Std_Time_WallTime_addMilliseconds(v_t_829_, v_s_830_);
    leanh::lean_dec(v_s_830_);
    leanh::lean_dec_ref(v_t_829_);
    return v_res_831_;
}
pub unsafe fn l_Std_Time_WallTime_subMilliseconds(
    mut v_t_832_: *mut leanh::LeanObject,
    mut v_s_833_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_849_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_834_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_WallTime_ofMilliseconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_WallTime_ofMilliseconds___closed__0_once),
        _init_l_Std_Time_WallTime_ofMilliseconds___closed__0,
    );
    v___x_835_ = lean_int_mul(v_s_833_, v___x_834_);
    v___x_836_ = l_Std_Time_Duration_ofNanoseconds(v___x_835_);
    leanh::lean_dec(v___x_835_);
    v_second_837_ = leanh::lean_ctor_get(v___x_836_, 0);
    leanh::lean_inc(v_second_837_);
    v_nano_838_ = leanh::lean_ctor_get(v___x_836_, 1);
    leanh::lean_inc(v_nano_838_);
    leanh::lean_dec_ref(v___x_836_);
    v_second_839_ = leanh::lean_ctor_get(v_t_832_, 0);
    v_nano_840_ = leanh::lean_ctor_get(v_t_832_, 1);
    v___x_841_ = lean_int_neg(v_second_837_);
    leanh::lean_dec(v_second_837_);
    v___x_842_ = lean_int_neg(v_nano_838_);
    leanh::lean_dec(v_nano_838_);
    v___x_843_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime__1___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime__1___lam__0___closed__2_once),
        _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2,
    );
    v___x_844_ = lean_int_mul(v_second_839_, v___x_843_);
    v___x_845_ = lean_int_add(v___x_844_, v_nano_840_);
    leanh::lean_dec(v___x_844_);
    v___x_846_ = lean_int_mul(v___x_841_, v___x_843_);
    leanh::lean_dec(v___x_841_);
    v___x_847_ = lean_int_add(v___x_846_, v___x_842_);
    leanh::lean_dec(v___x_842_);
    leanh::lean_dec(v___x_846_);
    v___x_848_ = lean_int_add(v___x_845_, v___x_847_);
    leanh::lean_dec(v___x_847_);
    leanh::lean_dec(v___x_845_);
    v___x_849_ = l_Std_Time_Duration_ofNanoseconds(v___x_848_);
    leanh::lean_dec(v___x_848_);
    return v___x_849_;
}
pub unsafe fn l_Std_Time_WallTime_subMilliseconds___boxed(
    mut v_t_850_: *mut leanh::LeanObject,
    mut v_s_851_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_852_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_852_ = l_Std_Time_WallTime_subMilliseconds(v_t_850_, v_s_851_);
    leanh::lean_dec(v_s_851_);
    leanh::lean_dec_ref(v_t_850_);
    return v_res_852_;
}
pub unsafe fn l_Std_Time_WallTime_addNanoseconds(
    mut v_t_853_: *mut leanh::LeanObject,
    mut v_s_854_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_second_855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_866_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_second_855_ = leanh::lean_ctor_get(v_t_853_, 0);
    v_nano_856_ = leanh::lean_ctor_get(v_t_853_, 1);
    v___x_857_ = l_Std_Time_Duration_ofNanoseconds(v_s_854_);
    v_second_858_ = leanh::lean_ctor_get(v___x_857_, 0);
    leanh::lean_inc(v_second_858_);
    v_nano_859_ = leanh::lean_ctor_get(v___x_857_, 1);
    leanh::lean_inc(v_nano_859_);
    leanh::lean_dec_ref(v___x_857_);
    v___x_860_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime__1___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime__1___lam__0___closed__2_once),
        _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2,
    );
    v___x_861_ = lean_int_mul(v_second_855_, v___x_860_);
    v___x_862_ = lean_int_add(v___x_861_, v_nano_856_);
    leanh::lean_dec(v___x_861_);
    v___x_863_ = lean_int_mul(v_second_858_, v___x_860_);
    leanh::lean_dec(v_second_858_);
    v___x_864_ = lean_int_add(v___x_863_, v_nano_859_);
    leanh::lean_dec(v_nano_859_);
    leanh::lean_dec(v___x_863_);
    v___x_865_ = lean_int_add(v___x_862_, v___x_864_);
    leanh::lean_dec(v___x_864_);
    leanh::lean_dec(v___x_862_);
    v___x_866_ = l_Std_Time_Duration_ofNanoseconds(v___x_865_);
    leanh::lean_dec(v___x_865_);
    return v___x_866_;
}
pub unsafe fn l_Std_Time_WallTime_addNanoseconds___boxed(
    mut v_t_867_: *mut leanh::LeanObject,
    mut v_s_868_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_869_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_869_ = l_Std_Time_WallTime_addNanoseconds(v_t_867_, v_s_868_);
    leanh::lean_dec(v_s_868_);
    leanh::lean_dec_ref(v_t_867_);
    return v_res_869_;
}
pub unsafe fn l_Std_Time_WallTime_subNanoseconds(
    mut v_t_870_: *mut leanh::LeanObject,
    mut v_s_871_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_885_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_872_ = l_Std_Time_Duration_ofNanoseconds(v_s_871_);
    v_second_873_ = leanh::lean_ctor_get(v___x_872_, 0);
    leanh::lean_inc(v_second_873_);
    v_nano_874_ = leanh::lean_ctor_get(v___x_872_, 1);
    leanh::lean_inc(v_nano_874_);
    leanh::lean_dec_ref(v___x_872_);
    v_second_875_ = leanh::lean_ctor_get(v_t_870_, 0);
    v_nano_876_ = leanh::lean_ctor_get(v_t_870_, 1);
    v___x_877_ = lean_int_neg(v_second_873_);
    leanh::lean_dec(v_second_873_);
    v___x_878_ = lean_int_neg(v_nano_874_);
    leanh::lean_dec(v_nano_874_);
    v___x_879_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime__1___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime__1___lam__0___closed__2_once),
        _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2,
    );
    v___x_880_ = lean_int_mul(v_second_875_, v___x_879_);
    v___x_881_ = lean_int_add(v___x_880_, v_nano_876_);
    leanh::lean_dec(v___x_880_);
    v___x_882_ = lean_int_mul(v___x_877_, v___x_879_);
    leanh::lean_dec(v___x_877_);
    v___x_883_ = lean_int_add(v___x_882_, v___x_878_);
    leanh::lean_dec(v___x_878_);
    leanh::lean_dec(v___x_882_);
    v___x_884_ = lean_int_add(v___x_881_, v___x_883_);
    leanh::lean_dec(v___x_883_);
    leanh::lean_dec(v___x_881_);
    v___x_885_ = l_Std_Time_Duration_ofNanoseconds(v___x_884_);
    leanh::lean_dec(v___x_884_);
    return v___x_885_;
}
pub unsafe fn l_Std_Time_WallTime_subNanoseconds___boxed(
    mut v_t_886_: *mut leanh::LeanObject,
    mut v_s_887_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_888_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_888_ = l_Std_Time_WallTime_subNanoseconds(v_t_886_, v_s_887_);
    leanh::lean_dec(v_s_887_);
    leanh::lean_dec_ref(v_t_886_);
    return v_res_888_;
}
pub unsafe fn l_Std_Time_WallTime_addSeconds(
    mut v_t_889_: *mut leanh::LeanObject,
    mut v_s_890_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_second_891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_900_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_second_891_ = leanh::lean_ctor_get(v_t_889_, 0);
    v_nano_892_ = leanh::lean_ctor_get(v_t_889_, 1);
    v___x_893_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime_repr___redArg___closed__14),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime_repr___redArg___closed__14_once),
        _init_l_Std_Time_instReprWallTime_repr___redArg___closed__14,
    );
    v___x_894_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime__1___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime__1___lam__0___closed__2_once),
        _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2,
    );
    v___x_895_ = lean_int_mul(v_second_891_, v___x_894_);
    v___x_896_ = lean_int_add(v___x_895_, v_nano_892_);
    leanh::lean_dec(v___x_895_);
    v___x_897_ = lean_int_mul(v_s_890_, v___x_894_);
    v___x_898_ = lean_int_add(v___x_897_, v___x_893_);
    leanh::lean_dec(v___x_897_);
    v___x_899_ = lean_int_add(v___x_896_, v___x_898_);
    leanh::lean_dec(v___x_898_);
    leanh::lean_dec(v___x_896_);
    v___x_900_ = l_Std_Time_Duration_ofNanoseconds(v___x_899_);
    leanh::lean_dec(v___x_899_);
    return v___x_900_;
}
pub unsafe fn l_Std_Time_WallTime_addSeconds___boxed(
    mut v_t_901_: *mut leanh::LeanObject,
    mut v_s_902_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_903_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_903_ = l_Std_Time_WallTime_addSeconds(v_t_901_, v_s_902_);
    leanh::lean_dec(v_s_902_);
    leanh::lean_dec_ref(v_t_901_);
    return v_res_903_;
}
pub unsafe fn _init_l_Std_Time_WallTime_subSeconds___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_904_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime_repr___redArg___closed__14),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime_repr___redArg___closed__14_once),
        _init_l_Std_Time_instReprWallTime_repr___redArg___closed__14,
    );
    v___x_905_ = lean_int_neg(v___x_904_);
    return v___x_905_;
}
pub unsafe fn l_Std_Time_WallTime_subSeconds(
    mut v_t_906_: *mut leanh::LeanObject,
    mut v_s_907_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_second_908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_918_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_second_908_ = leanh::lean_ctor_get(v_t_906_, 0);
    v_nano_909_ = leanh::lean_ctor_get(v_t_906_, 1);
    v___x_910_ = lean_int_neg(v_s_907_);
    v___x_911_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_WallTime_subSeconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_WallTime_subSeconds___closed__0_once),
        _init_l_Std_Time_WallTime_subSeconds___closed__0,
    );
    v___x_912_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime__1___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime__1___lam__0___closed__2_once),
        _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2,
    );
    v___x_913_ = lean_int_mul(v_second_908_, v___x_912_);
    v___x_914_ = lean_int_add(v___x_913_, v_nano_909_);
    leanh::lean_dec(v___x_913_);
    v___x_915_ = lean_int_mul(v___x_910_, v___x_912_);
    leanh::lean_dec(v___x_910_);
    v___x_916_ = lean_int_add(v___x_915_, v___x_911_);
    leanh::lean_dec(v___x_915_);
    v___x_917_ = lean_int_add(v___x_914_, v___x_916_);
    leanh::lean_dec(v___x_916_);
    leanh::lean_dec(v___x_914_);
    v___x_918_ = l_Std_Time_Duration_ofNanoseconds(v___x_917_);
    leanh::lean_dec(v___x_917_);
    return v___x_918_;
}
pub unsafe fn l_Std_Time_WallTime_subSeconds___boxed(
    mut v_t_919_: *mut leanh::LeanObject,
    mut v_s_920_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_921_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_921_ = l_Std_Time_WallTime_subSeconds(v_t_919_, v_s_920_);
    leanh::lean_dec(v_s_920_);
    leanh::lean_dec_ref(v_t_919_);
    return v_res_921_;
}
pub unsafe fn l_Std_Time_WallTime_addMinutes(
    mut v_t_922_: *mut leanh::LeanObject,
    mut v_m_923_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_second_924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_935_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_second_924_ = leanh::lean_ctor_get(v_t_922_, 0);
    v_nano_925_ = leanh::lean_ctor_get(v_t_922_, 1);
    v___x_926_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_WallTime_toMinutes___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_WallTime_toMinutes___closed__0_once),
        _init_l_Std_Time_WallTime_toMinutes___closed__0,
    );
    v___x_927_ = lean_int_mul(v_m_923_, v___x_926_);
    v___x_928_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime_repr___redArg___closed__14),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime_repr___redArg___closed__14_once),
        _init_l_Std_Time_instReprWallTime_repr___redArg___closed__14,
    );
    v___x_929_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime__1___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime__1___lam__0___closed__2_once),
        _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2,
    );
    v___x_930_ = lean_int_mul(v_second_924_, v___x_929_);
    v___x_931_ = lean_int_add(v___x_930_, v_nano_925_);
    leanh::lean_dec(v___x_930_);
    v___x_932_ = lean_int_mul(v___x_927_, v___x_929_);
    leanh::lean_dec(v___x_927_);
    v___x_933_ = lean_int_add(v___x_932_, v___x_928_);
    leanh::lean_dec(v___x_932_);
    v___x_934_ = lean_int_add(v___x_931_, v___x_933_);
    leanh::lean_dec(v___x_933_);
    leanh::lean_dec(v___x_931_);
    v___x_935_ = l_Std_Time_Duration_ofNanoseconds(v___x_934_);
    leanh::lean_dec(v___x_934_);
    return v___x_935_;
}
pub unsafe fn l_Std_Time_WallTime_addMinutes___boxed(
    mut v_t_936_: *mut leanh::LeanObject,
    mut v_m_937_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_938_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_938_ = l_Std_Time_WallTime_addMinutes(v_t_936_, v_m_937_);
    leanh::lean_dec(v_m_937_);
    leanh::lean_dec_ref(v_t_936_);
    return v_res_938_;
}
pub unsafe fn l_Std_Time_WallTime_subMinutes(
    mut v_t_939_: *mut leanh::LeanObject,
    mut v_m_940_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_second_941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_953_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_second_941_ = leanh::lean_ctor_get(v_t_939_, 0);
    v_nano_942_ = leanh::lean_ctor_get(v_t_939_, 1);
    v___x_943_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_WallTime_toMinutes___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_WallTime_toMinutes___closed__0_once),
        _init_l_Std_Time_WallTime_toMinutes___closed__0,
    );
    v___x_944_ = lean_int_mul(v_m_940_, v___x_943_);
    v___x_945_ = lean_int_neg(v___x_944_);
    leanh::lean_dec(v___x_944_);
    v___x_946_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_WallTime_subSeconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_WallTime_subSeconds___closed__0_once),
        _init_l_Std_Time_WallTime_subSeconds___closed__0,
    );
    v___x_947_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime__1___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime__1___lam__0___closed__2_once),
        _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2,
    );
    v___x_948_ = lean_int_mul(v_second_941_, v___x_947_);
    v___x_949_ = lean_int_add(v___x_948_, v_nano_942_);
    leanh::lean_dec(v___x_948_);
    v___x_950_ = lean_int_mul(v___x_945_, v___x_947_);
    leanh::lean_dec(v___x_945_);
    v___x_951_ = lean_int_add(v___x_950_, v___x_946_);
    leanh::lean_dec(v___x_950_);
    v___x_952_ = lean_int_add(v___x_949_, v___x_951_);
    leanh::lean_dec(v___x_951_);
    leanh::lean_dec(v___x_949_);
    v___x_953_ = l_Std_Time_Duration_ofNanoseconds(v___x_952_);
    leanh::lean_dec(v___x_952_);
    return v___x_953_;
}
pub unsafe fn l_Std_Time_WallTime_subMinutes___boxed(
    mut v_t_954_: *mut leanh::LeanObject,
    mut v_m_955_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_956_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_956_ = l_Std_Time_WallTime_subMinutes(v_t_954_, v_m_955_);
    leanh::lean_dec(v_m_955_);
    leanh::lean_dec_ref(v_t_954_);
    return v_res_956_;
}
pub unsafe fn _init_l_Std_Time_WallTime_addHours___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_958_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_957_ = leanh::lean_unsigned_to_nat(3600);
    v___x_958_ = lean_nat_to_int(v___x_957_);
    return v___x_958_;
}
pub unsafe fn l_Std_Time_WallTime_addHours(
    mut v_t_959_: *mut leanh::LeanObject,
    mut v_h_960_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_second_961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_972_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_second_961_ = leanh::lean_ctor_get(v_t_959_, 0);
    v_nano_962_ = leanh::lean_ctor_get(v_t_959_, 1);
    v___x_963_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_WallTime_addHours___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_WallTime_addHours___closed__0_once),
        _init_l_Std_Time_WallTime_addHours___closed__0,
    );
    v___x_964_ = lean_int_mul(v_h_960_, v___x_963_);
    v___x_965_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime_repr___redArg___closed__14),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime_repr___redArg___closed__14_once),
        _init_l_Std_Time_instReprWallTime_repr___redArg___closed__14,
    );
    v___x_966_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime__1___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime__1___lam__0___closed__2_once),
        _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2,
    );
    v___x_967_ = lean_int_mul(v_second_961_, v___x_966_);
    v___x_968_ = lean_int_add(v___x_967_, v_nano_962_);
    leanh::lean_dec(v___x_967_);
    v___x_969_ = lean_int_mul(v___x_964_, v___x_966_);
    leanh::lean_dec(v___x_964_);
    v___x_970_ = lean_int_add(v___x_969_, v___x_965_);
    leanh::lean_dec(v___x_969_);
    v___x_971_ = lean_int_add(v___x_968_, v___x_970_);
    leanh::lean_dec(v___x_970_);
    leanh::lean_dec(v___x_968_);
    v___x_972_ = l_Std_Time_Duration_ofNanoseconds(v___x_971_);
    leanh::lean_dec(v___x_971_);
    return v___x_972_;
}
pub unsafe fn l_Std_Time_WallTime_addHours___boxed(
    mut v_t_973_: *mut leanh::LeanObject,
    mut v_h_974_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_975_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_975_ = l_Std_Time_WallTime_addHours(v_t_973_, v_h_974_);
    leanh::lean_dec(v_h_974_);
    leanh::lean_dec_ref(v_t_973_);
    return v_res_975_;
}
pub unsafe fn l_Std_Time_WallTime_subHours(
    mut v_t_976_: *mut leanh::LeanObject,
    mut v_h_977_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_second_978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_990_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_second_978_ = leanh::lean_ctor_get(v_t_976_, 0);
    v_nano_979_ = leanh::lean_ctor_get(v_t_976_, 1);
    v___x_980_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_WallTime_addHours___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_WallTime_addHours___closed__0_once),
        _init_l_Std_Time_WallTime_addHours___closed__0,
    );
    v___x_981_ = lean_int_mul(v_h_977_, v___x_980_);
    v___x_982_ = lean_int_neg(v___x_981_);
    leanh::lean_dec(v___x_981_);
    v___x_983_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_WallTime_subSeconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_WallTime_subSeconds___closed__0_once),
        _init_l_Std_Time_WallTime_subSeconds___closed__0,
    );
    v___x_984_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime__1___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime__1___lam__0___closed__2_once),
        _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2,
    );
    v___x_985_ = lean_int_mul(v_second_978_, v___x_984_);
    v___x_986_ = lean_int_add(v___x_985_, v_nano_979_);
    leanh::lean_dec(v___x_985_);
    v___x_987_ = lean_int_mul(v___x_982_, v___x_984_);
    leanh::lean_dec(v___x_982_);
    v___x_988_ = lean_int_add(v___x_987_, v___x_983_);
    leanh::lean_dec(v___x_987_);
    v___x_989_ = lean_int_add(v___x_986_, v___x_988_);
    leanh::lean_dec(v___x_988_);
    leanh::lean_dec(v___x_986_);
    v___x_990_ = l_Std_Time_Duration_ofNanoseconds(v___x_989_);
    leanh::lean_dec(v___x_989_);
    return v___x_990_;
}
pub unsafe fn l_Std_Time_WallTime_subHours___boxed(
    mut v_t_991_: *mut leanh::LeanObject,
    mut v_h_992_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_993_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_993_ = l_Std_Time_WallTime_subHours(v_t_991_, v_h_992_);
    leanh::lean_dec(v_h_992_);
    leanh::lean_dec_ref(v_t_991_);
    return v_res_993_;
}
pub unsafe fn l_Std_Time_WallTime_addDays(
    mut v_t_994_: *mut leanh::LeanObject,
    mut v_d_995_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_second_996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1007_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_second_996_ = leanh::lean_ctor_get(v_t_994_, 0);
    v_nano_997_ = leanh::lean_ctor_get(v_t_994_, 1);
    v___x_998_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_WallTime_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_WallTime_toDays___closed__0_once),
        _init_l_Std_Time_WallTime_toDays___closed__0,
    );
    v___x_999_ = lean_int_mul(v_d_995_, v___x_998_);
    v___x_1000_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime_repr___redArg___closed__14),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime_repr___redArg___closed__14_once),
        _init_l_Std_Time_instReprWallTime_repr___redArg___closed__14,
    );
    v___x_1001_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime__1___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime__1___lam__0___closed__2_once),
        _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2,
    );
    v___x_1002_ = lean_int_mul(v_second_996_, v___x_1001_);
    v___x_1003_ = lean_int_add(v___x_1002_, v_nano_997_);
    leanh::lean_dec(v___x_1002_);
    v___x_1004_ = lean_int_mul(v___x_999_, v___x_1001_);
    leanh::lean_dec(v___x_999_);
    v___x_1005_ = lean_int_add(v___x_1004_, v___x_1000_);
    leanh::lean_dec(v___x_1004_);
    v___x_1006_ = lean_int_add(v___x_1003_, v___x_1005_);
    leanh::lean_dec(v___x_1005_);
    leanh::lean_dec(v___x_1003_);
    v___x_1007_ = l_Std_Time_Duration_ofNanoseconds(v___x_1006_);
    leanh::lean_dec(v___x_1006_);
    return v___x_1007_;
}
pub unsafe fn l_Std_Time_WallTime_addDays___boxed(
    mut v_t_1008_: *mut leanh::LeanObject,
    mut v_d_1009_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1010_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1010_ = l_Std_Time_WallTime_addDays(v_t_1008_, v_d_1009_);
    leanh::lean_dec(v_d_1009_);
    leanh::lean_dec_ref(v_t_1008_);
    return v_res_1010_;
}
pub unsafe fn l_Std_Time_WallTime_subDays(
    mut v_t_1011_: *mut leanh::LeanObject,
    mut v_d_1012_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_second_1013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_second_1013_ = leanh::lean_ctor_get(v_t_1011_, 0);
    v_nano_1014_ = leanh::lean_ctor_get(v_t_1011_, 1);
    v___x_1015_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_WallTime_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_WallTime_toDays___closed__0_once),
        _init_l_Std_Time_WallTime_toDays___closed__0,
    );
    v___x_1016_ = lean_int_mul(v_d_1012_, v___x_1015_);
    v___x_1017_ = lean_int_neg(v___x_1016_);
    leanh::lean_dec(v___x_1016_);
    v___x_1018_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_WallTime_subSeconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_WallTime_subSeconds___closed__0_once),
        _init_l_Std_Time_WallTime_subSeconds___closed__0,
    );
    v___x_1019_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime__1___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime__1___lam__0___closed__2_once),
        _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2,
    );
    v___x_1020_ = lean_int_mul(v_second_1013_, v___x_1019_);
    v___x_1021_ = lean_int_add(v___x_1020_, v_nano_1014_);
    leanh::lean_dec(v___x_1020_);
    v___x_1022_ = lean_int_mul(v___x_1017_, v___x_1019_);
    leanh::lean_dec(v___x_1017_);
    v___x_1023_ = lean_int_add(v___x_1022_, v___x_1018_);
    leanh::lean_dec(v___x_1022_);
    v___x_1024_ = lean_int_add(v___x_1021_, v___x_1023_);
    leanh::lean_dec(v___x_1023_);
    leanh::lean_dec(v___x_1021_);
    v___x_1025_ = l_Std_Time_Duration_ofNanoseconds(v___x_1024_);
    leanh::lean_dec(v___x_1024_);
    return v___x_1025_;
}
pub unsafe fn l_Std_Time_WallTime_subDays___boxed(
    mut v_t_1026_: *mut leanh::LeanObject,
    mut v_d_1027_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1028_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1028_ = l_Std_Time_WallTime_subDays(v_t_1026_, v_d_1027_);
    leanh::lean_dec(v_d_1027_);
    leanh::lean_dec_ref(v_t_1026_);
    return v_res_1028_;
}
pub unsafe fn l_Std_Time_WallTime_addWeeks(
    mut v_t_1029_: *mut leanh::LeanObject,
    mut v_d_1030_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_second_1031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1044_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_second_1031_ = leanh::lean_ctor_get(v_t_1029_, 0);
    v_nano_1032_ = leanh::lean_ctor_get(v_t_1029_, 1);
    v___x_1033_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime_repr___redArg___closed__7_once),
        _init_l_Std_Time_instReprWallTime_repr___redArg___closed__7,
    );
    v___x_1034_ = lean_int_mul(v_d_1030_, v___x_1033_);
    v___x_1035_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_WallTime_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_WallTime_toDays___closed__0_once),
        _init_l_Std_Time_WallTime_toDays___closed__0,
    );
    v___x_1036_ = lean_int_mul(v___x_1034_, v___x_1035_);
    leanh::lean_dec(v___x_1034_);
    v___x_1037_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime_repr___redArg___closed__14),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime_repr___redArg___closed__14_once),
        _init_l_Std_Time_instReprWallTime_repr___redArg___closed__14,
    );
    v___x_1038_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime__1___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime__1___lam__0___closed__2_once),
        _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2,
    );
    v___x_1039_ = lean_int_mul(v_second_1031_, v___x_1038_);
    v___x_1040_ = lean_int_add(v___x_1039_, v_nano_1032_);
    leanh::lean_dec(v___x_1039_);
    v___x_1041_ = lean_int_mul(v___x_1036_, v___x_1038_);
    leanh::lean_dec(v___x_1036_);
    v___x_1042_ = lean_int_add(v___x_1041_, v___x_1037_);
    leanh::lean_dec(v___x_1041_);
    v___x_1043_ = lean_int_add(v___x_1040_, v___x_1042_);
    leanh::lean_dec(v___x_1042_);
    leanh::lean_dec(v___x_1040_);
    v___x_1044_ = l_Std_Time_Duration_ofNanoseconds(v___x_1043_);
    leanh::lean_dec(v___x_1043_);
    return v___x_1044_;
}
pub unsafe fn l_Std_Time_WallTime_addWeeks___boxed(
    mut v_t_1045_: *mut leanh::LeanObject,
    mut v_d_1046_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1047_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1047_ = l_Std_Time_WallTime_addWeeks(v_t_1045_, v_d_1046_);
    leanh::lean_dec(v_d_1046_);
    leanh::lean_dec_ref(v_t_1045_);
    return v_res_1047_;
}
pub unsafe fn l_Std_Time_WallTime_subWeeks(
    mut v_t_1048_: *mut leanh::LeanObject,
    mut v_d_1049_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_second_1050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1064_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_second_1050_ = leanh::lean_ctor_get(v_t_1048_, 0);
    v_nano_1051_ = leanh::lean_ctor_get(v_t_1048_, 1);
    v___x_1052_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime_repr___redArg___closed__7_once),
        _init_l_Std_Time_instReprWallTime_repr___redArg___closed__7,
    );
    v___x_1053_ = lean_int_mul(v_d_1049_, v___x_1052_);
    v___x_1054_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_WallTime_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_WallTime_toDays___closed__0_once),
        _init_l_Std_Time_WallTime_toDays___closed__0,
    );
    v___x_1055_ = lean_int_mul(v___x_1053_, v___x_1054_);
    leanh::lean_dec(v___x_1053_);
    v___x_1056_ = lean_int_neg(v___x_1055_);
    leanh::lean_dec(v___x_1055_);
    v___x_1057_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_WallTime_subSeconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_WallTime_subSeconds___closed__0_once),
        _init_l_Std_Time_WallTime_subSeconds___closed__0,
    );
    v___x_1058_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime__1___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime__1___lam__0___closed__2_once),
        _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2,
    );
    v___x_1059_ = lean_int_mul(v_second_1050_, v___x_1058_);
    v___x_1060_ = lean_int_add(v___x_1059_, v_nano_1051_);
    leanh::lean_dec(v___x_1059_);
    v___x_1061_ = lean_int_mul(v___x_1056_, v___x_1058_);
    leanh::lean_dec(v___x_1056_);
    v___x_1062_ = lean_int_add(v___x_1061_, v___x_1057_);
    leanh::lean_dec(v___x_1061_);
    v___x_1063_ = lean_int_add(v___x_1060_, v___x_1062_);
    leanh::lean_dec(v___x_1062_);
    leanh::lean_dec(v___x_1060_);
    v___x_1064_ = l_Std_Time_Duration_ofNanoseconds(v___x_1063_);
    leanh::lean_dec(v___x_1063_);
    return v___x_1064_;
}
pub unsafe fn l_Std_Time_WallTime_subWeeks___boxed(
    mut v_t_1065_: *mut leanh::LeanObject,
    mut v_d_1066_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1067_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1067_ = l_Std_Time_WallTime_subWeeks(v_t_1065_, v_d_1066_);
    leanh::lean_dec(v_d_1066_);
    leanh::lean_dec_ref(v_t_1065_);
    return v_res_1067_;
}
pub unsafe fn l_Std_Time_WallTime_addDuration(
    mut v_t_1068_: *mut leanh::LeanObject,
    mut v_d_1069_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_second_1070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_1072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_second_1070_ = leanh::lean_ctor_get(v_t_1068_, 0);
    v_nano_1071_ = leanh::lean_ctor_get(v_t_1068_, 1);
    v_second_1072_ = leanh::lean_ctor_get(v_d_1069_, 0);
    v_nano_1073_ = leanh::lean_ctor_get(v_d_1069_, 1);
    v___x_1074_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime__1___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime__1___lam__0___closed__2_once),
        _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2,
    );
    v___x_1075_ = lean_int_mul(v_second_1070_, v___x_1074_);
    v___x_1076_ = lean_int_add(v___x_1075_, v_nano_1071_);
    leanh::lean_dec(v___x_1075_);
    v___x_1077_ = lean_int_mul(v_second_1072_, v___x_1074_);
    v___x_1078_ = lean_int_add(v___x_1077_, v_nano_1073_);
    leanh::lean_dec(v___x_1077_);
    v___x_1079_ = lean_int_add(v___x_1076_, v___x_1078_);
    leanh::lean_dec(v___x_1078_);
    leanh::lean_dec(v___x_1076_);
    v___x_1080_ = l_Std_Time_Duration_ofNanoseconds(v___x_1079_);
    leanh::lean_dec(v___x_1079_);
    return v___x_1080_;
}
pub unsafe fn l_Std_Time_WallTime_addDuration___boxed(
    mut v_t_1081_: *mut leanh::LeanObject,
    mut v_d_1082_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1083_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1083_ = l_Std_Time_WallTime_addDuration(v_t_1081_, v_d_1082_);
    leanh::lean_dec_ref(v_d_1082_);
    leanh::lean_dec_ref(v_t_1081_);
    return v_res_1083_;
}
pub unsafe fn l_Std_Time_WallTime_subDuration(
    mut v_t_1084_: *mut leanh::LeanObject,
    mut v_d_1085_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_second_1086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_1088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1098_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_second_1086_ = leanh::lean_ctor_get(v_d_1085_, 0);
    v_nano_1087_ = leanh::lean_ctor_get(v_d_1085_, 1);
    v_second_1088_ = leanh::lean_ctor_get(v_t_1084_, 0);
    v_nano_1089_ = leanh::lean_ctor_get(v_t_1084_, 1);
    v___x_1090_ = lean_int_neg(v_second_1086_);
    v___x_1091_ = lean_int_neg(v_nano_1087_);
    v___x_1092_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime__1___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime__1___lam__0___closed__2_once),
        _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2,
    );
    v___x_1093_ = lean_int_mul(v_second_1088_, v___x_1092_);
    v___x_1094_ = lean_int_add(v___x_1093_, v_nano_1089_);
    leanh::lean_dec(v___x_1093_);
    v___x_1095_ = lean_int_mul(v___x_1090_, v___x_1092_);
    leanh::lean_dec(v___x_1090_);
    v___x_1096_ = lean_int_add(v___x_1095_, v___x_1091_);
    leanh::lean_dec(v___x_1091_);
    leanh::lean_dec(v___x_1095_);
    v___x_1097_ = lean_int_add(v___x_1094_, v___x_1096_);
    leanh::lean_dec(v___x_1096_);
    leanh::lean_dec(v___x_1094_);
    v___x_1098_ = l_Std_Time_Duration_ofNanoseconds(v___x_1097_);
    leanh::lean_dec(v___x_1097_);
    return v___x_1098_;
}
pub unsafe fn l_Std_Time_WallTime_subDuration___boxed(
    mut v_t_1099_: *mut leanh::LeanObject,
    mut v_d_1100_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1101_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1101_ = l_Std_Time_WallTime_subDuration(v_t_1099_, v_d_1100_);
    leanh::lean_dec_ref(v_d_1100_);
    leanh::lean_dec_ref(v_t_1099_);
    return v_res_1101_;
}
pub unsafe fn l_Std_Time_WallTime_toDuration(
    mut v_wt_1102_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v_wt_1102_);
    return v_wt_1102_;
}
pub unsafe fn l_Std_Time_WallTime_toDuration___boxed(
    mut v_wt_1103_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1104_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1104_ = l_Std_Time_WallTime_toDuration(v_wt_1103_);
    leanh::lean_dec_ref(v_wt_1103_);
    return v_res_1104_;
}
pub unsafe fn l_Std_Time_WallTime_instHSubDuration__1___lam__0(
    mut v_x_1137_: *mut leanh::LeanObject,
    mut v_y_1138_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_second_1139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_1141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_second_1139_ = leanh::lean_ctor_get(v_y_1138_, 0);
    v_nano_1140_ = leanh::lean_ctor_get(v_y_1138_, 1);
    v_second_1141_ = leanh::lean_ctor_get(v_x_1137_, 0);
    v_nano_1142_ = leanh::lean_ctor_get(v_x_1137_, 1);
    v___x_1143_ = lean_int_neg(v_second_1139_);
    v___x_1144_ = lean_int_neg(v_nano_1140_);
    v___x_1145_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime__1___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime__1___lam__0___closed__2_once),
        _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2,
    );
    v___x_1146_ = lean_int_mul(v_second_1141_, v___x_1145_);
    v___x_1147_ = lean_int_add(v___x_1146_, v_nano_1142_);
    leanh::lean_dec(v___x_1146_);
    v___x_1148_ = lean_int_mul(v___x_1143_, v___x_1145_);
    leanh::lean_dec(v___x_1143_);
    v___x_1149_ = lean_int_add(v___x_1148_, v___x_1144_);
    leanh::lean_dec(v___x_1144_);
    leanh::lean_dec(v___x_1148_);
    v___x_1150_ = lean_int_add(v___x_1147_, v___x_1149_);
    leanh::lean_dec(v___x_1149_);
    leanh::lean_dec(v___x_1147_);
    v___x_1151_ = l_Std_Time_Duration_ofNanoseconds(v___x_1150_);
    leanh::lean_dec(v___x_1150_);
    return v___x_1151_;
}
pub unsafe fn l_Std_Time_WallTime_instHSubDuration__1___lam__0___boxed(
    mut v_x_1152_: *mut leanh::LeanObject,
    mut v_y_1153_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1154_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1154_ = l_Std_Time_WallTime_instHSubDuration__1___lam__0(v_x_1152_, v_y_1153_);
    leanh::lean_dec_ref(v_y_1153_);
    leanh::lean_dec_ref(v_x_1152_);
    return v_res_1154_;
}
pub unsafe fn l_Std_Time_WallTime_instOfNat(
    mut v_n_1157_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1158_ = lean_nat_to_int(v_n_1157_);
    v___x_1159_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime_repr___redArg___closed__14),
        core::ptr::addr_of_mut!(l_Std_Time_instReprWallTime_repr___redArg___closed__14_once),
        _init_l_Std_Time_instReprWallTime_repr___redArg___closed__14,
    );
    v___x_1160_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1160_, 0, v___x_1158_);
    leanh::lean_ctor_set(v___x_1160_, 1, v___x_1159_);
    return v___x_1160_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Time_DateTime_WallTime(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_System_IO(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Duration(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Std_Time_instInhabitedWallTime_default = _init_l_Std_Time_instInhabitedWallTime_default();
    leanh::lean_mark_persistent(l_Std_Time_instInhabitedWallTime_default);
    l_Std_Time_instInhabitedWallTime = _init_l_Std_Time_instInhabitedWallTime();
    leanh::lean_mark_persistent(l_Std_Time_instInhabitedWallTime);
    l_Std_Time_instLEWallTime = _init_l_Std_Time_instLEWallTime();
    leanh::lean_mark_persistent(l_Std_Time_instLEWallTime);
    l_Std_Time_instLTWallTime = _init_l_Std_Time_instLTWallTime();
    leanh::lean_mark_persistent(l_Std_Time_instLTWallTime);
    l_Std_Time_instOrdWallTime = _init_l_Std_Time_instOrdWallTime();
    leanh::lean_mark_persistent(l_Std_Time_instOrdWallTime);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Time_DateTime_WallTime(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Time_DateTime_WallTime(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_System_IO(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Time_Duration(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Time_DateTime_WallTime(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Time_DateTime_WallTime(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Time_DateTime_WallTime(builtin);
}