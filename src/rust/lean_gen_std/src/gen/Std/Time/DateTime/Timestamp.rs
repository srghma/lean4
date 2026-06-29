// Lean compiler output
// Module: Std.Time.DateTime.Timestamp
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
use crate::lean_imports_rs::Init::Data::Int::Basic::{
    lean_int_add, lean_int_dec_eq, lean_int_dec_lt, lean_int_mul, lean_int_neg, lean_nat_to_int,
};
use crate::lean_imports_rs::Init::Data::Int::DivMod::Basic::lean_int_div;
use crate::lean_imports_rs::Init::Data::String::Bootstrap::lean_string_length;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Std::Time::DateTime::Timestamp::lean_get_current_time;
pub static l_Std_Time_instReprTimestamp_repr___redArg___closed__0_value:
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
static mut l_Std_Time_instReprTimestamp_repr___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprTimestamp_repr___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprTimestamp_repr___redArg___closed__1_value:
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
static mut l_Std_Time_instReprTimestamp_repr___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprTimestamp_repr___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprTimestamp_repr___redArg___closed__2_value:
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
        core::ptr::addr_of!(l_Std_Time_instReprTimestamp_repr___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_instReprTimestamp_repr___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprTimestamp_repr___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprTimestamp_repr___redArg___closed__3_value:
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
        core::ptr::addr_of!(l_Std_Time_instReprTimestamp_repr___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_instReprTimestamp_repr___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprTimestamp_repr___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprTimestamp_repr___redArg___closed__4_value:
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
static mut l_Std_Time_instReprTimestamp_repr___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprTimestamp_repr___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprTimestamp_repr___redArg___closed__5_value:
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
        core::ptr::addr_of!(l_Std_Time_instReprTimestamp_repr___redArg___closed__4_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_instReprTimestamp_repr___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprTimestamp_repr___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprTimestamp_repr___redArg___closed__6_value:
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
        core::ptr::addr_of!(l_Std_Time_instReprTimestamp_repr___redArg___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_instReprTimestamp_repr___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_instReprTimestamp_repr___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprTimestamp_repr___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_instReprTimestamp_repr___redArg___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instReprTimestamp_repr___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_instReprTimestamp_repr___redArg___closed__8_value:
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
static mut l_Std_Time_instReprTimestamp_repr___redArg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprTimestamp_repr___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprTimestamp_repr___redArg___closed__9_value:
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
static mut l_Std_Time_instReprTimestamp_repr___redArg___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprTimestamp_repr___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_instReprTimestamp_repr___redArg___closed__10_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instReprTimestamp_repr___redArg___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instReprTimestamp_repr___redArg___closed__11_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instReprTimestamp_repr___redArg___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_instReprTimestamp_repr___redArg___closed__12_value:
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
        core::ptr::addr_of!(l_Std_Time_instReprTimestamp_repr___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_instReprTimestamp_repr___redArg___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprTimestamp_repr___redArg___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprTimestamp_repr___redArg___closed__13_value:
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
        core::ptr::addr_of!(l_Std_Time_instReprTimestamp_repr___redArg___closed__9_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_instReprTimestamp_repr___redArg___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprTimestamp_repr___redArg___closed__13_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_instReprTimestamp_repr___redArg___closed__14_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instReprTimestamp_repr___redArg___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_instReprTimestamp_repr___redArg___closed__15_value:
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
static mut l_Std_Time_instReprTimestamp_repr___redArg___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprTimestamp_repr___redArg___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprTimestamp_repr___redArg___closed__16_value:
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
static mut l_Std_Time_instReprTimestamp_repr___redArg___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprTimestamp_repr___redArg___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprTimestamp_repr___redArg___closed__17_value:
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
static mut l_Std_Time_instReprTimestamp_repr___redArg___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprTimestamp_repr___redArg___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprTimestamp___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instReprTimestamp_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instReprTimestamp___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprTimestamp___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_instReprTimestamp: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprTimestamp___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_instInhabitedTimestamp_default___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedTimestamp_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_instInhabitedTimestamp_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_instInhabitedTimestamp: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_instLETimestamp: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Std_Time_instLTTimestamp: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Time_instToStringTimestamp___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instToStringTimestamp___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instToStringTimestamp___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instToStringTimestamp___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_instToStringTimestamp: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instToStringTimestamp___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprTimestamp__1___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 25,
    m_capacity: 25,
    m_length: 24,
    m_data: [
        84, 105, 109, 101, 115, 116, 97, 109, 112, 46, 111, 102, 78, 97, 110, 111, 115, 101, 99,
        111, 110, 100, 115, 32, 0,
    ],
};
static mut l_Std_Time_instReprTimestamp__1___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprTimestamp__1___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprTimestamp__1___lam__0___closed__1_value:
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
        core::ptr::addr_of!(l_Std_Time_instReprTimestamp__1___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_instReprTimestamp__1___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprTimestamp__1___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instReprTimestamp__1___lam__0___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_instReprTimestamp__1___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instReprTimestamp__1___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instReprTimestamp__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprTimestamp__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_instReprTimestamp__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprTimestamp__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instOrdTimestamp___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instOrdTimestamp___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instOrdTimestamp___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdTimestamp___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_instOrdTimestamp___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instOrdTimestamp___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_instOrdTimestamp: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Timestamp_toMinutesSinceUnixEpoch___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Timestamp_toMinutesSinceUnixEpoch___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Timestamp_toDaysSinceUnixEpoch___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Timestamp_toDaysSinceUnixEpoch___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Timestamp_subSeconds___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Timestamp_subSeconds___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Timestamp_addHours___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Timestamp_addHours___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_Timestamp_instHAddDuration___closed__0_value:
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
    m_fun: l_Std_Time_Timestamp_addDuration___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_Timestamp_instHAddDuration___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Timestamp_instHAddDuration___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Timestamp_instHAddDuration: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Timestamp_instHAddDuration___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Timestamp_instHSubDuration___closed__0_value:
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
    m_fun: l_Std_Time_Timestamp_subDuration___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_Timestamp_instHSubDuration___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Timestamp_instHSubDuration___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Timestamp_instHSubDuration: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Timestamp_instHSubDuration___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Timestamp_instHAddOffset___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_Timestamp_addDays___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_Timestamp_instHAddOffset___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Timestamp_instHAddOffset___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Timestamp_instHAddOffset: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Timestamp_instHAddOffset___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Timestamp_instHSubOffset___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_Timestamp_subDays___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_Timestamp_instHSubOffset___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Timestamp_instHSubOffset___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Timestamp_instHSubOffset: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Timestamp_instHSubOffset___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Timestamp_instHAddOffset__1___closed__0_value:
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
    m_fun: l_Std_Time_Timestamp_addWeeks___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_Timestamp_instHAddOffset__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Timestamp_instHAddOffset__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Timestamp_instHAddOffset__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Timestamp_instHAddOffset__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Timestamp_instHSubOffset__1___closed__0_value:
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
    m_fun: l_Std_Time_Timestamp_subWeeks___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_Timestamp_instHSubOffset__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Timestamp_instHSubOffset__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Timestamp_instHSubOffset__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Timestamp_instHSubOffset__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Timestamp_instHAddOffset__2___closed__0_value:
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
    m_fun: l_Std_Time_Timestamp_addHours___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_Timestamp_instHAddOffset__2___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Timestamp_instHAddOffset__2___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Timestamp_instHAddOffset__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Timestamp_instHAddOffset__2___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Timestamp_instHSubOffset__2___closed__0_value:
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
    m_fun: l_Std_Time_Timestamp_subHours___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_Timestamp_instHSubOffset__2___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Timestamp_instHSubOffset__2___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Timestamp_instHSubOffset__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Timestamp_instHSubOffset__2___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Timestamp_instHAddOffset__3___closed__0_value:
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
    m_fun: l_Std_Time_Timestamp_addMinutes___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_Timestamp_instHAddOffset__3___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Timestamp_instHAddOffset__3___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Timestamp_instHAddOffset__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Timestamp_instHAddOffset__3___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Timestamp_instHSubOffset__3___closed__0_value:
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
    m_fun: l_Std_Time_Timestamp_subMinutes___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_Timestamp_instHSubOffset__3___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Timestamp_instHSubOffset__3___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Timestamp_instHSubOffset__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Timestamp_instHSubOffset__3___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Timestamp_instHAddOffset__4___closed__0_value:
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
    m_fun: l_Std_Time_Timestamp_addSeconds___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_Timestamp_instHAddOffset__4___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Timestamp_instHAddOffset__4___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Timestamp_instHAddOffset__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Timestamp_instHAddOffset__4___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Timestamp_instHSubOffset__4___closed__0_value:
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
    m_fun: l_Std_Time_Timestamp_subSeconds___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_Timestamp_instHSubOffset__4___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Timestamp_instHSubOffset__4___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Timestamp_instHSubOffset__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Timestamp_instHSubOffset__4___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Timestamp_instHAddOffset__5___closed__0_value:
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
    m_fun: l_Std_Time_Timestamp_addMilliseconds___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_Timestamp_instHAddOffset__5___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Timestamp_instHAddOffset__5___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Timestamp_instHAddOffset__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Timestamp_instHAddOffset__5___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Timestamp_instHSubOffset__5___closed__0_value:
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
    m_fun: l_Std_Time_Timestamp_subMilliseconds___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_Timestamp_instHSubOffset__5___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Timestamp_instHSubOffset__5___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Timestamp_instHSubOffset__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Timestamp_instHSubOffset__5___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Timestamp_instHAddOffset__6___closed__0_value:
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
    m_fun: l_Std_Time_Timestamp_addNanoseconds___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_Timestamp_instHAddOffset__6___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Timestamp_instHAddOffset__6___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Timestamp_instHAddOffset__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Timestamp_instHAddOffset__6___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Timestamp_instHSubOffset__6___closed__0_value:
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
    m_fun: l_Std_Time_Timestamp_subNanoseconds___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_Timestamp_instHSubOffset__6___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Timestamp_instHSubOffset__6___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Timestamp_instHSubOffset__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Timestamp_instHSubOffset__6___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Timestamp_instHSubDuration__1___closed__0_value:
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
    m_fun: l_Std_Time_Timestamp_instHSubDuration__1___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_Timestamp_instHSubDuration__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Timestamp_instHSubDuration__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Timestamp_instHSubDuration__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Timestamp_instHSubDuration__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Nat_cast___at___00Std_Time_instReprTimestamp_repr_spec__0(
    mut v_a_619_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_620_ = lean_nat_to_int(v_a_619_);
    return v___x_620_;
}
pub unsafe fn _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_634_ = crate::leanh::lean_unsigned_to_nat(7);
    v___x_635_ = lean_nat_to_int(v___x_634_);
    return v___x_635_;
}
pub unsafe fn _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_638_ = l_Std_Time_instReprTimestamp_repr___redArg___closed__0;
    v___x_639_ = lean_string_length(v___x_638_);
    return v___x_639_;
}
pub unsafe fn _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_640_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp_repr___redArg___closed__10),
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp_repr___redArg___closed__10_once),
        _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__10,
    );
    v___x_641_ = lean_nat_to_int(v___x_640_);
    return v___x_641_;
}
pub unsafe fn _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_646_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_647_ = lean_nat_to_int(v___x_646_);
    return v___x_647_;
}
pub unsafe fn l_Std_Time_instReprTimestamp_repr___redArg(
    mut v_x_651_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_second_652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_656_: u8 = 0;
    let mut v___x_657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_669_: u8 = 0;
    let mut v___x_670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_687_: u8 = 0;
    let mut v___x_688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_695_: u8 = 0;
    let mut v___x_696_: u8 = 0;
    let mut v___x_697_: u8 = 0;
    let mut v___x_698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_706_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_second_652_ = crate::leanh::lean_ctor_get(v_x_651_, 0);
                v_nano_653_ = crate::leanh::lean_ctor_get(v_x_651_, 1);
                v_isSharedCheck_706_ = (!crate::leanh::lean_is_exclusive(v_x_651_)) as u8;
                if v_isSharedCheck_706_ == 0 {
                    v___x_655_ = v_x_651_;
                    v_isShared_656_ = v_isSharedCheck_706_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nano_653_);
                    crate::leanh::lean_inc(v_second_652_);
                    crate::leanh::lean_dec(v_x_651_);
                    v___x_655_ = crate::leanh::lean_box(0);
                    v_isShared_656_ = v_isSharedCheck_706_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_657_ = l_Std_Time_instReprTimestamp_repr___redArg___closed__6;
                v___x_658_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp_repr___redArg___closed__7),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprTimestamp_repr___redArg___closed__7_once
                    ),
                    _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__7,
                );
                v___x_694_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprTimestamp_repr___redArg___closed__14
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprTimestamp_repr___redArg___closed__14_once
                    ),
                    _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__14,
                );
                v___x_695_ = lean_int_dec_lt(v___x_694_, v_second_652_);
                if v___x_695_ == 0 {
                    v___x_696_ = lean_int_dec_lt(v_second_652_, v___x_694_);
                    if v___x_696_ == 0 {
                        v___x_697_ = lean_int_dec_lt(v_nano_653_, v___x_694_);
                        if v___x_697_ == 0 {
                            v___x_698_ = l_Std_Time_instReprTimestamp_repr___redArg___closed__16;
                            crate::leanh::lean_inc(v_nano_653_);
                            v_fst_681_ = v___x_698_;
                            v_fst_682_ = v_second_652_;
                            v_snd_683_ = v_nano_653_;
                            state = 4;
                            continue;
                        } else {
                            v___x_699_ = l_Std_Time_instReprTimestamp_repr___redArg___closed__17;
                            v___x_700_ = lean_int_neg(v_second_652_);
                            crate::leanh::lean_dec(v_second_652_);
                            v___x_701_ = lean_int_neg(v_nano_653_);
                            v_fst_681_ = v___x_699_;
                            v_fst_682_ = v___x_700_;
                            v_snd_683_ = v___x_701_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v___x_702_ = l_Std_Time_instReprTimestamp_repr___redArg___closed__17;
                        v___x_703_ = lean_int_neg(v_second_652_);
                        crate::leanh::lean_dec(v_second_652_);
                        v___x_704_ = lean_int_neg(v_nano_653_);
                        v_fst_681_ = v___x_702_;
                        v_fst_682_ = v___x_703_;
                        v_snd_683_ = v___x_704_;
                        state = 4;
                        continue;
                    }
                } else {
                    v___x_705_ = l_Std_Time_instReprTimestamp_repr___redArg___closed__16;
                    crate::leanh::lean_inc(v_nano_653_);
                    v_fst_681_ = v___x_705_;
                    v_fst_682_ = v_second_652_;
                    v_snd_683_ = v_nano_653_;
                    state = 4;
                    continue;
                }
            }
            2 => {
                v___x_662_ = lean_string_append(v___y_660_, v___y_661_);
                crate::leanh::lean_dec_ref(v___y_661_);
                v___x_663_ = l_Std_Time_instReprTimestamp_repr___redArg___closed__8;
                v___x_664_ = lean_string_append(v___x_662_, v___x_663_);
                v___x_665_ = l_String_quote(v___x_664_);
                v___x_666_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_666_, 0, v___x_665_);
                if v_isShared_656_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_655_, 4);
                    crate::leanh::lean_ctor_set(v___x_655_, 1, v___x_666_);
                    crate::leanh::lean_ctor_set(v___x_655_, 0, v___x_658_);
                    v___x_668_ = v___x_655_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_679_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_679_, 0, v___x_658_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_679_, 1, v___x_666_);
                    v___x_668_ = v_reuseFailAlloc_679_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_669_ = 0;
                v___x_670_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_670_, 0, v___x_668_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_670_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_669_,
                );
                v___x_671_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_671_, 0, v___x_657_);
                crate::leanh::lean_ctor_set(v___x_671_, 1, v___x_670_);
                v___x_672_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprTimestamp_repr___redArg___closed__11
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprTimestamp_repr___redArg___closed__11_once
                    ),
                    _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__11,
                );
                v___x_673_ = l_Std_Time_instReprTimestamp_repr___redArg___closed__12;
                v___x_674_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_674_, 0, v___x_673_);
                crate::leanh::lean_ctor_set(v___x_674_, 1, v___x_671_);
                v___x_675_ = l_Std_Time_instReprTimestamp_repr___redArg___closed__13;
                v___x_676_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_676_, 0, v___x_674_);
                crate::leanh::lean_ctor_set(v___x_676_, 1, v___x_675_);
                v___x_677_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_677_, 0, v___x_672_);
                crate::leanh::lean_ctor_set(v___x_677_, 1, v___x_676_);
                v___x_678_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_678_, 0, v___x_677_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_678_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_669_,
                );
                return v___x_678_;
            }
            4 => {
                v___x_684_ = l_Int_repr(v_fst_682_);
                crate::leanh::lean_dec(v_fst_682_);
                crate::leanh::lean_inc_ref(v_fst_681_);
                v___x_685_ = lean_string_append(v_fst_681_, v___x_684_);
                crate::leanh::lean_dec_ref(v___x_684_);
                v___x_686_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprTimestamp_repr___redArg___closed__14
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprTimestamp_repr___redArg___closed__14_once
                    ),
                    _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__14,
                );
                v___x_687_ = lean_int_dec_eq(v_nano_653_, v___x_686_);
                crate::leanh::lean_dec(v_nano_653_);
                if v___x_687_ == 0 {
                    v___x_688_ = l_Std_Time_instReprTimestamp_repr___redArg___closed__15;
                    v___x_689_ = crate::leanh::lean_unsigned_to_nat(9);
                    v___x_690_ = l_Int_repr(v_snd_683_);
                    crate::leanh::lean_dec(v_snd_683_);
                    v___x_691_ = l_Std_Time_instToStringDuration_leftPad(v___x_689_, v___x_690_);
                    crate::leanh::lean_dec_ref(v___x_690_);
                    v___x_692_ = lean_string_append(v___x_688_, v___x_691_);
                    crate::leanh::lean_dec_ref(v___x_691_);
                    v___y_660_ = v___x_685_;
                    v___y_661_ = v___x_692_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_snd_683_);
                    v___x_693_ = l_Std_Time_instReprTimestamp_repr___redArg___closed__16;
                    v___y_660_ = v___x_685_;
                    v___y_661_ = v___x_693_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_instReprTimestamp_repr(
    mut v_x_707_: *mut crate::leanh::LeanObject,
    mut v_prec_708_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_709_ = l_Std_Time_instReprTimestamp_repr___redArg(v_x_707_);
    return v___x_709_;
}
pub unsafe fn l_Std_Time_instReprTimestamp_repr___boxed(
    mut v_x_710_: *mut crate::leanh::LeanObject,
    mut v_prec_711_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_712_ = l_Std_Time_instReprTimestamp_repr(v_x_710_, v_prec_711_);
    crate::leanh::lean_dec(v_prec_711_);
    return v_res_712_;
}
pub unsafe fn l_Std_Time_instDecidableEqTimestamp_decEq(
    mut v_x_715_: *mut crate::leanh::LeanObject,
    mut v_x_716_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_717_: u8 = 0;
    v___x_717_ = l_Std_Time_instDecidableEqDuration_decEq(v_x_715_, v_x_716_);
    return v___x_717_;
}
pub unsafe fn l_Std_Time_instDecidableEqTimestamp_decEq___boxed(
    mut v_x_718_: *mut crate::leanh::LeanObject,
    mut v_x_719_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_720_: u8 = 0;
    let mut v_r_721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_720_ = l_Std_Time_instDecidableEqTimestamp_decEq(v_x_718_, v_x_719_);
    crate::leanh::lean_dec_ref(v_x_719_);
    crate::leanh::lean_dec_ref(v_x_718_);
    v_r_721_ = crate::leanh::lean_box((v_res_720_) as usize);
    return v_r_721_;
}
pub unsafe fn l_Std_Time_instDecidableEqTimestamp(
    mut v_x_722_: *mut crate::leanh::LeanObject,
    mut v_x_723_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_724_: u8 = 0;
    v___x_724_ = l_Std_Time_instDecidableEqDuration_decEq(v_x_722_, v_x_723_);
    return v___x_724_;
}
pub unsafe fn l_Std_Time_instDecidableEqTimestamp___boxed(
    mut v_x_725_: *mut crate::leanh::LeanObject,
    mut v_x_726_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_727_: u8 = 0;
    let mut v_r_728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_727_ = l_Std_Time_instDecidableEqTimestamp(v_x_725_, v_x_726_);
    crate::leanh::lean_dec_ref(v_x_726_);
    crate::leanh::lean_dec_ref(v_x_725_);
    v_r_728_ = crate::leanh::lean_box((v_res_727_) as usize);
    return v_r_728_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedTimestamp_default___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_729_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp_repr___redArg___closed__14),
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp_repr___redArg___closed__14_once),
        _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__14,
    );
    v___x_730_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_730_, 0, v___x_729_);
    crate::leanh::lean_ctor_set(v___x_730_, 1, v___x_729_);
    return v___x_730_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedTimestamp_default() -> *mut crate::leanh::LeanObject {
    let mut v___x_731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_731_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedTimestamp_default___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedTimestamp_default___closed__0_once),
        _init_l_Std_Time_instInhabitedTimestamp_default___closed__0,
    );
    return v___x_731_;
}
pub unsafe fn l_Nat_cast___at___00Std_Time_instInhabitedTimestamp_default_spec__0(
    mut v_a_732_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_733_ = lean_nat_to_int(v_a_732_);
    v___x_734_ = l_Rat_ofInt(v___x_733_);
    return v___x_734_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedTimestamp() -> *mut crate::leanh::LeanObject {
    let mut v___x_735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_735_ = l_Std_Time_instInhabitedTimestamp_default;
    return v___x_735_;
}
pub unsafe fn _init_l_Std_Time_instLETimestamp() -> *mut crate::leanh::LeanObject {
    let mut v___x_736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_736_ = crate::leanh::lean_box(0);
    return v___x_736_;
}
pub unsafe fn l_Std_Time_instDecidableLeTimestamp(
    mut v_x_737_: *mut crate::leanh::LeanObject,
    mut v_y_738_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_739_: u8 = 0;
    v___x_739_ = l_Std_Time_Duration_instDecidableLe(v_x_737_, v_y_738_);
    return v___x_739_;
}
pub unsafe fn l_Std_Time_instDecidableLeTimestamp___boxed(
    mut v_x_740_: *mut crate::leanh::LeanObject,
    mut v_y_741_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_742_: u8 = 0;
    let mut v_r_743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_742_ = l_Std_Time_instDecidableLeTimestamp(v_x_740_, v_y_741_);
    crate::leanh::lean_dec_ref(v_y_741_);
    crate::leanh::lean_dec_ref(v_x_740_);
    v_r_743_ = crate::leanh::lean_box((v_res_742_) as usize);
    return v_r_743_;
}
pub unsafe fn _init_l_Std_Time_instLTTimestamp() -> *mut crate::leanh::LeanObject {
    let mut v___x_744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_744_ = crate::leanh::lean_box(0);
    return v___x_744_;
}
pub unsafe fn l_Std_Time_instDecidableLtTimestamp(
    mut v_x_745_: *mut crate::leanh::LeanObject,
    mut v_y_746_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_747_: u8 = 0;
    v___x_747_ = l_Std_Time_Duration_instDecidableLt(v_x_745_, v_y_746_);
    return v___x_747_;
}
pub unsafe fn l_Std_Time_instDecidableLtTimestamp___boxed(
    mut v_x_748_: *mut crate::leanh::LeanObject,
    mut v_y_749_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_750_: u8 = 0;
    let mut v_r_751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_750_ = l_Std_Time_instDecidableLtTimestamp(v_x_748_, v_y_749_);
    crate::leanh::lean_dec_ref(v_y_749_);
    crate::leanh::lean_dec_ref(v_x_748_);
    v_r_751_ = crate::leanh::lean_box((v_res_750_) as usize);
    return v_r_751_;
}
pub unsafe fn l_Std_Time_instToStringTimestamp___lam__0(
    mut v_s_752_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_second_753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_second_753_ = crate::leanh::lean_ctor_get(v_s_752_, 0);
    v___x_754_ = l_Int_repr(v_second_753_);
    return v___x_754_;
}
pub unsafe fn l_Std_Time_instToStringTimestamp___lam__0___boxed(
    mut v_s_755_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_756_ = l_Std_Time_instToStringTimestamp___lam__0(v_s_755_);
    crate::leanh::lean_dec_ref(v_s_755_);
    return v_res_756_;
}
pub unsafe fn _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_762_ = crate::leanh::lean_unsigned_to_nat(1000000000);
    v___x_763_ = lean_nat_to_int(v___x_762_);
    return v___x_763_;
}
pub unsafe fn l_Std_Time_instReprTimestamp__1___lam__0(
    mut v_s_764_: *mut crate::leanh::LeanObject,
    mut v___y_765_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_second_766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_770_: u8 = 0;
    let mut v___x_771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nanos_774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_781_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_second_766_ = crate::leanh::lean_ctor_get(v_s_764_, 0);
                v_nano_767_ = crate::leanh::lean_ctor_get(v_s_764_, 1);
                v_isSharedCheck_781_ = (!crate::leanh::lean_is_exclusive(v_s_764_)) as u8;
                if v_isSharedCheck_781_ == 0 {
                    v___x_769_ = v_s_764_;
                    v_isShared_770_ = v_isSharedCheck_781_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nano_767_);
                    crate::leanh::lean_inc(v_second_766_);
                    crate::leanh::lean_dec(v_s_764_);
                    v___x_769_ = crate::leanh::lean_box(0);
                    v_isShared_770_ = v_isSharedCheck_781_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_771_ = l_Std_Time_instReprTimestamp__1___lam__0___closed__1;
                v___x_772_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once
                    ),
                    _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2,
                );
                v___x_773_ = lean_int_mul(v_second_766_, v___x_772_);
                crate::leanh::lean_dec(v_second_766_);
                v_nanos_774_ = lean_int_add(v___x_773_, v_nano_767_);
                crate::leanh::lean_dec(v_nano_767_);
                crate::leanh::lean_dec(v___x_773_);
                v___x_775_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_776_ =
                    l_Std_Time_Nanosecond_instReprOrdinal___lam__0(v_nanos_774_, v___x_775_);
                crate::leanh::lean_dec(v_nanos_774_);
                if v_isShared_770_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_769_, 5);
                    crate::leanh::lean_ctor_set(v___x_769_, 1, v___x_776_);
                    crate::leanh::lean_ctor_set(v___x_769_, 0, v___x_771_);
                    v___x_778_ = v___x_769_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_780_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_780_, 0, v___x_771_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_780_, 1, v___x_776_);
                    v___x_778_ = v_reuseFailAlloc_780_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_779_ = l_Repr_addAppParen(v___x_778_, v___y_765_);
                return v___x_779_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_instReprTimestamp__1___lam__0___boxed(
    mut v_s_782_: *mut crate::leanh::LeanObject,
    mut v___y_783_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_784_ = l_Std_Time_instReprTimestamp__1___lam__0(v_s_782_, v___y_783_);
    crate::leanh::lean_dec(v___y_783_);
    return v_res_784_;
}
pub unsafe fn l_Std_Time_instOrdTimestamp___lam__0(
    mut v_x_787_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_x_787_);
    return v_x_787_;
}
pub unsafe fn l_Std_Time_instOrdTimestamp___lam__0___boxed(
    mut v_x_788_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_789_ = l_Std_Time_instOrdTimestamp___lam__0(v_x_788_);
    crate::leanh::lean_dec_ref(v_x_788_);
    return v_res_789_;
}
pub unsafe fn _init_l_Std_Time_instOrdTimestamp___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___f_791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_791_ = l_Std_Time_instOrdTimestamp___closed__0;
    v___x_792_ = l_Std_Time_instOrdDuration;
    v___x_793_ =
        crate::leanh::lean_alloc_closure(l_compareOn___boxed as *mut core::ffi::c_void, 6, 4);
    crate::leanh::lean_closure_set(v___x_793_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_793_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_793_, 2, v___x_792_);
    crate::leanh::lean_closure_set(v___x_793_, 3, v___f_791_);
    return v___x_793_;
}
pub unsafe fn _init_l_Std_Time_instOrdTimestamp() -> *mut crate::leanh::LeanObject {
    let mut v___x_794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_794_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instOrdTimestamp___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_instOrdTimestamp___closed__1_once),
        _init_l_Std_Time_instOrdTimestamp___closed__1,
    );
    return v___x_794_;
}
pub unsafe fn l_Std_Time_Timestamp_now___boxed(
    mut v_a_00___x40___internal___hyg_796_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_797_ = lean_get_current_time();
    return v_res_797_;
}
pub unsafe fn _init_l_Std_Time_Timestamp_toMinutesSinceUnixEpoch___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_798_ = crate::leanh::lean_unsigned_to_nat(60);
    v___x_799_ = lean_nat_to_int(v___x_798_);
    return v___x_799_;
}
pub unsafe fn l_Std_Time_Timestamp_toMinutesSinceUnixEpoch(
    mut v_tm_800_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_second_801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_second_801_ = crate::leanh::lean_ctor_get(v_tm_800_, 0);
    v___x_802_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toMinutesSinceUnixEpoch___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toMinutesSinceUnixEpoch___closed__0_once),
        _init_l_Std_Time_Timestamp_toMinutesSinceUnixEpoch___closed__0,
    );
    v___x_803_ = lean_int_div(v_second_801_, v___x_802_);
    return v___x_803_;
}
pub unsafe fn l_Std_Time_Timestamp_toMinutesSinceUnixEpoch___boxed(
    mut v_tm_804_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_805_ = l_Std_Time_Timestamp_toMinutesSinceUnixEpoch(v_tm_804_);
    crate::leanh::lean_dec_ref(v_tm_804_);
    return v_res_805_;
}
pub unsafe fn _init_l_Std_Time_Timestamp_toDaysSinceUnixEpoch___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_806_ = crate::leanh::lean_unsigned_to_nat(86400);
    v___x_807_ = lean_nat_to_int(v___x_806_);
    return v___x_807_;
}
pub unsafe fn l_Std_Time_Timestamp_toDaysSinceUnixEpoch(
    mut v_tm_808_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_second_809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_second_809_ = crate::leanh::lean_ctor_get(v_tm_808_, 0);
    v___x_810_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toDaysSinceUnixEpoch___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toDaysSinceUnixEpoch___closed__0_once),
        _init_l_Std_Time_Timestamp_toDaysSinceUnixEpoch___closed__0,
    );
    v___x_811_ = lean_int_div(v_second_809_, v___x_810_);
    return v___x_811_;
}
pub unsafe fn l_Std_Time_Timestamp_toDaysSinceUnixEpoch___boxed(
    mut v_tm_812_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_813_ = l_Std_Time_Timestamp_toDaysSinceUnixEpoch(v_tm_812_);
    crate::leanh::lean_dec_ref(v_tm_812_);
    return v_res_813_;
}
pub unsafe fn l_Std_Time_Timestamp_ofSecondsSinceUnixEpoch(
    mut v_secs_814_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_815_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp_repr___redArg___closed__14),
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp_repr___redArg___closed__14_once),
        _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__14,
    );
    v___x_816_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_816_, 0, v_secs_814_);
    crate::leanh::lean_ctor_set(v___x_816_, 1, v___x_815_);
    return v___x_816_;
}
pub unsafe fn l_Std_Time_Timestamp_ofNanosecondsSinceUnixEpoch(
    mut v_nanos_817_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_818_ = l_Std_Time_Duration_ofNanoseconds(v_nanos_817_);
    return v___x_818_;
}
pub unsafe fn l_Std_Time_Timestamp_ofNanosecondsSinceUnixEpoch___boxed(
    mut v_nanos_819_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_820_ = l_Std_Time_Timestamp_ofNanosecondsSinceUnixEpoch(v_nanos_819_);
    crate::leanh::lean_dec(v_nanos_819_);
    return v_res_820_;
}
pub unsafe fn l_Std_Time_Timestamp_ofDurationSinceUnixEpoch(
    mut v_duration_821_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_duration_821_);
    return v_duration_821_;
}
pub unsafe fn l_Std_Time_Timestamp_ofDurationSinceUnixEpoch___boxed(
    mut v_duration_822_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_823_ = l_Std_Time_Timestamp_ofDurationSinceUnixEpoch(v_duration_822_);
    crate::leanh::lean_dec_ref(v_duration_822_);
    return v_res_823_;
}
pub unsafe fn _init_l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_824_ = crate::leanh::lean_unsigned_to_nat(1000000);
    v___x_825_ = lean_nat_to_int(v___x_824_);
    return v___x_825_;
}
pub unsafe fn l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch(
    mut v_milli_826_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_827_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0_once),
        _init_l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0,
    );
    v___x_828_ = lean_int_mul(v_milli_826_, v___x_827_);
    v___x_829_ = l_Std_Time_Duration_ofNanoseconds(v___x_828_);
    crate::leanh::lean_dec(v___x_828_);
    return v___x_829_;
}
pub unsafe fn l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___boxed(
    mut v_milli_830_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_831_ = l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch(v_milli_830_);
    crate::leanh::lean_dec(v_milli_830_);
    return v_res_831_;
}
pub unsafe fn l_Std_Time_Timestamp_toSecondsSinceUnixEpoch(
    mut v_t_832_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_second_833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_second_833_ = crate::leanh::lean_ctor_get(v_t_832_, 0);
    crate::leanh::lean_inc(v_second_833_);
    return v_second_833_;
}
pub unsafe fn l_Std_Time_Timestamp_toSecondsSinceUnixEpoch___boxed(
    mut v_t_834_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_835_ = l_Std_Time_Timestamp_toSecondsSinceUnixEpoch(v_t_834_);
    crate::leanh::lean_dec_ref(v_t_834_);
    return v_res_835_;
}
pub unsafe fn l_Std_Time_Timestamp_toNanosecondsSinceUnixEpoch(
    mut v_tm_836_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_second_837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nanos_841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_second_837_ = crate::leanh::lean_ctor_get(v_tm_836_, 0);
    v_nano_838_ = crate::leanh::lean_ctor_get(v_tm_836_, 1);
    v___x_839_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once),
        _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2,
    );
    v___x_840_ = lean_int_mul(v_second_837_, v___x_839_);
    v_nanos_841_ = lean_int_add(v___x_840_, v_nano_838_);
    crate::leanh::lean_dec(v___x_840_);
    return v_nanos_841_;
}
pub unsafe fn l_Std_Time_Timestamp_toNanosecondsSinceUnixEpoch___boxed(
    mut v_tm_842_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_843_ = l_Std_Time_Timestamp_toNanosecondsSinceUnixEpoch(v_tm_842_);
    crate::leanh::lean_dec_ref(v_tm_842_);
    return v_res_843_;
}
pub unsafe fn l_Std_Time_Timestamp_toMillisecondsSinceUnixEpoch(
    mut v_tm_844_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_second_845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_second_845_ = crate::leanh::lean_ctor_get(v_tm_844_, 0);
    v_nano_846_ = crate::leanh::lean_ctor_get(v_tm_844_, 1);
    v___x_847_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once),
        _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2,
    );
    v___x_848_ = lean_int_mul(v_second_845_, v___x_847_);
    v___x_849_ = lean_int_add(v___x_848_, v_nano_846_);
    crate::leanh::lean_dec(v___x_848_);
    v___x_850_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0_once),
        _init_l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0,
    );
    v___x_851_ = lean_int_div(v___x_849_, v___x_850_);
    crate::leanh::lean_dec(v___x_849_);
    return v___x_851_;
}
pub unsafe fn l_Std_Time_Timestamp_toMillisecondsSinceUnixEpoch___boxed(
    mut v_tm_852_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_853_ = l_Std_Time_Timestamp_toMillisecondsSinceUnixEpoch(v_tm_852_);
    crate::leanh::lean_dec_ref(v_tm_852_);
    return v_res_853_;
}
pub unsafe fn l_Std_Time_Timestamp_since(
    mut v_f_854_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_860_: u8 = 0;
    let mut v_second_861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_877_: u8 = 0;
    let mut v_a_878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_881_: u8 = 0;
    let mut v___x_883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_885_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_856_ = lean_get_current_time();
                if crate::leanh::lean_obj_tag(v___x_856_) == 0 {
                    v_a_857_ = crate::leanh::lean_ctor_get(v___x_856_, 0);
                    v_isSharedCheck_877_ = (!crate::leanh::lean_is_exclusive(v___x_856_)) as u8;
                    if v_isSharedCheck_877_ == 0 {
                        v___x_859_ = v___x_856_;
                        v_isShared_860_ = v_isSharedCheck_877_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_857_);
                        crate::leanh::lean_dec(v___x_856_);
                        v___x_859_ = crate::leanh::lean_box(0);
                        v_isShared_860_ = v_isSharedCheck_877_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_878_ = crate::leanh::lean_ctor_get(v___x_856_, 0);
                    v_isSharedCheck_885_ = (!crate::leanh::lean_is_exclusive(v___x_856_)) as u8;
                    if v_isSharedCheck_885_ == 0 {
                        v___x_880_ = v___x_856_;
                        v_isShared_881_ = v_isSharedCheck_885_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_878_);
                        crate::leanh::lean_dec(v___x_856_);
                        v___x_880_ = crate::leanh::lean_box(0);
                        v_isShared_881_ = v_isSharedCheck_885_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_second_861_ = crate::leanh::lean_ctor_get(v_f_854_, 0);
                v_nano_862_ = crate::leanh::lean_ctor_get(v_f_854_, 1);
                v_second_863_ = crate::leanh::lean_ctor_get(v_a_857_, 0);
                crate::leanh::lean_inc(v_second_863_);
                v_nano_864_ = crate::leanh::lean_ctor_get(v_a_857_, 1);
                crate::leanh::lean_inc(v_nano_864_);
                crate::leanh::lean_dec(v_a_857_);
                v___x_865_ = lean_int_neg(v_second_861_);
                v___x_866_ = lean_int_neg(v_nano_862_);
                v___x_867_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once
                    ),
                    _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2,
                );
                v___x_868_ = lean_int_mul(v_second_863_, v___x_867_);
                crate::leanh::lean_dec(v_second_863_);
                v___x_869_ = lean_int_add(v___x_868_, v_nano_864_);
                crate::leanh::lean_dec(v_nano_864_);
                crate::leanh::lean_dec(v___x_868_);
                v___x_870_ = lean_int_mul(v___x_865_, v___x_867_);
                crate::leanh::lean_dec(v___x_865_);
                v___x_871_ = lean_int_add(v___x_870_, v___x_866_);
                crate::leanh::lean_dec(v___x_866_);
                crate::leanh::lean_dec(v___x_870_);
                v___x_872_ = lean_int_add(v___x_869_, v___x_871_);
                crate::leanh::lean_dec(v___x_871_);
                crate::leanh::lean_dec(v___x_869_);
                v___x_873_ = l_Std_Time_Duration_ofNanoseconds(v___x_872_);
                crate::leanh::lean_dec(v___x_872_);
                if v_isShared_860_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_859_, 0, v___x_873_);
                    v___x_875_ = v___x_859_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_876_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_876_, 0, v___x_873_);
                    v___x_875_ = v_reuseFailAlloc_876_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_875_;
            }
            3 => {
                if v_isShared_881_ == 0 {
                    v___x_883_ = v___x_880_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_884_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_884_, 0, v_a_878_);
                    v___x_883_ = v_reuseFailAlloc_884_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_883_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_Timestamp_since___boxed(
    mut v_f_886_: *mut crate::leanh::LeanObject,
    mut v_a_887_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_888_ = l_Std_Time_Timestamp_since(v_f_886_);
    crate::leanh::lean_dec_ref(v_f_886_);
    return v_res_888_;
}
pub unsafe fn l_Std_Time_Timestamp_toDurationSinceUnixEpoch(
    mut v_tm_889_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_tm_889_);
    return v_tm_889_;
}
pub unsafe fn l_Std_Time_Timestamp_toDurationSinceUnixEpoch___boxed(
    mut v_tm_890_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_891_ = l_Std_Time_Timestamp_toDurationSinceUnixEpoch(v_tm_890_);
    crate::leanh::lean_dec_ref(v_tm_890_);
    return v_res_891_;
}
pub unsafe fn l_Std_Time_Timestamp_addMilliseconds(
    mut v_t_892_: *mut crate::leanh::LeanObject,
    mut v_s_893_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_second_894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_second_894_ = crate::leanh::lean_ctor_get(v_t_892_, 0);
    v_nano_895_ = crate::leanh::lean_ctor_get(v_t_892_, 1);
    v___x_896_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0_once),
        _init_l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0,
    );
    v___x_897_ = lean_int_mul(v_s_893_, v___x_896_);
    v___x_898_ = l_Std_Time_Duration_ofNanoseconds(v___x_897_);
    crate::leanh::lean_dec(v___x_897_);
    v_second_899_ = crate::leanh::lean_ctor_get(v___x_898_, 0);
    crate::leanh::lean_inc(v_second_899_);
    v_nano_900_ = crate::leanh::lean_ctor_get(v___x_898_, 1);
    crate::leanh::lean_inc(v_nano_900_);
    crate::leanh::lean_dec_ref(v___x_898_);
    v___x_901_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once),
        _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2,
    );
    v___x_902_ = lean_int_mul(v_second_894_, v___x_901_);
    v___x_903_ = lean_int_add(v___x_902_, v_nano_895_);
    crate::leanh::lean_dec(v___x_902_);
    v___x_904_ = lean_int_mul(v_second_899_, v___x_901_);
    crate::leanh::lean_dec(v_second_899_);
    v___x_905_ = lean_int_add(v___x_904_, v_nano_900_);
    crate::leanh::lean_dec(v_nano_900_);
    crate::leanh::lean_dec(v___x_904_);
    v___x_906_ = lean_int_add(v___x_903_, v___x_905_);
    crate::leanh::lean_dec(v___x_905_);
    crate::leanh::lean_dec(v___x_903_);
    v___x_907_ = l_Std_Time_Duration_ofNanoseconds(v___x_906_);
    crate::leanh::lean_dec(v___x_906_);
    return v___x_907_;
}
pub unsafe fn l_Std_Time_Timestamp_addMilliseconds___boxed(
    mut v_t_908_: *mut crate::leanh::LeanObject,
    mut v_s_909_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_910_ = l_Std_Time_Timestamp_addMilliseconds(v_t_908_, v_s_909_);
    crate::leanh::lean_dec(v_s_909_);
    crate::leanh::lean_dec_ref(v_t_908_);
    return v_res_910_;
}
pub unsafe fn l_Std_Time_Timestamp_subMilliseconds(
    mut v_t_911_: *mut crate::leanh::LeanObject,
    mut v_s_912_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_913_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0_once),
        _init_l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0,
    );
    v___x_914_ = lean_int_mul(v_s_912_, v___x_913_);
    v___x_915_ = l_Std_Time_Duration_ofNanoseconds(v___x_914_);
    crate::leanh::lean_dec(v___x_914_);
    v_second_916_ = crate::leanh::lean_ctor_get(v___x_915_, 0);
    crate::leanh::lean_inc(v_second_916_);
    v_nano_917_ = crate::leanh::lean_ctor_get(v___x_915_, 1);
    crate::leanh::lean_inc(v_nano_917_);
    crate::leanh::lean_dec_ref(v___x_915_);
    v_second_918_ = crate::leanh::lean_ctor_get(v_t_911_, 0);
    v_nano_919_ = crate::leanh::lean_ctor_get(v_t_911_, 1);
    v___x_920_ = lean_int_neg(v_second_916_);
    crate::leanh::lean_dec(v_second_916_);
    v___x_921_ = lean_int_neg(v_nano_917_);
    crate::leanh::lean_dec(v_nano_917_);
    v___x_922_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once),
        _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2,
    );
    v___x_923_ = lean_int_mul(v_second_918_, v___x_922_);
    v___x_924_ = lean_int_add(v___x_923_, v_nano_919_);
    crate::leanh::lean_dec(v___x_923_);
    v___x_925_ = lean_int_mul(v___x_920_, v___x_922_);
    crate::leanh::lean_dec(v___x_920_);
    v___x_926_ = lean_int_add(v___x_925_, v___x_921_);
    crate::leanh::lean_dec(v___x_921_);
    crate::leanh::lean_dec(v___x_925_);
    v___x_927_ = lean_int_add(v___x_924_, v___x_926_);
    crate::leanh::lean_dec(v___x_926_);
    crate::leanh::lean_dec(v___x_924_);
    v___x_928_ = l_Std_Time_Duration_ofNanoseconds(v___x_927_);
    crate::leanh::lean_dec(v___x_927_);
    return v___x_928_;
}
pub unsafe fn l_Std_Time_Timestamp_subMilliseconds___boxed(
    mut v_t_929_: *mut crate::leanh::LeanObject,
    mut v_s_930_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_931_ = l_Std_Time_Timestamp_subMilliseconds(v_t_929_, v_s_930_);
    crate::leanh::lean_dec(v_s_930_);
    crate::leanh::lean_dec_ref(v_t_929_);
    return v_res_931_;
}
pub unsafe fn l_Std_Time_Timestamp_addNanoseconds(
    mut v_t_932_: *mut crate::leanh::LeanObject,
    mut v_s_933_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_second_934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_second_934_ = crate::leanh::lean_ctor_get(v_t_932_, 0);
    v_nano_935_ = crate::leanh::lean_ctor_get(v_t_932_, 1);
    v___x_936_ = l_Std_Time_Duration_ofNanoseconds(v_s_933_);
    v_second_937_ = crate::leanh::lean_ctor_get(v___x_936_, 0);
    crate::leanh::lean_inc(v_second_937_);
    v_nano_938_ = crate::leanh::lean_ctor_get(v___x_936_, 1);
    crate::leanh::lean_inc(v_nano_938_);
    crate::leanh::lean_dec_ref(v___x_936_);
    v___x_939_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once),
        _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2,
    );
    v___x_940_ = lean_int_mul(v_second_934_, v___x_939_);
    v___x_941_ = lean_int_add(v___x_940_, v_nano_935_);
    crate::leanh::lean_dec(v___x_940_);
    v___x_942_ = lean_int_mul(v_second_937_, v___x_939_);
    crate::leanh::lean_dec(v_second_937_);
    v___x_943_ = lean_int_add(v___x_942_, v_nano_938_);
    crate::leanh::lean_dec(v_nano_938_);
    crate::leanh::lean_dec(v___x_942_);
    v___x_944_ = lean_int_add(v___x_941_, v___x_943_);
    crate::leanh::lean_dec(v___x_943_);
    crate::leanh::lean_dec(v___x_941_);
    v___x_945_ = l_Std_Time_Duration_ofNanoseconds(v___x_944_);
    crate::leanh::lean_dec(v___x_944_);
    return v___x_945_;
}
pub unsafe fn l_Std_Time_Timestamp_addNanoseconds___boxed(
    mut v_t_946_: *mut crate::leanh::LeanObject,
    mut v_s_947_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_948_ = l_Std_Time_Timestamp_addNanoseconds(v_t_946_, v_s_947_);
    crate::leanh::lean_dec(v_s_947_);
    crate::leanh::lean_dec_ref(v_t_946_);
    return v_res_948_;
}
pub unsafe fn l_Std_Time_Timestamp_subNanoseconds(
    mut v_t_949_: *mut crate::leanh::LeanObject,
    mut v_s_950_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_951_ = l_Std_Time_Duration_ofNanoseconds(v_s_950_);
    v_second_952_ = crate::leanh::lean_ctor_get(v___x_951_, 0);
    crate::leanh::lean_inc(v_second_952_);
    v_nano_953_ = crate::leanh::lean_ctor_get(v___x_951_, 1);
    crate::leanh::lean_inc(v_nano_953_);
    crate::leanh::lean_dec_ref(v___x_951_);
    v_second_954_ = crate::leanh::lean_ctor_get(v_t_949_, 0);
    v_nano_955_ = crate::leanh::lean_ctor_get(v_t_949_, 1);
    v___x_956_ = lean_int_neg(v_second_952_);
    crate::leanh::lean_dec(v_second_952_);
    v___x_957_ = lean_int_neg(v_nano_953_);
    crate::leanh::lean_dec(v_nano_953_);
    v___x_958_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once),
        _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2,
    );
    v___x_959_ = lean_int_mul(v_second_954_, v___x_958_);
    v___x_960_ = lean_int_add(v___x_959_, v_nano_955_);
    crate::leanh::lean_dec(v___x_959_);
    v___x_961_ = lean_int_mul(v___x_956_, v___x_958_);
    crate::leanh::lean_dec(v___x_956_);
    v___x_962_ = lean_int_add(v___x_961_, v___x_957_);
    crate::leanh::lean_dec(v___x_957_);
    crate::leanh::lean_dec(v___x_961_);
    v___x_963_ = lean_int_add(v___x_960_, v___x_962_);
    crate::leanh::lean_dec(v___x_962_);
    crate::leanh::lean_dec(v___x_960_);
    v___x_964_ = l_Std_Time_Duration_ofNanoseconds(v___x_963_);
    crate::leanh::lean_dec(v___x_963_);
    return v___x_964_;
}
pub unsafe fn l_Std_Time_Timestamp_subNanoseconds___boxed(
    mut v_t_965_: *mut crate::leanh::LeanObject,
    mut v_s_966_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_967_ = l_Std_Time_Timestamp_subNanoseconds(v_t_965_, v_s_966_);
    crate::leanh::lean_dec(v_s_966_);
    crate::leanh::lean_dec_ref(v_t_965_);
    return v_res_967_;
}
pub unsafe fn l_Std_Time_Timestamp_addSeconds(
    mut v_t_968_: *mut crate::leanh::LeanObject,
    mut v_s_969_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_second_970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_second_970_ = crate::leanh::lean_ctor_get(v_t_968_, 0);
    v_nano_971_ = crate::leanh::lean_ctor_get(v_t_968_, 1);
    v___x_972_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp_repr___redArg___closed__14),
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp_repr___redArg___closed__14_once),
        _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__14,
    );
    v___x_973_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once),
        _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2,
    );
    v___x_974_ = lean_int_mul(v_second_970_, v___x_973_);
    v___x_975_ = lean_int_add(v___x_974_, v_nano_971_);
    crate::leanh::lean_dec(v___x_974_);
    v___x_976_ = lean_int_mul(v_s_969_, v___x_973_);
    v___x_977_ = lean_int_add(v___x_976_, v___x_972_);
    crate::leanh::lean_dec(v___x_976_);
    v___x_978_ = lean_int_add(v___x_975_, v___x_977_);
    crate::leanh::lean_dec(v___x_977_);
    crate::leanh::lean_dec(v___x_975_);
    v___x_979_ = l_Std_Time_Duration_ofNanoseconds(v___x_978_);
    crate::leanh::lean_dec(v___x_978_);
    return v___x_979_;
}
pub unsafe fn l_Std_Time_Timestamp_addSeconds___boxed(
    mut v_t_980_: *mut crate::leanh::LeanObject,
    mut v_s_981_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_982_ = l_Std_Time_Timestamp_addSeconds(v_t_980_, v_s_981_);
    crate::leanh::lean_dec(v_s_981_);
    crate::leanh::lean_dec_ref(v_t_980_);
    return v_res_982_;
}
pub unsafe fn _init_l_Std_Time_Timestamp_subSeconds___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_983_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp_repr___redArg___closed__14),
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp_repr___redArg___closed__14_once),
        _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__14,
    );
    v___x_984_ = lean_int_neg(v___x_983_);
    return v___x_984_;
}
pub unsafe fn l_Std_Time_Timestamp_subSeconds(
    mut v_t_985_: *mut crate::leanh::LeanObject,
    mut v_s_986_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_second_987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_second_987_ = crate::leanh::lean_ctor_get(v_t_985_, 0);
    v_nano_988_ = crate::leanh::lean_ctor_get(v_t_985_, 1);
    v___x_989_ = lean_int_neg(v_s_986_);
    v___x_990_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_subSeconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_subSeconds___closed__0_once),
        _init_l_Std_Time_Timestamp_subSeconds___closed__0,
    );
    v___x_991_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once),
        _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2,
    );
    v___x_992_ = lean_int_mul(v_second_987_, v___x_991_);
    v___x_993_ = lean_int_add(v___x_992_, v_nano_988_);
    crate::leanh::lean_dec(v___x_992_);
    v___x_994_ = lean_int_mul(v___x_989_, v___x_991_);
    crate::leanh::lean_dec(v___x_989_);
    v___x_995_ = lean_int_add(v___x_994_, v___x_990_);
    crate::leanh::lean_dec(v___x_994_);
    v___x_996_ = lean_int_add(v___x_993_, v___x_995_);
    crate::leanh::lean_dec(v___x_995_);
    crate::leanh::lean_dec(v___x_993_);
    v___x_997_ = l_Std_Time_Duration_ofNanoseconds(v___x_996_);
    crate::leanh::lean_dec(v___x_996_);
    return v___x_997_;
}
pub unsafe fn l_Std_Time_Timestamp_subSeconds___boxed(
    mut v_t_998_: *mut crate::leanh::LeanObject,
    mut v_s_999_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1000_ = l_Std_Time_Timestamp_subSeconds(v_t_998_, v_s_999_);
    crate::leanh::lean_dec(v_s_999_);
    crate::leanh::lean_dec_ref(v_t_998_);
    return v_res_1000_;
}
pub unsafe fn l_Std_Time_Timestamp_addMinutes(
    mut v_t_1001_: *mut crate::leanh::LeanObject,
    mut v_m_1002_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_second_1003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_second_1003_ = crate::leanh::lean_ctor_get(v_t_1001_, 0);
    v_nano_1004_ = crate::leanh::lean_ctor_get(v_t_1001_, 1);
    v___x_1005_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toMinutesSinceUnixEpoch___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toMinutesSinceUnixEpoch___closed__0_once),
        _init_l_Std_Time_Timestamp_toMinutesSinceUnixEpoch___closed__0,
    );
    v___x_1006_ = lean_int_mul(v_m_1002_, v___x_1005_);
    v___x_1007_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp_repr___redArg___closed__14),
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp_repr___redArg___closed__14_once),
        _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__14,
    );
    v___x_1008_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once),
        _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2,
    );
    v___x_1009_ = lean_int_mul(v_second_1003_, v___x_1008_);
    v___x_1010_ = lean_int_add(v___x_1009_, v_nano_1004_);
    crate::leanh::lean_dec(v___x_1009_);
    v___x_1011_ = lean_int_mul(v___x_1006_, v___x_1008_);
    crate::leanh::lean_dec(v___x_1006_);
    v___x_1012_ = lean_int_add(v___x_1011_, v___x_1007_);
    crate::leanh::lean_dec(v___x_1011_);
    v___x_1013_ = lean_int_add(v___x_1010_, v___x_1012_);
    crate::leanh::lean_dec(v___x_1012_);
    crate::leanh::lean_dec(v___x_1010_);
    v___x_1014_ = l_Std_Time_Duration_ofNanoseconds(v___x_1013_);
    crate::leanh::lean_dec(v___x_1013_);
    return v___x_1014_;
}
pub unsafe fn l_Std_Time_Timestamp_addMinutes___boxed(
    mut v_t_1015_: *mut crate::leanh::LeanObject,
    mut v_m_1016_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1017_ = l_Std_Time_Timestamp_addMinutes(v_t_1015_, v_m_1016_);
    crate::leanh::lean_dec(v_m_1016_);
    crate::leanh::lean_dec_ref(v_t_1015_);
    return v_res_1017_;
}
pub unsafe fn l_Std_Time_Timestamp_subMinutes(
    mut v_t_1018_: *mut crate::leanh::LeanObject,
    mut v_m_1019_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_second_1020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_second_1020_ = crate::leanh::lean_ctor_get(v_t_1018_, 0);
    v_nano_1021_ = crate::leanh::lean_ctor_get(v_t_1018_, 1);
    v___x_1022_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toMinutesSinceUnixEpoch___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toMinutesSinceUnixEpoch___closed__0_once),
        _init_l_Std_Time_Timestamp_toMinutesSinceUnixEpoch___closed__0,
    );
    v___x_1023_ = lean_int_mul(v_m_1019_, v___x_1022_);
    v___x_1024_ = lean_int_neg(v___x_1023_);
    crate::leanh::lean_dec(v___x_1023_);
    v___x_1025_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_subSeconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_subSeconds___closed__0_once),
        _init_l_Std_Time_Timestamp_subSeconds___closed__0,
    );
    v___x_1026_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once),
        _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2,
    );
    v___x_1027_ = lean_int_mul(v_second_1020_, v___x_1026_);
    v___x_1028_ = lean_int_add(v___x_1027_, v_nano_1021_);
    crate::leanh::lean_dec(v___x_1027_);
    v___x_1029_ = lean_int_mul(v___x_1024_, v___x_1026_);
    crate::leanh::lean_dec(v___x_1024_);
    v___x_1030_ = lean_int_add(v___x_1029_, v___x_1025_);
    crate::leanh::lean_dec(v___x_1029_);
    v___x_1031_ = lean_int_add(v___x_1028_, v___x_1030_);
    crate::leanh::lean_dec(v___x_1030_);
    crate::leanh::lean_dec(v___x_1028_);
    v___x_1032_ = l_Std_Time_Duration_ofNanoseconds(v___x_1031_);
    crate::leanh::lean_dec(v___x_1031_);
    return v___x_1032_;
}
pub unsafe fn l_Std_Time_Timestamp_subMinutes___boxed(
    mut v_t_1033_: *mut crate::leanh::LeanObject,
    mut v_m_1034_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1035_ = l_Std_Time_Timestamp_subMinutes(v_t_1033_, v_m_1034_);
    crate::leanh::lean_dec(v_m_1034_);
    crate::leanh::lean_dec_ref(v_t_1033_);
    return v_res_1035_;
}
pub unsafe fn _init_l_Std_Time_Timestamp_addHours___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_1036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1036_ = crate::leanh::lean_unsigned_to_nat(3600);
    v___x_1037_ = lean_nat_to_int(v___x_1036_);
    return v___x_1037_;
}
pub unsafe fn l_Std_Time_Timestamp_addHours(
    mut v_t_1038_: *mut crate::leanh::LeanObject,
    mut v_h_1039_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_second_1040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_second_1040_ = crate::leanh::lean_ctor_get(v_t_1038_, 0);
    v_nano_1041_ = crate::leanh::lean_ctor_get(v_t_1038_, 1);
    v___x_1042_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_addHours___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_addHours___closed__0_once),
        _init_l_Std_Time_Timestamp_addHours___closed__0,
    );
    v___x_1043_ = lean_int_mul(v_h_1039_, v___x_1042_);
    v___x_1044_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp_repr___redArg___closed__14),
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp_repr___redArg___closed__14_once),
        _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__14,
    );
    v___x_1045_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once),
        _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2,
    );
    v___x_1046_ = lean_int_mul(v_second_1040_, v___x_1045_);
    v___x_1047_ = lean_int_add(v___x_1046_, v_nano_1041_);
    crate::leanh::lean_dec(v___x_1046_);
    v___x_1048_ = lean_int_mul(v___x_1043_, v___x_1045_);
    crate::leanh::lean_dec(v___x_1043_);
    v___x_1049_ = lean_int_add(v___x_1048_, v___x_1044_);
    crate::leanh::lean_dec(v___x_1048_);
    v___x_1050_ = lean_int_add(v___x_1047_, v___x_1049_);
    crate::leanh::lean_dec(v___x_1049_);
    crate::leanh::lean_dec(v___x_1047_);
    v___x_1051_ = l_Std_Time_Duration_ofNanoseconds(v___x_1050_);
    crate::leanh::lean_dec(v___x_1050_);
    return v___x_1051_;
}
pub unsafe fn l_Std_Time_Timestamp_addHours___boxed(
    mut v_t_1052_: *mut crate::leanh::LeanObject,
    mut v_h_1053_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1054_ = l_Std_Time_Timestamp_addHours(v_t_1052_, v_h_1053_);
    crate::leanh::lean_dec(v_h_1053_);
    crate::leanh::lean_dec_ref(v_t_1052_);
    return v_res_1054_;
}
pub unsafe fn l_Std_Time_Timestamp_subHours(
    mut v_t_1055_: *mut crate::leanh::LeanObject,
    mut v_h_1056_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_second_1057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_second_1057_ = crate::leanh::lean_ctor_get(v_t_1055_, 0);
    v_nano_1058_ = crate::leanh::lean_ctor_get(v_t_1055_, 1);
    v___x_1059_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_addHours___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_addHours___closed__0_once),
        _init_l_Std_Time_Timestamp_addHours___closed__0,
    );
    v___x_1060_ = lean_int_mul(v_h_1056_, v___x_1059_);
    v___x_1061_ = lean_int_neg(v___x_1060_);
    crate::leanh::lean_dec(v___x_1060_);
    v___x_1062_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_subSeconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_subSeconds___closed__0_once),
        _init_l_Std_Time_Timestamp_subSeconds___closed__0,
    );
    v___x_1063_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once),
        _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2,
    );
    v___x_1064_ = lean_int_mul(v_second_1057_, v___x_1063_);
    v___x_1065_ = lean_int_add(v___x_1064_, v_nano_1058_);
    crate::leanh::lean_dec(v___x_1064_);
    v___x_1066_ = lean_int_mul(v___x_1061_, v___x_1063_);
    crate::leanh::lean_dec(v___x_1061_);
    v___x_1067_ = lean_int_add(v___x_1066_, v___x_1062_);
    crate::leanh::lean_dec(v___x_1066_);
    v___x_1068_ = lean_int_add(v___x_1065_, v___x_1067_);
    crate::leanh::lean_dec(v___x_1067_);
    crate::leanh::lean_dec(v___x_1065_);
    v___x_1069_ = l_Std_Time_Duration_ofNanoseconds(v___x_1068_);
    crate::leanh::lean_dec(v___x_1068_);
    return v___x_1069_;
}
pub unsafe fn l_Std_Time_Timestamp_subHours___boxed(
    mut v_t_1070_: *mut crate::leanh::LeanObject,
    mut v_h_1071_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1072_ = l_Std_Time_Timestamp_subHours(v_t_1070_, v_h_1071_);
    crate::leanh::lean_dec(v_h_1071_);
    crate::leanh::lean_dec_ref(v_t_1070_);
    return v_res_1072_;
}
pub unsafe fn l_Std_Time_Timestamp_addDays(
    mut v_t_1073_: *mut crate::leanh::LeanObject,
    mut v_d_1074_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_second_1075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_second_1075_ = crate::leanh::lean_ctor_get(v_t_1073_, 0);
    v_nano_1076_ = crate::leanh::lean_ctor_get(v_t_1073_, 1);
    v___x_1077_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toDaysSinceUnixEpoch___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toDaysSinceUnixEpoch___closed__0_once),
        _init_l_Std_Time_Timestamp_toDaysSinceUnixEpoch___closed__0,
    );
    v___x_1078_ = lean_int_mul(v_d_1074_, v___x_1077_);
    v___x_1079_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp_repr___redArg___closed__14),
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp_repr___redArg___closed__14_once),
        _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__14,
    );
    v___x_1080_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once),
        _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2,
    );
    v___x_1081_ = lean_int_mul(v_second_1075_, v___x_1080_);
    v___x_1082_ = lean_int_add(v___x_1081_, v_nano_1076_);
    crate::leanh::lean_dec(v___x_1081_);
    v___x_1083_ = lean_int_mul(v___x_1078_, v___x_1080_);
    crate::leanh::lean_dec(v___x_1078_);
    v___x_1084_ = lean_int_add(v___x_1083_, v___x_1079_);
    crate::leanh::lean_dec(v___x_1083_);
    v___x_1085_ = lean_int_add(v___x_1082_, v___x_1084_);
    crate::leanh::lean_dec(v___x_1084_);
    crate::leanh::lean_dec(v___x_1082_);
    v___x_1086_ = l_Std_Time_Duration_ofNanoseconds(v___x_1085_);
    crate::leanh::lean_dec(v___x_1085_);
    return v___x_1086_;
}
pub unsafe fn l_Std_Time_Timestamp_addDays___boxed(
    mut v_t_1087_: *mut crate::leanh::LeanObject,
    mut v_d_1088_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1089_ = l_Std_Time_Timestamp_addDays(v_t_1087_, v_d_1088_);
    crate::leanh::lean_dec(v_d_1088_);
    crate::leanh::lean_dec_ref(v_t_1087_);
    return v_res_1089_;
}
pub unsafe fn l_Std_Time_Timestamp_subDays(
    mut v_t_1090_: *mut crate::leanh::LeanObject,
    mut v_d_1091_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_second_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_second_1092_ = crate::leanh::lean_ctor_get(v_t_1090_, 0);
    v_nano_1093_ = crate::leanh::lean_ctor_get(v_t_1090_, 1);
    v___x_1094_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toDaysSinceUnixEpoch___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toDaysSinceUnixEpoch___closed__0_once),
        _init_l_Std_Time_Timestamp_toDaysSinceUnixEpoch___closed__0,
    );
    v___x_1095_ = lean_int_mul(v_d_1091_, v___x_1094_);
    v___x_1096_ = lean_int_neg(v___x_1095_);
    crate::leanh::lean_dec(v___x_1095_);
    v___x_1097_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_subSeconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_subSeconds___closed__0_once),
        _init_l_Std_Time_Timestamp_subSeconds___closed__0,
    );
    v___x_1098_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once),
        _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2,
    );
    v___x_1099_ = lean_int_mul(v_second_1092_, v___x_1098_);
    v___x_1100_ = lean_int_add(v___x_1099_, v_nano_1093_);
    crate::leanh::lean_dec(v___x_1099_);
    v___x_1101_ = lean_int_mul(v___x_1096_, v___x_1098_);
    crate::leanh::lean_dec(v___x_1096_);
    v___x_1102_ = lean_int_add(v___x_1101_, v___x_1097_);
    crate::leanh::lean_dec(v___x_1101_);
    v___x_1103_ = lean_int_add(v___x_1100_, v___x_1102_);
    crate::leanh::lean_dec(v___x_1102_);
    crate::leanh::lean_dec(v___x_1100_);
    v___x_1104_ = l_Std_Time_Duration_ofNanoseconds(v___x_1103_);
    crate::leanh::lean_dec(v___x_1103_);
    return v___x_1104_;
}
pub unsafe fn l_Std_Time_Timestamp_subDays___boxed(
    mut v_t_1105_: *mut crate::leanh::LeanObject,
    mut v_d_1106_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1107_ = l_Std_Time_Timestamp_subDays(v_t_1105_, v_d_1106_);
    crate::leanh::lean_dec(v_d_1106_);
    crate::leanh::lean_dec_ref(v_t_1105_);
    return v_res_1107_;
}
pub unsafe fn l_Std_Time_Timestamp_addWeeks(
    mut v_t_1108_: *mut crate::leanh::LeanObject,
    mut v_d_1109_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_second_1110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_second_1110_ = crate::leanh::lean_ctor_get(v_t_1108_, 0);
    v_nano_1111_ = crate::leanh::lean_ctor_get(v_t_1108_, 1);
    v___x_1112_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp_repr___redArg___closed__7_once),
        _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__7,
    );
    v___x_1113_ = lean_int_mul(v_d_1109_, v___x_1112_);
    v___x_1114_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toDaysSinceUnixEpoch___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toDaysSinceUnixEpoch___closed__0_once),
        _init_l_Std_Time_Timestamp_toDaysSinceUnixEpoch___closed__0,
    );
    v___x_1115_ = lean_int_mul(v___x_1113_, v___x_1114_);
    crate::leanh::lean_dec(v___x_1113_);
    v___x_1116_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp_repr___redArg___closed__14),
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp_repr___redArg___closed__14_once),
        _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__14,
    );
    v___x_1117_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once),
        _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2,
    );
    v___x_1118_ = lean_int_mul(v_second_1110_, v___x_1117_);
    v___x_1119_ = lean_int_add(v___x_1118_, v_nano_1111_);
    crate::leanh::lean_dec(v___x_1118_);
    v___x_1120_ = lean_int_mul(v___x_1115_, v___x_1117_);
    crate::leanh::lean_dec(v___x_1115_);
    v___x_1121_ = lean_int_add(v___x_1120_, v___x_1116_);
    crate::leanh::lean_dec(v___x_1120_);
    v___x_1122_ = lean_int_add(v___x_1119_, v___x_1121_);
    crate::leanh::lean_dec(v___x_1121_);
    crate::leanh::lean_dec(v___x_1119_);
    v___x_1123_ = l_Std_Time_Duration_ofNanoseconds(v___x_1122_);
    crate::leanh::lean_dec(v___x_1122_);
    return v___x_1123_;
}
pub unsafe fn l_Std_Time_Timestamp_addWeeks___boxed(
    mut v_t_1124_: *mut crate::leanh::LeanObject,
    mut v_d_1125_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1126_ = l_Std_Time_Timestamp_addWeeks(v_t_1124_, v_d_1125_);
    crate::leanh::lean_dec(v_d_1125_);
    crate::leanh::lean_dec_ref(v_t_1124_);
    return v_res_1126_;
}
pub unsafe fn l_Std_Time_Timestamp_subWeeks(
    mut v_t_1127_: *mut crate::leanh::LeanObject,
    mut v_d_1128_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_second_1129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_second_1129_ = crate::leanh::lean_ctor_get(v_t_1127_, 0);
    v_nano_1130_ = crate::leanh::lean_ctor_get(v_t_1127_, 1);
    v___x_1131_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp_repr___redArg___closed__7_once),
        _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__7,
    );
    v___x_1132_ = lean_int_mul(v_d_1128_, v___x_1131_);
    v___x_1133_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toDaysSinceUnixEpoch___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toDaysSinceUnixEpoch___closed__0_once),
        _init_l_Std_Time_Timestamp_toDaysSinceUnixEpoch___closed__0,
    );
    v___x_1134_ = lean_int_mul(v___x_1132_, v___x_1133_);
    crate::leanh::lean_dec(v___x_1132_);
    v___x_1135_ = lean_int_neg(v___x_1134_);
    crate::leanh::lean_dec(v___x_1134_);
    v___x_1136_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_subSeconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_subSeconds___closed__0_once),
        _init_l_Std_Time_Timestamp_subSeconds___closed__0,
    );
    v___x_1137_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once),
        _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2,
    );
    v___x_1138_ = lean_int_mul(v_second_1129_, v___x_1137_);
    v___x_1139_ = lean_int_add(v___x_1138_, v_nano_1130_);
    crate::leanh::lean_dec(v___x_1138_);
    v___x_1140_ = lean_int_mul(v___x_1135_, v___x_1137_);
    crate::leanh::lean_dec(v___x_1135_);
    v___x_1141_ = lean_int_add(v___x_1140_, v___x_1136_);
    crate::leanh::lean_dec(v___x_1140_);
    v___x_1142_ = lean_int_add(v___x_1139_, v___x_1141_);
    crate::leanh::lean_dec(v___x_1141_);
    crate::leanh::lean_dec(v___x_1139_);
    v___x_1143_ = l_Std_Time_Duration_ofNanoseconds(v___x_1142_);
    crate::leanh::lean_dec(v___x_1142_);
    return v___x_1143_;
}
pub unsafe fn l_Std_Time_Timestamp_subWeeks___boxed(
    mut v_t_1144_: *mut crate::leanh::LeanObject,
    mut v_d_1145_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1146_ = l_Std_Time_Timestamp_subWeeks(v_t_1144_, v_d_1145_);
    crate::leanh::lean_dec(v_d_1145_);
    crate::leanh::lean_dec_ref(v_t_1144_);
    return v_res_1146_;
}
pub unsafe fn l_Std_Time_Timestamp_addDuration(
    mut v_t_1147_: *mut crate::leanh::LeanObject,
    mut v_d_1148_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_second_1149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_1151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_second_1149_ = crate::leanh::lean_ctor_get(v_t_1147_, 0);
    v_nano_1150_ = crate::leanh::lean_ctor_get(v_t_1147_, 1);
    v_second_1151_ = crate::leanh::lean_ctor_get(v_d_1148_, 0);
    v_nano_1152_ = crate::leanh::lean_ctor_get(v_d_1148_, 1);
    v___x_1153_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once),
        _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2,
    );
    v___x_1154_ = lean_int_mul(v_second_1149_, v___x_1153_);
    v___x_1155_ = lean_int_add(v___x_1154_, v_nano_1150_);
    crate::leanh::lean_dec(v___x_1154_);
    v___x_1156_ = lean_int_mul(v_second_1151_, v___x_1153_);
    v___x_1157_ = lean_int_add(v___x_1156_, v_nano_1152_);
    crate::leanh::lean_dec(v___x_1156_);
    v___x_1158_ = lean_int_add(v___x_1155_, v___x_1157_);
    crate::leanh::lean_dec(v___x_1157_);
    crate::leanh::lean_dec(v___x_1155_);
    v___x_1159_ = l_Std_Time_Duration_ofNanoseconds(v___x_1158_);
    crate::leanh::lean_dec(v___x_1158_);
    return v___x_1159_;
}
pub unsafe fn l_Std_Time_Timestamp_addDuration___boxed(
    mut v_t_1160_: *mut crate::leanh::LeanObject,
    mut v_d_1161_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1162_ = l_Std_Time_Timestamp_addDuration(v_t_1160_, v_d_1161_);
    crate::leanh::lean_dec_ref(v_d_1161_);
    crate::leanh::lean_dec_ref(v_t_1160_);
    return v_res_1162_;
}
pub unsafe fn l_Std_Time_Timestamp_subDuration(
    mut v_t_1163_: *mut crate::leanh::LeanObject,
    mut v_d_1164_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_second_1165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_1167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_second_1165_ = crate::leanh::lean_ctor_get(v_d_1164_, 0);
    v_nano_1166_ = crate::leanh::lean_ctor_get(v_d_1164_, 1);
    v_second_1167_ = crate::leanh::lean_ctor_get(v_t_1163_, 0);
    v_nano_1168_ = crate::leanh::lean_ctor_get(v_t_1163_, 1);
    v___x_1169_ = lean_int_neg(v_second_1165_);
    v___x_1170_ = lean_int_neg(v_nano_1166_);
    v___x_1171_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once),
        _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2,
    );
    v___x_1172_ = lean_int_mul(v_second_1167_, v___x_1171_);
    v___x_1173_ = lean_int_add(v___x_1172_, v_nano_1168_);
    crate::leanh::lean_dec(v___x_1172_);
    v___x_1174_ = lean_int_mul(v___x_1169_, v___x_1171_);
    crate::leanh::lean_dec(v___x_1169_);
    v___x_1175_ = lean_int_add(v___x_1174_, v___x_1170_);
    crate::leanh::lean_dec(v___x_1170_);
    crate::leanh::lean_dec(v___x_1174_);
    v___x_1176_ = lean_int_add(v___x_1173_, v___x_1175_);
    crate::leanh::lean_dec(v___x_1175_);
    crate::leanh::lean_dec(v___x_1173_);
    v___x_1177_ = l_Std_Time_Duration_ofNanoseconds(v___x_1176_);
    crate::leanh::lean_dec(v___x_1176_);
    return v___x_1177_;
}
pub unsafe fn l_Std_Time_Timestamp_subDuration___boxed(
    mut v_t_1178_: *mut crate::leanh::LeanObject,
    mut v_d_1179_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1180_ = l_Std_Time_Timestamp_subDuration(v_t_1178_, v_d_1179_);
    crate::leanh::lean_dec_ref(v_d_1179_);
    crate::leanh::lean_dec_ref(v_t_1178_);
    return v_res_1180_;
}
pub unsafe fn l_Std_Time_Timestamp_instHSubDuration__1___lam__0(
    mut v_x_1213_: *mut crate::leanh::LeanObject,
    mut v_y_1214_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_second_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_1217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_second_1215_ = crate::leanh::lean_ctor_get(v_y_1214_, 0);
    v_nano_1216_ = crate::leanh::lean_ctor_get(v_y_1214_, 1);
    v_second_1217_ = crate::leanh::lean_ctor_get(v_x_1213_, 0);
    v_nano_1218_ = crate::leanh::lean_ctor_get(v_x_1213_, 1);
    v___x_1219_ = lean_int_neg(v_second_1215_);
    v___x_1220_ = lean_int_neg(v_nano_1216_);
    v___x_1221_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once),
        _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2,
    );
    v___x_1222_ = lean_int_mul(v_second_1217_, v___x_1221_);
    v___x_1223_ = lean_int_add(v___x_1222_, v_nano_1218_);
    crate::leanh::lean_dec(v___x_1222_);
    v___x_1224_ = lean_int_mul(v___x_1219_, v___x_1221_);
    crate::leanh::lean_dec(v___x_1219_);
    v___x_1225_ = lean_int_add(v___x_1224_, v___x_1220_);
    crate::leanh::lean_dec(v___x_1220_);
    crate::leanh::lean_dec(v___x_1224_);
    v___x_1226_ = lean_int_add(v___x_1223_, v___x_1225_);
    crate::leanh::lean_dec(v___x_1225_);
    crate::leanh::lean_dec(v___x_1223_);
    v___x_1227_ = l_Std_Time_Duration_ofNanoseconds(v___x_1226_);
    crate::leanh::lean_dec(v___x_1226_);
    return v___x_1227_;
}
pub unsafe fn l_Std_Time_Timestamp_instHSubDuration__1___lam__0___boxed(
    mut v_x_1228_: *mut crate::leanh::LeanObject,
    mut v_y_1229_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1230_ = l_Std_Time_Timestamp_instHSubDuration__1___lam__0(v_x_1228_, v_y_1229_);
    crate::leanh::lean_dec_ref(v_y_1229_);
    crate::leanh::lean_dec_ref(v_x_1228_);
    return v_res_1230_;
}
pub unsafe fn l_Std_Time_Timestamp_instOfNat(
    mut v_n_1233_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1234_ = lean_nat_to_int(v_n_1233_);
    v___x_1235_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp_repr___redArg___closed__14),
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp_repr___redArg___closed__14_once),
        _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__14,
    );
    v___x_1236_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1236_, 0, v___x_1234_);
    crate::leanh::lean_ctor_set(v___x_1236_, 1, v___x_1235_);
    return v___x_1236_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Time_DateTime_Timestamp(
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
    l_Std_Time_instInhabitedTimestamp_default = _init_l_Std_Time_instInhabitedTimestamp_default();
    crate::leanh::lean_mark_persistent(l_Std_Time_instInhabitedTimestamp_default);
    l_Std_Time_instInhabitedTimestamp = _init_l_Std_Time_instInhabitedTimestamp();
    crate::leanh::lean_mark_persistent(l_Std_Time_instInhabitedTimestamp);
    l_Std_Time_instLETimestamp = _init_l_Std_Time_instLETimestamp();
    crate::leanh::lean_mark_persistent(l_Std_Time_instLETimestamp);
    l_Std_Time_instLTTimestamp = _init_l_Std_Time_instLTTimestamp();
    crate::leanh::lean_mark_persistent(l_Std_Time_instLTTimestamp);
    l_Std_Time_instOrdTimestamp = _init_l_Std_Time_instOrdTimestamp();
    crate::leanh::lean_mark_persistent(l_Std_Time_instOrdTimestamp);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Time_DateTime_Timestamp(
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
pub unsafe fn initialize_Std_Time_DateTime_Timestamp(builtin: u8) -> *mut crate::leanh::LeanObject {
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
    res = runtime_initialize_Std_Time_DateTime_Timestamp(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Time_DateTime_Timestamp(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Time_DateTime_Timestamp(builtin);
}
