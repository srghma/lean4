// Lean compiler output
// Module: Std.Time.DateTime.Timestamp
// Imports: Init.System.IO Std.Time.Duration
use crate::ffi::{
    lean_get_current_time, lean_int_add, lean_int_dec_eq, lean_int_dec_lt, lean_int_div,
    lean_int_mul, lean_int_neg, lean_nat_to_int, lean_string_append, lean_string_length,
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
pub static l_Std_Time_instReprTimestamp_repr___redArg___closed__0_value:
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
static mut l_Std_Time_instReprTimestamp_repr___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprTimestamp_repr___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instReprTimestamp_repr___redArg___closed__1_value:
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
static mut l_Std_Time_instReprTimestamp_repr___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprTimestamp_repr___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instReprTimestamp_repr___redArg___closed__2_value:
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
        core::ptr::addr_of!(l_Std_Time_instReprTimestamp_repr___redArg___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_instReprTimestamp_repr___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprTimestamp_repr___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instReprTimestamp_repr___redArg___closed__3_value:
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
        core::ptr::addr_of!(l_Std_Time_instReprTimestamp_repr___redArg___closed__2_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_instReprTimestamp_repr___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprTimestamp_repr___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instReprTimestamp_repr___redArg___closed__4_value:
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
static mut l_Std_Time_instReprTimestamp_repr___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprTimestamp_repr___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instReprTimestamp_repr___redArg___closed__5_value:
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
        core::ptr::addr_of!(l_Std_Time_instReprTimestamp_repr___redArg___closed__4_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_instReprTimestamp_repr___redArg___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprTimestamp_repr___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instReprTimestamp_repr___redArg___closed__6_value:
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
        core::ptr::addr_of!(l_Std_Time_instReprTimestamp_repr___redArg___closed__3_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_instReprTimestamp_repr___redArg___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_instReprTimestamp_repr___redArg___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprTimestamp_repr___redArg___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_instReprTimestamp_repr___redArg___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instReprTimestamp_repr___redArg___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_instReprTimestamp_repr___redArg___closed__8_value:
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
static mut l_Std_Time_instReprTimestamp_repr___redArg___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprTimestamp_repr___redArg___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instReprTimestamp_repr___redArg___closed__9_value:
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
static mut l_Std_Time_instReprTimestamp_repr___redArg___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprTimestamp_repr___redArg___closed__9_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_instReprTimestamp_repr___redArg___closed__10_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instReprTimestamp_repr___redArg___closed__10: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instReprTimestamp_repr___redArg___closed__11_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instReprTimestamp_repr___redArg___closed__11: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_instReprTimestamp_repr___redArg___closed__12_value:
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
        core::ptr::addr_of!(l_Std_Time_instReprTimestamp_repr___redArg___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_instReprTimestamp_repr___redArg___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprTimestamp_repr___redArg___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instReprTimestamp_repr___redArg___closed__13_value:
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
        core::ptr::addr_of!(l_Std_Time_instReprTimestamp_repr___redArg___closed__9_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_instReprTimestamp_repr___redArg___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprTimestamp_repr___redArg___closed__13_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_instReprTimestamp_repr___redArg___closed__14_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instReprTimestamp_repr___redArg___closed__14: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_instReprTimestamp_repr___redArg___closed__15_value:
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
static mut l_Std_Time_instReprTimestamp_repr___redArg___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprTimestamp_repr___redArg___closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instReprTimestamp_repr___redArg___closed__16_value:
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
static mut l_Std_Time_instReprTimestamp_repr___redArg___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprTimestamp_repr___redArg___closed__16_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instReprTimestamp_repr___redArg___closed__17_value:
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
static mut l_Std_Time_instReprTimestamp_repr___redArg___closed__17: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprTimestamp_repr___redArg___closed__17_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instReprTimestamp___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instReprTimestamp_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instReprTimestamp___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprTimestamp___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instReprTimestamp: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprTimestamp___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_instInhabitedTimestamp_default___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedTimestamp_default___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_instInhabitedTimestamp_default: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_instInhabitedTimestamp: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_instLETimestamp: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Std_Time_instLTTimestamp: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Time_instToStringTimestamp___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instToStringTimestamp___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instToStringTimestamp___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instToStringTimestamp___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instToStringTimestamp: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instToStringTimestamp___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instReprTimestamp__1___lam__0___closed__0_value:
    leanh::LeanStringObject<25> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Time_instReprTimestamp__1___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprTimestamp__1___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instReprTimestamp__1___lam__0___closed__1_value:
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
        core::ptr::addr_of!(l_Std_Time_instReprTimestamp__1___lam__0___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_instReprTimestamp__1___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprTimestamp__1___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instReprTimestamp__1___lam__0___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_instReprTimestamp__1___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instReprTimestamp__1___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instReprTimestamp__1___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprTimestamp__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_instReprTimestamp__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprTimestamp__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_instOrdTimestamp___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instOrdTimestamp___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instOrdTimestamp___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdTimestamp___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_instOrdTimestamp___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instOrdTimestamp___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_instOrdTimestamp: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Timestamp_toMinutesSinceUnixEpoch___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Timestamp_toMinutesSinceUnixEpoch___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Timestamp_toDaysSinceUnixEpoch___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Timestamp_toDaysSinceUnixEpoch___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Timestamp_subSeconds___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Timestamp_subSeconds___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Timestamp_addHours___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Timestamp_addHours___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_Timestamp_instHAddDuration___closed__0_value:
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
    m_fun: l_Std_Time_Timestamp_addDuration___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_Timestamp_instHAddDuration___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Timestamp_instHAddDuration___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_Timestamp_instHAddDuration: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Timestamp_instHAddDuration___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Timestamp_instHSubDuration___closed__0_value:
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
    m_fun: l_Std_Time_Timestamp_subDuration___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_Timestamp_instHSubDuration___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Timestamp_instHSubDuration___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_Timestamp_instHSubDuration: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Timestamp_instHSubDuration___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Timestamp_instHAddOffset___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_Timestamp_addDays___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_Timestamp_instHAddOffset___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Timestamp_instHAddOffset___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_Timestamp_instHAddOffset: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Timestamp_instHAddOffset___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Timestamp_instHSubOffset___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_Timestamp_subDays___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_Timestamp_instHSubOffset___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Timestamp_instHSubOffset___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_Timestamp_instHSubOffset: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Timestamp_instHSubOffset___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Timestamp_instHAddOffset__1___closed__0_value:
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
    m_fun: l_Std_Time_Timestamp_addWeeks___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_Timestamp_instHAddOffset__1___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Timestamp_instHAddOffset__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_Timestamp_instHAddOffset__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Timestamp_instHAddOffset__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Timestamp_instHSubOffset__1___closed__0_value:
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
    m_fun: l_Std_Time_Timestamp_subWeeks___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_Timestamp_instHSubOffset__1___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Timestamp_instHSubOffset__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_Timestamp_instHSubOffset__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Timestamp_instHSubOffset__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Timestamp_instHAddOffset__2___closed__0_value:
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
    m_fun: l_Std_Time_Timestamp_addHours___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_Timestamp_instHAddOffset__2___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Timestamp_instHAddOffset__2___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_Timestamp_instHAddOffset__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Timestamp_instHAddOffset__2___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Timestamp_instHSubOffset__2___closed__0_value:
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
    m_fun: l_Std_Time_Timestamp_subHours___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_Timestamp_instHSubOffset__2___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Timestamp_instHSubOffset__2___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_Timestamp_instHSubOffset__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Timestamp_instHSubOffset__2___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Timestamp_instHAddOffset__3___closed__0_value:
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
    m_fun: l_Std_Time_Timestamp_addMinutes___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_Timestamp_instHAddOffset__3___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Timestamp_instHAddOffset__3___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_Timestamp_instHAddOffset__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Timestamp_instHAddOffset__3___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Timestamp_instHSubOffset__3___closed__0_value:
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
    m_fun: l_Std_Time_Timestamp_subMinutes___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_Timestamp_instHSubOffset__3___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Timestamp_instHSubOffset__3___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_Timestamp_instHSubOffset__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Timestamp_instHSubOffset__3___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Timestamp_instHAddOffset__4___closed__0_value:
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
    m_fun: l_Std_Time_Timestamp_addSeconds___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_Timestamp_instHAddOffset__4___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Timestamp_instHAddOffset__4___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_Timestamp_instHAddOffset__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Timestamp_instHAddOffset__4___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Timestamp_instHSubOffset__4___closed__0_value:
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
    m_fun: l_Std_Time_Timestamp_subSeconds___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_Timestamp_instHSubOffset__4___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Timestamp_instHSubOffset__4___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_Timestamp_instHSubOffset__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Timestamp_instHSubOffset__4___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Timestamp_instHAddOffset__5___closed__0_value:
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
    m_fun: l_Std_Time_Timestamp_addMilliseconds___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_Timestamp_instHAddOffset__5___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Timestamp_instHAddOffset__5___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_Timestamp_instHAddOffset__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Timestamp_instHAddOffset__5___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Timestamp_instHSubOffset__5___closed__0_value:
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
    m_fun: l_Std_Time_Timestamp_subMilliseconds___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_Timestamp_instHSubOffset__5___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Timestamp_instHSubOffset__5___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_Timestamp_instHSubOffset__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Timestamp_instHSubOffset__5___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Timestamp_instHAddOffset__6___closed__0_value:
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
    m_fun: l_Std_Time_Timestamp_addNanoseconds___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_Timestamp_instHAddOffset__6___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Timestamp_instHAddOffset__6___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_Timestamp_instHAddOffset__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Timestamp_instHAddOffset__6___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Timestamp_instHSubOffset__6___closed__0_value:
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
    m_fun: l_Std_Time_Timestamp_subNanoseconds___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_Timestamp_instHSubOffset__6___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Timestamp_instHSubOffset__6___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_Timestamp_instHSubOffset__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Timestamp_instHSubOffset__6___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Timestamp_instHSubDuration__1___closed__0_value:
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
    m_fun: l_Std_Time_Timestamp_instHSubDuration__1___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_Timestamp_instHSubDuration__1___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Timestamp_instHSubDuration__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_Timestamp_instHSubDuration__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Timestamp_instHSubDuration__1___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Nat_cast___at___00Std_Time_instReprTimestamp_repr_spec__0(
    mut v_a_619_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_620_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_620_ = lean_nat_to_int(v_a_619_);
    return v___x_620_;
}
pub unsafe fn _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_635_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_634_ = leanh::lean_unsigned_to_nat(7);
    v___x_635_ = lean_nat_to_int(v___x_634_);
    return v___x_635_;
}
pub unsafe fn _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_639_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_638_ = l_Std_Time_instReprTimestamp_repr___redArg___closed__0;
    v___x_639_ = lean_string_length(v___x_638_);
    return v___x_639_;
}
pub unsafe fn _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_641_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_640_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp_repr___redArg___closed__10),
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp_repr___redArg___closed__10_once),
        _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__10,
    );
    v___x_641_ = lean_nat_to_int(v___x_640_);
    return v___x_641_;
}
pub unsafe fn _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__14()
-> *mut leanh::LeanObject {
    let mut v___x_646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_647_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_646_ = leanh::lean_unsigned_to_nat(0);
    v___x_647_ = lean_nat_to_int(v___x_646_);
    return v___x_647_;
}
pub unsafe fn l_Std_Time_instReprTimestamp_repr___redArg(
    mut v_x_651_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_second_652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_656_: u8 = 0;
    let mut v___x_657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_669_: u8 = 0;
    let mut v___x_670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_687_: u8 = 0;
    let mut v___x_688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_695_: u8 = 0;
    let mut v___x_696_: u8 = 0;
    let mut v___x_697_: u8 = 0;
    let mut v___x_698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_706_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_second_652_ = leanh::lean_ctor_get(v_x_651_, 0);
                v_nano_653_ = leanh::lean_ctor_get(v_x_651_, 1);
                v_isSharedCheck_706_ = (!leanh::lean_is_exclusive(v_x_651_)) as u8;
                if v_isSharedCheck_706_ == 0 {
                    v___x_655_ = v_x_651_;
                    v_isShared_656_ = v_isSharedCheck_706_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_nano_653_);
                    leanh::lean_inc(v_second_652_);
                    leanh::lean_dec(v_x_651_);
                    v___x_655_ = leanh::lean_box(0);
                    v_isShared_656_ = v_isSharedCheck_706_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_657_ = l_Std_Time_instReprTimestamp_repr___redArg___closed__6;
                v___x_658_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp_repr___redArg___closed__7),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprTimestamp_repr___redArg___closed__7_once
                    ),
                    _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__7,
                );
                v___x_694_ = leanh::lean_obj_once(
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
                            leanh::lean_inc(v_nano_653_);
                            v_fst_681_ = v___x_698_;
                            v_fst_682_ = v_second_652_;
                            v_snd_683_ = v_nano_653_;
                            state = 4;
                            continue;
                        } else {
                            v___x_699_ = l_Std_Time_instReprTimestamp_repr___redArg___closed__17;
                            v___x_700_ = lean_int_neg(v_second_652_);
                            leanh::lean_dec(v_second_652_);
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
                        leanh::lean_dec(v_second_652_);
                        v___x_704_ = lean_int_neg(v_nano_653_);
                        v_fst_681_ = v___x_702_;
                        v_fst_682_ = v___x_703_;
                        v_snd_683_ = v___x_704_;
                        state = 4;
                        continue;
                    }
                } else {
                    v___x_705_ = l_Std_Time_instReprTimestamp_repr___redArg___closed__16;
                    leanh::lean_inc(v_nano_653_);
                    v_fst_681_ = v___x_705_;
                    v_fst_682_ = v_second_652_;
                    v_snd_683_ = v_nano_653_;
                    state = 4;
                    continue;
                }
            }
            2 => {
                v___x_662_ = lean_string_append(v___y_660_, v___y_661_);
                leanh::lean_dec_ref(v___y_661_);
                v___x_663_ = l_Std_Time_instReprTimestamp_repr___redArg___closed__8;
                v___x_664_ = lean_string_append(v___x_662_, v___x_663_);
                v___x_665_ = l_String_quote(v___x_664_);
                v___x_666_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_666_, 0, v___x_665_);
                if v_isShared_656_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_655_, 4);
                    leanh::lean_ctor_set(v___x_655_, 1, v___x_666_);
                    leanh::lean_ctor_set(v___x_655_, 0, v___x_658_);
                    v___x_668_ = v___x_655_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_679_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_679_, 0, v___x_658_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_679_, 1, v___x_666_);
                    v___x_668_ = v_reuseFailAlloc_679_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_669_ = 0;
                v___x_670_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_670_, 0, v___x_668_);
                leanh::lean_ctor_set_uint8(
                    v___x_670_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_669_,
                );
                v___x_671_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_671_, 0, v___x_657_);
                leanh::lean_ctor_set(v___x_671_, 1, v___x_670_);
                v___x_672_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprTimestamp_repr___redArg___closed__11
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprTimestamp_repr___redArg___closed__11_once
                    ),
                    _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__11,
                );
                v___x_673_ = l_Std_Time_instReprTimestamp_repr___redArg___closed__12;
                v___x_674_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_674_, 0, v___x_673_);
                leanh::lean_ctor_set(v___x_674_, 1, v___x_671_);
                v___x_675_ = l_Std_Time_instReprTimestamp_repr___redArg___closed__13;
                v___x_676_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_676_, 0, v___x_674_);
                leanh::lean_ctor_set(v___x_676_, 1, v___x_675_);
                v___x_677_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_677_, 0, v___x_672_);
                leanh::lean_ctor_set(v___x_677_, 1, v___x_676_);
                v___x_678_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_678_, 0, v___x_677_);
                leanh::lean_ctor_set_uint8(
                    v___x_678_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_669_,
                );
                return v___x_678_;
            }
            4 => {
                v___x_684_ = l_Int_repr(v_fst_682_);
                leanh::lean_dec(v_fst_682_);
                leanh::lean_inc_ref(v_fst_681_);
                v___x_685_ = lean_string_append(v_fst_681_, v___x_684_);
                leanh::lean_dec_ref(v___x_684_);
                v___x_686_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprTimestamp_repr___redArg___closed__14
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprTimestamp_repr___redArg___closed__14_once
                    ),
                    _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__14,
                );
                v___x_687_ = lean_int_dec_eq(v_nano_653_, v___x_686_);
                leanh::lean_dec(v_nano_653_);
                if v___x_687_ == 0 {
                    v___x_688_ = l_Std_Time_instReprTimestamp_repr___redArg___closed__15;
                    v___x_689_ = leanh::lean_unsigned_to_nat(9);
                    v___x_690_ = l_Int_repr(v_snd_683_);
                    leanh::lean_dec(v_snd_683_);
                    v___x_691_ = l_Std_Time_instToStringDuration_leftPad(v___x_689_, v___x_690_);
                    leanh::lean_dec_ref(v___x_690_);
                    v___x_692_ = lean_string_append(v___x_688_, v___x_691_);
                    leanh::lean_dec_ref(v___x_691_);
                    v___y_660_ = v___x_685_;
                    v___y_661_ = v___x_692_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_snd_683_);
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
    mut v_x_707_: *mut leanh::LeanObject,
    mut v_prec_708_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_709_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_709_ = l_Std_Time_instReprTimestamp_repr___redArg(v_x_707_);
    return v___x_709_;
}
pub unsafe fn l_Std_Time_instReprTimestamp_repr___boxed(
    mut v_x_710_: *mut leanh::LeanObject,
    mut v_prec_711_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_712_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_712_ = l_Std_Time_instReprTimestamp_repr(v_x_710_, v_prec_711_);
    leanh::lean_dec(v_prec_711_);
    return v_res_712_;
}
pub unsafe fn l_Std_Time_instDecidableEqTimestamp_decEq(
    mut v_x_715_: *mut leanh::LeanObject,
    mut v_x_716_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_717_: u8 = 0;
    v___x_717_ = l_Std_Time_instDecidableEqDuration_decEq(v_x_715_, v_x_716_);
    return v___x_717_;
}
pub unsafe fn l_Std_Time_instDecidableEqTimestamp_decEq___boxed(
    mut v_x_718_: *mut leanh::LeanObject,
    mut v_x_719_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_720_: u8 = 0;
    let mut v_r_721_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_720_ = l_Std_Time_instDecidableEqTimestamp_decEq(v_x_718_, v_x_719_);
    leanh::lean_dec_ref(v_x_719_);
    leanh::lean_dec_ref(v_x_718_);
    v_r_721_ = leanh::lean_box((v_res_720_) as usize);
    return v_r_721_;
}
pub unsafe fn l_Std_Time_instDecidableEqTimestamp(
    mut v_x_722_: *mut leanh::LeanObject,
    mut v_x_723_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_724_: u8 = 0;
    v___x_724_ = l_Std_Time_instDecidableEqDuration_decEq(v_x_722_, v_x_723_);
    return v___x_724_;
}
pub unsafe fn l_Std_Time_instDecidableEqTimestamp___boxed(
    mut v_x_725_: *mut leanh::LeanObject,
    mut v_x_726_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_727_: u8 = 0;
    let mut v_r_728_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_727_ = l_Std_Time_instDecidableEqTimestamp(v_x_725_, v_x_726_);
    leanh::lean_dec_ref(v_x_726_);
    leanh::lean_dec_ref(v_x_725_);
    v_r_728_ = leanh::lean_box((v_res_727_) as usize);
    return v_r_728_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedTimestamp_default___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_730_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_729_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp_repr___redArg___closed__14),
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp_repr___redArg___closed__14_once),
        _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__14,
    );
    v___x_730_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_730_, 0, v___x_729_);
    leanh::lean_ctor_set(v___x_730_, 1, v___x_729_);
    return v___x_730_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedTimestamp_default() -> *mut leanh::LeanObject {
    let mut v___x_731_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_731_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedTimestamp_default___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedTimestamp_default___closed__0_once),
        _init_l_Std_Time_instInhabitedTimestamp_default___closed__0,
    );
    return v___x_731_;
}
pub unsafe fn l_Nat_cast___at___00Std_Time_instInhabitedTimestamp_default_spec__0(
    mut v_a_732_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_734_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_733_ = lean_nat_to_int(v_a_732_);
    v___x_734_ = l_Rat_ofInt(v___x_733_);
    return v___x_734_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedTimestamp() -> *mut leanh::LeanObject {
    let mut v___x_735_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_735_ = l_Std_Time_instInhabitedTimestamp_default;
    return v___x_735_;
}
pub unsafe fn _init_l_Std_Time_instLETimestamp() -> *mut leanh::LeanObject {
    let mut v___x_736_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_736_ = leanh::lean_box(0);
    return v___x_736_;
}
pub unsafe fn l_Std_Time_instDecidableLeTimestamp(
    mut v_x_737_: *mut leanh::LeanObject,
    mut v_y_738_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_739_: u8 = 0;
    v___x_739_ = l_Std_Time_Duration_instDecidableLe(v_x_737_, v_y_738_);
    return v___x_739_;
}
pub unsafe fn l_Std_Time_instDecidableLeTimestamp___boxed(
    mut v_x_740_: *mut leanh::LeanObject,
    mut v_y_741_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_742_: u8 = 0;
    let mut v_r_743_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_742_ = l_Std_Time_instDecidableLeTimestamp(v_x_740_, v_y_741_);
    leanh::lean_dec_ref(v_y_741_);
    leanh::lean_dec_ref(v_x_740_);
    v_r_743_ = leanh::lean_box((v_res_742_) as usize);
    return v_r_743_;
}
pub unsafe fn _init_l_Std_Time_instLTTimestamp() -> *mut leanh::LeanObject {
    let mut v___x_744_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_744_ = leanh::lean_box(0);
    return v___x_744_;
}
pub unsafe fn l_Std_Time_instDecidableLtTimestamp(
    mut v_x_745_: *mut leanh::LeanObject,
    mut v_y_746_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_747_: u8 = 0;
    v___x_747_ = l_Std_Time_Duration_instDecidableLt(v_x_745_, v_y_746_);
    return v___x_747_;
}
pub unsafe fn l_Std_Time_instDecidableLtTimestamp___boxed(
    mut v_x_748_: *mut leanh::LeanObject,
    mut v_y_749_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_750_: u8 = 0;
    let mut v_r_751_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_750_ = l_Std_Time_instDecidableLtTimestamp(v_x_748_, v_y_749_);
    leanh::lean_dec_ref(v_y_749_);
    leanh::lean_dec_ref(v_x_748_);
    v_r_751_ = leanh::lean_box((v_res_750_) as usize);
    return v_r_751_;
}
pub unsafe fn l_Std_Time_instToStringTimestamp___lam__0(
    mut v_s_752_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_second_753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_754_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_second_753_ = leanh::lean_ctor_get(v_s_752_, 0);
    v___x_754_ = l_Int_repr(v_second_753_);
    return v___x_754_;
}
pub unsafe fn l_Std_Time_instToStringTimestamp___lam__0___boxed(
    mut v_s_755_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_756_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_756_ = l_Std_Time_instToStringTimestamp___lam__0(v_s_755_);
    leanh::lean_dec_ref(v_s_755_);
    return v_res_756_;
}
pub unsafe fn _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_763_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_762_ = leanh::lean_unsigned_to_nat(1000000000);
    v___x_763_ = lean_nat_to_int(v___x_762_);
    return v___x_763_;
}
pub unsafe fn l_Std_Time_instReprTimestamp__1___lam__0(
    mut v_s_764_: *mut leanh::LeanObject,
    mut v___y_765_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_second_766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_770_: u8 = 0;
    let mut v___x_771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nanos_774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_781_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_second_766_ = leanh::lean_ctor_get(v_s_764_, 0);
                v_nano_767_ = leanh::lean_ctor_get(v_s_764_, 1);
                v_isSharedCheck_781_ = (!leanh::lean_is_exclusive(v_s_764_)) as u8;
                if v_isSharedCheck_781_ == 0 {
                    v___x_769_ = v_s_764_;
                    v_isShared_770_ = v_isSharedCheck_781_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_nano_767_);
                    leanh::lean_inc(v_second_766_);
                    leanh::lean_dec(v_s_764_);
                    v___x_769_ = leanh::lean_box(0);
                    v_isShared_770_ = v_isSharedCheck_781_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_771_ = l_Std_Time_instReprTimestamp__1___lam__0___closed__1;
                v___x_772_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once
                    ),
                    _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2,
                );
                v___x_773_ = lean_int_mul(v_second_766_, v___x_772_);
                leanh::lean_dec(v_second_766_);
                v_nanos_774_ = lean_int_add(v___x_773_, v_nano_767_);
                leanh::lean_dec(v_nano_767_);
                leanh::lean_dec(v___x_773_);
                v___x_775_ = leanh::lean_unsigned_to_nat(0);
                v___x_776_ =
                    l_Std_Time_Nanosecond_instReprOrdinal___lam__0(v_nanos_774_, v___x_775_);
                leanh::lean_dec(v_nanos_774_);
                if v_isShared_770_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_769_, 5);
                    leanh::lean_ctor_set(v___x_769_, 1, v___x_776_);
                    leanh::lean_ctor_set(v___x_769_, 0, v___x_771_);
                    v___x_778_ = v___x_769_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_780_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_780_, 0, v___x_771_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_780_, 1, v___x_776_);
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
    mut v_s_782_: *mut leanh::LeanObject,
    mut v___y_783_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_784_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_784_ = l_Std_Time_instReprTimestamp__1___lam__0(v_s_782_, v___y_783_);
    leanh::lean_dec(v___y_783_);
    return v_res_784_;
}
pub unsafe fn l_Std_Time_instOrdTimestamp___lam__0(
    mut v_x_787_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v_x_787_);
    return v_x_787_;
}
pub unsafe fn l_Std_Time_instOrdTimestamp___lam__0___boxed(
    mut v_x_788_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_789_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_789_ = l_Std_Time_instOrdTimestamp___lam__0(v_x_788_);
    leanh::lean_dec_ref(v_x_788_);
    return v_res_789_;
}
pub unsafe fn _init_l_Std_Time_instOrdTimestamp___closed__1() -> *mut leanh::LeanObject {
    let mut v___f_791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_793_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_791_ = l_Std_Time_instOrdTimestamp___closed__0;
    v___x_792_ = l_Std_Time_instOrdDuration;
    v___x_793_ =
        leanh::lean_alloc_closure(l_compareOn___boxed as *mut core::ffi::c_void, 6, 4);
    leanh::lean_closure_set(v___x_793_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_793_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_793_, 2, v___x_792_);
    leanh::lean_closure_set(v___x_793_, 3, v___f_791_);
    return v___x_793_;
}
pub unsafe fn _init_l_Std_Time_instOrdTimestamp() -> *mut leanh::LeanObject {
    let mut v___x_794_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_794_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instOrdTimestamp___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_instOrdTimestamp___closed__1_once),
        _init_l_Std_Time_instOrdTimestamp___closed__1,
    );
    return v___x_794_;
}
pub unsafe fn l_Std_Time_Timestamp_now___boxed(
    mut v_a_00___x40___internal___hyg_796_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_797_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_797_ = lean_get_current_time();
    return v_res_797_;
}
pub unsafe fn _init_l_Std_Time_Timestamp_toMinutesSinceUnixEpoch___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_799_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_798_ = leanh::lean_unsigned_to_nat(60);
    v___x_799_ = lean_nat_to_int(v___x_798_);
    return v___x_799_;
}
pub unsafe fn l_Std_Time_Timestamp_toMinutesSinceUnixEpoch(
    mut v_tm_800_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_second_801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_803_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_second_801_ = leanh::lean_ctor_get(v_tm_800_, 0);
    v___x_802_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toMinutesSinceUnixEpoch___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toMinutesSinceUnixEpoch___closed__0_once),
        _init_l_Std_Time_Timestamp_toMinutesSinceUnixEpoch___closed__0,
    );
    v___x_803_ = lean_int_div(v_second_801_, v___x_802_);
    return v___x_803_;
}
pub unsafe fn l_Std_Time_Timestamp_toMinutesSinceUnixEpoch___boxed(
    mut v_tm_804_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_805_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_805_ = l_Std_Time_Timestamp_toMinutesSinceUnixEpoch(v_tm_804_);
    leanh::lean_dec_ref(v_tm_804_);
    return v_res_805_;
}
pub unsafe fn _init_l_Std_Time_Timestamp_toDaysSinceUnixEpoch___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_807_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_806_ = leanh::lean_unsigned_to_nat(86400);
    v___x_807_ = lean_nat_to_int(v___x_806_);
    return v___x_807_;
}
pub unsafe fn l_Std_Time_Timestamp_toDaysSinceUnixEpoch(
    mut v_tm_808_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_second_809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_811_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_second_809_ = leanh::lean_ctor_get(v_tm_808_, 0);
    v___x_810_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toDaysSinceUnixEpoch___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toDaysSinceUnixEpoch___closed__0_once),
        _init_l_Std_Time_Timestamp_toDaysSinceUnixEpoch___closed__0,
    );
    v___x_811_ = lean_int_div(v_second_809_, v___x_810_);
    return v___x_811_;
}
pub unsafe fn l_Std_Time_Timestamp_toDaysSinceUnixEpoch___boxed(
    mut v_tm_812_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_813_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_813_ = l_Std_Time_Timestamp_toDaysSinceUnixEpoch(v_tm_812_);
    leanh::lean_dec_ref(v_tm_812_);
    return v_res_813_;
}
pub unsafe fn l_Std_Time_Timestamp_ofSecondsSinceUnixEpoch(
    mut v_secs_814_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_816_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_815_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp_repr___redArg___closed__14),
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp_repr___redArg___closed__14_once),
        _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__14,
    );
    v___x_816_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_816_, 0, v_secs_814_);
    leanh::lean_ctor_set(v___x_816_, 1, v___x_815_);
    return v___x_816_;
}
pub unsafe fn l_Std_Time_Timestamp_ofNanosecondsSinceUnixEpoch(
    mut v_nanos_817_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_818_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_818_ = l_Std_Time_Duration_ofNanoseconds(v_nanos_817_);
    return v___x_818_;
}
pub unsafe fn l_Std_Time_Timestamp_ofNanosecondsSinceUnixEpoch___boxed(
    mut v_nanos_819_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_820_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_820_ = l_Std_Time_Timestamp_ofNanosecondsSinceUnixEpoch(v_nanos_819_);
    leanh::lean_dec(v_nanos_819_);
    return v_res_820_;
}
pub unsafe fn l_Std_Time_Timestamp_ofDurationSinceUnixEpoch(
    mut v_duration_821_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v_duration_821_);
    return v_duration_821_;
}
pub unsafe fn l_Std_Time_Timestamp_ofDurationSinceUnixEpoch___boxed(
    mut v_duration_822_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_823_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_823_ = l_Std_Time_Timestamp_ofDurationSinceUnixEpoch(v_duration_822_);
    leanh::lean_dec_ref(v_duration_822_);
    return v_res_823_;
}
pub unsafe fn _init_l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_825_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_824_ = leanh::lean_unsigned_to_nat(1000000);
    v___x_825_ = lean_nat_to_int(v___x_824_);
    return v___x_825_;
}
pub unsafe fn l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch(
    mut v_milli_826_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_829_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_827_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0_once),
        _init_l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0,
    );
    v___x_828_ = lean_int_mul(v_milli_826_, v___x_827_);
    v___x_829_ = l_Std_Time_Duration_ofNanoseconds(v___x_828_);
    leanh::lean_dec(v___x_828_);
    return v___x_829_;
}
pub unsafe fn l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___boxed(
    mut v_milli_830_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_831_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_831_ = l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch(v_milli_830_);
    leanh::lean_dec(v_milli_830_);
    return v_res_831_;
}
pub unsafe fn l_Std_Time_Timestamp_toSecondsSinceUnixEpoch(
    mut v_t_832_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_second_833_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_second_833_ = leanh::lean_ctor_get(v_t_832_, 0);
    leanh::lean_inc(v_second_833_);
    return v_second_833_;
}
pub unsafe fn l_Std_Time_Timestamp_toSecondsSinceUnixEpoch___boxed(
    mut v_t_834_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_835_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_835_ = l_Std_Time_Timestamp_toSecondsSinceUnixEpoch(v_t_834_);
    leanh::lean_dec_ref(v_t_834_);
    return v_res_835_;
}
pub unsafe fn l_Std_Time_Timestamp_toNanosecondsSinceUnixEpoch(
    mut v_tm_836_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_second_837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nanos_841_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_second_837_ = leanh::lean_ctor_get(v_tm_836_, 0);
    v_nano_838_ = leanh::lean_ctor_get(v_tm_836_, 1);
    v___x_839_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once),
        _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2,
    );
    v___x_840_ = lean_int_mul(v_second_837_, v___x_839_);
    v_nanos_841_ = lean_int_add(v___x_840_, v_nano_838_);
    leanh::lean_dec(v___x_840_);
    return v_nanos_841_;
}
pub unsafe fn l_Std_Time_Timestamp_toNanosecondsSinceUnixEpoch___boxed(
    mut v_tm_842_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_843_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_843_ = l_Std_Time_Timestamp_toNanosecondsSinceUnixEpoch(v_tm_842_);
    leanh::lean_dec_ref(v_tm_842_);
    return v_res_843_;
}
pub unsafe fn l_Std_Time_Timestamp_toMillisecondsSinceUnixEpoch(
    mut v_tm_844_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_second_845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_851_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_second_845_ = leanh::lean_ctor_get(v_tm_844_, 0);
    v_nano_846_ = leanh::lean_ctor_get(v_tm_844_, 1);
    v___x_847_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once),
        _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2,
    );
    v___x_848_ = lean_int_mul(v_second_845_, v___x_847_);
    v___x_849_ = lean_int_add(v___x_848_, v_nano_846_);
    leanh::lean_dec(v___x_848_);
    v___x_850_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0_once),
        _init_l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0,
    );
    v___x_851_ = lean_int_div(v___x_849_, v___x_850_);
    leanh::lean_dec(v___x_849_);
    return v___x_851_;
}
pub unsafe fn l_Std_Time_Timestamp_toMillisecondsSinceUnixEpoch___boxed(
    mut v_tm_852_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_853_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_853_ = l_Std_Time_Timestamp_toMillisecondsSinceUnixEpoch(v_tm_852_);
    leanh::lean_dec_ref(v_tm_852_);
    return v_res_853_;
}
pub unsafe fn l_Std_Time_Timestamp_since(
    mut v_f_854_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_860_: u8 = 0;
    let mut v_second_861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_877_: u8 = 0;
    let mut v_a_878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_881_: u8 = 0;
    let mut v___x_883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_885_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_856_ = lean_get_current_time();
                if leanh::lean_obj_tag(v___x_856_) == 0 {
                    v_a_857_ = leanh::lean_ctor_get(v___x_856_, 0);
                    v_isSharedCheck_877_ = (!leanh::lean_is_exclusive(v___x_856_)) as u8;
                    if v_isSharedCheck_877_ == 0 {
                        v___x_859_ = v___x_856_;
                        v_isShared_860_ = v_isSharedCheck_877_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_857_);
                        leanh::lean_dec(v___x_856_);
                        v___x_859_ = leanh::lean_box(0);
                        v_isShared_860_ = v_isSharedCheck_877_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_878_ = leanh::lean_ctor_get(v___x_856_, 0);
                    v_isSharedCheck_885_ = (!leanh::lean_is_exclusive(v___x_856_)) as u8;
                    if v_isSharedCheck_885_ == 0 {
                        v___x_880_ = v___x_856_;
                        v_isShared_881_ = v_isSharedCheck_885_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_878_);
                        leanh::lean_dec(v___x_856_);
                        v___x_880_ = leanh::lean_box(0);
                        v_isShared_881_ = v_isSharedCheck_885_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_second_861_ = leanh::lean_ctor_get(v_f_854_, 0);
                v_nano_862_ = leanh::lean_ctor_get(v_f_854_, 1);
                v_second_863_ = leanh::lean_ctor_get(v_a_857_, 0);
                leanh::lean_inc(v_second_863_);
                v_nano_864_ = leanh::lean_ctor_get(v_a_857_, 1);
                leanh::lean_inc(v_nano_864_);
                leanh::lean_dec(v_a_857_);
                v___x_865_ = lean_int_neg(v_second_861_);
                v___x_866_ = lean_int_neg(v_nano_862_);
                v___x_867_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once
                    ),
                    _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2,
                );
                v___x_868_ = lean_int_mul(v_second_863_, v___x_867_);
                leanh::lean_dec(v_second_863_);
                v___x_869_ = lean_int_add(v___x_868_, v_nano_864_);
                leanh::lean_dec(v_nano_864_);
                leanh::lean_dec(v___x_868_);
                v___x_870_ = lean_int_mul(v___x_865_, v___x_867_);
                leanh::lean_dec(v___x_865_);
                v___x_871_ = lean_int_add(v___x_870_, v___x_866_);
                leanh::lean_dec(v___x_866_);
                leanh::lean_dec(v___x_870_);
                v___x_872_ = lean_int_add(v___x_869_, v___x_871_);
                leanh::lean_dec(v___x_871_);
                leanh::lean_dec(v___x_869_);
                v___x_873_ = l_Std_Time_Duration_ofNanoseconds(v___x_872_);
                leanh::lean_dec(v___x_872_);
                if v_isShared_860_ == 0 {
                    leanh::lean_ctor_set(v___x_859_, 0, v___x_873_);
                    v___x_875_ = v___x_859_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_876_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_876_, 0, v___x_873_);
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
                    v_reuseFailAlloc_884_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_884_, 0, v_a_878_);
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
    mut v_f_886_: *mut leanh::LeanObject,
    mut v_a_887_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_888_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_888_ = l_Std_Time_Timestamp_since(v_f_886_);
    leanh::lean_dec_ref(v_f_886_);
    return v_res_888_;
}
pub unsafe fn l_Std_Time_Timestamp_toDurationSinceUnixEpoch(
    mut v_tm_889_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v_tm_889_);
    return v_tm_889_;
}
pub unsafe fn l_Std_Time_Timestamp_toDurationSinceUnixEpoch___boxed(
    mut v_tm_890_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_891_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_891_ = l_Std_Time_Timestamp_toDurationSinceUnixEpoch(v_tm_890_);
    leanh::lean_dec_ref(v_tm_890_);
    return v_res_891_;
}
pub unsafe fn l_Std_Time_Timestamp_addMilliseconds(
    mut v_t_892_: *mut leanh::LeanObject,
    mut v_s_893_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_second_894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_907_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_second_894_ = leanh::lean_ctor_get(v_t_892_, 0);
    v_nano_895_ = leanh::lean_ctor_get(v_t_892_, 1);
    v___x_896_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0_once),
        _init_l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0,
    );
    v___x_897_ = lean_int_mul(v_s_893_, v___x_896_);
    v___x_898_ = l_Std_Time_Duration_ofNanoseconds(v___x_897_);
    leanh::lean_dec(v___x_897_);
    v_second_899_ = leanh::lean_ctor_get(v___x_898_, 0);
    leanh::lean_inc(v_second_899_);
    v_nano_900_ = leanh::lean_ctor_get(v___x_898_, 1);
    leanh::lean_inc(v_nano_900_);
    leanh::lean_dec_ref(v___x_898_);
    v___x_901_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once),
        _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2,
    );
    v___x_902_ = lean_int_mul(v_second_894_, v___x_901_);
    v___x_903_ = lean_int_add(v___x_902_, v_nano_895_);
    leanh::lean_dec(v___x_902_);
    v___x_904_ = lean_int_mul(v_second_899_, v___x_901_);
    leanh::lean_dec(v_second_899_);
    v___x_905_ = lean_int_add(v___x_904_, v_nano_900_);
    leanh::lean_dec(v_nano_900_);
    leanh::lean_dec(v___x_904_);
    v___x_906_ = lean_int_add(v___x_903_, v___x_905_);
    leanh::lean_dec(v___x_905_);
    leanh::lean_dec(v___x_903_);
    v___x_907_ = l_Std_Time_Duration_ofNanoseconds(v___x_906_);
    leanh::lean_dec(v___x_906_);
    return v___x_907_;
}
pub unsafe fn l_Std_Time_Timestamp_addMilliseconds___boxed(
    mut v_t_908_: *mut leanh::LeanObject,
    mut v_s_909_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_910_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_910_ = l_Std_Time_Timestamp_addMilliseconds(v_t_908_, v_s_909_);
    leanh::lean_dec(v_s_909_);
    leanh::lean_dec_ref(v_t_908_);
    return v_res_910_;
}
pub unsafe fn l_Std_Time_Timestamp_subMilliseconds(
    mut v_t_911_: *mut leanh::LeanObject,
    mut v_s_912_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_913_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0_once),
        _init_l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0,
    );
    v___x_914_ = lean_int_mul(v_s_912_, v___x_913_);
    v___x_915_ = l_Std_Time_Duration_ofNanoseconds(v___x_914_);
    leanh::lean_dec(v___x_914_);
    v_second_916_ = leanh::lean_ctor_get(v___x_915_, 0);
    leanh::lean_inc(v_second_916_);
    v_nano_917_ = leanh::lean_ctor_get(v___x_915_, 1);
    leanh::lean_inc(v_nano_917_);
    leanh::lean_dec_ref(v___x_915_);
    v_second_918_ = leanh::lean_ctor_get(v_t_911_, 0);
    v_nano_919_ = leanh::lean_ctor_get(v_t_911_, 1);
    v___x_920_ = lean_int_neg(v_second_916_);
    leanh::lean_dec(v_second_916_);
    v___x_921_ = lean_int_neg(v_nano_917_);
    leanh::lean_dec(v_nano_917_);
    v___x_922_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once),
        _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2,
    );
    v___x_923_ = lean_int_mul(v_second_918_, v___x_922_);
    v___x_924_ = lean_int_add(v___x_923_, v_nano_919_);
    leanh::lean_dec(v___x_923_);
    v___x_925_ = lean_int_mul(v___x_920_, v___x_922_);
    leanh::lean_dec(v___x_920_);
    v___x_926_ = lean_int_add(v___x_925_, v___x_921_);
    leanh::lean_dec(v___x_921_);
    leanh::lean_dec(v___x_925_);
    v___x_927_ = lean_int_add(v___x_924_, v___x_926_);
    leanh::lean_dec(v___x_926_);
    leanh::lean_dec(v___x_924_);
    v___x_928_ = l_Std_Time_Duration_ofNanoseconds(v___x_927_);
    leanh::lean_dec(v___x_927_);
    return v___x_928_;
}
pub unsafe fn l_Std_Time_Timestamp_subMilliseconds___boxed(
    mut v_t_929_: *mut leanh::LeanObject,
    mut v_s_930_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_931_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_931_ = l_Std_Time_Timestamp_subMilliseconds(v_t_929_, v_s_930_);
    leanh::lean_dec(v_s_930_);
    leanh::lean_dec_ref(v_t_929_);
    return v_res_931_;
}
pub unsafe fn l_Std_Time_Timestamp_addNanoseconds(
    mut v_t_932_: *mut leanh::LeanObject,
    mut v_s_933_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_second_934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_945_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_second_934_ = leanh::lean_ctor_get(v_t_932_, 0);
    v_nano_935_ = leanh::lean_ctor_get(v_t_932_, 1);
    v___x_936_ = l_Std_Time_Duration_ofNanoseconds(v_s_933_);
    v_second_937_ = leanh::lean_ctor_get(v___x_936_, 0);
    leanh::lean_inc(v_second_937_);
    v_nano_938_ = leanh::lean_ctor_get(v___x_936_, 1);
    leanh::lean_inc(v_nano_938_);
    leanh::lean_dec_ref(v___x_936_);
    v___x_939_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once),
        _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2,
    );
    v___x_940_ = lean_int_mul(v_second_934_, v___x_939_);
    v___x_941_ = lean_int_add(v___x_940_, v_nano_935_);
    leanh::lean_dec(v___x_940_);
    v___x_942_ = lean_int_mul(v_second_937_, v___x_939_);
    leanh::lean_dec(v_second_937_);
    v___x_943_ = lean_int_add(v___x_942_, v_nano_938_);
    leanh::lean_dec(v_nano_938_);
    leanh::lean_dec(v___x_942_);
    v___x_944_ = lean_int_add(v___x_941_, v___x_943_);
    leanh::lean_dec(v___x_943_);
    leanh::lean_dec(v___x_941_);
    v___x_945_ = l_Std_Time_Duration_ofNanoseconds(v___x_944_);
    leanh::lean_dec(v___x_944_);
    return v___x_945_;
}
pub unsafe fn l_Std_Time_Timestamp_addNanoseconds___boxed(
    mut v_t_946_: *mut leanh::LeanObject,
    mut v_s_947_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_948_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_948_ = l_Std_Time_Timestamp_addNanoseconds(v_t_946_, v_s_947_);
    leanh::lean_dec(v_s_947_);
    leanh::lean_dec_ref(v_t_946_);
    return v_res_948_;
}
pub unsafe fn l_Std_Time_Timestamp_subNanoseconds(
    mut v_t_949_: *mut leanh::LeanObject,
    mut v_s_950_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_964_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_951_ = l_Std_Time_Duration_ofNanoseconds(v_s_950_);
    v_second_952_ = leanh::lean_ctor_get(v___x_951_, 0);
    leanh::lean_inc(v_second_952_);
    v_nano_953_ = leanh::lean_ctor_get(v___x_951_, 1);
    leanh::lean_inc(v_nano_953_);
    leanh::lean_dec_ref(v___x_951_);
    v_second_954_ = leanh::lean_ctor_get(v_t_949_, 0);
    v_nano_955_ = leanh::lean_ctor_get(v_t_949_, 1);
    v___x_956_ = lean_int_neg(v_second_952_);
    leanh::lean_dec(v_second_952_);
    v___x_957_ = lean_int_neg(v_nano_953_);
    leanh::lean_dec(v_nano_953_);
    v___x_958_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once),
        _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2,
    );
    v___x_959_ = lean_int_mul(v_second_954_, v___x_958_);
    v___x_960_ = lean_int_add(v___x_959_, v_nano_955_);
    leanh::lean_dec(v___x_959_);
    v___x_961_ = lean_int_mul(v___x_956_, v___x_958_);
    leanh::lean_dec(v___x_956_);
    v___x_962_ = lean_int_add(v___x_961_, v___x_957_);
    leanh::lean_dec(v___x_957_);
    leanh::lean_dec(v___x_961_);
    v___x_963_ = lean_int_add(v___x_960_, v___x_962_);
    leanh::lean_dec(v___x_962_);
    leanh::lean_dec(v___x_960_);
    v___x_964_ = l_Std_Time_Duration_ofNanoseconds(v___x_963_);
    leanh::lean_dec(v___x_963_);
    return v___x_964_;
}
pub unsafe fn l_Std_Time_Timestamp_subNanoseconds___boxed(
    mut v_t_965_: *mut leanh::LeanObject,
    mut v_s_966_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_967_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_967_ = l_Std_Time_Timestamp_subNanoseconds(v_t_965_, v_s_966_);
    leanh::lean_dec(v_s_966_);
    leanh::lean_dec_ref(v_t_965_);
    return v_res_967_;
}
pub unsafe fn l_Std_Time_Timestamp_addSeconds(
    mut v_t_968_: *mut leanh::LeanObject,
    mut v_s_969_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_second_970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_979_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_second_970_ = leanh::lean_ctor_get(v_t_968_, 0);
    v_nano_971_ = leanh::lean_ctor_get(v_t_968_, 1);
    v___x_972_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp_repr___redArg___closed__14),
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp_repr___redArg___closed__14_once),
        _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__14,
    );
    v___x_973_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once),
        _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2,
    );
    v___x_974_ = lean_int_mul(v_second_970_, v___x_973_);
    v___x_975_ = lean_int_add(v___x_974_, v_nano_971_);
    leanh::lean_dec(v___x_974_);
    v___x_976_ = lean_int_mul(v_s_969_, v___x_973_);
    v___x_977_ = lean_int_add(v___x_976_, v___x_972_);
    leanh::lean_dec(v___x_976_);
    v___x_978_ = lean_int_add(v___x_975_, v___x_977_);
    leanh::lean_dec(v___x_977_);
    leanh::lean_dec(v___x_975_);
    v___x_979_ = l_Std_Time_Duration_ofNanoseconds(v___x_978_);
    leanh::lean_dec(v___x_978_);
    return v___x_979_;
}
pub unsafe fn l_Std_Time_Timestamp_addSeconds___boxed(
    mut v_t_980_: *mut leanh::LeanObject,
    mut v_s_981_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_982_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_982_ = l_Std_Time_Timestamp_addSeconds(v_t_980_, v_s_981_);
    leanh::lean_dec(v_s_981_);
    leanh::lean_dec_ref(v_t_980_);
    return v_res_982_;
}
pub unsafe fn _init_l_Std_Time_Timestamp_subSeconds___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_984_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_983_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp_repr___redArg___closed__14),
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp_repr___redArg___closed__14_once),
        _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__14,
    );
    v___x_984_ = lean_int_neg(v___x_983_);
    return v___x_984_;
}
pub unsafe fn l_Std_Time_Timestamp_subSeconds(
    mut v_t_985_: *mut leanh::LeanObject,
    mut v_s_986_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_second_987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_997_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_second_987_ = leanh::lean_ctor_get(v_t_985_, 0);
    v_nano_988_ = leanh::lean_ctor_get(v_t_985_, 1);
    v___x_989_ = lean_int_neg(v_s_986_);
    v___x_990_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_subSeconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_subSeconds___closed__0_once),
        _init_l_Std_Time_Timestamp_subSeconds___closed__0,
    );
    v___x_991_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once),
        _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2,
    );
    v___x_992_ = lean_int_mul(v_second_987_, v___x_991_);
    v___x_993_ = lean_int_add(v___x_992_, v_nano_988_);
    leanh::lean_dec(v___x_992_);
    v___x_994_ = lean_int_mul(v___x_989_, v___x_991_);
    leanh::lean_dec(v___x_989_);
    v___x_995_ = lean_int_add(v___x_994_, v___x_990_);
    leanh::lean_dec(v___x_994_);
    v___x_996_ = lean_int_add(v___x_993_, v___x_995_);
    leanh::lean_dec(v___x_995_);
    leanh::lean_dec(v___x_993_);
    v___x_997_ = l_Std_Time_Duration_ofNanoseconds(v___x_996_);
    leanh::lean_dec(v___x_996_);
    return v___x_997_;
}
pub unsafe fn l_Std_Time_Timestamp_subSeconds___boxed(
    mut v_t_998_: *mut leanh::LeanObject,
    mut v_s_999_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1000_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1000_ = l_Std_Time_Timestamp_subSeconds(v_t_998_, v_s_999_);
    leanh::lean_dec(v_s_999_);
    leanh::lean_dec_ref(v_t_998_);
    return v_res_1000_;
}
pub unsafe fn l_Std_Time_Timestamp_addMinutes(
    mut v_t_1001_: *mut leanh::LeanObject,
    mut v_m_1002_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_second_1003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1014_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_second_1003_ = leanh::lean_ctor_get(v_t_1001_, 0);
    v_nano_1004_ = leanh::lean_ctor_get(v_t_1001_, 1);
    v___x_1005_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toMinutesSinceUnixEpoch___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toMinutesSinceUnixEpoch___closed__0_once),
        _init_l_Std_Time_Timestamp_toMinutesSinceUnixEpoch___closed__0,
    );
    v___x_1006_ = lean_int_mul(v_m_1002_, v___x_1005_);
    v___x_1007_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp_repr___redArg___closed__14),
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp_repr___redArg___closed__14_once),
        _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__14,
    );
    v___x_1008_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once),
        _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2,
    );
    v___x_1009_ = lean_int_mul(v_second_1003_, v___x_1008_);
    v___x_1010_ = lean_int_add(v___x_1009_, v_nano_1004_);
    leanh::lean_dec(v___x_1009_);
    v___x_1011_ = lean_int_mul(v___x_1006_, v___x_1008_);
    leanh::lean_dec(v___x_1006_);
    v___x_1012_ = lean_int_add(v___x_1011_, v___x_1007_);
    leanh::lean_dec(v___x_1011_);
    v___x_1013_ = lean_int_add(v___x_1010_, v___x_1012_);
    leanh::lean_dec(v___x_1012_);
    leanh::lean_dec(v___x_1010_);
    v___x_1014_ = l_Std_Time_Duration_ofNanoseconds(v___x_1013_);
    leanh::lean_dec(v___x_1013_);
    return v___x_1014_;
}
pub unsafe fn l_Std_Time_Timestamp_addMinutes___boxed(
    mut v_t_1015_: *mut leanh::LeanObject,
    mut v_m_1016_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1017_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1017_ = l_Std_Time_Timestamp_addMinutes(v_t_1015_, v_m_1016_);
    leanh::lean_dec(v_m_1016_);
    leanh::lean_dec_ref(v_t_1015_);
    return v_res_1017_;
}
pub unsafe fn l_Std_Time_Timestamp_subMinutes(
    mut v_t_1018_: *mut leanh::LeanObject,
    mut v_m_1019_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_second_1020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1032_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_second_1020_ = leanh::lean_ctor_get(v_t_1018_, 0);
    v_nano_1021_ = leanh::lean_ctor_get(v_t_1018_, 1);
    v___x_1022_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toMinutesSinceUnixEpoch___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toMinutesSinceUnixEpoch___closed__0_once),
        _init_l_Std_Time_Timestamp_toMinutesSinceUnixEpoch___closed__0,
    );
    v___x_1023_ = lean_int_mul(v_m_1019_, v___x_1022_);
    v___x_1024_ = lean_int_neg(v___x_1023_);
    leanh::lean_dec(v___x_1023_);
    v___x_1025_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_subSeconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_subSeconds___closed__0_once),
        _init_l_Std_Time_Timestamp_subSeconds___closed__0,
    );
    v___x_1026_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once),
        _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2,
    );
    v___x_1027_ = lean_int_mul(v_second_1020_, v___x_1026_);
    v___x_1028_ = lean_int_add(v___x_1027_, v_nano_1021_);
    leanh::lean_dec(v___x_1027_);
    v___x_1029_ = lean_int_mul(v___x_1024_, v___x_1026_);
    leanh::lean_dec(v___x_1024_);
    v___x_1030_ = lean_int_add(v___x_1029_, v___x_1025_);
    leanh::lean_dec(v___x_1029_);
    v___x_1031_ = lean_int_add(v___x_1028_, v___x_1030_);
    leanh::lean_dec(v___x_1030_);
    leanh::lean_dec(v___x_1028_);
    v___x_1032_ = l_Std_Time_Duration_ofNanoseconds(v___x_1031_);
    leanh::lean_dec(v___x_1031_);
    return v___x_1032_;
}
pub unsafe fn l_Std_Time_Timestamp_subMinutes___boxed(
    mut v_t_1033_: *mut leanh::LeanObject,
    mut v_m_1034_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1035_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1035_ = l_Std_Time_Timestamp_subMinutes(v_t_1033_, v_m_1034_);
    leanh::lean_dec(v_m_1034_);
    leanh::lean_dec_ref(v_t_1033_);
    return v_res_1035_;
}
pub unsafe fn _init_l_Std_Time_Timestamp_addHours___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_1036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1036_ = leanh::lean_unsigned_to_nat(3600);
    v___x_1037_ = lean_nat_to_int(v___x_1036_);
    return v___x_1037_;
}
pub unsafe fn l_Std_Time_Timestamp_addHours(
    mut v_t_1038_: *mut leanh::LeanObject,
    mut v_h_1039_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_second_1040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1051_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_second_1040_ = leanh::lean_ctor_get(v_t_1038_, 0);
    v_nano_1041_ = leanh::lean_ctor_get(v_t_1038_, 1);
    v___x_1042_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_addHours___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_addHours___closed__0_once),
        _init_l_Std_Time_Timestamp_addHours___closed__0,
    );
    v___x_1043_ = lean_int_mul(v_h_1039_, v___x_1042_);
    v___x_1044_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp_repr___redArg___closed__14),
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp_repr___redArg___closed__14_once),
        _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__14,
    );
    v___x_1045_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once),
        _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2,
    );
    v___x_1046_ = lean_int_mul(v_second_1040_, v___x_1045_);
    v___x_1047_ = lean_int_add(v___x_1046_, v_nano_1041_);
    leanh::lean_dec(v___x_1046_);
    v___x_1048_ = lean_int_mul(v___x_1043_, v___x_1045_);
    leanh::lean_dec(v___x_1043_);
    v___x_1049_ = lean_int_add(v___x_1048_, v___x_1044_);
    leanh::lean_dec(v___x_1048_);
    v___x_1050_ = lean_int_add(v___x_1047_, v___x_1049_);
    leanh::lean_dec(v___x_1049_);
    leanh::lean_dec(v___x_1047_);
    v___x_1051_ = l_Std_Time_Duration_ofNanoseconds(v___x_1050_);
    leanh::lean_dec(v___x_1050_);
    return v___x_1051_;
}
pub unsafe fn l_Std_Time_Timestamp_addHours___boxed(
    mut v_t_1052_: *mut leanh::LeanObject,
    mut v_h_1053_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1054_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1054_ = l_Std_Time_Timestamp_addHours(v_t_1052_, v_h_1053_);
    leanh::lean_dec(v_h_1053_);
    leanh::lean_dec_ref(v_t_1052_);
    return v_res_1054_;
}
pub unsafe fn l_Std_Time_Timestamp_subHours(
    mut v_t_1055_: *mut leanh::LeanObject,
    mut v_h_1056_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_second_1057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_second_1057_ = leanh::lean_ctor_get(v_t_1055_, 0);
    v_nano_1058_ = leanh::lean_ctor_get(v_t_1055_, 1);
    v___x_1059_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_addHours___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_addHours___closed__0_once),
        _init_l_Std_Time_Timestamp_addHours___closed__0,
    );
    v___x_1060_ = lean_int_mul(v_h_1056_, v___x_1059_);
    v___x_1061_ = lean_int_neg(v___x_1060_);
    leanh::lean_dec(v___x_1060_);
    v___x_1062_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_subSeconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_subSeconds___closed__0_once),
        _init_l_Std_Time_Timestamp_subSeconds___closed__0,
    );
    v___x_1063_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once),
        _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2,
    );
    v___x_1064_ = lean_int_mul(v_second_1057_, v___x_1063_);
    v___x_1065_ = lean_int_add(v___x_1064_, v_nano_1058_);
    leanh::lean_dec(v___x_1064_);
    v___x_1066_ = lean_int_mul(v___x_1061_, v___x_1063_);
    leanh::lean_dec(v___x_1061_);
    v___x_1067_ = lean_int_add(v___x_1066_, v___x_1062_);
    leanh::lean_dec(v___x_1066_);
    v___x_1068_ = lean_int_add(v___x_1065_, v___x_1067_);
    leanh::lean_dec(v___x_1067_);
    leanh::lean_dec(v___x_1065_);
    v___x_1069_ = l_Std_Time_Duration_ofNanoseconds(v___x_1068_);
    leanh::lean_dec(v___x_1068_);
    return v___x_1069_;
}
pub unsafe fn l_Std_Time_Timestamp_subHours___boxed(
    mut v_t_1070_: *mut leanh::LeanObject,
    mut v_h_1071_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1072_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1072_ = l_Std_Time_Timestamp_subHours(v_t_1070_, v_h_1071_);
    leanh::lean_dec(v_h_1071_);
    leanh::lean_dec_ref(v_t_1070_);
    return v_res_1072_;
}
pub unsafe fn l_Std_Time_Timestamp_addDays(
    mut v_t_1073_: *mut leanh::LeanObject,
    mut v_d_1074_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_second_1075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1086_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_second_1075_ = leanh::lean_ctor_get(v_t_1073_, 0);
    v_nano_1076_ = leanh::lean_ctor_get(v_t_1073_, 1);
    v___x_1077_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toDaysSinceUnixEpoch___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toDaysSinceUnixEpoch___closed__0_once),
        _init_l_Std_Time_Timestamp_toDaysSinceUnixEpoch___closed__0,
    );
    v___x_1078_ = lean_int_mul(v_d_1074_, v___x_1077_);
    v___x_1079_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp_repr___redArg___closed__14),
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp_repr___redArg___closed__14_once),
        _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__14,
    );
    v___x_1080_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once),
        _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2,
    );
    v___x_1081_ = lean_int_mul(v_second_1075_, v___x_1080_);
    v___x_1082_ = lean_int_add(v___x_1081_, v_nano_1076_);
    leanh::lean_dec(v___x_1081_);
    v___x_1083_ = lean_int_mul(v___x_1078_, v___x_1080_);
    leanh::lean_dec(v___x_1078_);
    v___x_1084_ = lean_int_add(v___x_1083_, v___x_1079_);
    leanh::lean_dec(v___x_1083_);
    v___x_1085_ = lean_int_add(v___x_1082_, v___x_1084_);
    leanh::lean_dec(v___x_1084_);
    leanh::lean_dec(v___x_1082_);
    v___x_1086_ = l_Std_Time_Duration_ofNanoseconds(v___x_1085_);
    leanh::lean_dec(v___x_1085_);
    return v___x_1086_;
}
pub unsafe fn l_Std_Time_Timestamp_addDays___boxed(
    mut v_t_1087_: *mut leanh::LeanObject,
    mut v_d_1088_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1089_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1089_ = l_Std_Time_Timestamp_addDays(v_t_1087_, v_d_1088_);
    leanh::lean_dec(v_d_1088_);
    leanh::lean_dec_ref(v_t_1087_);
    return v_res_1089_;
}
pub unsafe fn l_Std_Time_Timestamp_subDays(
    mut v_t_1090_: *mut leanh::LeanObject,
    mut v_d_1091_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_second_1092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_second_1092_ = leanh::lean_ctor_get(v_t_1090_, 0);
    v_nano_1093_ = leanh::lean_ctor_get(v_t_1090_, 1);
    v___x_1094_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toDaysSinceUnixEpoch___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toDaysSinceUnixEpoch___closed__0_once),
        _init_l_Std_Time_Timestamp_toDaysSinceUnixEpoch___closed__0,
    );
    v___x_1095_ = lean_int_mul(v_d_1091_, v___x_1094_);
    v___x_1096_ = lean_int_neg(v___x_1095_);
    leanh::lean_dec(v___x_1095_);
    v___x_1097_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_subSeconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_subSeconds___closed__0_once),
        _init_l_Std_Time_Timestamp_subSeconds___closed__0,
    );
    v___x_1098_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once),
        _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2,
    );
    v___x_1099_ = lean_int_mul(v_second_1092_, v___x_1098_);
    v___x_1100_ = lean_int_add(v___x_1099_, v_nano_1093_);
    leanh::lean_dec(v___x_1099_);
    v___x_1101_ = lean_int_mul(v___x_1096_, v___x_1098_);
    leanh::lean_dec(v___x_1096_);
    v___x_1102_ = lean_int_add(v___x_1101_, v___x_1097_);
    leanh::lean_dec(v___x_1101_);
    v___x_1103_ = lean_int_add(v___x_1100_, v___x_1102_);
    leanh::lean_dec(v___x_1102_);
    leanh::lean_dec(v___x_1100_);
    v___x_1104_ = l_Std_Time_Duration_ofNanoseconds(v___x_1103_);
    leanh::lean_dec(v___x_1103_);
    return v___x_1104_;
}
pub unsafe fn l_Std_Time_Timestamp_subDays___boxed(
    mut v_t_1105_: *mut leanh::LeanObject,
    mut v_d_1106_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1107_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1107_ = l_Std_Time_Timestamp_subDays(v_t_1105_, v_d_1106_);
    leanh::lean_dec(v_d_1106_);
    leanh::lean_dec_ref(v_t_1105_);
    return v_res_1107_;
}
pub unsafe fn l_Std_Time_Timestamp_addWeeks(
    mut v_t_1108_: *mut leanh::LeanObject,
    mut v_d_1109_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_second_1110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1123_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_second_1110_ = leanh::lean_ctor_get(v_t_1108_, 0);
    v_nano_1111_ = leanh::lean_ctor_get(v_t_1108_, 1);
    v___x_1112_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp_repr___redArg___closed__7_once),
        _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__7,
    );
    v___x_1113_ = lean_int_mul(v_d_1109_, v___x_1112_);
    v___x_1114_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toDaysSinceUnixEpoch___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toDaysSinceUnixEpoch___closed__0_once),
        _init_l_Std_Time_Timestamp_toDaysSinceUnixEpoch___closed__0,
    );
    v___x_1115_ = lean_int_mul(v___x_1113_, v___x_1114_);
    leanh::lean_dec(v___x_1113_);
    v___x_1116_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp_repr___redArg___closed__14),
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp_repr___redArg___closed__14_once),
        _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__14,
    );
    v___x_1117_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once),
        _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2,
    );
    v___x_1118_ = lean_int_mul(v_second_1110_, v___x_1117_);
    v___x_1119_ = lean_int_add(v___x_1118_, v_nano_1111_);
    leanh::lean_dec(v___x_1118_);
    v___x_1120_ = lean_int_mul(v___x_1115_, v___x_1117_);
    leanh::lean_dec(v___x_1115_);
    v___x_1121_ = lean_int_add(v___x_1120_, v___x_1116_);
    leanh::lean_dec(v___x_1120_);
    v___x_1122_ = lean_int_add(v___x_1119_, v___x_1121_);
    leanh::lean_dec(v___x_1121_);
    leanh::lean_dec(v___x_1119_);
    v___x_1123_ = l_Std_Time_Duration_ofNanoseconds(v___x_1122_);
    leanh::lean_dec(v___x_1122_);
    return v___x_1123_;
}
pub unsafe fn l_Std_Time_Timestamp_addWeeks___boxed(
    mut v_t_1124_: *mut leanh::LeanObject,
    mut v_d_1125_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1126_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1126_ = l_Std_Time_Timestamp_addWeeks(v_t_1124_, v_d_1125_);
    leanh::lean_dec(v_d_1125_);
    leanh::lean_dec_ref(v_t_1124_);
    return v_res_1126_;
}
pub unsafe fn l_Std_Time_Timestamp_subWeeks(
    mut v_t_1127_: *mut leanh::LeanObject,
    mut v_d_1128_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_second_1129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1143_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_second_1129_ = leanh::lean_ctor_get(v_t_1127_, 0);
    v_nano_1130_ = leanh::lean_ctor_get(v_t_1127_, 1);
    v___x_1131_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp_repr___redArg___closed__7_once),
        _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__7,
    );
    v___x_1132_ = lean_int_mul(v_d_1128_, v___x_1131_);
    v___x_1133_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toDaysSinceUnixEpoch___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_toDaysSinceUnixEpoch___closed__0_once),
        _init_l_Std_Time_Timestamp_toDaysSinceUnixEpoch___closed__0,
    );
    v___x_1134_ = lean_int_mul(v___x_1132_, v___x_1133_);
    leanh::lean_dec(v___x_1132_);
    v___x_1135_ = lean_int_neg(v___x_1134_);
    leanh::lean_dec(v___x_1134_);
    v___x_1136_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_subSeconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Timestamp_subSeconds___closed__0_once),
        _init_l_Std_Time_Timestamp_subSeconds___closed__0,
    );
    v___x_1137_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once),
        _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2,
    );
    v___x_1138_ = lean_int_mul(v_second_1129_, v___x_1137_);
    v___x_1139_ = lean_int_add(v___x_1138_, v_nano_1130_);
    leanh::lean_dec(v___x_1138_);
    v___x_1140_ = lean_int_mul(v___x_1135_, v___x_1137_);
    leanh::lean_dec(v___x_1135_);
    v___x_1141_ = lean_int_add(v___x_1140_, v___x_1136_);
    leanh::lean_dec(v___x_1140_);
    v___x_1142_ = lean_int_add(v___x_1139_, v___x_1141_);
    leanh::lean_dec(v___x_1141_);
    leanh::lean_dec(v___x_1139_);
    v___x_1143_ = l_Std_Time_Duration_ofNanoseconds(v___x_1142_);
    leanh::lean_dec(v___x_1142_);
    return v___x_1143_;
}
pub unsafe fn l_Std_Time_Timestamp_subWeeks___boxed(
    mut v_t_1144_: *mut leanh::LeanObject,
    mut v_d_1145_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1146_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1146_ = l_Std_Time_Timestamp_subWeeks(v_t_1144_, v_d_1145_);
    leanh::lean_dec(v_d_1145_);
    leanh::lean_dec_ref(v_t_1144_);
    return v_res_1146_;
}
pub unsafe fn l_Std_Time_Timestamp_addDuration(
    mut v_t_1147_: *mut leanh::LeanObject,
    mut v_d_1148_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_second_1149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_1151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1159_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_second_1149_ = leanh::lean_ctor_get(v_t_1147_, 0);
    v_nano_1150_ = leanh::lean_ctor_get(v_t_1147_, 1);
    v_second_1151_ = leanh::lean_ctor_get(v_d_1148_, 0);
    v_nano_1152_ = leanh::lean_ctor_get(v_d_1148_, 1);
    v___x_1153_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once),
        _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2,
    );
    v___x_1154_ = lean_int_mul(v_second_1149_, v___x_1153_);
    v___x_1155_ = lean_int_add(v___x_1154_, v_nano_1150_);
    leanh::lean_dec(v___x_1154_);
    v___x_1156_ = lean_int_mul(v_second_1151_, v___x_1153_);
    v___x_1157_ = lean_int_add(v___x_1156_, v_nano_1152_);
    leanh::lean_dec(v___x_1156_);
    v___x_1158_ = lean_int_add(v___x_1155_, v___x_1157_);
    leanh::lean_dec(v___x_1157_);
    leanh::lean_dec(v___x_1155_);
    v___x_1159_ = l_Std_Time_Duration_ofNanoseconds(v___x_1158_);
    leanh::lean_dec(v___x_1158_);
    return v___x_1159_;
}
pub unsafe fn l_Std_Time_Timestamp_addDuration___boxed(
    mut v_t_1160_: *mut leanh::LeanObject,
    mut v_d_1161_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1162_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1162_ = l_Std_Time_Timestamp_addDuration(v_t_1160_, v_d_1161_);
    leanh::lean_dec_ref(v_d_1161_);
    leanh::lean_dec_ref(v_t_1160_);
    return v_res_1162_;
}
pub unsafe fn l_Std_Time_Timestamp_subDuration(
    mut v_t_1163_: *mut leanh::LeanObject,
    mut v_d_1164_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_second_1165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_1167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1177_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_second_1165_ = leanh::lean_ctor_get(v_d_1164_, 0);
    v_nano_1166_ = leanh::lean_ctor_get(v_d_1164_, 1);
    v_second_1167_ = leanh::lean_ctor_get(v_t_1163_, 0);
    v_nano_1168_ = leanh::lean_ctor_get(v_t_1163_, 1);
    v___x_1169_ = lean_int_neg(v_second_1165_);
    v___x_1170_ = lean_int_neg(v_nano_1166_);
    v___x_1171_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once),
        _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2,
    );
    v___x_1172_ = lean_int_mul(v_second_1167_, v___x_1171_);
    v___x_1173_ = lean_int_add(v___x_1172_, v_nano_1168_);
    leanh::lean_dec(v___x_1172_);
    v___x_1174_ = lean_int_mul(v___x_1169_, v___x_1171_);
    leanh::lean_dec(v___x_1169_);
    v___x_1175_ = lean_int_add(v___x_1174_, v___x_1170_);
    leanh::lean_dec(v___x_1170_);
    leanh::lean_dec(v___x_1174_);
    v___x_1176_ = lean_int_add(v___x_1173_, v___x_1175_);
    leanh::lean_dec(v___x_1175_);
    leanh::lean_dec(v___x_1173_);
    v___x_1177_ = l_Std_Time_Duration_ofNanoseconds(v___x_1176_);
    leanh::lean_dec(v___x_1176_);
    return v___x_1177_;
}
pub unsafe fn l_Std_Time_Timestamp_subDuration___boxed(
    mut v_t_1178_: *mut leanh::LeanObject,
    mut v_d_1179_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1180_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1180_ = l_Std_Time_Timestamp_subDuration(v_t_1178_, v_d_1179_);
    leanh::lean_dec_ref(v_d_1179_);
    leanh::lean_dec_ref(v_t_1178_);
    return v_res_1180_;
}
pub unsafe fn l_Std_Time_Timestamp_instHSubDuration__1___lam__0(
    mut v_x_1213_: *mut leanh::LeanObject,
    mut v_y_1214_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_second_1215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_1217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1227_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_second_1215_ = leanh::lean_ctor_get(v_y_1214_, 0);
    v_nano_1216_ = leanh::lean_ctor_get(v_y_1214_, 1);
    v_second_1217_ = leanh::lean_ctor_get(v_x_1213_, 0);
    v_nano_1218_ = leanh::lean_ctor_get(v_x_1213_, 1);
    v___x_1219_ = lean_int_neg(v_second_1215_);
    v___x_1220_ = lean_int_neg(v_nano_1216_);
    v___x_1221_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once),
        _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2,
    );
    v___x_1222_ = lean_int_mul(v_second_1217_, v___x_1221_);
    v___x_1223_ = lean_int_add(v___x_1222_, v_nano_1218_);
    leanh::lean_dec(v___x_1222_);
    v___x_1224_ = lean_int_mul(v___x_1219_, v___x_1221_);
    leanh::lean_dec(v___x_1219_);
    v___x_1225_ = lean_int_add(v___x_1224_, v___x_1220_);
    leanh::lean_dec(v___x_1220_);
    leanh::lean_dec(v___x_1224_);
    v___x_1226_ = lean_int_add(v___x_1223_, v___x_1225_);
    leanh::lean_dec(v___x_1225_);
    leanh::lean_dec(v___x_1223_);
    v___x_1227_ = l_Std_Time_Duration_ofNanoseconds(v___x_1226_);
    leanh::lean_dec(v___x_1226_);
    return v___x_1227_;
}
pub unsafe fn l_Std_Time_Timestamp_instHSubDuration__1___lam__0___boxed(
    mut v_x_1228_: *mut leanh::LeanObject,
    mut v_y_1229_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1230_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1230_ = l_Std_Time_Timestamp_instHSubDuration__1___lam__0(v_x_1228_, v_y_1229_);
    leanh::lean_dec_ref(v_y_1229_);
    leanh::lean_dec_ref(v_x_1228_);
    return v_res_1230_;
}
pub unsafe fn l_Std_Time_Timestamp_instOfNat(
    mut v_n_1233_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1236_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1234_ = lean_nat_to_int(v_n_1233_);
    v___x_1235_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp_repr___redArg___closed__14),
        core::ptr::addr_of_mut!(l_Std_Time_instReprTimestamp_repr___redArg___closed__14_once),
        _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__14,
    );
    v___x_1236_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1236_, 0, v___x_1234_);
    leanh::lean_ctor_set(v___x_1236_, 1, v___x_1235_);
    return v___x_1236_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Time_DateTime_Timestamp(
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
    l_Std_Time_instInhabitedTimestamp_default = _init_l_Std_Time_instInhabitedTimestamp_default();
    leanh::lean_mark_persistent(l_Std_Time_instInhabitedTimestamp_default);
    l_Std_Time_instInhabitedTimestamp = _init_l_Std_Time_instInhabitedTimestamp();
    leanh::lean_mark_persistent(l_Std_Time_instInhabitedTimestamp);
    l_Std_Time_instLETimestamp = _init_l_Std_Time_instLETimestamp();
    leanh::lean_mark_persistent(l_Std_Time_instLETimestamp);
    l_Std_Time_instLTTimestamp = _init_l_Std_Time_instLTTimestamp();
    leanh::lean_mark_persistent(l_Std_Time_instLTTimestamp);
    l_Std_Time_instOrdTimestamp = _init_l_Std_Time_instOrdTimestamp();
    leanh::lean_mark_persistent(l_Std_Time_instOrdTimestamp);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Time_DateTime_Timestamp(
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
pub unsafe fn initialize_Std_Time_DateTime_Timestamp(builtin: u8) -> *mut leanh::LeanObject {
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
    res = runtime_initialize_Std_Time_DateTime_Timestamp(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Time_DateTime_Timestamp(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Time_DateTime_Timestamp(builtin);
}