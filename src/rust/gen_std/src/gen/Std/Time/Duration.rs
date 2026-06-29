// Lean compiler output
// Module: Std.Time.Duration
// Imports: Std.Time.Date Init.Data.String.Basic Init.Data.String.Length
use crate::r#gen::Init::Data::Int::Repr::l_Int_repr;
use crate::r#gen::Init::Data::Ord::Basic::{l_compareLex___boxed, l_compareOn___boxed};
use crate::r#gen::Init::Data::Rat::Basic::l_Rat_ofInt;
use crate::r#gen::Init::Data::Repr::l_String_quote;
use crate::r#gen::Init::Data::String::Basic::{
    initialize_Init_Data_String_Basic, runtime_initialize_Init_Data_String_Basic,
};
use crate::r#gen::Init::Data::String::Length::{
    initialize_Init_Data_String_Length, runtime_initialize_Init_Data_String_Length,
};
use crate::r#gen::Init::Prelude::l_Function_comp;
use crate::r#gen::Std::Time::Date::Unit::Day::l_Std_Time_Day_Offset_toSeconds___boxed;
use crate::r#gen::Std::Time::Date::Unit::Week::l_Std_Time_Week_Offset_toDays___boxed;
use crate::r#gen::Std::Time::Date::{initialize_Std_Time_Date, runtime_initialize_Std_Time_Date};
use crate::r#gen::Std::Time::Time::PlainTime::{
    l_Std_Time_PlainTime_ofNanoseconds, l_Std_Time_PlainTime_toNanoseconds,
};
use crate::r#gen::Std::Time::Time::Unit::Basic::{
    l_Std_Time_Hour_Offset_toSeconds___boxed, l_Std_Time_Minute_Offset_toSeconds___boxed,
};
use crate::r#gen::Std::Time::Time::Unit::Nanosecond::{
    l_Std_Time_Nanosecond_Span_toOffset, l_Std_Time_Nanosecond_instOrdSpan___aux__1___boxed,
    l_Std_Time_Nanosecond_instReprOrdinal___lam__0,
};
use crate::r#gen::Std::Time::Time::Unit::Second::{
    l_Std_Time_Second_instOrdOffset___aux__1___boxed, l_Std_Time_Second_instReprOffset___lam__0,
};
use crate::ffi::{
    lean_int_add, lean_int_dec_eq, lean_int_dec_le, lean_int_dec_lt, lean_int_mul, lean_int_neg,
    lean_int_sub, lean_nat_to_int,
};
use crate::ffi::{
    lean_int_div, lean_int_ediv, lean_int_mod,
};
use crate::ffi::lean_string_push;
use crate::ffi::lean_string_append;
use crate::ffi::lean_string_length;
use crate::ffi::{lean_nat_dec_eq, lean_nat_sub};
pub static l_Std_Time_instReprDuration_repr___redArg___closed__0_value:
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
static mut l_Std_Time_instReprDuration_repr___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprDuration_repr___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprDuration_repr___redArg___closed__1_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [115, 101, 99, 111, 110, 100, 0],
};
static mut l_Std_Time_instReprDuration_repr___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprDuration_repr___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprDuration_repr___redArg___closed__2_value:
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
        core::ptr::addr_of!(l_Std_Time_instReprDuration_repr___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_instReprDuration_repr___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprDuration_repr___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprDuration_repr___redArg___closed__3_value:
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
        core::ptr::addr_of!(l_Std_Time_instReprDuration_repr___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_instReprDuration_repr___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprDuration_repr___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprDuration_repr___redArg___closed__4_value:
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
static mut l_Std_Time_instReprDuration_repr___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprDuration_repr___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprDuration_repr___redArg___closed__5_value:
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
        core::ptr::addr_of!(l_Std_Time_instReprDuration_repr___redArg___closed__4_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_instReprDuration_repr___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprDuration_repr___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprDuration_repr___redArg___closed__6_value:
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
        core::ptr::addr_of!(l_Std_Time_instReprDuration_repr___redArg___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_instReprDuration_repr___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_instReprDuration_repr___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprDuration_repr___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_instReprDuration_repr___redArg___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instReprDuration_repr___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_instReprDuration_repr___redArg___closed__8_value:
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
    m_data: [44, 0],
};
static mut l_Std_Time_instReprDuration_repr___redArg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprDuration_repr___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprDuration_repr___redArg___closed__9_value:
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
        core::ptr::addr_of!(l_Std_Time_instReprDuration_repr___redArg___closed__8_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_instReprDuration_repr___redArg___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprDuration_repr___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprDuration_repr___redArg___closed__10_value:
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
    m_data: [110, 97, 110, 111, 0],
};
static mut l_Std_Time_instReprDuration_repr___redArg___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprDuration_repr___redArg___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprDuration_repr___redArg___closed__11_value:
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
        core::ptr::addr_of!(l_Std_Time_instReprDuration_repr___redArg___closed__10_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_instReprDuration_repr___redArg___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprDuration_repr___redArg___closed__11_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_instReprDuration_repr___redArg___closed__12_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instReprDuration_repr___redArg___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_instReprDuration_repr___redArg___closed__13_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [112, 114, 111, 111, 102, 0],
};
static mut l_Std_Time_instReprDuration_repr___redArg___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprDuration_repr___redArg___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprDuration_repr___redArg___closed__14_value:
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
        core::ptr::addr_of!(l_Std_Time_instReprDuration_repr___redArg___closed__13_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_instReprDuration_repr___redArg___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprDuration_repr___redArg___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprDuration_repr___redArg___closed__15_value:
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
    m_data: [95, 0],
};
static mut l_Std_Time_instReprDuration_repr___redArg___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprDuration_repr___redArg___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprDuration_repr___redArg___closed__16_value:
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
        core::ptr::addr_of!(l_Std_Time_instReprDuration_repr___redArg___closed__15_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_instReprDuration_repr___redArg___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprDuration_repr___redArg___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprDuration_repr___redArg___closed__17_value:
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
static mut l_Std_Time_instReprDuration_repr___redArg___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprDuration_repr___redArg___closed__17_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_instReprDuration_repr___redArg___closed__18_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instReprDuration_repr___redArg___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instReprDuration_repr___redArg___closed__19_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instReprDuration_repr___redArg___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_instReprDuration_repr___redArg___closed__20_value:
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
        core::ptr::addr_of!(l_Std_Time_instReprDuration_repr___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_instReprDuration_repr___redArg___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprDuration_repr___redArg___closed__20_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprDuration_repr___redArg___closed__21_value:
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
        core::ptr::addr_of!(l_Std_Time_instReprDuration_repr___redArg___closed__17_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_instReprDuration_repr___redArg___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprDuration_repr___redArg___closed__21_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprDuration___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instReprDuration_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instReprDuration___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprDuration___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_instReprDuration: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprDuration___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instToStringDuration_leftPad___closed__0_value:
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
static mut l_Std_Time_instToStringDuration_leftPad___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instToStringDuration_leftPad___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instToStringDuration___lam__0___closed__0_value:
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
static mut l_Std_Time_instToStringDuration___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instToStringDuration___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_instToStringDuration___lam__0___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instToStringDuration___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_instToStringDuration___lam__0___closed__2_value:
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
static mut l_Std_Time_instToStringDuration___lam__0___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instToStringDuration___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instToStringDuration___lam__0___closed__3_value:
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
static mut l_Std_Time_instToStringDuration___lam__0___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instToStringDuration___lam__0___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instToStringDuration___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instToStringDuration___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instToStringDuration___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instToStringDuration___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_instToStringDuration: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instToStringDuration___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprDuration__1___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instReprDuration__1___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instReprDuration__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprDuration__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_instReprDuration__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprDuration__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_instInhabitedDuration___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedDuration___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedDuration___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedDuration___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_instInhabitedDuration: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_instOrdDuration___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instOrdDuration___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instOrdDuration___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdDuration___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instOrdDuration___closed__1_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instOrdDuration___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instOrdDuration___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdDuration___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instOrdDuration___closed__2_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_Second_instOrdOffset___aux__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instOrdDuration___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdDuration___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instOrdDuration___closed__3_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_Nanosecond_instOrdSpan___aux__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instOrdDuration___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdDuration___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instOrdDuration___closed__4_value: crate::leanh::LeanClosureObject<4> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_compareOn___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 4,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_instOrdDuration___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_instOrdDuration___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_instOrdDuration___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdDuration___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instOrdDuration___closed__5_value: crate::leanh::LeanClosureObject<4> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_compareOn___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 4,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_instOrdDuration___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_instOrdDuration___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_instOrdDuration___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdDuration___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instOrdDuration___closed__6_value: crate::leanh::LeanClosureObject<4> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_compareLex___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 4,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_instOrdDuration___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_instOrdDuration___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_instOrdDuration___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdDuration___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_instOrdDuration: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdDuration___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_Duration_ofNanoseconds___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Duration_ofNanoseconds___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Duration_ofMillisecond___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Duration_ofMillisecond___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Duration_toMilliseconds___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Duration_toMilliseconds___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Duration_instLE: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Std_Time_Duration_instLT: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Duration_toMinutes___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Duration_toMinutes___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Duration_toDays___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Duration_toDays___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Duration_subSeconds___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Duration_subSeconds___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Duration_addHours___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Duration_addHours___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Duration_addWeeks___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Duration_addWeeks___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_Duration_instHAddOffset___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_Duration_addDays___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_Duration_instHAddOffset___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Duration_instHAddOffset___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Duration_instHAddOffset: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Duration_instHAddOffset___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Duration_instHSubOffset___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_Duration_subDays___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_Duration_instHSubOffset___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Duration_instHSubOffset___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Duration_instHSubOffset: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Duration_instHSubOffset___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Duration_instHAddOffset__1___closed__0_value:
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
    m_fun: l_Std_Time_Duration_addWeeks___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_Duration_instHAddOffset__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Duration_instHAddOffset__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Duration_instHAddOffset__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Duration_instHAddOffset__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Duration_instHSubOffset__1___closed__0_value:
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
    m_fun: l_Std_Time_Duration_subWeeks___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_Duration_instHSubOffset__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Duration_instHSubOffset__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Duration_instHSubOffset__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Duration_instHSubOffset__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Duration_instHAddOffset__2___closed__0_value:
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
    m_fun: l_Std_Time_Duration_addHours___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_Duration_instHAddOffset__2___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Duration_instHAddOffset__2___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Duration_instHAddOffset__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Duration_instHAddOffset__2___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Duration_instHSubOffset__2___closed__0_value:
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
    m_fun: l_Std_Time_Duration_subHours___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_Duration_instHSubOffset__2___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Duration_instHSubOffset__2___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Duration_instHSubOffset__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Duration_instHSubOffset__2___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Duration_instHAddOffset__3___closed__0_value:
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
    m_fun: l_Std_Time_Duration_addMinutes___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_Duration_instHAddOffset__3___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Duration_instHAddOffset__3___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Duration_instHAddOffset__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Duration_instHAddOffset__3___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Duration_instHSubOffset__3___closed__0_value:
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
    m_fun: l_Std_Time_Duration_subMinutes___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_Duration_instHSubOffset__3___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Duration_instHSubOffset__3___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Duration_instHSubOffset__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Duration_instHSubOffset__3___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Duration_instHAddOffset__4___closed__0_value:
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
    m_fun: l_Std_Time_Duration_addSeconds___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_Duration_instHAddOffset__4___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Duration_instHAddOffset__4___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Duration_instHAddOffset__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Duration_instHAddOffset__4___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Duration_instHSubOffset__4___closed__0_value:
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
    m_fun: l_Std_Time_Duration_subSeconds___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_Duration_instHSubOffset__4___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Duration_instHSubOffset__4___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Duration_instHSubOffset__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Duration_instHSubOffset__4___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Duration_instHAddOffset__5___closed__0_value:
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
    m_fun: l_Std_Time_Duration_addNanoseconds___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_Duration_instHAddOffset__5___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Duration_instHAddOffset__5___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Duration_instHAddOffset__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Duration_instHAddOffset__5___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Duration_instHSubOffset__5___closed__0_value:
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
    m_fun: l_Std_Time_Duration_subNanoseconds___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_Duration_instHSubOffset__5___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Duration_instHSubOffset__5___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Duration_instHSubOffset__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Duration_instHSubOffset__5___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Duration_instHAddOffset__6___closed__0_value:
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
    m_fun: l_Std_Time_Duration_addMilliseconds___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_Duration_instHAddOffset__6___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Duration_instHAddOffset__6___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Duration_instHAddOffset__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Duration_instHAddOffset__6___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Duration_instHSubOffset__6___closed__0_value:
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
    m_fun: l_Std_Time_Duration_subMilliseconds___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_Duration_instHSubOffset__6___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Duration_instHSubOffset__6___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Duration_instHSubOffset__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Duration_instHSubOffset__6___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Duration_instHSub___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_Duration_sub___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_Duration_instHSub___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Duration_instHSub___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Duration_instHSub: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Duration_instHSub___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Duration_instHAdd___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_Duration_add___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_Duration_instHAdd___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Duration_instHAdd___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Duration_instHAdd: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Duration_instHAdd___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Duration_instCoeOffset___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_Duration_ofNanoseconds___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_Duration_instCoeOffset___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Duration_instCoeOffset___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Duration_instCoeOffset: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Duration_instCoeOffset___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Duration_instCoeOffset__1___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_Duration_ofSeconds as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_Duration_instCoeOffset__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Duration_instCoeOffset__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Duration_instCoeOffset__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Duration_instCoeOffset__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Duration_instCoeOffset__2___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_Minute_Offset_toSeconds___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_Duration_instCoeOffset__2___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Duration_instCoeOffset__2___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Duration_instCoeOffset__2___closed__1_value: crate::leanh::LeanClosureObject<
    5,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Function_comp as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 5,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Duration_instCoeOffset__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Duration_instCoeOffset__2___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Duration_instCoeOffset__2___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Duration_instCoeOffset__2___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Duration_instCoeOffset__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Duration_instCoeOffset__2___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Duration_instCoeOffset__3___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_Hour_Offset_toSeconds___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_Duration_instCoeOffset__3___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Duration_instCoeOffset__3___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Duration_instCoeOffset__3___closed__1_value: crate::leanh::LeanClosureObject<
    5,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Function_comp as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 5,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Duration_instCoeOffset__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Duration_instCoeOffset__3___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Duration_instCoeOffset__3___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Duration_instCoeOffset__3___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Duration_instCoeOffset__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Duration_instCoeOffset__3___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Duration_instCoeOffset__4___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_Day_Offset_toSeconds___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_Duration_instCoeOffset__4___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Duration_instCoeOffset__4___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Duration_instCoeOffset__4___closed__1_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_Week_Offset_toDays___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_Duration_instCoeOffset__4___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Duration_instCoeOffset__4___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Duration_instCoeOffset__4___closed__2_value: crate::leanh::LeanClosureObject<
    5,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Function_comp as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 5,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Duration_instCoeOffset__4___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Duration_instCoeOffset__4___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Duration_instCoeOffset__4___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Duration_instCoeOffset__4___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Duration_instCoeOffset__4___closed__3_value: crate::leanh::LeanClosureObject<
    5,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Function_comp as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 5,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Duration_instCoeOffset__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Duration_instCoeOffset__4___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Duration_instCoeOffset__4___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Duration_instCoeOffset__4___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Duration_instCoeOffset__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Duration_instCoeOffset__4___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Duration_instCoeOffset__5___closed__0_value: crate::leanh::LeanClosureObject<
    5,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Function_comp as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 5,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Duration_instCoeOffset__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Duration_instCoeOffset__4___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Duration_instCoeOffset__5___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Duration_instCoeOffset__5___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Duration_instCoeOffset__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Duration_instCoeOffset__5___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Duration_instHMulInt___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_Duration_instHMulInt___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_Duration_instHMulInt___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Duration_instHMulInt___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Duration_instHMulInt: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Duration_instHMulInt___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Duration_instHMulInt__1___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_Duration_instHMulInt__1___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_Duration_instHMulInt__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Duration_instHMulInt__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Duration_instHMulInt__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Duration_instHMulInt__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Duration_instHAddPlainTime___closed__0_value:
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
    m_fun: l_Std_Time_Duration_instHAddPlainTime___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_Duration_instHAddPlainTime___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Duration_instHAddPlainTime___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Duration_instHAddPlainTime: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Duration_instHAddPlainTime___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Duration_instHSubPlainTime___closed__0_value:
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
    m_fun: l_Std_Time_Duration_instHSubPlainTime___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_Duration_instHSubPlainTime___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Duration_instHSubPlainTime___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_Duration_instHSubPlainTime: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Duration_instHSubPlainTime___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Nat_cast___at___00Std_Time_instReprDuration_repr_spec__0(
    mut v_a_782_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_783_ = lean_nat_to_int(v_a_782_);
    return v___x_783_;
}
pub unsafe fn _init_l_Std_Time_instReprDuration_repr___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_797_ = crate::leanh::lean_unsigned_to_nat(10);
    v___x_798_ = lean_nat_to_int(v___x_797_);
    return v___x_798_;
}
pub unsafe fn _init_l_Std_Time_instReprDuration_repr___redArg___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_805_ = crate::leanh::lean_unsigned_to_nat(8);
    v___x_806_ = lean_nat_to_int(v___x_805_);
    return v___x_806_;
}
pub unsafe fn _init_l_Std_Time_instReprDuration_repr___redArg___closed__18()
-> *mut crate::leanh::LeanObject {
    let mut v___x_814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_814_ = l_Std_Time_instReprDuration_repr___redArg___closed__0;
    v___x_815_ = lean_string_length(v___x_814_);
    return v___x_815_;
}
pub unsafe fn _init_l_Std_Time_instReprDuration_repr___redArg___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_816_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprDuration_repr___redArg___closed__18),
        core::ptr::addr_of_mut!(l_Std_Time_instReprDuration_repr___redArg___closed__18_once),
        _init_l_Std_Time_instReprDuration_repr___redArg___closed__18,
    );
    v___x_817_ = lean_nat_to_int(v___x_816_);
    return v___x_817_;
}
pub unsafe fn l_Std_Time_instReprDuration_repr___redArg(
    mut v_x_822_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_second_823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_827_: u8 = 0;
    let mut v___x_828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_835_: u8 = 0;
    let mut v___x_836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_865_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_second_823_ = crate::leanh::lean_ctor_get(v_x_822_, 0);
                v_nano_824_ = crate::leanh::lean_ctor_get(v_x_822_, 1);
                v_isSharedCheck_865_ = (!crate::leanh::lean_is_exclusive(v_x_822_)) as u8;
                if v_isSharedCheck_865_ == 0 {
                    v___x_826_ = v_x_822_;
                    v_isShared_827_ = v_isSharedCheck_865_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nano_824_);
                    crate::leanh::lean_inc(v_second_823_);
                    crate::leanh::lean_dec(v_x_822_);
                    v___x_826_ = crate::leanh::lean_box(0);
                    v_isShared_827_ = v_isSharedCheck_865_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_828_ = l_Std_Time_instReprDuration_repr___redArg___closed__5;
                v___x_829_ = l_Std_Time_instReprDuration_repr___redArg___closed__6;
                v___x_830_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_instReprDuration_repr___redArg___closed__7),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprDuration_repr___redArg___closed__7_once
                    ),
                    _init_l_Std_Time_instReprDuration_repr___redArg___closed__7,
                );
                v___x_831_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_832_ = l_Std_Time_Second_instReprOffset___lam__0(v_second_823_, v___x_831_);
                crate::leanh::lean_dec(v_second_823_);
                if v_isShared_827_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_826_, 4);
                    crate::leanh::lean_ctor_set(v___x_826_, 1, v___x_832_);
                    crate::leanh::lean_ctor_set(v___x_826_, 0, v___x_830_);
                    v___x_834_ = v___x_826_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_864_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_864_, 0, v___x_830_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_864_, 1, v___x_832_);
                    v___x_834_ = v_reuseFailAlloc_864_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_835_ = 0;
                v___x_836_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_836_, 0, v___x_834_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_836_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_835_,
                );
                v___x_837_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_837_, 0, v___x_829_);
                crate::leanh::lean_ctor_set(v___x_837_, 1, v___x_836_);
                v___x_838_ = l_Std_Time_instReprDuration_repr___redArg___closed__9;
                v___x_839_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_839_, 0, v___x_837_);
                crate::leanh::lean_ctor_set(v___x_839_, 1, v___x_838_);
                v___x_840_ = crate::leanh::lean_box(1);
                v___x_841_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_841_, 0, v___x_839_);
                crate::leanh::lean_ctor_set(v___x_841_, 1, v___x_840_);
                v___x_842_ = l_Std_Time_instReprDuration_repr___redArg___closed__11;
                v___x_843_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_843_, 0, v___x_841_);
                crate::leanh::lean_ctor_set(v___x_843_, 1, v___x_842_);
                v___x_844_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_844_, 0, v___x_843_);
                crate::leanh::lean_ctor_set(v___x_844_, 1, v___x_828_);
                v___x_845_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_instReprDuration_repr___redArg___closed__12),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprDuration_repr___redArg___closed__12_once
                    ),
                    _init_l_Std_Time_instReprDuration_repr___redArg___closed__12,
                );
                v___x_846_ =
                    l_Std_Time_Nanosecond_instReprOrdinal___lam__0(v_nano_824_, v___x_831_);
                crate::leanh::lean_dec(v_nano_824_);
                v___x_847_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_847_, 0, v___x_845_);
                crate::leanh::lean_ctor_set(v___x_847_, 1, v___x_846_);
                v___x_848_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_848_, 0, v___x_847_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_848_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_835_,
                );
                v___x_849_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_849_, 0, v___x_844_);
                crate::leanh::lean_ctor_set(v___x_849_, 1, v___x_848_);
                v___x_850_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_850_, 0, v___x_849_);
                crate::leanh::lean_ctor_set(v___x_850_, 1, v___x_838_);
                v___x_851_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_851_, 0, v___x_850_);
                crate::leanh::lean_ctor_set(v___x_851_, 1, v___x_840_);
                v___x_852_ = l_Std_Time_instReprDuration_repr___redArg___closed__14;
                v___x_853_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_853_, 0, v___x_851_);
                crate::leanh::lean_ctor_set(v___x_853_, 1, v___x_852_);
                v___x_854_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_854_, 0, v___x_853_);
                crate::leanh::lean_ctor_set(v___x_854_, 1, v___x_828_);
                v___x_855_ = l_Std_Time_instReprDuration_repr___redArg___closed__16;
                v___x_856_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_856_, 0, v___x_854_);
                crate::leanh::lean_ctor_set(v___x_856_, 1, v___x_855_);
                v___x_857_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_instReprDuration_repr___redArg___closed__19),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprDuration_repr___redArg___closed__19_once
                    ),
                    _init_l_Std_Time_instReprDuration_repr___redArg___closed__19,
                );
                v___x_858_ = l_Std_Time_instReprDuration_repr___redArg___closed__20;
                v___x_859_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_859_, 0, v___x_858_);
                crate::leanh::lean_ctor_set(v___x_859_, 1, v___x_856_);
                v___x_860_ = l_Std_Time_instReprDuration_repr___redArg___closed__21;
                v___x_861_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_861_, 0, v___x_859_);
                crate::leanh::lean_ctor_set(v___x_861_, 1, v___x_860_);
                v___x_862_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_862_, 0, v___x_857_);
                crate::leanh::lean_ctor_set(v___x_862_, 1, v___x_861_);
                v___x_863_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_863_, 0, v___x_862_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_863_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_835_,
                );
                return v___x_863_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_instReprDuration_repr(
    mut v_x_866_: *mut crate::leanh::LeanObject,
    mut v_prec_867_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_868_ = l_Std_Time_instReprDuration_repr___redArg(v_x_866_);
    return v___x_868_;
}
pub unsafe fn l_Std_Time_instReprDuration_repr___boxed(
    mut v_x_869_: *mut crate::leanh::LeanObject,
    mut v_prec_870_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_871_ = l_Std_Time_instReprDuration_repr(v_x_869_, v_prec_870_);
    crate::leanh::lean_dec(v_prec_870_);
    return v_res_871_;
}
pub unsafe fn l_Std_Time_instDecidableEqDuration_decEq(
    mut v_x_874_: *mut crate::leanh::LeanObject,
    mut v_x_875_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_second_876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_880_: u8 = 0;
    v_second_876_ = crate::leanh::lean_ctor_get(v_x_874_, 0);
    v_nano_877_ = crate::leanh::lean_ctor_get(v_x_874_, 1);
    v_second_878_ = crate::leanh::lean_ctor_get(v_x_875_, 0);
    v_nano_879_ = crate::leanh::lean_ctor_get(v_x_875_, 1);
    v___x_880_ = lean_int_dec_eq(v_second_876_, v_second_878_);
    if v___x_880_ == 0 {
        return v___x_880_;
    } else {
        let mut v___x_881_: u8 = 0;
        v___x_881_ = lean_int_dec_eq(v_nano_877_, v_nano_879_);
        return v___x_881_;
    }
}
pub unsafe fn l_Std_Time_instDecidableEqDuration_decEq___boxed(
    mut v_x_882_: *mut crate::leanh::LeanObject,
    mut v_x_883_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_884_: u8 = 0;
    let mut v_r_885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_884_ = l_Std_Time_instDecidableEqDuration_decEq(v_x_882_, v_x_883_);
    crate::leanh::lean_dec_ref(v_x_883_);
    crate::leanh::lean_dec_ref(v_x_882_);
    v_r_885_ = crate::leanh::lean_box((v_res_884_) as usize);
    return v_r_885_;
}
pub unsafe fn l_Std_Time_instDecidableEqDuration(
    mut v_x_886_: *mut crate::leanh::LeanObject,
    mut v_x_887_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_888_: u8 = 0;
    v___x_888_ = l_Std_Time_instDecidableEqDuration_decEq(v_x_886_, v_x_887_);
    return v___x_888_;
}
pub unsafe fn l_Std_Time_instDecidableEqDuration___boxed(
    mut v_x_889_: *mut crate::leanh::LeanObject,
    mut v_x_890_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_891_: u8 = 0;
    let mut v_r_892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_891_ = l_Std_Time_instDecidableEqDuration(v_x_889_, v_x_890_);
    crate::leanh::lean_dec_ref(v_x_890_);
    crate::leanh::lean_dec_ref(v_x_889_);
    v_r_892_ = crate::leanh::lean_box((v_res_891_) as usize);
    return v_r_892_;
}
pub unsafe fn l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Std_Time_instToStringDuration_leftPad_spec__0(
    mut v_x_893_: *mut crate::leanh::LeanObject,
    mut v_x_894_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_896_: u8 = 0;
    let mut v___x_897_: u32 = 0;
    let mut v_one_898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_895_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_896_ = lean_nat_dec_eq(v_x_893_, v_zero_895_);
                if v_isZero_896_ == 1 {
                    crate::leanh::lean_dec(v_x_893_);
                    return v_x_894_;
                } else {
                    v___x_897_ = 48;
                    v_one_898_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_899_ = lean_nat_sub(v_x_893_, v_one_898_);
                    crate::leanh::lean_dec(v_x_893_);
                    v___x_900_ = lean_string_push(v_x_894_, v___x_897_);
                    v_x_893_ = v_n_899_;
                    v_x_894_ = v___x_900_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_instToStringDuration_leftPad(
    mut v_n_903_: *mut crate::leanh::LeanObject,
    mut v_s_904_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_905_ = l_Std_Time_instToStringDuration_leftPad___closed__0;
    v___x_906_ = lean_string_length(v_s_904_);
    v___x_907_ = lean_nat_sub(v_n_903_, v___x_906_);
    v___x_908_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Std_Time_instToStringDuration_leftPad_spec__0(v___x_907_, v___x_905_);
    v___x_909_ = lean_string_append(v___x_908_, v_s_904_);
    return v___x_909_;
}
pub unsafe fn l_Std_Time_instToStringDuration_leftPad___boxed(
    mut v_n_910_: *mut crate::leanh::LeanObject,
    mut v_s_911_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_912_ = l_Std_Time_instToStringDuration_leftPad(v_n_910_, v_s_911_);
    crate::leanh::lean_dec_ref(v_s_911_);
    crate::leanh::lean_dec(v_n_910_);
    return v_res_912_;
}
pub unsafe fn _init_l_Std_Time_instToStringDuration___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_914_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_915_ = lean_nat_to_int(v___x_914_);
    return v___x_915_;
}
pub unsafe fn l_Std_Time_instToStringDuration___lam__0(
    mut v_s_918_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_934_: u8 = 0;
    let mut v___x_935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_942_: u8 = 0;
    let mut v___x_943_: u8 = 0;
    let mut v___x_944_: u8 = 0;
    let mut v___x_945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_second_925_ = crate::leanh::lean_ctor_get(v_s_918_, 0);
                crate::leanh::lean_inc(v_second_925_);
                v_nano_926_ = crate::leanh::lean_ctor_get(v_s_918_, 1);
                crate::leanh::lean_inc(v_nano_926_);
                crate::leanh::lean_dec_ref(v_s_918_);
                v___x_941_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_instToStringDuration___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instToStringDuration___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_instToStringDuration___lam__0___closed__1,
                );
                v___x_942_ = lean_int_dec_lt(v___x_941_, v_second_925_);
                if v___x_942_ == 0 {
                    v___x_943_ = lean_int_dec_lt(v_second_925_, v___x_941_);
                    if v___x_943_ == 0 {
                        v___x_944_ = lean_int_dec_lt(v_nano_926_, v___x_941_);
                        if v___x_944_ == 0 {
                            v___x_945_ = l_Std_Time_instToStringDuration_leftPad___closed__0;
                            crate::leanh::lean_inc(v_nano_926_);
                            v_fst_928_ = v___x_945_;
                            v_fst_929_ = v_second_925_;
                            v_snd_930_ = v_nano_926_;
                            state = 2;
                            continue;
                        } else {
                            v___x_946_ = l_Std_Time_instToStringDuration___lam__0___closed__3;
                            v___x_947_ = lean_int_neg(v_second_925_);
                            crate::leanh::lean_dec(v_second_925_);
                            v___x_948_ = lean_int_neg(v_nano_926_);
                            v_fst_928_ = v___x_946_;
                            v_fst_929_ = v___x_947_;
                            v_snd_930_ = v___x_948_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___x_949_ = l_Std_Time_instToStringDuration___lam__0___closed__3;
                        v___x_950_ = lean_int_neg(v_second_925_);
                        crate::leanh::lean_dec(v_second_925_);
                        v___x_951_ = lean_int_neg(v_nano_926_);
                        v_fst_928_ = v___x_949_;
                        v_fst_929_ = v___x_950_;
                        v_snd_930_ = v___x_951_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_952_ = l_Std_Time_instToStringDuration_leftPad___closed__0;
                    crate::leanh::lean_inc(v_nano_926_);
                    v_fst_928_ = v___x_952_;
                    v_fst_929_ = v_second_925_;
                    v_snd_930_ = v_nano_926_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_922_ = lean_string_append(v___y_920_, v___y_921_);
                crate::leanh::lean_dec_ref(v___y_921_);
                v___x_923_ = l_Std_Time_instToStringDuration___lam__0___closed__0;
                v___x_924_ = lean_string_append(v___x_922_, v___x_923_);
                return v___x_924_;
            }
            2 => {
                v___x_931_ = l_Int_repr(v_fst_929_);
                crate::leanh::lean_dec(v_fst_929_);
                crate::leanh::lean_inc_ref(v_fst_928_);
                v___x_932_ = lean_string_append(v_fst_928_, v___x_931_);
                crate::leanh::lean_dec_ref(v___x_931_);
                v___x_933_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_instToStringDuration___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instToStringDuration___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_instToStringDuration___lam__0___closed__1,
                );
                v___x_934_ = lean_int_dec_eq(v_nano_926_, v___x_933_);
                crate::leanh::lean_dec(v_nano_926_);
                if v___x_934_ == 0 {
                    v___x_935_ = l_Std_Time_instToStringDuration___lam__0___closed__2;
                    v___x_936_ = crate::leanh::lean_unsigned_to_nat(9);
                    v___x_937_ = l_Int_repr(v_snd_930_);
                    crate::leanh::lean_dec(v_snd_930_);
                    v___x_938_ = l_Std_Time_instToStringDuration_leftPad(v___x_936_, v___x_937_);
                    crate::leanh::lean_dec_ref(v___x_937_);
                    v___x_939_ = lean_string_append(v___x_935_, v___x_938_);
                    crate::leanh::lean_dec_ref(v___x_938_);
                    v___y_920_ = v___x_932_;
                    v___y_921_ = v___x_939_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_snd_930_);
                    v___x_940_ = l_Std_Time_instToStringDuration_leftPad___closed__0;
                    v___y_920_ = v___x_932_;
                    v___y_921_ = v___x_940_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_instReprDuration__1___lam__0(
    mut v_s_955_: *mut crate::leanh::LeanObject,
    mut v___y_956_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_974_: u8 = 0;
    let mut v___x_975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_982_: u8 = 0;
    let mut v___x_983_: u8 = 0;
    let mut v___x_984_: u8 = 0;
    let mut v___x_985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_second_965_ = crate::leanh::lean_ctor_get(v_s_955_, 0);
                crate::leanh::lean_inc(v_second_965_);
                v_nano_966_ = crate::leanh::lean_ctor_get(v_s_955_, 1);
                crate::leanh::lean_inc(v_nano_966_);
                crate::leanh::lean_dec_ref(v_s_955_);
                v___x_981_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_instToStringDuration___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instToStringDuration___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_instToStringDuration___lam__0___closed__1,
                );
                v___x_982_ = lean_int_dec_lt(v___x_981_, v_second_965_);
                if v___x_982_ == 0 {
                    v___x_983_ = lean_int_dec_lt(v_second_965_, v___x_981_);
                    if v___x_983_ == 0 {
                        v___x_984_ = lean_int_dec_lt(v_nano_966_, v___x_981_);
                        if v___x_984_ == 0 {
                            v___x_985_ = l_Std_Time_instToStringDuration_leftPad___closed__0;
                            crate::leanh::lean_inc(v_nano_966_);
                            v_fst_968_ = v___x_985_;
                            v_fst_969_ = v_second_965_;
                            v_snd_970_ = v_nano_966_;
                            state = 2;
                            continue;
                        } else {
                            v___x_986_ = l_Std_Time_instToStringDuration___lam__0___closed__3;
                            v___x_987_ = lean_int_neg(v_second_965_);
                            crate::leanh::lean_dec(v_second_965_);
                            v___x_988_ = lean_int_neg(v_nano_966_);
                            v_fst_968_ = v___x_986_;
                            v_fst_969_ = v___x_987_;
                            v_snd_970_ = v___x_988_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___x_989_ = l_Std_Time_instToStringDuration___lam__0___closed__3;
                        v___x_990_ = lean_int_neg(v_second_965_);
                        crate::leanh::lean_dec(v_second_965_);
                        v___x_991_ = lean_int_neg(v_nano_966_);
                        v_fst_968_ = v___x_989_;
                        v_fst_969_ = v___x_990_;
                        v_snd_970_ = v___x_991_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_992_ = l_Std_Time_instToStringDuration_leftPad___closed__0;
                    crate::leanh::lean_inc(v_nano_966_);
                    v_fst_968_ = v___x_992_;
                    v_fst_969_ = v_second_965_;
                    v_snd_970_ = v_nano_966_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_960_ = lean_string_append(v___y_958_, v___y_959_);
                crate::leanh::lean_dec_ref(v___y_959_);
                v___x_961_ = l_Std_Time_instToStringDuration___lam__0___closed__0;
                v___x_962_ = lean_string_append(v___x_960_, v___x_961_);
                v___x_963_ = l_String_quote(v___x_962_);
                v___x_964_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_964_, 0, v___x_963_);
                return v___x_964_;
            }
            2 => {
                v___x_971_ = l_Int_repr(v_fst_969_);
                crate::leanh::lean_dec(v_fst_969_);
                crate::leanh::lean_inc_ref(v_fst_968_);
                v___x_972_ = lean_string_append(v_fst_968_, v___x_971_);
                crate::leanh::lean_dec_ref(v___x_971_);
                v___x_973_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_instToStringDuration___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instToStringDuration___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_instToStringDuration___lam__0___closed__1,
                );
                v___x_974_ = lean_int_dec_eq(v_nano_966_, v___x_973_);
                crate::leanh::lean_dec(v_nano_966_);
                if v___x_974_ == 0 {
                    v___x_975_ = l_Std_Time_instToStringDuration___lam__0___closed__2;
                    v___x_976_ = crate::leanh::lean_unsigned_to_nat(9);
                    v___x_977_ = l_Int_repr(v_snd_970_);
                    crate::leanh::lean_dec(v_snd_970_);
                    v___x_978_ = l_Std_Time_instToStringDuration_leftPad(v___x_976_, v___x_977_);
                    crate::leanh::lean_dec_ref(v___x_977_);
                    v___x_979_ = lean_string_append(v___x_975_, v___x_978_);
                    crate::leanh::lean_dec_ref(v___x_978_);
                    v___y_958_ = v___x_972_;
                    v___y_959_ = v___x_979_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_snd_970_);
                    v___x_980_ = l_Std_Time_instToStringDuration_leftPad___closed__0;
                    v___y_958_ = v___x_972_;
                    v___y_959_ = v___x_980_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_instReprDuration__1___lam__0___boxed(
    mut v_s_993_: *mut crate::leanh::LeanObject,
    mut v___y_994_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_995_ = l_Std_Time_instReprDuration__1___lam__0(v_s_993_, v___y_994_);
    crate::leanh::lean_dec(v___y_994_);
    return v_res_995_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedDuration___closed__0() -> *mut crate::leanh::LeanObject
{
    let mut v___x_998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_998_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_999_ = lean_nat_to_int(v___x_998_);
    return v___x_999_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedDuration___closed__1() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1000_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedDuration___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedDuration___closed__0_once),
        _init_l_Std_Time_instInhabitedDuration___closed__0,
    );
    v___x_1001_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1001_, 0, v___x_1000_);
    crate::leanh::lean_ctor_set(v___x_1001_, 1, v___x_1000_);
    return v___x_1001_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedDuration() -> *mut crate::leanh::LeanObject {
    let mut v___x_1002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1002_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedDuration___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedDuration___closed__1_once),
        _init_l_Std_Time_instInhabitedDuration___closed__1,
    );
    return v___x_1002_;
}
pub unsafe fn l_Std_Time_instOfNatDuration(
    mut v_n_1003_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1004_ = lean_nat_to_int(v_n_1003_);
    v___x_1005_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instToStringDuration___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_instToStringDuration___lam__0___closed__1_once),
        _init_l_Std_Time_instToStringDuration___lam__0___closed__1,
    );
    v___x_1006_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1006_, 0, v___x_1004_);
    crate::leanh::lean_ctor_set(v___x_1006_, 1, v___x_1005_);
    return v___x_1006_;
}
pub unsafe fn l_Std_Time_instOrdDuration___lam__0(
    mut v_x_1007_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_second_1008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_second_1008_ = crate::leanh::lean_ctor_get(v_x_1007_, 0);
    crate::leanh::lean_inc(v_second_1008_);
    return v_second_1008_;
}
pub unsafe fn l_Std_Time_instOrdDuration___lam__0___boxed(
    mut v_x_1009_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1010_ = l_Std_Time_instOrdDuration___lam__0(v_x_1009_);
    crate::leanh::lean_dec_ref(v_x_1009_);
    return v_res_1010_;
}
pub unsafe fn l_Std_Time_instOrdDuration___lam__1(
    mut v_x_1011_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_nano_1012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_nano_1012_ = crate::leanh::lean_ctor_get(v_x_1011_, 1);
    crate::leanh::lean_inc(v_nano_1012_);
    return v_nano_1012_;
}
pub unsafe fn l_Std_Time_instOrdDuration___lam__1___boxed(
    mut v_x_1013_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1014_ = l_Std_Time_instOrdDuration___lam__1(v_x_1013_);
    crate::leanh::lean_dec_ref(v_x_1013_);
    return v_res_1014_;
}
pub unsafe fn l_Std_Time_Duration_neg(
    mut v_duration_1029_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_second_1030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1034_: u8 = 0;
    let mut v___x_1035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1040_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_second_1030_ = crate::leanh::lean_ctor_get(v_duration_1029_, 0);
                v_nano_1031_ = crate::leanh::lean_ctor_get(v_duration_1029_, 1);
                v_isSharedCheck_1040_ = (!crate::leanh::lean_is_exclusive(v_duration_1029_)) as u8;
                if v_isSharedCheck_1040_ == 0 {
                    v___x_1033_ = v_duration_1029_;
                    v_isShared_1034_ = v_isSharedCheck_1040_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nano_1031_);
                    crate::leanh::lean_inc(v_second_1030_);
                    crate::leanh::lean_dec(v_duration_1029_);
                    v___x_1033_ = crate::leanh::lean_box(0);
                    v_isShared_1034_ = v_isSharedCheck_1040_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1035_ = lean_int_neg(v_second_1030_);
                crate::leanh::lean_dec(v_second_1030_);
                v___x_1036_ = lean_int_neg(v_nano_1031_);
                crate::leanh::lean_dec(v_nano_1031_);
                if v_isShared_1034_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1033_, 1, v___x_1036_);
                    crate::leanh::lean_ctor_set(v___x_1033_, 0, v___x_1035_);
                    v___x_1038_ = v___x_1033_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1039_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1039_, 0, v___x_1035_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1039_, 1, v___x_1036_);
                    v___x_1038_ = v_reuseFailAlloc_1039_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1038_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_Duration_ofSeconds(
    mut v_s_1041_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1042_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instToStringDuration___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_instToStringDuration___lam__0___closed__1_once),
        _init_l_Std_Time_instToStringDuration___lam__0___closed__1,
    );
    v___x_1043_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1043_, 0, v_s_1041_);
    crate::leanh::lean_ctor_set(v___x_1043_, 1, v___x_1042_);
    return v___x_1043_;
}
pub unsafe fn l_Int_cast___at___00Std_Time_Duration_ofNanoseconds_spec__1(
    mut v_a_1044_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1045_ = l_Rat_ofInt(v_a_1044_);
    return v___x_1045_;
}
pub unsafe fn _init_l_Std_Time_Duration_ofNanoseconds___closed__0() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1046_ = crate::leanh::lean_unsigned_to_nat(1000000000);
    v___x_1047_ = lean_nat_to_int(v___x_1046_);
    return v___x_1047_;
}
pub unsafe fn l_Std_Time_Duration_ofNanoseconds(
    mut v_s_1048_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1049_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Duration_ofNanoseconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Duration_ofNanoseconds___closed__0_once),
        _init_l_Std_Time_Duration_ofNanoseconds___closed__0,
    );
    v___x_1050_ = lean_int_div(v_s_1048_, v___x_1049_);
    v___x_1051_ = lean_int_mod(v_s_1048_, v___x_1049_);
    v___x_1052_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1052_, 0, v___x_1050_);
    crate::leanh::lean_ctor_set(v___x_1052_, 1, v___x_1051_);
    return v___x_1052_;
}
pub unsafe fn l_Std_Time_Duration_ofNanoseconds___boxed(
    mut v_s_1053_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1054_ = l_Std_Time_Duration_ofNanoseconds(v_s_1053_);
    crate::leanh::lean_dec(v_s_1053_);
    return v_res_1054_;
}
pub unsafe fn l_Nat_cast___at___00Std_Time_Duration_ofNanoseconds_spec__0(
    mut v_a_1055_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1056_ = lean_nat_to_int(v_a_1055_);
    v___x_1057_ = l_Rat_ofInt(v___x_1056_);
    return v___x_1057_;
}
pub unsafe fn _init_l_Std_Time_Duration_ofMillisecond___closed__0() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1058_ = crate::leanh::lean_unsigned_to_nat(1000000);
    v___x_1059_ = lean_nat_to_int(v___x_1058_);
    return v___x_1059_;
}
pub unsafe fn l_Std_Time_Duration_ofMillisecond(
    mut v_s_1060_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1061_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Duration_ofMillisecond___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Duration_ofMillisecond___closed__0_once),
        _init_l_Std_Time_Duration_ofMillisecond___closed__0,
    );
    v___x_1062_ = lean_int_mul(v_s_1060_, v___x_1061_);
    v___x_1063_ = l_Std_Time_Duration_ofNanoseconds(v___x_1062_);
    crate::leanh::lean_dec(v___x_1062_);
    return v___x_1063_;
}
pub unsafe fn l_Std_Time_Duration_ofMillisecond___boxed(
    mut v_s_1064_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1065_ = l_Std_Time_Duration_ofMillisecond(v_s_1064_);
    crate::leanh::lean_dec(v_s_1064_);
    return v_res_1065_;
}
pub unsafe fn l_Std_Time_Duration_isZero(mut v_d_1066_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v_second_1067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1070_: u8 = 0;
    v_second_1067_ = crate::leanh::lean_ctor_get(v_d_1066_, 0);
    v_nano_1068_ = crate::leanh::lean_ctor_get(v_d_1066_, 1);
    v___x_1069_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instToStringDuration___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_instToStringDuration___lam__0___closed__1_once),
        _init_l_Std_Time_instToStringDuration___lam__0___closed__1,
    );
    v___x_1070_ = lean_int_dec_eq(v_second_1067_, v___x_1069_);
    if v___x_1070_ == 0 {
        return v___x_1070_;
    } else {
        let mut v___x_1071_: u8 = 0;
        v___x_1071_ = lean_int_dec_eq(v_nano_1068_, v___x_1069_);
        return v___x_1071_;
    }
}
pub unsafe fn l_Std_Time_Duration_isZero___boxed(
    mut v_d_1072_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1073_: u8 = 0;
    let mut v_r_1074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1073_ = l_Std_Time_Duration_isZero(v_d_1072_);
    crate::leanh::lean_dec_ref(v_d_1072_);
    v_r_1074_ = crate::leanh::lean_box((v_res_1073_) as usize);
    return v_r_1074_;
}
pub unsafe fn l_Std_Time_Duration_toSeconds(
    mut v_duration_1075_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_second_1076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_second_1076_ = crate::leanh::lean_ctor_get(v_duration_1075_, 0);
    crate::leanh::lean_inc(v_second_1076_);
    return v_second_1076_;
}
pub unsafe fn l_Std_Time_Duration_toSeconds___boxed(
    mut v_duration_1077_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1078_ = l_Std_Time_Duration_toSeconds(v_duration_1077_);
    crate::leanh::lean_dec_ref(v_duration_1077_);
    return v_res_1078_;
}
pub unsafe fn _init_l_Std_Time_Duration_toMilliseconds___closed__0() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1079_ = crate::leanh::lean_unsigned_to_nat(1000);
    v___x_1080_ = lean_nat_to_int(v___x_1079_);
    return v___x_1080_;
}
pub unsafe fn l_Std_Time_Duration_toMilliseconds(
    mut v_duration_1081_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_second_1082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_millis_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_second_1082_ = crate::leanh::lean_ctor_get(v_duration_1081_, 0);
    v_nano_1083_ = crate::leanh::lean_ctor_get(v_duration_1081_, 1);
    v___x_1084_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Duration_toMilliseconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Duration_toMilliseconds___closed__0_once),
        _init_l_Std_Time_Duration_toMilliseconds___closed__0,
    );
    v___x_1085_ = lean_int_mul(v_second_1082_, v___x_1084_);
    v___x_1086_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Duration_ofMillisecond___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Duration_ofMillisecond___closed__0_once),
        _init_l_Std_Time_Duration_ofMillisecond___closed__0,
    );
    v___x_1087_ = lean_int_ediv(v_nano_1083_, v___x_1086_);
    v_millis_1088_ = lean_int_add(v___x_1085_, v___x_1087_);
    crate::leanh::lean_dec(v___x_1087_);
    crate::leanh::lean_dec(v___x_1085_);
    return v_millis_1088_;
}
pub unsafe fn l_Std_Time_Duration_toMilliseconds___boxed(
    mut v_duration_1089_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1090_ = l_Std_Time_Duration_toMilliseconds(v_duration_1089_);
    crate::leanh::lean_dec_ref(v_duration_1089_);
    return v_res_1090_;
}
pub unsafe fn l_Std_Time_Duration_toNanoseconds(
    mut v_duration_1091_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_second_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nanos_1096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_second_1092_ = crate::leanh::lean_ctor_get(v_duration_1091_, 0);
    v_nano_1093_ = crate::leanh::lean_ctor_get(v_duration_1091_, 1);
    v___x_1094_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Duration_ofNanoseconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Duration_ofNanoseconds___closed__0_once),
        _init_l_Std_Time_Duration_ofNanoseconds___closed__0,
    );
    v___x_1095_ = lean_int_mul(v_second_1092_, v___x_1094_);
    v_nanos_1096_ = lean_int_add(v___x_1095_, v_nano_1093_);
    crate::leanh::lean_dec(v___x_1095_);
    return v_nanos_1096_;
}
pub unsafe fn l_Std_Time_Duration_toNanoseconds___boxed(
    mut v_duration_1097_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1098_ = l_Std_Time_Duration_toNanoseconds(v_duration_1097_);
    crate::leanh::lean_dec_ref(v_duration_1097_);
    return v_res_1098_;
}
pub unsafe fn _init_l_Std_Time_Duration_instLE() -> *mut crate::leanh::LeanObject {
    let mut v___x_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1099_ = crate::leanh::lean_box(0);
    return v___x_1099_;
}
pub unsafe fn l_Std_Time_Duration_instDecidableLe(
    mut v_x_1100_: *mut crate::leanh::LeanObject,
    mut v_y_1101_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_second_1102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nanos_1108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nanos_1110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1111_: u8 = 0;
    v_second_1102_ = crate::leanh::lean_ctor_get(v_x_1100_, 0);
    v_nano_1103_ = crate::leanh::lean_ctor_get(v_x_1100_, 1);
    v_second_1104_ = crate::leanh::lean_ctor_get(v_y_1101_, 0);
    v_nano_1105_ = crate::leanh::lean_ctor_get(v_y_1101_, 1);
    v___x_1106_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Duration_ofNanoseconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Duration_ofNanoseconds___closed__0_once),
        _init_l_Std_Time_Duration_ofNanoseconds___closed__0,
    );
    v___x_1107_ = lean_int_mul(v_second_1102_, v___x_1106_);
    v_nanos_1108_ = lean_int_add(v___x_1107_, v_nano_1103_);
    crate::leanh::lean_dec(v___x_1107_);
    v___x_1109_ = lean_int_mul(v_second_1104_, v___x_1106_);
    v_nanos_1110_ = lean_int_add(v___x_1109_, v_nano_1105_);
    crate::leanh::lean_dec(v___x_1109_);
    v___x_1111_ = lean_int_dec_le(v_nanos_1108_, v_nanos_1110_);
    crate::leanh::lean_dec(v_nanos_1110_);
    crate::leanh::lean_dec(v_nanos_1108_);
    return v___x_1111_;
}
pub unsafe fn l_Std_Time_Duration_instDecidableLe___boxed(
    mut v_x_1112_: *mut crate::leanh::LeanObject,
    mut v_y_1113_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1114_: u8 = 0;
    let mut v_r_1115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1114_ = l_Std_Time_Duration_instDecidableLe(v_x_1112_, v_y_1113_);
    crate::leanh::lean_dec_ref(v_y_1113_);
    crate::leanh::lean_dec_ref(v_x_1112_);
    v_r_1115_ = crate::leanh::lean_box((v_res_1114_) as usize);
    return v_r_1115_;
}
pub unsafe fn _init_l_Std_Time_Duration_instLT() -> *mut crate::leanh::LeanObject {
    let mut v___x_1116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1116_ = crate::leanh::lean_box(0);
    return v___x_1116_;
}
pub unsafe fn l_Std_Time_Duration_instDecidableLt(
    mut v_x_1117_: *mut crate::leanh::LeanObject,
    mut v_y_1118_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_second_1119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_1121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nanos_1125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nanos_1127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1128_: u8 = 0;
    v_second_1119_ = crate::leanh::lean_ctor_get(v_x_1117_, 0);
    v_nano_1120_ = crate::leanh::lean_ctor_get(v_x_1117_, 1);
    v_second_1121_ = crate::leanh::lean_ctor_get(v_y_1118_, 0);
    v_nano_1122_ = crate::leanh::lean_ctor_get(v_y_1118_, 1);
    v___x_1123_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Duration_ofNanoseconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Duration_ofNanoseconds___closed__0_once),
        _init_l_Std_Time_Duration_ofNanoseconds___closed__0,
    );
    v___x_1124_ = lean_int_mul(v_second_1119_, v___x_1123_);
    v_nanos_1125_ = lean_int_add(v___x_1124_, v_nano_1120_);
    crate::leanh::lean_dec(v___x_1124_);
    v___x_1126_ = lean_int_mul(v_second_1121_, v___x_1123_);
    v_nanos_1127_ = lean_int_add(v___x_1126_, v_nano_1122_);
    crate::leanh::lean_dec(v___x_1126_);
    v___x_1128_ = lean_int_dec_lt(v_nanos_1125_, v_nanos_1127_);
    crate::leanh::lean_dec(v_nanos_1127_);
    crate::leanh::lean_dec(v_nanos_1125_);
    return v___x_1128_;
}
pub unsafe fn l_Std_Time_Duration_instDecidableLt___boxed(
    mut v_x_1129_: *mut crate::leanh::LeanObject,
    mut v_y_1130_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1131_: u8 = 0;
    let mut v_r_1132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1131_ = l_Std_Time_Duration_instDecidableLt(v_x_1129_, v_y_1130_);
    crate::leanh::lean_dec_ref(v_y_1130_);
    crate::leanh::lean_dec_ref(v_x_1129_);
    v_r_1132_ = crate::leanh::lean_box((v_res_1131_) as usize);
    return v_r_1132_;
}
pub unsafe fn _init_l_Std_Time_Duration_toMinutes___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_1133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1133_ = crate::leanh::lean_unsigned_to_nat(60);
    v___x_1134_ = lean_nat_to_int(v___x_1133_);
    return v___x_1134_;
}
pub unsafe fn l_Std_Time_Duration_toMinutes(
    mut v_tm_1135_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_second_1136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_second_1136_ = crate::leanh::lean_ctor_get(v_tm_1135_, 0);
    v___x_1137_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Duration_toMinutes___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Duration_toMinutes___closed__0_once),
        _init_l_Std_Time_Duration_toMinutes___closed__0,
    );
    v___x_1138_ = lean_int_div(v_second_1136_, v___x_1137_);
    return v___x_1138_;
}
pub unsafe fn l_Std_Time_Duration_toMinutes___boxed(
    mut v_tm_1139_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1140_ = l_Std_Time_Duration_toMinutes(v_tm_1139_);
    crate::leanh::lean_dec_ref(v_tm_1139_);
    return v_res_1140_;
}
pub unsafe fn _init_l_Std_Time_Duration_toDays___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_1141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1141_ = crate::leanh::lean_unsigned_to_nat(86400);
    v___x_1142_ = lean_nat_to_int(v___x_1141_);
    return v___x_1142_;
}
pub unsafe fn l_Std_Time_Duration_toDays(
    mut v_tm_1143_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_second_1144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_second_1144_ = crate::leanh::lean_ctor_get(v_tm_1143_, 0);
    v___x_1145_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Duration_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Duration_toDays___closed__0_once),
        _init_l_Std_Time_Duration_toDays___closed__0,
    );
    v___x_1146_ = lean_int_div(v_second_1144_, v___x_1145_);
    return v___x_1146_;
}
pub unsafe fn l_Std_Time_Duration_toDays___boxed(
    mut v_tm_1147_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1148_ = l_Std_Time_Duration_toDays(v_tm_1147_);
    crate::leanh::lean_dec_ref(v_tm_1147_);
    return v_res_1148_;
}
pub unsafe fn l_Std_Time_Duration_fromComponents(
    mut v_secs_1149_: *mut crate::leanh::LeanObject,
    mut v_nanos_1150_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1151_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Duration_ofNanoseconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Duration_ofNanoseconds___closed__0_once),
        _init_l_Std_Time_Duration_ofNanoseconds___closed__0,
    );
    v___x_1152_ = lean_int_mul(v_secs_1149_, v___x_1151_);
    v___x_1153_ = l_Std_Time_Nanosecond_Span_toOffset(v_nanos_1150_);
    v___x_1154_ = lean_int_add(v___x_1152_, v___x_1153_);
    crate::leanh::lean_dec(v___x_1153_);
    crate::leanh::lean_dec(v___x_1152_);
    v___x_1155_ = l_Std_Time_Duration_ofNanoseconds(v___x_1154_);
    crate::leanh::lean_dec(v___x_1154_);
    return v___x_1155_;
}
pub unsafe fn l_Std_Time_Duration_fromComponents___boxed(
    mut v_secs_1156_: *mut crate::leanh::LeanObject,
    mut v_nanos_1157_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1158_ = l_Std_Time_Duration_fromComponents(v_secs_1156_, v_nanos_1157_);
    crate::leanh::lean_dec(v_nanos_1157_);
    crate::leanh::lean_dec(v_secs_1156_);
    return v_res_1158_;
}
pub unsafe fn l_Std_Time_Duration_add(
    mut v_t_u2081_1159_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_1160_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_second_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_1163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_second_1161_ = crate::leanh::lean_ctor_get(v_t_u2081_1159_, 0);
    v_nano_1162_ = crate::leanh::lean_ctor_get(v_t_u2081_1159_, 1);
    v_second_1163_ = crate::leanh::lean_ctor_get(v_t_u2082_1160_, 0);
    v_nano_1164_ = crate::leanh::lean_ctor_get(v_t_u2082_1160_, 1);
    v___x_1165_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Duration_ofNanoseconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Duration_ofNanoseconds___closed__0_once),
        _init_l_Std_Time_Duration_ofNanoseconds___closed__0,
    );
    v___x_1166_ = lean_int_mul(v_second_1161_, v___x_1165_);
    v___x_1167_ = lean_int_add(v___x_1166_, v_nano_1162_);
    crate::leanh::lean_dec(v___x_1166_);
    v___x_1168_ = lean_int_mul(v_second_1163_, v___x_1165_);
    v___x_1169_ = lean_int_add(v___x_1168_, v_nano_1164_);
    crate::leanh::lean_dec(v___x_1168_);
    v___x_1170_ = lean_int_add(v___x_1167_, v___x_1169_);
    crate::leanh::lean_dec(v___x_1169_);
    crate::leanh::lean_dec(v___x_1167_);
    v___x_1171_ = l_Std_Time_Duration_ofNanoseconds(v___x_1170_);
    crate::leanh::lean_dec(v___x_1170_);
    return v___x_1171_;
}
pub unsafe fn l_Std_Time_Duration_add___boxed(
    mut v_t_u2081_1172_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_1173_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1174_ = l_Std_Time_Duration_add(v_t_u2081_1172_, v_t_u2082_1173_);
    crate::leanh::lean_dec_ref(v_t_u2082_1173_);
    crate::leanh::lean_dec_ref(v_t_u2081_1172_);
    return v_res_1174_;
}
pub unsafe fn l_Std_Time_Duration_sub(
    mut v_t_u2081_1175_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_1176_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_second_1177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_second_1177_ = crate::leanh::lean_ctor_get(v_t_u2082_1176_, 0);
    v_nano_1178_ = crate::leanh::lean_ctor_get(v_t_u2082_1176_, 1);
    v_second_1179_ = crate::leanh::lean_ctor_get(v_t_u2081_1175_, 0);
    v_nano_1180_ = crate::leanh::lean_ctor_get(v_t_u2081_1175_, 1);
    v___x_1181_ = lean_int_neg(v_second_1177_);
    v___x_1182_ = lean_int_neg(v_nano_1178_);
    v___x_1183_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Duration_ofNanoseconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Duration_ofNanoseconds___closed__0_once),
        _init_l_Std_Time_Duration_ofNanoseconds___closed__0,
    );
    v___x_1184_ = lean_int_mul(v_second_1179_, v___x_1183_);
    v___x_1185_ = lean_int_add(v___x_1184_, v_nano_1180_);
    crate::leanh::lean_dec(v___x_1184_);
    v___x_1186_ = lean_int_mul(v___x_1181_, v___x_1183_);
    crate::leanh::lean_dec(v___x_1181_);
    v___x_1187_ = lean_int_add(v___x_1186_, v___x_1182_);
    crate::leanh::lean_dec(v___x_1182_);
    crate::leanh::lean_dec(v___x_1186_);
    v___x_1188_ = lean_int_add(v___x_1185_, v___x_1187_);
    crate::leanh::lean_dec(v___x_1187_);
    crate::leanh::lean_dec(v___x_1185_);
    v___x_1189_ = l_Std_Time_Duration_ofNanoseconds(v___x_1188_);
    crate::leanh::lean_dec(v___x_1188_);
    return v___x_1189_;
}
pub unsafe fn l_Std_Time_Duration_sub___boxed(
    mut v_t_u2081_1190_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_1191_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1192_ = l_Std_Time_Duration_sub(v_t_u2081_1190_, v_t_u2082_1191_);
    crate::leanh::lean_dec_ref(v_t_u2082_1191_);
    crate::leanh::lean_dec_ref(v_t_u2081_1190_);
    return v_res_1192_;
}
pub unsafe fn l_Std_Time_Duration_addNanoseconds(
    mut v_t_1193_: *mut crate::leanh::LeanObject,
    mut v_s_1194_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_second_1195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_1198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_second_1195_ = crate::leanh::lean_ctor_get(v_t_1193_, 0);
    v_nano_1196_ = crate::leanh::lean_ctor_get(v_t_1193_, 1);
    v___x_1197_ = l_Std_Time_Duration_ofNanoseconds(v_s_1194_);
    v_second_1198_ = crate::leanh::lean_ctor_get(v___x_1197_, 0);
    crate::leanh::lean_inc(v_second_1198_);
    v_nano_1199_ = crate::leanh::lean_ctor_get(v___x_1197_, 1);
    crate::leanh::lean_inc(v_nano_1199_);
    crate::leanh::lean_dec_ref(v___x_1197_);
    v___x_1200_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Duration_ofNanoseconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Duration_ofNanoseconds___closed__0_once),
        _init_l_Std_Time_Duration_ofNanoseconds___closed__0,
    );
    v___x_1201_ = lean_int_mul(v_second_1195_, v___x_1200_);
    v___x_1202_ = lean_int_add(v___x_1201_, v_nano_1196_);
    crate::leanh::lean_dec(v___x_1201_);
    v___x_1203_ = lean_int_mul(v_second_1198_, v___x_1200_);
    crate::leanh::lean_dec(v_second_1198_);
    v___x_1204_ = lean_int_add(v___x_1203_, v_nano_1199_);
    crate::leanh::lean_dec(v_nano_1199_);
    crate::leanh::lean_dec(v___x_1203_);
    v___x_1205_ = lean_int_add(v___x_1202_, v___x_1204_);
    crate::leanh::lean_dec(v___x_1204_);
    crate::leanh::lean_dec(v___x_1202_);
    v___x_1206_ = l_Std_Time_Duration_ofNanoseconds(v___x_1205_);
    crate::leanh::lean_dec(v___x_1205_);
    return v___x_1206_;
}
pub unsafe fn l_Std_Time_Duration_addNanoseconds___boxed(
    mut v_t_1207_: *mut crate::leanh::LeanObject,
    mut v_s_1208_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1209_ = l_Std_Time_Duration_addNanoseconds(v_t_1207_, v_s_1208_);
    crate::leanh::lean_dec(v_s_1208_);
    crate::leanh::lean_dec_ref(v_t_1207_);
    return v_res_1209_;
}
pub unsafe fn l_Std_Time_Duration_addMilliseconds(
    mut v_t_1210_: *mut crate::leanh::LeanObject,
    mut v_s_1211_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_second_1212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_1217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_second_1212_ = crate::leanh::lean_ctor_get(v_t_1210_, 0);
    v_nano_1213_ = crate::leanh::lean_ctor_get(v_t_1210_, 1);
    v___x_1214_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Duration_ofMillisecond___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Duration_ofMillisecond___closed__0_once),
        _init_l_Std_Time_Duration_ofMillisecond___closed__0,
    );
    v___x_1215_ = lean_int_mul(v_s_1211_, v___x_1214_);
    v___x_1216_ = l_Std_Time_Duration_ofNanoseconds(v___x_1215_);
    crate::leanh::lean_dec(v___x_1215_);
    v_second_1217_ = crate::leanh::lean_ctor_get(v___x_1216_, 0);
    crate::leanh::lean_inc(v_second_1217_);
    v_nano_1218_ = crate::leanh::lean_ctor_get(v___x_1216_, 1);
    crate::leanh::lean_inc(v_nano_1218_);
    crate::leanh::lean_dec_ref(v___x_1216_);
    v___x_1219_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Duration_ofNanoseconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Duration_ofNanoseconds___closed__0_once),
        _init_l_Std_Time_Duration_ofNanoseconds___closed__0,
    );
    v___x_1220_ = lean_int_mul(v_second_1212_, v___x_1219_);
    v___x_1221_ = lean_int_add(v___x_1220_, v_nano_1213_);
    crate::leanh::lean_dec(v___x_1220_);
    v___x_1222_ = lean_int_mul(v_second_1217_, v___x_1219_);
    crate::leanh::lean_dec(v_second_1217_);
    v___x_1223_ = lean_int_add(v___x_1222_, v_nano_1218_);
    crate::leanh::lean_dec(v_nano_1218_);
    crate::leanh::lean_dec(v___x_1222_);
    v___x_1224_ = lean_int_add(v___x_1221_, v___x_1223_);
    crate::leanh::lean_dec(v___x_1223_);
    crate::leanh::lean_dec(v___x_1221_);
    v___x_1225_ = l_Std_Time_Duration_ofNanoseconds(v___x_1224_);
    crate::leanh::lean_dec(v___x_1224_);
    return v___x_1225_;
}
pub unsafe fn l_Std_Time_Duration_addMilliseconds___boxed(
    mut v_t_1226_: *mut crate::leanh::LeanObject,
    mut v_s_1227_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1228_ = l_Std_Time_Duration_addMilliseconds(v_t_1226_, v_s_1227_);
    crate::leanh::lean_dec(v_s_1227_);
    crate::leanh::lean_dec_ref(v_t_1226_);
    return v_res_1228_;
}
pub unsafe fn l_Std_Time_Duration_subMilliseconds(
    mut v_t_1229_: *mut crate::leanh::LeanObject,
    mut v_s_1230_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_1234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_1236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1231_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Duration_ofMillisecond___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Duration_ofMillisecond___closed__0_once),
        _init_l_Std_Time_Duration_ofMillisecond___closed__0,
    );
    v___x_1232_ = lean_int_mul(v_s_1230_, v___x_1231_);
    v___x_1233_ = l_Std_Time_Duration_ofNanoseconds(v___x_1232_);
    crate::leanh::lean_dec(v___x_1232_);
    v_second_1234_ = crate::leanh::lean_ctor_get(v___x_1233_, 0);
    crate::leanh::lean_inc(v_second_1234_);
    v_nano_1235_ = crate::leanh::lean_ctor_get(v___x_1233_, 1);
    crate::leanh::lean_inc(v_nano_1235_);
    crate::leanh::lean_dec_ref(v___x_1233_);
    v_second_1236_ = crate::leanh::lean_ctor_get(v_t_1229_, 0);
    v_nano_1237_ = crate::leanh::lean_ctor_get(v_t_1229_, 1);
    v___x_1238_ = lean_int_neg(v_second_1234_);
    crate::leanh::lean_dec(v_second_1234_);
    v___x_1239_ = lean_int_neg(v_nano_1235_);
    crate::leanh::lean_dec(v_nano_1235_);
    v___x_1240_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Duration_ofNanoseconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Duration_ofNanoseconds___closed__0_once),
        _init_l_Std_Time_Duration_ofNanoseconds___closed__0,
    );
    v___x_1241_ = lean_int_mul(v_second_1236_, v___x_1240_);
    v___x_1242_ = lean_int_add(v___x_1241_, v_nano_1237_);
    crate::leanh::lean_dec(v___x_1241_);
    v___x_1243_ = lean_int_mul(v___x_1238_, v___x_1240_);
    crate::leanh::lean_dec(v___x_1238_);
    v___x_1244_ = lean_int_add(v___x_1243_, v___x_1239_);
    crate::leanh::lean_dec(v___x_1239_);
    crate::leanh::lean_dec(v___x_1243_);
    v___x_1245_ = lean_int_add(v___x_1242_, v___x_1244_);
    crate::leanh::lean_dec(v___x_1244_);
    crate::leanh::lean_dec(v___x_1242_);
    v___x_1246_ = l_Std_Time_Duration_ofNanoseconds(v___x_1245_);
    crate::leanh::lean_dec(v___x_1245_);
    return v___x_1246_;
}
pub unsafe fn l_Std_Time_Duration_subMilliseconds___boxed(
    mut v_t_1247_: *mut crate::leanh::LeanObject,
    mut v_s_1248_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1249_ = l_Std_Time_Duration_subMilliseconds(v_t_1247_, v_s_1248_);
    crate::leanh::lean_dec(v_s_1248_);
    crate::leanh::lean_dec_ref(v_t_1247_);
    return v_res_1249_;
}
pub unsafe fn l_Std_Time_Duration_subNanoseconds(
    mut v_t_1250_: *mut crate::leanh::LeanObject,
    mut v_s_1251_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1252_ = l_Std_Time_Duration_ofNanoseconds(v_s_1251_);
    v_second_1253_ = crate::leanh::lean_ctor_get(v___x_1252_, 0);
    crate::leanh::lean_inc(v_second_1253_);
    v_nano_1254_ = crate::leanh::lean_ctor_get(v___x_1252_, 1);
    crate::leanh::lean_inc(v_nano_1254_);
    crate::leanh::lean_dec_ref(v___x_1252_);
    v_second_1255_ = crate::leanh::lean_ctor_get(v_t_1250_, 0);
    v_nano_1256_ = crate::leanh::lean_ctor_get(v_t_1250_, 1);
    v___x_1257_ = lean_int_neg(v_second_1253_);
    crate::leanh::lean_dec(v_second_1253_);
    v___x_1258_ = lean_int_neg(v_nano_1254_);
    crate::leanh::lean_dec(v_nano_1254_);
    v___x_1259_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Duration_ofNanoseconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Duration_ofNanoseconds___closed__0_once),
        _init_l_Std_Time_Duration_ofNanoseconds___closed__0,
    );
    v___x_1260_ = lean_int_mul(v_second_1255_, v___x_1259_);
    v___x_1261_ = lean_int_add(v___x_1260_, v_nano_1256_);
    crate::leanh::lean_dec(v___x_1260_);
    v___x_1262_ = lean_int_mul(v___x_1257_, v___x_1259_);
    crate::leanh::lean_dec(v___x_1257_);
    v___x_1263_ = lean_int_add(v___x_1262_, v___x_1258_);
    crate::leanh::lean_dec(v___x_1258_);
    crate::leanh::lean_dec(v___x_1262_);
    v___x_1264_ = lean_int_add(v___x_1261_, v___x_1263_);
    crate::leanh::lean_dec(v___x_1263_);
    crate::leanh::lean_dec(v___x_1261_);
    v___x_1265_ = l_Std_Time_Duration_ofNanoseconds(v___x_1264_);
    crate::leanh::lean_dec(v___x_1264_);
    return v___x_1265_;
}
pub unsafe fn l_Std_Time_Duration_subNanoseconds___boxed(
    mut v_t_1266_: *mut crate::leanh::LeanObject,
    mut v_s_1267_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1268_ = l_Std_Time_Duration_subNanoseconds(v_t_1266_, v_s_1267_);
    crate::leanh::lean_dec(v_s_1267_);
    crate::leanh::lean_dec_ref(v_t_1266_);
    return v_res_1268_;
}
pub unsafe fn l_Std_Time_Duration_addSeconds(
    mut v_t_1269_: *mut crate::leanh::LeanObject,
    mut v_s_1270_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_second_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_second_1271_ = crate::leanh::lean_ctor_get(v_t_1269_, 0);
    v_nano_1272_ = crate::leanh::lean_ctor_get(v_t_1269_, 1);
    v___x_1273_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instToStringDuration___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_instToStringDuration___lam__0___closed__1_once),
        _init_l_Std_Time_instToStringDuration___lam__0___closed__1,
    );
    v___x_1274_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Duration_ofNanoseconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Duration_ofNanoseconds___closed__0_once),
        _init_l_Std_Time_Duration_ofNanoseconds___closed__0,
    );
    v___x_1275_ = lean_int_mul(v_second_1271_, v___x_1274_);
    v___x_1276_ = lean_int_add(v___x_1275_, v_nano_1272_);
    crate::leanh::lean_dec(v___x_1275_);
    v___x_1277_ = lean_int_mul(v_s_1270_, v___x_1274_);
    v___x_1278_ = lean_int_add(v___x_1277_, v___x_1273_);
    crate::leanh::lean_dec(v___x_1277_);
    v___x_1279_ = lean_int_add(v___x_1276_, v___x_1278_);
    crate::leanh::lean_dec(v___x_1278_);
    crate::leanh::lean_dec(v___x_1276_);
    v___x_1280_ = l_Std_Time_Duration_ofNanoseconds(v___x_1279_);
    crate::leanh::lean_dec(v___x_1279_);
    return v___x_1280_;
}
pub unsafe fn l_Std_Time_Duration_addSeconds___boxed(
    mut v_t_1281_: *mut crate::leanh::LeanObject,
    mut v_s_1282_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1283_ = l_Std_Time_Duration_addSeconds(v_t_1281_, v_s_1282_);
    crate::leanh::lean_dec(v_s_1282_);
    crate::leanh::lean_dec_ref(v_t_1281_);
    return v_res_1283_;
}
pub unsafe fn _init_l_Std_Time_Duration_subSeconds___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_1284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1284_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instToStringDuration___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_instToStringDuration___lam__0___closed__1_once),
        _init_l_Std_Time_instToStringDuration___lam__0___closed__1,
    );
    v___x_1285_ = lean_int_neg(v___x_1284_);
    return v___x_1285_;
}
pub unsafe fn l_Std_Time_Duration_subSeconds(
    mut v_t_1286_: *mut crate::leanh::LeanObject,
    mut v_s_1287_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_second_1288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_second_1288_ = crate::leanh::lean_ctor_get(v_t_1286_, 0);
    v_nano_1289_ = crate::leanh::lean_ctor_get(v_t_1286_, 1);
    v___x_1290_ = lean_int_neg(v_s_1287_);
    v___x_1291_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Duration_subSeconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Duration_subSeconds___closed__0_once),
        _init_l_Std_Time_Duration_subSeconds___closed__0,
    );
    v___x_1292_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Duration_ofNanoseconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Duration_ofNanoseconds___closed__0_once),
        _init_l_Std_Time_Duration_ofNanoseconds___closed__0,
    );
    v___x_1293_ = lean_int_mul(v_second_1288_, v___x_1292_);
    v___x_1294_ = lean_int_add(v___x_1293_, v_nano_1289_);
    crate::leanh::lean_dec(v___x_1293_);
    v___x_1295_ = lean_int_mul(v___x_1290_, v___x_1292_);
    crate::leanh::lean_dec(v___x_1290_);
    v___x_1296_ = lean_int_add(v___x_1295_, v___x_1291_);
    crate::leanh::lean_dec(v___x_1295_);
    v___x_1297_ = lean_int_add(v___x_1294_, v___x_1296_);
    crate::leanh::lean_dec(v___x_1296_);
    crate::leanh::lean_dec(v___x_1294_);
    v___x_1298_ = l_Std_Time_Duration_ofNanoseconds(v___x_1297_);
    crate::leanh::lean_dec(v___x_1297_);
    return v___x_1298_;
}
pub unsafe fn l_Std_Time_Duration_subSeconds___boxed(
    mut v_t_1299_: *mut crate::leanh::LeanObject,
    mut v_s_1300_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1301_ = l_Std_Time_Duration_subSeconds(v_t_1299_, v_s_1300_);
    crate::leanh::lean_dec(v_s_1300_);
    crate::leanh::lean_dec_ref(v_t_1299_);
    return v_res_1301_;
}
pub unsafe fn l_Std_Time_Duration_addMinutes(
    mut v_t_1302_: *mut crate::leanh::LeanObject,
    mut v_m_1303_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_second_1304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_seconds_1307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_second_1304_ = crate::leanh::lean_ctor_get(v_t_1302_, 0);
    v_nano_1305_ = crate::leanh::lean_ctor_get(v_t_1302_, 1);
    v___x_1306_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Duration_toMinutes___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Duration_toMinutes___closed__0_once),
        _init_l_Std_Time_Duration_toMinutes___closed__0,
    );
    v_seconds_1307_ = lean_int_mul(v_m_1303_, v___x_1306_);
    v___x_1308_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instToStringDuration___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_instToStringDuration___lam__0___closed__1_once),
        _init_l_Std_Time_instToStringDuration___lam__0___closed__1,
    );
    v___x_1309_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Duration_ofNanoseconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Duration_ofNanoseconds___closed__0_once),
        _init_l_Std_Time_Duration_ofNanoseconds___closed__0,
    );
    v___x_1310_ = lean_int_mul(v_second_1304_, v___x_1309_);
    v___x_1311_ = lean_int_add(v___x_1310_, v_nano_1305_);
    crate::leanh::lean_dec(v___x_1310_);
    v___x_1312_ = lean_int_mul(v_seconds_1307_, v___x_1309_);
    crate::leanh::lean_dec(v_seconds_1307_);
    v___x_1313_ = lean_int_add(v___x_1312_, v___x_1308_);
    crate::leanh::lean_dec(v___x_1312_);
    v___x_1314_ = lean_int_add(v___x_1311_, v___x_1313_);
    crate::leanh::lean_dec(v___x_1313_);
    crate::leanh::lean_dec(v___x_1311_);
    v___x_1315_ = l_Std_Time_Duration_ofNanoseconds(v___x_1314_);
    crate::leanh::lean_dec(v___x_1314_);
    return v___x_1315_;
}
pub unsafe fn l_Std_Time_Duration_addMinutes___boxed(
    mut v_t_1316_: *mut crate::leanh::LeanObject,
    mut v_m_1317_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1318_ = l_Std_Time_Duration_addMinutes(v_t_1316_, v_m_1317_);
    crate::leanh::lean_dec(v_m_1317_);
    crate::leanh::lean_dec_ref(v_t_1316_);
    return v_res_1318_;
}
pub unsafe fn l_Std_Time_Duration_subMinutes(
    mut v_t_1319_: *mut crate::leanh::LeanObject,
    mut v_m_1320_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_second_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_seconds_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_second_1321_ = crate::leanh::lean_ctor_get(v_t_1319_, 0);
    v_nano_1322_ = crate::leanh::lean_ctor_get(v_t_1319_, 1);
    v___x_1323_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Duration_toMinutes___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Duration_toMinutes___closed__0_once),
        _init_l_Std_Time_Duration_toMinutes___closed__0,
    );
    v_seconds_1324_ = lean_int_mul(v_m_1320_, v___x_1323_);
    v___x_1325_ = lean_int_neg(v_seconds_1324_);
    crate::leanh::lean_dec(v_seconds_1324_);
    v___x_1326_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Duration_subSeconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Duration_subSeconds___closed__0_once),
        _init_l_Std_Time_Duration_subSeconds___closed__0,
    );
    v___x_1327_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Duration_ofNanoseconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Duration_ofNanoseconds___closed__0_once),
        _init_l_Std_Time_Duration_ofNanoseconds___closed__0,
    );
    v___x_1328_ = lean_int_mul(v_second_1321_, v___x_1327_);
    v___x_1329_ = lean_int_add(v___x_1328_, v_nano_1322_);
    crate::leanh::lean_dec(v___x_1328_);
    v___x_1330_ = lean_int_mul(v___x_1325_, v___x_1327_);
    crate::leanh::lean_dec(v___x_1325_);
    v___x_1331_ = lean_int_add(v___x_1330_, v___x_1326_);
    crate::leanh::lean_dec(v___x_1330_);
    v___x_1332_ = lean_int_add(v___x_1329_, v___x_1331_);
    crate::leanh::lean_dec(v___x_1331_);
    crate::leanh::lean_dec(v___x_1329_);
    v___x_1333_ = l_Std_Time_Duration_ofNanoseconds(v___x_1332_);
    crate::leanh::lean_dec(v___x_1332_);
    return v___x_1333_;
}
pub unsafe fn l_Std_Time_Duration_subMinutes___boxed(
    mut v_t_1334_: *mut crate::leanh::LeanObject,
    mut v_m_1335_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1336_ = l_Std_Time_Duration_subMinutes(v_t_1334_, v_m_1335_);
    crate::leanh::lean_dec(v_m_1335_);
    crate::leanh::lean_dec_ref(v_t_1334_);
    return v_res_1336_;
}
pub unsafe fn _init_l_Std_Time_Duration_addHours___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1337_ = crate::leanh::lean_unsigned_to_nat(3600);
    v___x_1338_ = lean_nat_to_int(v___x_1337_);
    return v___x_1338_;
}
pub unsafe fn l_Std_Time_Duration_addHours(
    mut v_t_1339_: *mut crate::leanh::LeanObject,
    mut v_h_1340_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_second_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_seconds_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_second_1341_ = crate::leanh::lean_ctor_get(v_t_1339_, 0);
    v_nano_1342_ = crate::leanh::lean_ctor_get(v_t_1339_, 1);
    v___x_1343_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Duration_addHours___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Duration_addHours___closed__0_once),
        _init_l_Std_Time_Duration_addHours___closed__0,
    );
    v_seconds_1344_ = lean_int_mul(v_h_1340_, v___x_1343_);
    v___x_1345_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instToStringDuration___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_instToStringDuration___lam__0___closed__1_once),
        _init_l_Std_Time_instToStringDuration___lam__0___closed__1,
    );
    v___x_1346_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Duration_ofNanoseconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Duration_ofNanoseconds___closed__0_once),
        _init_l_Std_Time_Duration_ofNanoseconds___closed__0,
    );
    v___x_1347_ = lean_int_mul(v_second_1341_, v___x_1346_);
    v___x_1348_ = lean_int_add(v___x_1347_, v_nano_1342_);
    crate::leanh::lean_dec(v___x_1347_);
    v___x_1349_ = lean_int_mul(v_seconds_1344_, v___x_1346_);
    crate::leanh::lean_dec(v_seconds_1344_);
    v___x_1350_ = lean_int_add(v___x_1349_, v___x_1345_);
    crate::leanh::lean_dec(v___x_1349_);
    v___x_1351_ = lean_int_add(v___x_1348_, v___x_1350_);
    crate::leanh::lean_dec(v___x_1350_);
    crate::leanh::lean_dec(v___x_1348_);
    v___x_1352_ = l_Std_Time_Duration_ofNanoseconds(v___x_1351_);
    crate::leanh::lean_dec(v___x_1351_);
    return v___x_1352_;
}
pub unsafe fn l_Std_Time_Duration_addHours___boxed(
    mut v_t_1353_: *mut crate::leanh::LeanObject,
    mut v_h_1354_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1355_ = l_Std_Time_Duration_addHours(v_t_1353_, v_h_1354_);
    crate::leanh::lean_dec(v_h_1354_);
    crate::leanh::lean_dec_ref(v_t_1353_);
    return v_res_1355_;
}
pub unsafe fn l_Std_Time_Duration_subHours(
    mut v_t_1356_: *mut crate::leanh::LeanObject,
    mut v_h_1357_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_second_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_seconds_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_second_1358_ = crate::leanh::lean_ctor_get(v_t_1356_, 0);
    v_nano_1359_ = crate::leanh::lean_ctor_get(v_t_1356_, 1);
    v___x_1360_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Duration_addHours___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Duration_addHours___closed__0_once),
        _init_l_Std_Time_Duration_addHours___closed__0,
    );
    v_seconds_1361_ = lean_int_mul(v_h_1357_, v___x_1360_);
    v___x_1362_ = lean_int_neg(v_seconds_1361_);
    crate::leanh::lean_dec(v_seconds_1361_);
    v___x_1363_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Duration_subSeconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Duration_subSeconds___closed__0_once),
        _init_l_Std_Time_Duration_subSeconds___closed__0,
    );
    v___x_1364_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Duration_ofNanoseconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Duration_ofNanoseconds___closed__0_once),
        _init_l_Std_Time_Duration_ofNanoseconds___closed__0,
    );
    v___x_1365_ = lean_int_mul(v_second_1358_, v___x_1364_);
    v___x_1366_ = lean_int_add(v___x_1365_, v_nano_1359_);
    crate::leanh::lean_dec(v___x_1365_);
    v___x_1367_ = lean_int_mul(v___x_1362_, v___x_1364_);
    crate::leanh::lean_dec(v___x_1362_);
    v___x_1368_ = lean_int_add(v___x_1367_, v___x_1363_);
    crate::leanh::lean_dec(v___x_1367_);
    v___x_1369_ = lean_int_add(v___x_1366_, v___x_1368_);
    crate::leanh::lean_dec(v___x_1368_);
    crate::leanh::lean_dec(v___x_1366_);
    v___x_1370_ = l_Std_Time_Duration_ofNanoseconds(v___x_1369_);
    crate::leanh::lean_dec(v___x_1369_);
    return v___x_1370_;
}
pub unsafe fn l_Std_Time_Duration_subHours___boxed(
    mut v_t_1371_: *mut crate::leanh::LeanObject,
    mut v_h_1372_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1373_ = l_Std_Time_Duration_subHours(v_t_1371_, v_h_1372_);
    crate::leanh::lean_dec(v_h_1372_);
    crate::leanh::lean_dec_ref(v_t_1371_);
    return v_res_1373_;
}
pub unsafe fn l_Std_Time_Duration_addDays(
    mut v_t_1374_: *mut crate::leanh::LeanObject,
    mut v_d_1375_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_second_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_seconds_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_second_1376_ = crate::leanh::lean_ctor_get(v_t_1374_, 0);
    v_nano_1377_ = crate::leanh::lean_ctor_get(v_t_1374_, 1);
    v___x_1378_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Duration_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Duration_toDays___closed__0_once),
        _init_l_Std_Time_Duration_toDays___closed__0,
    );
    v_seconds_1379_ = lean_int_mul(v_d_1375_, v___x_1378_);
    v___x_1380_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instToStringDuration___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_instToStringDuration___lam__0___closed__1_once),
        _init_l_Std_Time_instToStringDuration___lam__0___closed__1,
    );
    v___x_1381_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Duration_ofNanoseconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Duration_ofNanoseconds___closed__0_once),
        _init_l_Std_Time_Duration_ofNanoseconds___closed__0,
    );
    v___x_1382_ = lean_int_mul(v_second_1376_, v___x_1381_);
    v___x_1383_ = lean_int_add(v___x_1382_, v_nano_1377_);
    crate::leanh::lean_dec(v___x_1382_);
    v___x_1384_ = lean_int_mul(v_seconds_1379_, v___x_1381_);
    crate::leanh::lean_dec(v_seconds_1379_);
    v___x_1385_ = lean_int_add(v___x_1384_, v___x_1380_);
    crate::leanh::lean_dec(v___x_1384_);
    v___x_1386_ = lean_int_add(v___x_1383_, v___x_1385_);
    crate::leanh::lean_dec(v___x_1385_);
    crate::leanh::lean_dec(v___x_1383_);
    v___x_1387_ = l_Std_Time_Duration_ofNanoseconds(v___x_1386_);
    crate::leanh::lean_dec(v___x_1386_);
    return v___x_1387_;
}
pub unsafe fn l_Std_Time_Duration_addDays___boxed(
    mut v_t_1388_: *mut crate::leanh::LeanObject,
    mut v_d_1389_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1390_ = l_Std_Time_Duration_addDays(v_t_1388_, v_d_1389_);
    crate::leanh::lean_dec(v_d_1389_);
    crate::leanh::lean_dec_ref(v_t_1388_);
    return v_res_1390_;
}
pub unsafe fn l_Std_Time_Duration_subDays(
    mut v_t_1391_: *mut crate::leanh::LeanObject,
    mut v_d_1392_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_second_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_seconds_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_second_1393_ = crate::leanh::lean_ctor_get(v_t_1391_, 0);
    v_nano_1394_ = crate::leanh::lean_ctor_get(v_t_1391_, 1);
    v___x_1395_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Duration_toDays___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Duration_toDays___closed__0_once),
        _init_l_Std_Time_Duration_toDays___closed__0,
    );
    v_seconds_1396_ = lean_int_mul(v_d_1392_, v___x_1395_);
    v___x_1397_ = lean_int_neg(v_seconds_1396_);
    crate::leanh::lean_dec(v_seconds_1396_);
    v___x_1398_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Duration_subSeconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Duration_subSeconds___closed__0_once),
        _init_l_Std_Time_Duration_subSeconds___closed__0,
    );
    v___x_1399_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Duration_ofNanoseconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Duration_ofNanoseconds___closed__0_once),
        _init_l_Std_Time_Duration_ofNanoseconds___closed__0,
    );
    v___x_1400_ = lean_int_mul(v_second_1393_, v___x_1399_);
    v___x_1401_ = lean_int_add(v___x_1400_, v_nano_1394_);
    crate::leanh::lean_dec(v___x_1400_);
    v___x_1402_ = lean_int_mul(v___x_1397_, v___x_1399_);
    crate::leanh::lean_dec(v___x_1397_);
    v___x_1403_ = lean_int_add(v___x_1402_, v___x_1398_);
    crate::leanh::lean_dec(v___x_1402_);
    v___x_1404_ = lean_int_add(v___x_1401_, v___x_1403_);
    crate::leanh::lean_dec(v___x_1403_);
    crate::leanh::lean_dec(v___x_1401_);
    v___x_1405_ = l_Std_Time_Duration_ofNanoseconds(v___x_1404_);
    crate::leanh::lean_dec(v___x_1404_);
    return v___x_1405_;
}
pub unsafe fn l_Std_Time_Duration_subDays___boxed(
    mut v_t_1406_: *mut crate::leanh::LeanObject,
    mut v_d_1407_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1408_ = l_Std_Time_Duration_subDays(v_t_1406_, v_d_1407_);
    crate::leanh::lean_dec(v_d_1407_);
    crate::leanh::lean_dec_ref(v_t_1406_);
    return v_res_1408_;
}
pub unsafe fn _init_l_Std_Time_Duration_addWeeks___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1409_ = crate::leanh::lean_unsigned_to_nat(604800);
    v___x_1410_ = lean_nat_to_int(v___x_1409_);
    return v___x_1410_;
}
pub unsafe fn l_Std_Time_Duration_addWeeks(
    mut v_t_1411_: *mut crate::leanh::LeanObject,
    mut v_w_1412_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_second_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_seconds_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_second_1413_ = crate::leanh::lean_ctor_get(v_t_1411_, 0);
    v_nano_1414_ = crate::leanh::lean_ctor_get(v_t_1411_, 1);
    v___x_1415_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Duration_addWeeks___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Duration_addWeeks___closed__0_once),
        _init_l_Std_Time_Duration_addWeeks___closed__0,
    );
    v_seconds_1416_ = lean_int_mul(v_w_1412_, v___x_1415_);
    v___x_1417_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instToStringDuration___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_instToStringDuration___lam__0___closed__1_once),
        _init_l_Std_Time_instToStringDuration___lam__0___closed__1,
    );
    v___x_1418_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Duration_ofNanoseconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Duration_ofNanoseconds___closed__0_once),
        _init_l_Std_Time_Duration_ofNanoseconds___closed__0,
    );
    v___x_1419_ = lean_int_mul(v_second_1413_, v___x_1418_);
    v___x_1420_ = lean_int_add(v___x_1419_, v_nano_1414_);
    crate::leanh::lean_dec(v___x_1419_);
    v___x_1421_ = lean_int_mul(v_seconds_1416_, v___x_1418_);
    crate::leanh::lean_dec(v_seconds_1416_);
    v___x_1422_ = lean_int_add(v___x_1421_, v___x_1417_);
    crate::leanh::lean_dec(v___x_1421_);
    v___x_1423_ = lean_int_add(v___x_1420_, v___x_1422_);
    crate::leanh::lean_dec(v___x_1422_);
    crate::leanh::lean_dec(v___x_1420_);
    v___x_1424_ = l_Std_Time_Duration_ofNanoseconds(v___x_1423_);
    crate::leanh::lean_dec(v___x_1423_);
    return v___x_1424_;
}
pub unsafe fn l_Std_Time_Duration_addWeeks___boxed(
    mut v_t_1425_: *mut crate::leanh::LeanObject,
    mut v_w_1426_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1427_ = l_Std_Time_Duration_addWeeks(v_t_1425_, v_w_1426_);
    crate::leanh::lean_dec(v_w_1426_);
    crate::leanh::lean_dec_ref(v_t_1425_);
    return v_res_1427_;
}
pub unsafe fn l_Std_Time_Duration_subWeeks(
    mut v_t_1428_: *mut crate::leanh::LeanObject,
    mut v_w_1429_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_second_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_seconds_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_second_1430_ = crate::leanh::lean_ctor_get(v_t_1428_, 0);
    v_nano_1431_ = crate::leanh::lean_ctor_get(v_t_1428_, 1);
    v___x_1432_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Duration_addWeeks___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Duration_addWeeks___closed__0_once),
        _init_l_Std_Time_Duration_addWeeks___closed__0,
    );
    v_seconds_1433_ = lean_int_mul(v_w_1429_, v___x_1432_);
    v___x_1434_ = lean_int_neg(v_seconds_1433_);
    crate::leanh::lean_dec(v_seconds_1433_);
    v___x_1435_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Duration_subSeconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Duration_subSeconds___closed__0_once),
        _init_l_Std_Time_Duration_subSeconds___closed__0,
    );
    v___x_1436_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Duration_ofNanoseconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Duration_ofNanoseconds___closed__0_once),
        _init_l_Std_Time_Duration_ofNanoseconds___closed__0,
    );
    v___x_1437_ = lean_int_mul(v_second_1430_, v___x_1436_);
    v___x_1438_ = lean_int_add(v___x_1437_, v_nano_1431_);
    crate::leanh::lean_dec(v___x_1437_);
    v___x_1439_ = lean_int_mul(v___x_1434_, v___x_1436_);
    crate::leanh::lean_dec(v___x_1434_);
    v___x_1440_ = lean_int_add(v___x_1439_, v___x_1435_);
    crate::leanh::lean_dec(v___x_1439_);
    v___x_1441_ = lean_int_add(v___x_1438_, v___x_1440_);
    crate::leanh::lean_dec(v___x_1440_);
    crate::leanh::lean_dec(v___x_1438_);
    v___x_1442_ = l_Std_Time_Duration_ofNanoseconds(v___x_1441_);
    crate::leanh::lean_dec(v___x_1441_);
    return v___x_1442_;
}
pub unsafe fn l_Std_Time_Duration_subWeeks___boxed(
    mut v_t_1443_: *mut crate::leanh::LeanObject,
    mut v_w_1444_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1445_ = l_Std_Time_Duration_subWeeks(v_t_1443_, v_w_1444_);
    crate::leanh::lean_dec(v_w_1444_);
    crate::leanh::lean_dec_ref(v_t_1443_);
    return v_res_1445_;
}
pub unsafe fn l_Std_Time_Duration_instHMulInt___lam__0(
    mut v_i_1505_: *mut crate::leanh::LeanObject,
    mut v_d_1506_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_second_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_second_1507_ = crate::leanh::lean_ctor_get(v_d_1506_, 0);
    v_nano_1508_ = crate::leanh::lean_ctor_get(v_d_1506_, 1);
    v___x_1509_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Duration_ofNanoseconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Duration_ofNanoseconds___closed__0_once),
        _init_l_Std_Time_Duration_ofNanoseconds___closed__0,
    );
    v___x_1510_ = lean_int_mul(v_second_1507_, v___x_1509_);
    v___x_1511_ = lean_int_add(v___x_1510_, v_nano_1508_);
    crate::leanh::lean_dec(v___x_1510_);
    v___x_1512_ = lean_int_mul(v___x_1511_, v_i_1505_);
    crate::leanh::lean_dec(v___x_1511_);
    v___x_1513_ = l_Std_Time_Duration_ofNanoseconds(v___x_1512_);
    crate::leanh::lean_dec(v___x_1512_);
    return v___x_1513_;
}
pub unsafe fn l_Std_Time_Duration_instHMulInt___lam__0___boxed(
    mut v_i_1514_: *mut crate::leanh::LeanObject,
    mut v_d_1515_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1516_ = l_Std_Time_Duration_instHMulInt___lam__0(v_i_1514_, v_d_1515_);
    crate::leanh::lean_dec_ref(v_d_1515_);
    crate::leanh::lean_dec(v_i_1514_);
    return v_res_1516_;
}
pub unsafe fn l_Std_Time_Duration_instHMulInt__1___lam__0(
    mut v_d_1519_: *mut crate::leanh::LeanObject,
    mut v_i_1520_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_second_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_second_1521_ = crate::leanh::lean_ctor_get(v_d_1519_, 0);
    v_nano_1522_ = crate::leanh::lean_ctor_get(v_d_1519_, 1);
    v___x_1523_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Duration_ofNanoseconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Duration_ofNanoseconds___closed__0_once),
        _init_l_Std_Time_Duration_ofNanoseconds___closed__0,
    );
    v___x_1524_ = lean_int_mul(v_second_1521_, v___x_1523_);
    v___x_1525_ = lean_int_add(v___x_1524_, v_nano_1522_);
    crate::leanh::lean_dec(v___x_1524_);
    v___x_1526_ = lean_int_mul(v___x_1525_, v_i_1520_);
    crate::leanh::lean_dec(v___x_1525_);
    v___x_1527_ = l_Std_Time_Duration_ofNanoseconds(v___x_1526_);
    crate::leanh::lean_dec(v___x_1526_);
    return v___x_1527_;
}
pub unsafe fn l_Std_Time_Duration_instHMulInt__1___lam__0___boxed(
    mut v_d_1528_: *mut crate::leanh::LeanObject,
    mut v_i_1529_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1530_ = l_Std_Time_Duration_instHMulInt__1___lam__0(v_d_1528_, v_i_1529_);
    crate::leanh::lean_dec(v_i_1529_);
    crate::leanh::lean_dec_ref(v_d_1528_);
    return v_res_1530_;
}
pub unsafe fn l_Std_Time_Duration_instHAddPlainTime___lam__0(
    mut v_pt_1533_: *mut crate::leanh::LeanObject,
    mut v_d_1534_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_second_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_second_1535_ = crate::leanh::lean_ctor_get(v_d_1534_, 0);
    v_nano_1536_ = crate::leanh::lean_ctor_get(v_d_1534_, 1);
    v___x_1537_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Duration_ofNanoseconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Duration_ofNanoseconds___closed__0_once),
        _init_l_Std_Time_Duration_ofNanoseconds___closed__0,
    );
    v___x_1538_ = lean_int_mul(v_second_1535_, v___x_1537_);
    v___x_1539_ = lean_int_add(v___x_1538_, v_nano_1536_);
    crate::leanh::lean_dec(v___x_1538_);
    v___x_1540_ = l_Std_Time_PlainTime_toNanoseconds(v_pt_1533_);
    v___x_1541_ = lean_int_add(v___x_1539_, v___x_1540_);
    crate::leanh::lean_dec(v___x_1540_);
    crate::leanh::lean_dec(v___x_1539_);
    v___x_1542_ = l_Std_Time_PlainTime_ofNanoseconds(v___x_1541_);
    crate::leanh::lean_dec(v___x_1541_);
    return v___x_1542_;
}
pub unsafe fn l_Std_Time_Duration_instHAddPlainTime___lam__0___boxed(
    mut v_pt_1543_: *mut crate::leanh::LeanObject,
    mut v_d_1544_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1545_ = l_Std_Time_Duration_instHAddPlainTime___lam__0(v_pt_1543_, v_d_1544_);
    crate::leanh::lean_dec_ref(v_d_1544_);
    crate::leanh::lean_dec_ref(v_pt_1543_);
    return v_res_1545_;
}
pub unsafe fn l_Std_Time_Duration_instHSubPlainTime___lam__0(
    mut v_pt_1548_: *mut crate::leanh::LeanObject,
    mut v_d_1549_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_second_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_second_1550_ = crate::leanh::lean_ctor_get(v_d_1549_, 0);
    v_nano_1551_ = crate::leanh::lean_ctor_get(v_d_1549_, 1);
    v___x_1552_ = l_Std_Time_PlainTime_toNanoseconds(v_pt_1548_);
    v___x_1553_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Duration_ofNanoseconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Duration_ofNanoseconds___closed__0_once),
        _init_l_Std_Time_Duration_ofNanoseconds___closed__0,
    );
    v___x_1554_ = lean_int_mul(v_second_1550_, v___x_1553_);
    v___x_1555_ = lean_int_add(v___x_1554_, v_nano_1551_);
    crate::leanh::lean_dec(v___x_1554_);
    v___x_1556_ = lean_int_sub(v___x_1552_, v___x_1555_);
    crate::leanh::lean_dec(v___x_1555_);
    crate::leanh::lean_dec(v___x_1552_);
    v___x_1557_ = l_Std_Time_PlainTime_ofNanoseconds(v___x_1556_);
    crate::leanh::lean_dec(v___x_1556_);
    return v___x_1557_;
}
pub unsafe fn l_Std_Time_Duration_instHSubPlainTime___lam__0___boxed(
    mut v_pt_1558_: *mut crate::leanh::LeanObject,
    mut v_d_1559_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1560_ = l_Std_Time_Duration_instHSubPlainTime___lam__0(v_pt_1558_, v_d_1559_);
    crate::leanh::lean_dec_ref(v_d_1559_);
    crate::leanh::lean_dec_ref(v_pt_1558_);
    return v_res_1560_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Time_Duration(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Time_Date(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Length(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Std_Time_instInhabitedDuration = _init_l_Std_Time_instInhabitedDuration();
    crate::leanh::lean_mark_persistent(l_Std_Time_instInhabitedDuration);
    l_Std_Time_Duration_instLE = _init_l_Std_Time_Duration_instLE();
    crate::leanh::lean_mark_persistent(l_Std_Time_Duration_instLE);
    l_Std_Time_Duration_instLT = _init_l_Std_Time_Duration_instLT();
    crate::leanh::lean_mark_persistent(l_Std_Time_Duration_instLT);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Time_Duration(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Time_Duration(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Time_Date(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Length(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Duration(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Time_Duration(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Time_Duration(builtin);
}
