// Lean compiler output
// Module: Std.Time.Zoned.ZoneRules
// Imports: Std.Time.DateTime Std.Time.Zoned.TimeZone
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_get_size, lean_array_size, lean_array_to_list,
    lean_array_uget_borrowed, lean_int_add, lean_int_dec_lt, lean_int_mul, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_nat_to_int,
    lean_string_length, lean_usize_add, lean_usize_dec_lt,
};
use crate::r#gen::Init::Data::Format::Basic::l_Std_Format_fill;
use crate::r#gen::Init::Data::Rat::Basic::l_Rat_ofInt;
use crate::r#gen::Init::Data::Repr::{l_Bool_repr___redArg, l_Repr_addAppParen, l_String_quote};
use crate::r#gen::Std::Time::DateTime::{
    initialize_Std_Time_DateTime, runtime_initialize_Std_Time_DateTime,
};
use crate::r#gen::Std::Time::Duration::{
    l_Std_Time_Duration_instDecidableLt, l_Std_Time_Duration_ofNanoseconds,
};
use crate::r#gen::Std::Time::Time::Unit::Second::{
    l_Std_Time_Second_instInhabitedOffset, l_Std_Time_Second_instReprOffset___lam__0,
};
use crate::r#gen::Std::Time::Zoned::Offset::{
    l_Std_Time_TimeZone_Offset_toIsoString, l_Std_Time_TimeZone_instReprOffset_repr___redArg,
};
use crate::r#gen::Std::Time::Zoned::TimeZone::{
    initialize_Std_Time_Zoned_TimeZone, runtime_initialize_Std_Time_Zoned_TimeZone,
};
pub static l_Std_Time_TimeZone_instReprUTLocal_repr___closed__0_value:
    leanh::LeanStringObject<29> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 29,
    m_capacity: 29,
    m_length: 28,
    m_data: [
        83, 116, 100, 46, 84, 105, 109, 101, 46, 84, 105, 109, 101, 90, 111, 110, 101, 46, 85, 84,
        76, 111, 99, 97, 108, 46, 117, 116, 0,
    ],
};
static mut l_Std_Time_TimeZone_instReprUTLocal_repr___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_instReprUTLocal_repr___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_TimeZone_instReprUTLocal_repr___closed__1_value:
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
        core::ptr::addr_of!(l_Std_Time_TimeZone_instReprUTLocal_repr___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_TimeZone_instReprUTLocal_repr___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_instReprUTLocal_repr___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_TimeZone_instReprUTLocal_repr___closed__2_value:
    leanh::LeanStringObject<32> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 32,
    m_capacity: 32,
    m_length: 31,
    m_data: [
        83, 116, 100, 46, 84, 105, 109, 101, 46, 84, 105, 109, 101, 90, 111, 110, 101, 46, 85, 84,
        76, 111, 99, 97, 108, 46, 108, 111, 99, 97, 108, 0,
    ],
};
static mut l_Std_Time_TimeZone_instReprUTLocal_repr___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_instReprUTLocal_repr___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_TimeZone_instReprUTLocal_repr___closed__3_value:
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
        core::ptr::addr_of!(l_Std_Time_TimeZone_instReprUTLocal_repr___closed__2_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_TimeZone_instReprUTLocal_repr___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_instReprUTLocal_repr___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_TimeZone_instReprUTLocal_repr___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_TimeZone_instReprUTLocal_repr___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_TimeZone_instReprUTLocal_repr___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_TimeZone_instReprUTLocal_repr___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_TimeZone_instReprUTLocal___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_TimeZone_instReprUTLocal_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_TimeZone_instReprUTLocal___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_instReprUTLocal___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_TimeZone_instReprUTLocal: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_instReprUTLocal___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_TimeZone_instInhabitedUTLocal_default: u8 = 0;
pub static mut l_Std_Time_TimeZone_instInhabitedUTLocal: u8 = 0;
pub static l_Std_Time_TimeZone_instReprStdWall_repr___closed__0_value:
    leanh::LeanStringObject<31> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 31,
    m_capacity: 31,
    m_length: 30,
    m_data: [
        83, 116, 100, 46, 84, 105, 109, 101, 46, 84, 105, 109, 101, 90, 111, 110, 101, 46, 83, 116,
        100, 87, 97, 108, 108, 46, 119, 97, 108, 108, 0,
    ],
};
static mut l_Std_Time_TimeZone_instReprStdWall_repr___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_instReprStdWall_repr___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_TimeZone_instReprStdWall_repr___closed__1_value:
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
        core::ptr::addr_of!(l_Std_Time_TimeZone_instReprStdWall_repr___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_TimeZone_instReprStdWall_repr___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_instReprStdWall_repr___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_TimeZone_instReprStdWall_repr___closed__2_value:
    leanh::LeanStringObject<35> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 35,
    m_capacity: 35,
    m_length: 34,
    m_data: [
        83, 116, 100, 46, 84, 105, 109, 101, 46, 84, 105, 109, 101, 90, 111, 110, 101, 46, 83, 116,
        100, 87, 97, 108, 108, 46, 115, 116, 97, 110, 100, 97, 114, 100, 0,
    ],
};
static mut l_Std_Time_TimeZone_instReprStdWall_repr___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_instReprStdWall_repr___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_TimeZone_instReprStdWall_repr___closed__3_value:
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
        core::ptr::addr_of!(l_Std_Time_TimeZone_instReprStdWall_repr___closed__2_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_TimeZone_instReprStdWall_repr___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_instReprStdWall_repr___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_TimeZone_instReprStdWall___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_TimeZone_instReprStdWall_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_TimeZone_instReprStdWall___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_instReprStdWall___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_TimeZone_instReprStdWall: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_instReprStdWall___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_TimeZone_instInhabitedStdWall_default: u8 = 0;
pub static mut l_Std_Time_TimeZone_instInhabitedStdWall: u8 = 0;
pub static l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__0_value:
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
static mut l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__1_value:
    leanh::LeanStringObject<10> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [103, 109, 116, 79, 102, 102, 115, 101, 116, 0],
};
static mut l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__2_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__1_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__3_value:
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
        core::ptr::addr_of!(
            l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__2_value
        ) as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__4_value:
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
static mut l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__5_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__4_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__6_value:
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
        core::ptr::addr_of!(
            l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__3_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__5_value
        ) as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__7:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__8_value:
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
    m_data: [44, 0],
};
static mut l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__8:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__9_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__8_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__9:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__10_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [105, 115, 68, 115, 116, 0],
};
static mut l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__10:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__11_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__10_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__11:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__11_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__12_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__12:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__13_value:
    leanh::LeanStringObject<13> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [97, 98, 98, 114, 101, 118, 105, 97, 116, 105, 111, 110, 0],
};
static mut l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__13:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__14_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__13_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__14:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__14_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__15_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__15:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__16_value:
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
    m_data: [119, 97, 108, 108, 0],
};
static mut l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__16:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__16_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__17_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__16_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__17:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__17_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__18_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__18:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__19_value:
    leanh::LeanStringObject<8> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [117, 116, 76, 111, 99, 97, 108, 0],
};
static mut l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__19:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__19_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__20_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__19_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__20:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__20_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__21_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__21:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__22_value:
    leanh::LeanStringObject<11> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [105, 100, 101, 110, 116, 105, 102, 105, 101, 114, 0],
};
static mut l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__22:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__22_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__23_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__22_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__23:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__23_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__24_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__24:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__25_value:
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
static mut l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__25:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__25_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__26_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__26:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__27_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__27:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__28_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__0_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__28:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__28_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__29_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__25_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__29:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__29_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_TimeZone_instReprLocalTimeType___closed__0_value:
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
    m_fun: l_Std_Time_TimeZone_instReprLocalTimeType_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_TimeZone_instReprLocalTimeType___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_instReprLocalTimeType___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_TimeZone_instReprLocalTimeType: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_instReprLocalTimeType___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__1_value:
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
static mut l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Std_Time_TimeZone_instInhabitedLocalTimeType_default:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Std_Time_TimeZone_instInhabitedLocalTimeType: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_TimeZone_instReprTransition_repr___redArg___closed__0_value:
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
    m_data: [116, 105, 109, 101, 0],
};
static mut l_Std_Time_TimeZone_instReprTransition_repr___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_instReprTransition_repr___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_TimeZone_instReprTransition_repr___redArg___closed__1_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Time_TimeZone_instReprTransition_repr___redArg___closed__0_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Time_TimeZone_instReprTransition_repr___redArg___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_instReprTransition_repr___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_TimeZone_instReprTransition_repr___redArg___closed__2_value:
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
        core::ptr::addr_of!(l_Std_Time_TimeZone_instReprTransition_repr___redArg___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_TimeZone_instReprTransition_repr___redArg___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_instReprTransition_repr___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_TimeZone_instReprTransition_repr___redArg___closed__3_value:
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
        core::ptr::addr_of!(l_Std_Time_TimeZone_instReprTransition_repr___redArg___closed__2_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__5_value
        ) as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_TimeZone_instReprTransition_repr___redArg___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_instReprTransition_repr___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_TimeZone_instReprTransition_repr___redArg___closed__4_value:
    leanh::LeanStringObject<14> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [
        108, 111, 99, 97, 108, 84, 105, 109, 101, 84, 121, 112, 101, 0,
    ],
};
static mut l_Std_Time_TimeZone_instReprTransition_repr___redArg___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_instReprTransition_repr___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_TimeZone_instReprTransition_repr___redArg___closed__5_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Time_TimeZone_instReprTransition_repr___redArg___closed__4_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Time_TimeZone_instReprTransition_repr___redArg___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_instReprTransition_repr___redArg___closed__5_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_TimeZone_instReprTransition_repr___redArg___closed__6_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_TimeZone_instReprTransition_repr___redArg___closed__6:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Time_TimeZone_instReprTransition___closed__0_value:
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
    m_fun: l_Std_Time_TimeZone_instReprTransition_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_TimeZone_instReprTransition___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_instReprTransition___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_TimeZone_instReprTransition: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_instReprTransition___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_TimeZone_instInhabitedTransition_default___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_TimeZone_instInhabitedTransition_default___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Std_Time_TimeZone_instInhabitedTransition_default: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_TimeZone_instInhabitedTransition: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__0_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [35, 91, 0]};
static mut l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__1_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 5 }, m_objs: [core::ptr::addr_of!(l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__9_value) as *mut leanh::LeanObject,((( 1 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__2_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [93, 0]};
static mut l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__2_value
) as *mut leanh::LeanObject;
static mut l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__5_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__0_value) as *mut leanh::LeanObject] };
static mut l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__5_value
) as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__6_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__2_value) as *mut leanh::LeanObject] };
static mut l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__6_value
) as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__7_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [35, 91, 93, 0]};
static mut l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__7:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__7_value
) as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__8_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__7_value) as *mut leanh::LeanObject] };
static mut l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__8:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__8_value
) as *mut leanh::LeanObject;
pub static l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__0_value:
    leanh::LeanStringObject<21> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        105, 110, 105, 116, 105, 97, 108, 76, 111, 99, 97, 108, 84, 105, 109, 101, 84, 121, 112,
        101, 0,
    ],
};
static mut l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__1_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__0_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__2_value:
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
        core::ptr::addr_of!(l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__3_value:
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
        core::ptr::addr_of!(l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__2_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__5_value
        ) as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__5_value:
    leanh::LeanStringObject<12> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [116, 114, 97, 110, 115, 105, 116, 105, 111, 110, 115, 0],
};
static mut l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__6_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__5_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__7:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Time_TimeZone_instReprZoneRules___closed__0_value:
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
    m_fun: l_Std_Time_TimeZone_instReprZoneRules_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_TimeZone_instReprZoneRules___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_instReprZoneRules___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_TimeZone_instReprZoneRules: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_instReprZoneRules___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_TimeZone_instInhabitedZoneRules_default___closed__0_value:
    leanh::LeanArrayObject<0> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Std_Time_TimeZone_instInhabitedZoneRules_default___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_instInhabitedZoneRules_default___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_TimeZone_instInhabitedZoneRules_default___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_TimeZone_instInhabitedZoneRules_default___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Std_Time_TimeZone_instInhabitedZoneRules_default: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_TimeZone_instInhabitedZoneRules: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_TimeZone_Transition_apply___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_TimeZone_Transition_apply___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_TimeZone_Transition_timezoneAt___closed__0_value:
    leanh::LeanStringObject<28> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 28,
    m_capacity: 28,
    m_length: 27,
    m_data: [
        99, 97, 110, 110, 111, 116, 32, 102, 105, 110, 100, 32, 108, 111, 99, 97, 108, 32, 116,
        105, 109, 101, 122, 111, 110, 101, 46, 0,
    ],
};
static mut l_Std_Time_TimeZone_Transition_timezoneAt___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_Transition_timezoneAt___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_TimeZone_Transition_timezoneAt___closed__1_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_TimeZone_Transition_timezoneAt___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_TimeZone_Transition_timezoneAt___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_Transition_timezoneAt___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_TimeZone_ZoneRules_fixedOffsetZone___closed__0_value:
    leanh::LeanArrayObject<0> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Std_Time_TimeZone_ZoneRules_fixedOffsetZone___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_ZoneRules_fixedOffsetZone___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_TimeZone_ZoneRules_UTC___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_TimeZone_ZoneRules_UTC___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_TimeZone_ZoneRules_UTC___closed__1_value: leanh::LeanStringObject<4> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [85, 84, 67, 0],
    };
static mut l_Std_Time_TimeZone_ZoneRules_UTC___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_ZoneRules_UTC___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_TimeZone_ZoneRules_UTC___closed__2_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_TimeZone_ZoneRules_UTC___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_TimeZone_ZoneRules_UTC___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_ZoneRules_UTC___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_TimeZone_ZoneRules_UTC___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_TimeZone_ZoneRules_UTC___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_TimeZone_ZoneRules_UTC: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Std_Time_TimeZone_UTLocal_ctorIdx(
    mut v_x_794_: u8,
) -> *mut leanh::LeanObject {
    if v_x_794_ == 0 {
        let mut v___x_795_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_795_ = leanh::lean_unsigned_to_nat(0);
        return v___x_795_;
    } else {
        let mut v___x_796_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_796_ = leanh::lean_unsigned_to_nat(1);
        return v___x_796_;
    }
}
pub unsafe fn l_Std_Time_TimeZone_UTLocal_ctorIdx___boxed(
    mut v_x_797_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_boxed_798_: u8 = 0;
    let mut v_res_799_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_798_ = (leanh::lean_unbox(v_x_797_) as u8);
    v_res_799_ = l_Std_Time_TimeZone_UTLocal_ctorIdx(v_x_boxed_798_);
    return v_res_799_;
}
pub unsafe fn l_Std_Time_TimeZone_UTLocal_toCtorIdx(
    mut v_x_800_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_801_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_801_ = l_Std_Time_TimeZone_UTLocal_ctorIdx(v_x_800_);
    return v___x_801_;
}
pub unsafe fn l_Std_Time_TimeZone_UTLocal_toCtorIdx___boxed(
    mut v_x_802_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_4__boxed_803_: u8 = 0;
    let mut v_res_804_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_803_ = (leanh::lean_unbox(v_x_802_) as u8);
    v_res_804_ = l_Std_Time_TimeZone_UTLocal_toCtorIdx(v_x_4__boxed_803_);
    return v_res_804_;
}
pub unsafe fn l_Std_Time_TimeZone_UTLocal_ctorElim___redArg(
    mut v_k_805_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_k_805_);
    return v_k_805_;
}
pub unsafe fn l_Std_Time_TimeZone_UTLocal_ctorElim___redArg___boxed(
    mut v_k_806_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_807_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_807_ = l_Std_Time_TimeZone_UTLocal_ctorElim___redArg(v_k_806_);
    leanh::lean_dec(v_k_806_);
    return v_res_807_;
}
pub unsafe fn l_Std_Time_TimeZone_UTLocal_ctorElim(
    mut v_motive_808_: *mut leanh::LeanObject,
    mut v_ctorIdx_809_: *mut leanh::LeanObject,
    mut v_t_810_: u8,
    mut v_h_811_: *mut leanh::LeanObject,
    mut v_k_812_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_k_812_);
    return v_k_812_;
}
pub unsafe fn l_Std_Time_TimeZone_UTLocal_ctorElim___boxed(
    mut v_motive_813_: *mut leanh::LeanObject,
    mut v_ctorIdx_814_: *mut leanh::LeanObject,
    mut v_t_815_: *mut leanh::LeanObject,
    mut v_h_816_: *mut leanh::LeanObject,
    mut v_k_817_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_818_: u8 = 0;
    let mut v_res_819_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_818_ = (leanh::lean_unbox(v_t_815_) as u8);
    v_res_819_ = l_Std_Time_TimeZone_UTLocal_ctorElim(
        v_motive_813_,
        v_ctorIdx_814_,
        v_t_boxed_818_,
        v_h_816_,
        v_k_817_,
    );
    leanh::lean_dec(v_k_817_);
    leanh::lean_dec(v_ctorIdx_814_);
    return v_res_819_;
}
pub unsafe fn l_Std_Time_TimeZone_UTLocal_ut_elim___redArg(
    mut v_ut_820_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_ut_820_);
    return v_ut_820_;
}
pub unsafe fn l_Std_Time_TimeZone_UTLocal_ut_elim___redArg___boxed(
    mut v_ut_821_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_822_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_822_ = l_Std_Time_TimeZone_UTLocal_ut_elim___redArg(v_ut_821_);
    leanh::lean_dec(v_ut_821_);
    return v_res_822_;
}
pub unsafe fn l_Std_Time_TimeZone_UTLocal_ut_elim(
    mut v_motive_823_: *mut leanh::LeanObject,
    mut v_t_824_: u8,
    mut v_h_825_: *mut leanh::LeanObject,
    mut v_ut_826_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_ut_826_);
    return v_ut_826_;
}
pub unsafe fn l_Std_Time_TimeZone_UTLocal_ut_elim___boxed(
    mut v_motive_827_: *mut leanh::LeanObject,
    mut v_t_828_: *mut leanh::LeanObject,
    mut v_h_829_: *mut leanh::LeanObject,
    mut v_ut_830_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_831_: u8 = 0;
    let mut v_res_832_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_831_ = (leanh::lean_unbox(v_t_828_) as u8);
    v_res_832_ =
        l_Std_Time_TimeZone_UTLocal_ut_elim(v_motive_827_, v_t_boxed_831_, v_h_829_, v_ut_830_);
    leanh::lean_dec(v_ut_830_);
    return v_res_832_;
}
pub unsafe fn l_Std_Time_TimeZone_UTLocal_local_elim___redArg(
    mut v_local_833_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_local_833_);
    return v_local_833_;
}
pub unsafe fn l_Std_Time_TimeZone_UTLocal_local_elim___redArg___boxed(
    mut v_local_834_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_835_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_835_ = l_Std_Time_TimeZone_UTLocal_local_elim___redArg(v_local_834_);
    leanh::lean_dec(v_local_834_);
    return v_res_835_;
}
pub unsafe fn l_Std_Time_TimeZone_UTLocal_local_elim(
    mut v_motive_836_: *mut leanh::LeanObject,
    mut v_t_837_: u8,
    mut v_h_838_: *mut leanh::LeanObject,
    mut v_local_839_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_local_839_);
    return v_local_839_;
}
pub unsafe fn l_Std_Time_TimeZone_UTLocal_local_elim___boxed(
    mut v_motive_840_: *mut leanh::LeanObject,
    mut v_t_841_: *mut leanh::LeanObject,
    mut v_h_842_: *mut leanh::LeanObject,
    mut v_local_843_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_844_: u8 = 0;
    let mut v_res_845_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_844_ = (leanh::lean_unbox(v_t_841_) as u8);
    v_res_845_ = l_Std_Time_TimeZone_UTLocal_local_elim(
        v_motive_840_,
        v_t_boxed_844_,
        v_h_842_,
        v_local_843_,
    );
    leanh::lean_dec(v_local_843_);
    return v_res_845_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_instReprUTLocal_repr___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_853_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_852_ = leanh::lean_unsigned_to_nat(2);
    v___x_853_ = lean_nat_to_int(v___x_852_);
    return v___x_853_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_instReprUTLocal_repr___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_855_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_854_ = leanh::lean_unsigned_to_nat(1);
    v___x_855_ = lean_nat_to_int(v___x_854_);
    return v___x_855_;
}
pub unsafe fn l_Std_Time_TimeZone_instReprUTLocal_repr(
    mut v_x_856_: u8,
    mut v_prec_857_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_862_: u8 = 0;
    let mut v___x_863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_869_: u8 = 0;
    let mut v___x_870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_873_: u8 = 0;
    let mut v___x_874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_877_: u8 = 0;
    let mut v___x_878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_x_856_ == 0 {
                    v___x_872_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_873_ = lean_nat_dec_le(v___x_872_, v_prec_857_);
                    if v___x_873_ == 0 {
                        v___x_874_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Time_TimeZone_instReprUTLocal_repr___closed__4
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Time_TimeZone_instReprUTLocal_repr___closed__4_once
                            ),
                            _init_l_Std_Time_TimeZone_instReprUTLocal_repr___closed__4,
                        );
                        v___y_859_ = v___x_874_;
                        state = 1;
                        continue;
                    } else {
                        v___x_875_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Time_TimeZone_instReprUTLocal_repr___closed__5
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Time_TimeZone_instReprUTLocal_repr___closed__5_once
                            ),
                            _init_l_Std_Time_TimeZone_instReprUTLocal_repr___closed__5,
                        );
                        v___y_859_ = v___x_875_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_876_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_877_ = lean_nat_dec_le(v___x_876_, v_prec_857_);
                    if v___x_877_ == 0 {
                        v___x_878_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Time_TimeZone_instReprUTLocal_repr___closed__4
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Time_TimeZone_instReprUTLocal_repr___closed__4_once
                            ),
                            _init_l_Std_Time_TimeZone_instReprUTLocal_repr___closed__4,
                        );
                        v___y_866_ = v___x_878_;
                        state = 2;
                        continue;
                    } else {
                        v___x_879_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Time_TimeZone_instReprUTLocal_repr___closed__5
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Time_TimeZone_instReprUTLocal_repr___closed__5_once
                            ),
                            _init_l_Std_Time_TimeZone_instReprUTLocal_repr___closed__5,
                        );
                        v___y_866_ = v___x_879_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_860_ = l_Std_Time_TimeZone_instReprUTLocal_repr___closed__1;
                leanh::lean_inc(v___y_859_);
                v___x_861_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_861_, 0, v___y_859_);
                leanh::lean_ctor_set(v___x_861_, 1, v___x_860_);
                v___x_862_ = 0;
                v___x_863_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_863_, 0, v___x_861_);
                leanh::lean_ctor_set_uint8(
                    v___x_863_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_862_,
                );
                v___x_864_ = l_Repr_addAppParen(v___x_863_, v_prec_857_);
                return v___x_864_;
            }
            2 => {
                v___x_867_ = l_Std_Time_TimeZone_instReprUTLocal_repr___closed__3;
                leanh::lean_inc(v___y_866_);
                v___x_868_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_868_, 0, v___y_866_);
                leanh::lean_ctor_set(v___x_868_, 1, v___x_867_);
                v___x_869_ = 0;
                v___x_870_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_870_, 0, v___x_868_);
                leanh::lean_ctor_set_uint8(
                    v___x_870_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_869_,
                );
                v___x_871_ = l_Repr_addAppParen(v___x_870_, v_prec_857_);
                return v___x_871_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_TimeZone_instReprUTLocal_repr___boxed(
    mut v_x_880_: *mut leanh::LeanObject,
    mut v_prec_881_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_121__boxed_882_: u8 = 0;
    let mut v_res_883_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_121__boxed_882_ = (leanh::lean_unbox(v_x_880_) as u8);
    v_res_883_ = l_Std_Time_TimeZone_instReprUTLocal_repr(v_x_121__boxed_882_, v_prec_881_);
    leanh::lean_dec(v_prec_881_);
    return v_res_883_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_instInhabitedUTLocal_default() -> u8 {
    let mut v___x_886_: u8 = 0;
    v___x_886_ = 0;
    return v___x_886_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_instInhabitedUTLocal() -> u8 {
    let mut v___x_887_: u8 = 0;
    v___x_887_ = 0;
    return v___x_887_;
}
pub unsafe fn l_Std_Time_TimeZone_StdWall_ctorIdx(
    mut v_x_888_: u8,
) -> *mut leanh::LeanObject {
    if v_x_888_ == 0 {
        let mut v___x_889_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_889_ = leanh::lean_unsigned_to_nat(0);
        return v___x_889_;
    } else {
        let mut v___x_890_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_890_ = leanh::lean_unsigned_to_nat(1);
        return v___x_890_;
    }
}
pub unsafe fn l_Std_Time_TimeZone_StdWall_ctorIdx___boxed(
    mut v_x_891_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_boxed_892_: u8 = 0;
    let mut v_res_893_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_892_ = (leanh::lean_unbox(v_x_891_) as u8);
    v_res_893_ = l_Std_Time_TimeZone_StdWall_ctorIdx(v_x_boxed_892_);
    return v_res_893_;
}
pub unsafe fn l_Std_Time_TimeZone_StdWall_toCtorIdx(
    mut v_x_894_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_895_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_895_ = l_Std_Time_TimeZone_StdWall_ctorIdx(v_x_894_);
    return v___x_895_;
}
pub unsafe fn l_Std_Time_TimeZone_StdWall_toCtorIdx___boxed(
    mut v_x_896_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_4__boxed_897_: u8 = 0;
    let mut v_res_898_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_897_ = (leanh::lean_unbox(v_x_896_) as u8);
    v_res_898_ = l_Std_Time_TimeZone_StdWall_toCtorIdx(v_x_4__boxed_897_);
    return v_res_898_;
}
pub unsafe fn l_Std_Time_TimeZone_StdWall_ctorElim___redArg(
    mut v_k_899_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_k_899_);
    return v_k_899_;
}
pub unsafe fn l_Std_Time_TimeZone_StdWall_ctorElim___redArg___boxed(
    mut v_k_900_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_901_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_901_ = l_Std_Time_TimeZone_StdWall_ctorElim___redArg(v_k_900_);
    leanh::lean_dec(v_k_900_);
    return v_res_901_;
}
pub unsafe fn l_Std_Time_TimeZone_StdWall_ctorElim(
    mut v_motive_902_: *mut leanh::LeanObject,
    mut v_ctorIdx_903_: *mut leanh::LeanObject,
    mut v_t_904_: u8,
    mut v_h_905_: *mut leanh::LeanObject,
    mut v_k_906_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_k_906_);
    return v_k_906_;
}
pub unsafe fn l_Std_Time_TimeZone_StdWall_ctorElim___boxed(
    mut v_motive_907_: *mut leanh::LeanObject,
    mut v_ctorIdx_908_: *mut leanh::LeanObject,
    mut v_t_909_: *mut leanh::LeanObject,
    mut v_h_910_: *mut leanh::LeanObject,
    mut v_k_911_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_912_: u8 = 0;
    let mut v_res_913_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_912_ = (leanh::lean_unbox(v_t_909_) as u8);
    v_res_913_ = l_Std_Time_TimeZone_StdWall_ctorElim(
        v_motive_907_,
        v_ctorIdx_908_,
        v_t_boxed_912_,
        v_h_910_,
        v_k_911_,
    );
    leanh::lean_dec(v_k_911_);
    leanh::lean_dec(v_ctorIdx_908_);
    return v_res_913_;
}
pub unsafe fn l_Std_Time_TimeZone_StdWall_wall_elim___redArg(
    mut v_wall_914_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_wall_914_);
    return v_wall_914_;
}
pub unsafe fn l_Std_Time_TimeZone_StdWall_wall_elim___redArg___boxed(
    mut v_wall_915_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_916_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_916_ = l_Std_Time_TimeZone_StdWall_wall_elim___redArg(v_wall_915_);
    leanh::lean_dec(v_wall_915_);
    return v_res_916_;
}
pub unsafe fn l_Std_Time_TimeZone_StdWall_wall_elim(
    mut v_motive_917_: *mut leanh::LeanObject,
    mut v_t_918_: u8,
    mut v_h_919_: *mut leanh::LeanObject,
    mut v_wall_920_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_wall_920_);
    return v_wall_920_;
}
pub unsafe fn l_Std_Time_TimeZone_StdWall_wall_elim___boxed(
    mut v_motive_921_: *mut leanh::LeanObject,
    mut v_t_922_: *mut leanh::LeanObject,
    mut v_h_923_: *mut leanh::LeanObject,
    mut v_wall_924_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_925_: u8 = 0;
    let mut v_res_926_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_925_ = (leanh::lean_unbox(v_t_922_) as u8);
    v_res_926_ =
        l_Std_Time_TimeZone_StdWall_wall_elim(v_motive_921_, v_t_boxed_925_, v_h_923_, v_wall_924_);
    leanh::lean_dec(v_wall_924_);
    return v_res_926_;
}
pub unsafe fn l_Std_Time_TimeZone_StdWall_standard_elim___redArg(
    mut v_standard_927_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_standard_927_);
    return v_standard_927_;
}
pub unsafe fn l_Std_Time_TimeZone_StdWall_standard_elim___redArg___boxed(
    mut v_standard_928_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_929_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_929_ = l_Std_Time_TimeZone_StdWall_standard_elim___redArg(v_standard_928_);
    leanh::lean_dec(v_standard_928_);
    return v_res_929_;
}
pub unsafe fn l_Std_Time_TimeZone_StdWall_standard_elim(
    mut v_motive_930_: *mut leanh::LeanObject,
    mut v_t_931_: u8,
    mut v_h_932_: *mut leanh::LeanObject,
    mut v_standard_933_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_standard_933_);
    return v_standard_933_;
}
pub unsafe fn l_Std_Time_TimeZone_StdWall_standard_elim___boxed(
    mut v_motive_934_: *mut leanh::LeanObject,
    mut v_t_935_: *mut leanh::LeanObject,
    mut v_h_936_: *mut leanh::LeanObject,
    mut v_standard_937_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_938_: u8 = 0;
    let mut v_res_939_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_938_ = (leanh::lean_unbox(v_t_935_) as u8);
    v_res_939_ = l_Std_Time_TimeZone_StdWall_standard_elim(
        v_motive_934_,
        v_t_boxed_938_,
        v_h_936_,
        v_standard_937_,
    );
    leanh::lean_dec(v_standard_937_);
    return v_res_939_;
}
pub unsafe fn l_Std_Time_TimeZone_instReprStdWall_repr(
    mut v_x_946_: u8,
    mut v_prec_947_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_952_: u8 = 0;
    let mut v___x_953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_959_: u8 = 0;
    let mut v___x_960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_963_: u8 = 0;
    let mut v___x_964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_967_: u8 = 0;
    let mut v___x_968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_x_946_ == 0 {
                    v___x_962_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_963_ = lean_nat_dec_le(v___x_962_, v_prec_947_);
                    if v___x_963_ == 0 {
                        v___x_964_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Time_TimeZone_instReprUTLocal_repr___closed__4
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Time_TimeZone_instReprUTLocal_repr___closed__4_once
                            ),
                            _init_l_Std_Time_TimeZone_instReprUTLocal_repr___closed__4,
                        );
                        v___y_949_ = v___x_964_;
                        state = 1;
                        continue;
                    } else {
                        v___x_965_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Time_TimeZone_instReprUTLocal_repr___closed__5
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Time_TimeZone_instReprUTLocal_repr___closed__5_once
                            ),
                            _init_l_Std_Time_TimeZone_instReprUTLocal_repr___closed__5,
                        );
                        v___y_949_ = v___x_965_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_966_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_967_ = lean_nat_dec_le(v___x_966_, v_prec_947_);
                    if v___x_967_ == 0 {
                        v___x_968_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Time_TimeZone_instReprUTLocal_repr___closed__4
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Time_TimeZone_instReprUTLocal_repr___closed__4_once
                            ),
                            _init_l_Std_Time_TimeZone_instReprUTLocal_repr___closed__4,
                        );
                        v___y_956_ = v___x_968_;
                        state = 2;
                        continue;
                    } else {
                        v___x_969_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Time_TimeZone_instReprUTLocal_repr___closed__5
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Time_TimeZone_instReprUTLocal_repr___closed__5_once
                            ),
                            _init_l_Std_Time_TimeZone_instReprUTLocal_repr___closed__5,
                        );
                        v___y_956_ = v___x_969_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_950_ = l_Std_Time_TimeZone_instReprStdWall_repr___closed__1;
                leanh::lean_inc(v___y_949_);
                v___x_951_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_951_, 0, v___y_949_);
                leanh::lean_ctor_set(v___x_951_, 1, v___x_950_);
                v___x_952_ = 0;
                v___x_953_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_953_, 0, v___x_951_);
                leanh::lean_ctor_set_uint8(
                    v___x_953_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_952_,
                );
                v___x_954_ = l_Repr_addAppParen(v___x_953_, v_prec_947_);
                return v___x_954_;
            }
            2 => {
                v___x_957_ = l_Std_Time_TimeZone_instReprStdWall_repr___closed__3;
                leanh::lean_inc(v___y_956_);
                v___x_958_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_958_, 0, v___y_956_);
                leanh::lean_ctor_set(v___x_958_, 1, v___x_957_);
                v___x_959_ = 0;
                v___x_960_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_960_, 0, v___x_958_);
                leanh::lean_ctor_set_uint8(
                    v___x_960_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_959_,
                );
                v___x_961_ = l_Repr_addAppParen(v___x_960_, v_prec_947_);
                return v___x_961_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_TimeZone_instReprStdWall_repr___boxed(
    mut v_x_970_: *mut leanh::LeanObject,
    mut v_prec_971_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_117__boxed_972_: u8 = 0;
    let mut v_res_973_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_117__boxed_972_ = (leanh::lean_unbox(v_x_970_) as u8);
    v_res_973_ = l_Std_Time_TimeZone_instReprStdWall_repr(v_x_117__boxed_972_, v_prec_971_);
    leanh::lean_dec(v_prec_971_);
    return v_res_973_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_instInhabitedStdWall_default() -> u8 {
    let mut v___x_976_: u8 = 0;
    v___x_976_ = 0;
    return v___x_976_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_instInhabitedStdWall() -> u8 {
    let mut v___x_977_: u8 = 0;
    v___x_977_ = 0;
    return v___x_977_;
}
pub unsafe fn l_Nat_cast___at___00Std_Time_TimeZone_instReprLocalTimeType_repr_spec__0(
    mut v_a_978_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_979_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_979_ = lean_nat_to_int(v_a_978_);
    return v___x_979_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_993_ = leanh::lean_unsigned_to_nat(13);
    v___x_994_ = lean_nat_to_int(v___x_993_);
    return v___x_994_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_1001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1001_ = leanh::lean_unsigned_to_nat(9);
    v___x_1002_ = lean_nat_to_int(v___x_1001_);
    return v___x_1002_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_1006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1007_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1006_ = leanh::lean_unsigned_to_nat(16);
    v___x_1007_ = lean_nat_to_int(v___x_1006_);
    return v___x_1007_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__18()
-> *mut leanh::LeanObject {
    let mut v___x_1011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1012_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1011_ = leanh::lean_unsigned_to_nat(8);
    v___x_1012_ = lean_nat_to_int(v___x_1011_);
    return v___x_1012_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__21()
-> *mut leanh::LeanObject {
    let mut v___x_1016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1017_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1016_ = leanh::lean_unsigned_to_nat(11);
    v___x_1017_ = lean_nat_to_int(v___x_1016_);
    return v___x_1017_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__24()
-> *mut leanh::LeanObject {
    let mut v___x_1021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1021_ = leanh::lean_unsigned_to_nat(14);
    v___x_1022_ = lean_nat_to_int(v___x_1021_);
    return v___x_1022_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__26()
-> *mut leanh::LeanObject {
    let mut v___x_1024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1024_ = l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__0;
    v___x_1025_ = lean_string_length(v___x_1024_);
    return v___x_1025_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__27()
-> *mut leanh::LeanObject {
    let mut v___x_1026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1027_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1026_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__26
        ),
        core::ptr::addr_of_mut!(
            l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__26_once
        ),
        _init_l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__26,
    );
    v___x_1027_ = lean_nat_to_int(v___x_1026_);
    return v___x_1027_;
}
pub unsafe fn l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg(
    mut v_x_1032_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_gmtOffset_1033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isDst_1034_: u8 = 0;
    let mut v_abbreviation_1035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_wall_1036_: u8 = 0;
    let mut v_utLocal_1037_: u8 = 0;
    let mut v_identifier_1038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1045_: u8 = 0;
    let mut v___x_1046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1051_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_1065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1076_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_1087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1093_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_1105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1108_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_gmtOffset_1033_ = leanh::lean_ctor_get(v_x_1032_, 0);
    leanh::lean_inc(v_gmtOffset_1033_);
    v_isDst_1034_ = leanh::lean_ctor_get_uint8(
        v_x_1032_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
    );
    v_abbreviation_1035_ = leanh::lean_ctor_get(v_x_1032_, 1);
    leanh::lean_inc_ref(v_abbreviation_1035_);
    v_wall_1036_ = leanh::lean_ctor_get_uint8(
        v_x_1032_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 1) as u32,
    );
    v_utLocal_1037_ = leanh::lean_ctor_get_uint8(
        v_x_1032_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 2) as u32,
    );
    v_identifier_1038_ = leanh::lean_ctor_get(v_x_1032_, 2);
    leanh::lean_inc_ref(v_identifier_1038_);
    leanh::lean_dec_ref(v_x_1032_);
    v___x_1039_ = l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__5;
    v___x_1040_ = l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__6;
    v___x_1041_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__7
        ),
        core::ptr::addr_of_mut!(
            l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__7_once
        ),
        _init_l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__7,
    );
    v___x_1042_ = leanh::lean_unsigned_to_nat(0);
    v___x_1043_ = l_Std_Time_TimeZone_instReprOffset_repr___redArg(v_gmtOffset_1033_);
    leanh::lean_dec(v_gmtOffset_1033_);
    v___x_1044_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1044_, 0, v___x_1041_);
    leanh::lean_ctor_set(v___x_1044_, 1, v___x_1043_);
    v___x_1045_ = 0;
    v___x_1046_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1046_, 0, v___x_1044_);
    leanh::lean_ctor_set_uint8(
        v___x_1046_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1045_,
    );
    v___x_1047_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1047_, 0, v___x_1040_);
    leanh::lean_ctor_set(v___x_1047_, 1, v___x_1046_);
    v___x_1048_ = l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__9;
    v___x_1049_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1049_, 0, v___x_1047_);
    leanh::lean_ctor_set(v___x_1049_, 1, v___x_1048_);
    v___x_1050_ = leanh::lean_box(1);
    v___x_1051_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1051_, 0, v___x_1049_);
    leanh::lean_ctor_set(v___x_1051_, 1, v___x_1050_);
    v___x_1052_ = l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__11;
    v___x_1053_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1053_, 0, v___x_1051_);
    leanh::lean_ctor_set(v___x_1053_, 1, v___x_1052_);
    v___x_1054_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1054_, 0, v___x_1053_);
    leanh::lean_ctor_set(v___x_1054_, 1, v___x_1039_);
    v___x_1055_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__12
        ),
        core::ptr::addr_of_mut!(
            l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__12_once
        ),
        _init_l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__12,
    );
    v___x_1056_ = l_Bool_repr___redArg(v_isDst_1034_);
    v___x_1057_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1057_, 0, v___x_1055_);
    leanh::lean_ctor_set(v___x_1057_, 1, v___x_1056_);
    v___x_1058_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1058_, 0, v___x_1057_);
    leanh::lean_ctor_set_uint8(
        v___x_1058_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1045_,
    );
    v___x_1059_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1059_, 0, v___x_1054_);
    leanh::lean_ctor_set(v___x_1059_, 1, v___x_1058_);
    v___x_1060_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1060_, 0, v___x_1059_);
    leanh::lean_ctor_set(v___x_1060_, 1, v___x_1048_);
    v___x_1061_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1061_, 0, v___x_1060_);
    leanh::lean_ctor_set(v___x_1061_, 1, v___x_1050_);
    v___x_1062_ = l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__14;
    v___x_1063_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1063_, 0, v___x_1061_);
    leanh::lean_ctor_set(v___x_1063_, 1, v___x_1062_);
    v___x_1064_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1064_, 0, v___x_1063_);
    leanh::lean_ctor_set(v___x_1064_, 1, v___x_1039_);
    v___x_1065_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__15
        ),
        core::ptr::addr_of_mut!(
            l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__15_once
        ),
        _init_l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__15,
    );
    v___x_1066_ = l_String_quote(v_abbreviation_1035_);
    v___x_1067_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1067_, 0, v___x_1066_);
    v___x_1068_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1068_, 0, v___x_1065_);
    leanh::lean_ctor_set(v___x_1068_, 1, v___x_1067_);
    v___x_1069_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1069_, 0, v___x_1068_);
    leanh::lean_ctor_set_uint8(
        v___x_1069_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1045_,
    );
    v___x_1070_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1070_, 0, v___x_1064_);
    leanh::lean_ctor_set(v___x_1070_, 1, v___x_1069_);
    v___x_1071_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1071_, 0, v___x_1070_);
    leanh::lean_ctor_set(v___x_1071_, 1, v___x_1048_);
    v___x_1072_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1072_, 0, v___x_1071_);
    leanh::lean_ctor_set(v___x_1072_, 1, v___x_1050_);
    v___x_1073_ = l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__17;
    v___x_1074_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1074_, 0, v___x_1072_);
    leanh::lean_ctor_set(v___x_1074_, 1, v___x_1073_);
    v___x_1075_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1075_, 0, v___x_1074_);
    leanh::lean_ctor_set(v___x_1075_, 1, v___x_1039_);
    v___x_1076_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__18
        ),
        core::ptr::addr_of_mut!(
            l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__18_once
        ),
        _init_l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__18,
    );
    v___x_1077_ = l_Std_Time_TimeZone_instReprStdWall_repr(v_wall_1036_, v___x_1042_);
    v___x_1078_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1078_, 0, v___x_1076_);
    leanh::lean_ctor_set(v___x_1078_, 1, v___x_1077_);
    v___x_1079_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1079_, 0, v___x_1078_);
    leanh::lean_ctor_set_uint8(
        v___x_1079_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1045_,
    );
    v___x_1080_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1080_, 0, v___x_1075_);
    leanh::lean_ctor_set(v___x_1080_, 1, v___x_1079_);
    v___x_1081_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1081_, 0, v___x_1080_);
    leanh::lean_ctor_set(v___x_1081_, 1, v___x_1048_);
    v___x_1082_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1082_, 0, v___x_1081_);
    leanh::lean_ctor_set(v___x_1082_, 1, v___x_1050_);
    v___x_1083_ = l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__20;
    v___x_1084_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1084_, 0, v___x_1082_);
    leanh::lean_ctor_set(v___x_1084_, 1, v___x_1083_);
    v___x_1085_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1085_, 0, v___x_1084_);
    leanh::lean_ctor_set(v___x_1085_, 1, v___x_1039_);
    v___x_1086_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__21
        ),
        core::ptr::addr_of_mut!(
            l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__21_once
        ),
        _init_l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__21,
    );
    v___x_1087_ = l_Std_Time_TimeZone_instReprUTLocal_repr(v_utLocal_1037_, v___x_1042_);
    v___x_1088_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1088_, 0, v___x_1086_);
    leanh::lean_ctor_set(v___x_1088_, 1, v___x_1087_);
    v___x_1089_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1089_, 0, v___x_1088_);
    leanh::lean_ctor_set_uint8(
        v___x_1089_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1045_,
    );
    v___x_1090_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1090_, 0, v___x_1085_);
    leanh::lean_ctor_set(v___x_1090_, 1, v___x_1089_);
    v___x_1091_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1091_, 0, v___x_1090_);
    leanh::lean_ctor_set(v___x_1091_, 1, v___x_1048_);
    v___x_1092_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1092_, 0, v___x_1091_);
    leanh::lean_ctor_set(v___x_1092_, 1, v___x_1050_);
    v___x_1093_ = l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__23;
    v___x_1094_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1094_, 0, v___x_1092_);
    leanh::lean_ctor_set(v___x_1094_, 1, v___x_1093_);
    v___x_1095_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1095_, 0, v___x_1094_);
    leanh::lean_ctor_set(v___x_1095_, 1, v___x_1039_);
    v___x_1096_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__24
        ),
        core::ptr::addr_of_mut!(
            l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__24_once
        ),
        _init_l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__24,
    );
    v___x_1097_ = l_String_quote(v_identifier_1038_);
    v___x_1098_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1098_, 0, v___x_1097_);
    v___x_1099_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1099_, 0, v___x_1096_);
    leanh::lean_ctor_set(v___x_1099_, 1, v___x_1098_);
    v___x_1100_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1100_, 0, v___x_1099_);
    leanh::lean_ctor_set_uint8(
        v___x_1100_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1045_,
    );
    v___x_1101_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1101_, 0, v___x_1095_);
    leanh::lean_ctor_set(v___x_1101_, 1, v___x_1100_);
    v___x_1102_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__27
        ),
        core::ptr::addr_of_mut!(
            l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__27_once
        ),
        _init_l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__27,
    );
    v___x_1103_ = l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__28;
    v___x_1104_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1104_, 0, v___x_1103_);
    leanh::lean_ctor_set(v___x_1104_, 1, v___x_1101_);
    v___x_1105_ = l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__29;
    v___x_1106_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1106_, 0, v___x_1104_);
    leanh::lean_ctor_set(v___x_1106_, 1, v___x_1105_);
    v___x_1107_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1107_, 0, v___x_1102_);
    leanh::lean_ctor_set(v___x_1107_, 1, v___x_1106_);
    v___x_1108_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1108_, 0, v___x_1107_);
    leanh::lean_ctor_set_uint8(
        v___x_1108_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1045_,
    );
    return v___x_1108_;
}
pub unsafe fn l_Std_Time_TimeZone_instReprLocalTimeType_repr(
    mut v_x_1109_: *mut leanh::LeanObject,
    mut v_prec_1110_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1111_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1111_ = l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg(v_x_1109_);
    return v___x_1111_;
}
pub unsafe fn l_Std_Time_TimeZone_instReprLocalTimeType_repr___boxed(
    mut v_x_1112_: *mut leanh::LeanObject,
    mut v_prec_1113_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1114_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1114_ = l_Std_Time_TimeZone_instReprLocalTimeType_repr(v_x_1112_, v_prec_1113_);
    leanh::lean_dec(v_prec_1113_);
    return v_res_1114_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1117_ = leanh::lean_unsigned_to_nat(0);
    v___x_1118_ = lean_nat_to_int(v___x_1117_);
    return v___x_1118_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1120_: u8 = 0;
    let mut v___x_1121_: u8 = 0;
    let mut v___x_1122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1123_: u8 = 0;
    let mut v___x_1124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1125_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1120_ = 0;
    v___x_1121_ = 0;
    v___x_1122_ = l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__1;
    v___x_1123_ = 0;
    v___x_1124_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__0),
        core::ptr::addr_of_mut!(
            l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__0_once
        ),
        _init_l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__0,
    );
    v___x_1125_ = leanh::lean_alloc_ctor(0, 3, (3) as u32);
    leanh::lean_ctor_set(v___x_1125_, 0, v___x_1124_);
    leanh::lean_ctor_set(v___x_1125_, 1, v___x_1122_);
    leanh::lean_ctor_set(v___x_1125_, 2, v___x_1122_);
    leanh::lean_ctor_set_uint8(
        v___x_1125_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
        v___x_1123_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_1125_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 1) as u32,
        v___x_1121_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_1125_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 2) as u32,
        v___x_1120_,
    );
    return v___x_1125_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_instInhabitedLocalTimeType_default()
-> *mut leanh::LeanObject {
    let mut v___x_1126_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1126_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__2),
        core::ptr::addr_of_mut!(
            l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__2_once
        ),
        _init_l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__2,
    );
    return v___x_1126_;
}
pub unsafe fn l_Nat_cast___at___00Std_Time_TimeZone_instInhabitedLocalTimeType_default_spec__0(
    mut v_a_1127_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1129_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1128_ = lean_nat_to_int(v_a_1127_);
    v___x_1129_ = l_Rat_ofInt(v___x_1128_);
    return v___x_1129_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_instInhabitedLocalTimeType() -> *mut leanh::LeanObject
{
    let mut v___x_1130_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1130_ = l_Std_Time_TimeZone_instInhabitedLocalTimeType_default;
    return v___x_1130_;
}
pub unsafe fn l_Std_Time_TimeZone_LocalTimeType_getTimeZone(
    mut v_time_1131_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_gmtOffset_1132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isDst_1133_: u8 = 0;
    let mut v_abbreviation_1134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_identifier_1135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1136_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_gmtOffset_1132_ = leanh::lean_ctor_get(v_time_1131_, 0);
    v_isDst_1133_ = leanh::lean_ctor_get_uint8(
        v_time_1131_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
    );
    v_abbreviation_1134_ = leanh::lean_ctor_get(v_time_1131_, 1);
    v_identifier_1135_ = leanh::lean_ctor_get(v_time_1131_, 2);
    leanh::lean_inc_ref(v_abbreviation_1134_);
    leanh::lean_inc_ref(v_identifier_1135_);
    leanh::lean_inc(v_gmtOffset_1132_);
    v___x_1136_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
    leanh::lean_ctor_set(v___x_1136_, 0, v_gmtOffset_1132_);
    leanh::lean_ctor_set(v___x_1136_, 1, v_identifier_1135_);
    leanh::lean_ctor_set(v___x_1136_, 2, v_abbreviation_1134_);
    leanh::lean_ctor_set_uint8(
        v___x_1136_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
        v_isDst_1133_,
    );
    return v___x_1136_;
}
pub unsafe fn l_Std_Time_TimeZone_LocalTimeType_getTimeZone___boxed(
    mut v_time_1137_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1138_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1138_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_time_1137_);
    leanh::lean_dec_ref(v_time_1137_);
    return v_res_1138_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_instReprTransition_repr___redArg___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_1151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1151_ = leanh::lean_unsigned_to_nat(17);
    v___x_1152_ = lean_nat_to_int(v___x_1151_);
    return v___x_1152_;
}
pub unsafe fn l_Std_Time_TimeZone_instReprTransition_repr___redArg(
    mut v_x_1153_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_time_1154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_localTimeType_1155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1158_: u8 = 0;
    let mut v___x_1159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: u8 = 0;
    let mut v___x_1167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1189_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_time_1154_ = leanh::lean_ctor_get(v_x_1153_, 0);
                v_localTimeType_1155_ = leanh::lean_ctor_get(v_x_1153_, 1);
                v_isSharedCheck_1189_ = (!leanh::lean_is_exclusive(v_x_1153_)) as u8;
                if v_isSharedCheck_1189_ == 0 {
                    v___x_1157_ = v_x_1153_;
                    v_isShared_1158_ = v_isSharedCheck_1189_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_localTimeType_1155_);
                    leanh::lean_inc(v_time_1154_);
                    leanh::lean_dec(v_x_1153_);
                    v___x_1157_ = leanh::lean_box(0);
                    v_isShared_1158_ = v_isSharedCheck_1189_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1159_ = l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__5;
                v___x_1160_ = l_Std_Time_TimeZone_instReprTransition_repr___redArg___closed__3;
                v___x_1161_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__18
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__18_once
                    ),
                    _init_l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__18,
                );
                v___x_1162_ = leanh::lean_unsigned_to_nat(0);
                v___x_1163_ = l_Std_Time_Second_instReprOffset___lam__0(v_time_1154_, v___x_1162_);
                leanh::lean_dec(v_time_1154_);
                if v_isShared_1158_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1157_, 4);
                    leanh::lean_ctor_set(v___x_1157_, 1, v___x_1163_);
                    leanh::lean_ctor_set(v___x_1157_, 0, v___x_1161_);
                    v___x_1165_ = v___x_1157_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1188_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1188_, 0, v___x_1161_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1188_, 1, v___x_1163_);
                    v___x_1165_ = v_reuseFailAlloc_1188_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1166_ = 0;
                v___x_1167_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1167_, 0, v___x_1165_);
                leanh::lean_ctor_set_uint8(
                    v___x_1167_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1166_,
                );
                v___x_1168_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1168_, 0, v___x_1160_);
                leanh::lean_ctor_set(v___x_1168_, 1, v___x_1167_);
                v___x_1169_ = l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__9;
                v___x_1170_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1170_, 0, v___x_1168_);
                leanh::lean_ctor_set(v___x_1170_, 1, v___x_1169_);
                v___x_1171_ = leanh::lean_box(1);
                v___x_1172_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1172_, 0, v___x_1170_);
                leanh::lean_ctor_set(v___x_1172_, 1, v___x_1171_);
                v___x_1173_ = l_Std_Time_TimeZone_instReprTransition_repr___redArg___closed__5;
                v___x_1174_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1174_, 0, v___x_1172_);
                leanh::lean_ctor_set(v___x_1174_, 1, v___x_1173_);
                v___x_1175_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1175_, 0, v___x_1174_);
                leanh::lean_ctor_set(v___x_1175_, 1, v___x_1159_);
                v___x_1176_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_TimeZone_instReprTransition_repr___redArg___closed__6
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_TimeZone_instReprTransition_repr___redArg___closed__6_once
                    ),
                    _init_l_Std_Time_TimeZone_instReprTransition_repr___redArg___closed__6,
                );
                v___x_1177_ =
                    l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg(v_localTimeType_1155_);
                v___x_1178_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1178_, 0, v___x_1176_);
                leanh::lean_ctor_set(v___x_1178_, 1, v___x_1177_);
                v___x_1179_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1179_, 0, v___x_1178_);
                leanh::lean_ctor_set_uint8(
                    v___x_1179_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1166_,
                );
                v___x_1180_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1180_, 0, v___x_1175_);
                leanh::lean_ctor_set(v___x_1180_, 1, v___x_1179_);
                v___x_1181_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__27
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__27_once
                    ),
                    _init_l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__27,
                );
                v___x_1182_ = l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__28;
                v___x_1183_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1183_, 0, v___x_1182_);
                leanh::lean_ctor_set(v___x_1183_, 1, v___x_1180_);
                v___x_1184_ = l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__29;
                v___x_1185_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1185_, 0, v___x_1183_);
                leanh::lean_ctor_set(v___x_1185_, 1, v___x_1184_);
                v___x_1186_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1186_, 0, v___x_1181_);
                leanh::lean_ctor_set(v___x_1186_, 1, v___x_1185_);
                v___x_1187_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1187_, 0, v___x_1186_);
                leanh::lean_ctor_set_uint8(
                    v___x_1187_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1166_,
                );
                return v___x_1187_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_TimeZone_instReprTransition_repr(
    mut v_x_1190_: *mut leanh::LeanObject,
    mut v_prec_1191_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1192_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1192_ = l_Std_Time_TimeZone_instReprTransition_repr___redArg(v_x_1190_);
    return v___x_1192_;
}
pub unsafe fn l_Std_Time_TimeZone_instReprTransition_repr___boxed(
    mut v_x_1193_: *mut leanh::LeanObject,
    mut v_prec_1194_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1195_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1195_ = l_Std_Time_TimeZone_instReprTransition_repr(v_x_1193_, v_prec_1194_);
    leanh::lean_dec(v_prec_1194_);
    return v_res_1195_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_instInhabitedTransition_default___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1198_ = l_Std_Time_TimeZone_instInhabitedLocalTimeType_default;
    v___x_1199_ = l_Std_Time_Second_instInhabitedOffset;
    v___x_1200_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1200_, 0, v___x_1199_);
    leanh::lean_ctor_set(v___x_1200_, 1, v___x_1198_);
    return v___x_1200_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_instInhabitedTransition_default()
-> *mut leanh::LeanObject {
    let mut v___x_1201_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1201_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_TimeZone_instInhabitedTransition_default___closed__0),
        core::ptr::addr_of_mut!(
            l_Std_Time_TimeZone_instInhabitedTransition_default___closed__0_once
        ),
        _init_l_Std_Time_TimeZone_instInhabitedTransition_default___closed__0,
    );
    return v___x_1201_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_instInhabitedTransition() -> *mut leanh::LeanObject {
    let mut v___x_1202_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1202_ = l_Std_Time_TimeZone_instInhabitedTransition_default;
    return v___x_1202_;
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0_spec__0_spec__1_spec__2(
    mut v_x_1203_: *mut leanh::LeanObject,
    mut v_x_1204_: *mut leanh::LeanObject,
    mut v_x_1205_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_1206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1210_: u8 = 0;
    let mut v___x_1212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1217_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1205_) == 0 {
                    leanh::lean_dec(v_x_1203_);
                    return v_x_1204_;
                } else {
                    v_head_1206_ = leanh::lean_ctor_get(v_x_1205_, 0);
                    v_tail_1207_ = leanh::lean_ctor_get(v_x_1205_, 1);
                    v_isSharedCheck_1217_ = (!leanh::lean_is_exclusive(v_x_1205_)) as u8;
                    if v_isSharedCheck_1217_ == 0 {
                        v___x_1209_ = v_x_1205_;
                        v_isShared_1210_ = v_isSharedCheck_1217_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1207_);
                        leanh::lean_inc(v_head_1206_);
                        leanh::lean_dec(v_x_1205_);
                        v___x_1209_ = leanh::lean_box(0);
                        v_isShared_1210_ = v_isSharedCheck_1217_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_x_1203_);
                if v_isShared_1210_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1209_, 5);
                    leanh::lean_ctor_set(v___x_1209_, 1, v_x_1203_);
                    leanh::lean_ctor_set(v___x_1209_, 0, v_x_1204_);
                    v___x_1212_ = v___x_1209_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1216_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1216_, 0, v_x_1204_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1216_, 1, v_x_1203_);
                    v___x_1212_ = v_reuseFailAlloc_1216_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1213_ = l_Std_Time_TimeZone_instReprTransition_repr___redArg(v_head_1206_);
                v___x_1214_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1214_, 0, v___x_1212_);
                leanh::lean_ctor_set(v___x_1214_, 1, v___x_1213_);
                v_x_1204_ = v___x_1214_;
                v_x_1205_ = v_tail_1207_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0_spec__0_spec__1(
    mut v_x_1218_: *mut leanh::LeanObject,
    mut v_x_1219_: *mut leanh::LeanObject,
    mut v_x_1220_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_1221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1225_: u8 = 0;
    let mut v___x_1227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1232_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1220_) == 0 {
                    leanh::lean_dec(v_x_1218_);
                    return v_x_1219_;
                } else {
                    v_head_1221_ = leanh::lean_ctor_get(v_x_1220_, 0);
                    v_tail_1222_ = leanh::lean_ctor_get(v_x_1220_, 1);
                    v_isSharedCheck_1232_ = (!leanh::lean_is_exclusive(v_x_1220_)) as u8;
                    if v_isSharedCheck_1232_ == 0 {
                        v___x_1224_ = v_x_1220_;
                        v_isShared_1225_ = v_isSharedCheck_1232_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1222_);
                        leanh::lean_inc(v_head_1221_);
                        leanh::lean_dec(v_x_1220_);
                        v___x_1224_ = leanh::lean_box(0);
                        v_isShared_1225_ = v_isSharedCheck_1232_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_x_1218_);
                if v_isShared_1225_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1224_, 5);
                    leanh::lean_ctor_set(v___x_1224_, 1, v_x_1218_);
                    leanh::lean_ctor_set(v___x_1224_, 0, v_x_1219_);
                    v___x_1227_ = v___x_1224_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1231_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1231_, 0, v_x_1219_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1231_, 1, v_x_1218_);
                    v___x_1227_ = v_reuseFailAlloc_1231_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1228_ = l_Std_Time_TimeZone_instReprTransition_repr___redArg(v_head_1221_);
                v___x_1229_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1229_, 0, v___x_1227_);
                leanh::lean_ctor_set(v___x_1229_, 1, v___x_1228_);
                v___x_1230_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0_spec__0_spec__1_spec__2(v_x_1218_, v___x_1229_, v_tail_1222_);
                return v___x_1230_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0_spec__0(
    mut v_x_1233_: *mut leanh::LeanObject,
    mut v_x_1234_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1233_) == 0 {
        let mut v___x_1235_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_1234_);
        v___x_1235_ = leanh::lean_box(0);
        return v___x_1235_;
    } else {
        let mut v_tail_1236_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_tail_1236_ = leanh::lean_ctor_get(v_x_1233_, 1);
        if leanh::lean_obj_tag(v_tail_1236_) == 0 {
            let mut v_head_1237_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1238_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_x_1234_);
            v_head_1237_ = leanh::lean_ctor_get(v_x_1233_, 0);
            leanh::lean_inc(v_head_1237_);
            leanh::lean_dec_ref_known(v_x_1233_, 2);
            v___x_1238_ = l_Std_Time_TimeZone_instReprTransition_repr___redArg(v_head_1237_);
            return v___x_1238_;
        } else {
            let mut v_head_1239_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1240_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1241_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc(v_tail_1236_);
            v_head_1239_ = leanh::lean_ctor_get(v_x_1233_, 0);
            leanh::lean_inc(v_head_1239_);
            leanh::lean_dec_ref_known(v_x_1233_, 2);
            v___x_1240_ = l_Std_Time_TimeZone_instReprTransition_repr___redArg(v_head_1239_);
            v___x_1241_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0_spec__0_spec__1(v_x_1234_, v___x_1240_, v_tail_1236_);
            return v___x_1241_;
        }
    }
}
pub unsafe fn _init_l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1248_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1247_ =
        l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__0;
    v___x_1248_ = lean_string_length(v___x_1247_);
    return v___x_1248_;
}
pub unsafe fn _init_l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1249_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__3_once
        ),
        _init_l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__3,
    );
    v___x_1250_ = lean_nat_to_int(v___x_1249_);
    return v___x_1250_;
}
pub unsafe fn l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0(
    mut v_xs_1258_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: u8 = 0;
    v___x_1259_ = lean_array_get_size(v_xs_1258_);
    v___x_1260_ = leanh::lean_unsigned_to_nat(0);
    v___x_1261_ = lean_nat_dec_eq(v___x_1259_, v___x_1260_);
    if v___x_1261_ == 0 {
        let mut v___x_1262_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1263_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1264_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1265_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1266_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1267_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1268_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1269_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1270_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1271_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1262_ = lean_array_to_list(v_xs_1258_);
        v___x_1263_ =
            l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__1;
        v___x_1264_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0_spec__0(v___x_1262_, v___x_1263_);
        v___x_1265_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__4), core::ptr::addr_of_mut!(l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__4_once), _init_l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__4);
        v___x_1266_ =
            l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__5;
        v___x_1267_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1267_, 0, v___x_1266_);
        leanh::lean_ctor_set(v___x_1267_, 1, v___x_1264_);
        v___x_1268_ =
            l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__6;
        v___x_1269_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1269_, 0, v___x_1267_);
        leanh::lean_ctor_set(v___x_1269_, 1, v___x_1268_);
        v___x_1270_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1270_, 0, v___x_1265_);
        leanh::lean_ctor_set(v___x_1270_, 1, v___x_1269_);
        v___x_1271_ = l_Std_Format_fill(v___x_1270_);
        return v___x_1271_;
    } else {
        let mut v___x_1272_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_xs_1258_);
        v___x_1272_ =
            l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__8;
        return v___x_1272_;
    }
}
pub unsafe fn _init_l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1283_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1282_ = leanh::lean_unsigned_to_nat(24);
    v___x_1283_ = lean_nat_to_int(v___x_1282_);
    return v___x_1283_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_1287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1287_ = leanh::lean_unsigned_to_nat(15);
    v___x_1288_ = lean_nat_to_int(v___x_1287_);
    return v___x_1288_;
}
pub unsafe fn l_Std_Time_TimeZone_instReprZoneRules_repr___redArg(
    mut v_x_1289_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_initialLocalTimeType_1290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_transitions_1291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1294_: u8 = 0;
    let mut v___x_1295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: u8 = 0;
    let mut v___x_1302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1324_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_initialLocalTimeType_1290_ = leanh::lean_ctor_get(v_x_1289_, 0);
                v_transitions_1291_ = leanh::lean_ctor_get(v_x_1289_, 1);
                v_isSharedCheck_1324_ = (!leanh::lean_is_exclusive(v_x_1289_)) as u8;
                if v_isSharedCheck_1324_ == 0 {
                    v___x_1293_ = v_x_1289_;
                    v_isShared_1294_ = v_isSharedCheck_1324_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_transitions_1291_);
                    leanh::lean_inc(v_initialLocalTimeType_1290_);
                    leanh::lean_dec(v_x_1289_);
                    v___x_1293_ = leanh::lean_box(0);
                    v_isShared_1294_ = v_isSharedCheck_1324_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1295_ = l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__5;
                v___x_1296_ = l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__3;
                v___x_1297_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__4
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__4_once
                    ),
                    _init_l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__4,
                );
                v___x_1298_ = l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg(
                    v_initialLocalTimeType_1290_,
                );
                if v_isShared_1294_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1293_, 4);
                    leanh::lean_ctor_set(v___x_1293_, 1, v___x_1298_);
                    leanh::lean_ctor_set(v___x_1293_, 0, v___x_1297_);
                    v___x_1300_ = v___x_1293_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1323_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1323_, 0, v___x_1297_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1323_, 1, v___x_1298_);
                    v___x_1300_ = v_reuseFailAlloc_1323_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1301_ = 0;
                v___x_1302_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1302_, 0, v___x_1300_);
                leanh::lean_ctor_set_uint8(
                    v___x_1302_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1301_,
                );
                v___x_1303_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1303_, 0, v___x_1296_);
                leanh::lean_ctor_set(v___x_1303_, 1, v___x_1302_);
                v___x_1304_ = l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__9;
                v___x_1305_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1305_, 0, v___x_1303_);
                leanh::lean_ctor_set(v___x_1305_, 1, v___x_1304_);
                v___x_1306_ = leanh::lean_box(1);
                v___x_1307_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1307_, 0, v___x_1305_);
                leanh::lean_ctor_set(v___x_1307_, 1, v___x_1306_);
                v___x_1308_ = l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__6;
                v___x_1309_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1309_, 0, v___x_1307_);
                leanh::lean_ctor_set(v___x_1309_, 1, v___x_1308_);
                v___x_1310_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1310_, 0, v___x_1309_);
                leanh::lean_ctor_set(v___x_1310_, 1, v___x_1295_);
                v___x_1311_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__7
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__7_once
                    ),
                    _init_l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__7,
                );
                v___x_1312_ =
                    l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0(
                        v_transitions_1291_,
                    );
                v___x_1313_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1313_, 0, v___x_1311_);
                leanh::lean_ctor_set(v___x_1313_, 1, v___x_1312_);
                v___x_1314_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1314_, 0, v___x_1313_);
                leanh::lean_ctor_set_uint8(
                    v___x_1314_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1301_,
                );
                v___x_1315_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1315_, 0, v___x_1310_);
                leanh::lean_ctor_set(v___x_1315_, 1, v___x_1314_);
                v___x_1316_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__27
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__27_once
                    ),
                    _init_l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__27,
                );
                v___x_1317_ = l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__28;
                v___x_1318_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1318_, 0, v___x_1317_);
                leanh::lean_ctor_set(v___x_1318_, 1, v___x_1315_);
                v___x_1319_ = l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__29;
                v___x_1320_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1320_, 0, v___x_1318_);
                leanh::lean_ctor_set(v___x_1320_, 1, v___x_1319_);
                v___x_1321_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1321_, 0, v___x_1316_);
                leanh::lean_ctor_set(v___x_1321_, 1, v___x_1320_);
                v___x_1322_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1322_, 0, v___x_1321_);
                leanh::lean_ctor_set_uint8(
                    v___x_1322_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1301_,
                );
                return v___x_1322_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_TimeZone_instReprZoneRules_repr(
    mut v_x_1325_: *mut leanh::LeanObject,
    mut v_prec_1326_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1327_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1327_ = l_Std_Time_TimeZone_instReprZoneRules_repr___redArg(v_x_1325_);
    return v___x_1327_;
}
pub unsafe fn l_Std_Time_TimeZone_instReprZoneRules_repr___boxed(
    mut v_x_1328_: *mut leanh::LeanObject,
    mut v_prec_1329_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1330_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1330_ = l_Std_Time_TimeZone_instReprZoneRules_repr(v_x_1328_, v_prec_1329_);
    leanh::lean_dec(v_prec_1329_);
    return v_res_1330_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_instInhabitedZoneRules_default___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1335_ = l_Std_Time_TimeZone_instInhabitedZoneRules_default___closed__0;
    v___x_1336_ = l_Std_Time_TimeZone_instInhabitedLocalTimeType_default;
    v___x_1337_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1337_, 0, v___x_1336_);
    leanh::lean_ctor_set(v___x_1337_, 1, v___x_1335_);
    return v___x_1337_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_instInhabitedZoneRules_default()
-> *mut leanh::LeanObject {
    let mut v___x_1338_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1338_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_TimeZone_instInhabitedZoneRules_default___closed__1),
        core::ptr::addr_of_mut!(
            l_Std_Time_TimeZone_instInhabitedZoneRules_default___closed__1_once
        ),
        _init_l_Std_Time_TimeZone_instInhabitedZoneRules_default___closed__1,
    );
    return v___x_1338_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_instInhabitedZoneRules() -> *mut leanh::LeanObject {
    let mut v___x_1339_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1339_ = l_Std_Time_TimeZone_instInhabitedZoneRules_default;
    return v___x_1339_;
}
pub unsafe fn l_Std_Time_TimeZone_Transition_timestamp(
    mut v_t_1340_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_time_1341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1344_: u8 = 0;
    let mut v___x_1345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1349_: u8 = 0;
    let mut v_unused_1350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_time_1341_ = leanh::lean_ctor_get(v_t_1340_, 0);
                v_isSharedCheck_1349_ = (!leanh::lean_is_exclusive(v_t_1340_)) as u8;
                if v_isSharedCheck_1349_ == 0 {
                    v_unused_1350_ = leanh::lean_ctor_get(v_t_1340_, 1);
                    leanh::lean_dec(v_unused_1350_);
                    v___x_1343_ = v_t_1340_;
                    v_isShared_1344_ = v_isSharedCheck_1349_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_time_1341_);
                    leanh::lean_dec(v_t_1340_);
                    v___x_1343_ = leanh::lean_box(0);
                    v_isShared_1344_ = v_isSharedCheck_1349_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1345_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__0_once
                    ),
                    _init_l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__0,
                );
                if v_isShared_1344_ == 0 {
                    leanh::lean_ctor_set(v___x_1343_, 1, v___x_1345_);
                    v___x_1347_ = v___x_1343_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1348_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1348_, 0, v_time_1341_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1348_, 1, v___x_1345_);
                    v___x_1347_ = v_reuseFailAlloc_1348_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1347_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_TimeZone_Transition_createTimeZoneFromTransition(
    mut v_transition_1351_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_localTimeType_1352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_gmtOffset_1353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isDst_1354_: u8 = 0;
    let mut v_abbreviation_1355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_identifier_1356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_localTimeType_1352_ = leanh::lean_ctor_get(v_transition_1351_, 1);
    v_gmtOffset_1353_ = leanh::lean_ctor_get(v_localTimeType_1352_, 0);
    v_isDst_1354_ = leanh::lean_ctor_get_uint8(
        v_localTimeType_1352_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
    );
    v_abbreviation_1355_ = leanh::lean_ctor_get(v_localTimeType_1352_, 1);
    v_identifier_1356_ = leanh::lean_ctor_get(v_localTimeType_1352_, 2);
    leanh::lean_inc_ref(v_abbreviation_1355_);
    leanh::lean_inc_ref(v_identifier_1356_);
    leanh::lean_inc(v_gmtOffset_1353_);
    v___x_1357_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
    leanh::lean_ctor_set(v___x_1357_, 0, v_gmtOffset_1353_);
    leanh::lean_ctor_set(v___x_1357_, 1, v_identifier_1356_);
    leanh::lean_ctor_set(v___x_1357_, 2, v_abbreviation_1355_);
    leanh::lean_ctor_set_uint8(
        v___x_1357_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
        v_isDst_1354_,
    );
    return v___x_1357_;
}
pub unsafe fn l_Std_Time_TimeZone_Transition_createTimeZoneFromTransition___boxed(
    mut v_transition_1358_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1359_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1359_ = l_Std_Time_TimeZone_Transition_createTimeZoneFromTransition(v_transition_1358_);
    leanh::lean_dec_ref(v_transition_1358_);
    return v_res_1359_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_Transition_apply___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1360_ = leanh::lean_unsigned_to_nat(1000000000);
    v___x_1361_ = lean_nat_to_int(v___x_1360_);
    return v___x_1361_;
}
pub unsafe fn l_Std_Time_TimeZone_Transition_apply(
    mut v_timestamp_1362_: *mut leanh::LeanObject,
    mut v_transition_1363_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_localTimeType_1364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_gmtOffset_1365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_1366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_localTimeType_1364_ = leanh::lean_ctor_get(v_transition_1363_, 1);
    v_gmtOffset_1365_ = leanh::lean_ctor_get(v_localTimeType_1364_, 0);
    v_second_1366_ = leanh::lean_ctor_get(v_timestamp_1362_, 0);
    v_nano_1367_ = leanh::lean_ctor_get(v_timestamp_1362_, 1);
    v___x_1368_ = lean_int_add(v_gmtOffset_1365_, v_gmtOffset_1365_);
    v___x_1369_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__0),
        core::ptr::addr_of_mut!(
            l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__0_once
        ),
        _init_l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__0,
    );
    v___x_1370_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_TimeZone_Transition_apply___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_TimeZone_Transition_apply___closed__0_once),
        _init_l_Std_Time_TimeZone_Transition_apply___closed__0,
    );
    v___x_1371_ = lean_int_mul(v_second_1366_, v___x_1370_);
    v___x_1372_ = lean_int_add(v___x_1371_, v_nano_1367_);
    leanh::lean_dec(v___x_1371_);
    v___x_1373_ = lean_int_mul(v___x_1368_, v___x_1370_);
    leanh::lean_dec(v___x_1368_);
    v___x_1374_ = lean_int_add(v___x_1373_, v___x_1369_);
    leanh::lean_dec(v___x_1373_);
    v___x_1375_ = lean_int_add(v___x_1372_, v___x_1374_);
    leanh::lean_dec(v___x_1374_);
    leanh::lean_dec(v___x_1372_);
    v___x_1376_ = l_Std_Time_Duration_ofNanoseconds(v___x_1375_);
    leanh::lean_dec(v___x_1375_);
    return v___x_1376_;
}
pub unsafe fn l_Std_Time_TimeZone_Transition_apply___boxed(
    mut v_timestamp_1377_: *mut leanh::LeanObject,
    mut v_transition_1378_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1379_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1379_ = l_Std_Time_TimeZone_Transition_apply(v_timestamp_1377_, v_transition_1378_);
    leanh::lean_dec_ref(v_transition_1378_);
    leanh::lean_dec_ref(v_timestamp_1377_);
    return v_res_1379_;
}
pub unsafe fn l_Array_findIdx_x3f_loop___at___00Std_Time_TimeZone_Transition_findTransitionIndexForTimestamp_spec__0(
    mut v_value_1380_: *mut leanh::LeanObject,
    mut v_as_1381_: *mut leanh::LeanObject,
    mut v_j_1382_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: u8 = 0;
    let mut v___x_1385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_1387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1388_: u8 = 0;
    let mut v___x_1389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1383_ = lean_array_get_size(v_as_1381_);
                v___x_1384_ = lean_nat_dec_lt(v_j_1382_, v___x_1383_);
                if v___x_1384_ == 0 {
                    leanh::lean_dec(v_j_1382_);
                    v___x_1385_ = leanh::lean_box(0);
                    return v___x_1385_;
                } else {
                    v___x_1386_ = lean_array_fget_borrowed(v_as_1381_, v_j_1382_);
                    v_time_1387_ = leanh::lean_ctor_get(v___x_1386_, 0);
                    v___x_1388_ = lean_int_dec_lt(v_value_1380_, v_time_1387_);
                    if v___x_1388_ == 0 {
                        v___x_1389_ = leanh::lean_unsigned_to_nat(1);
                        v___x_1390_ = lean_nat_add(v_j_1382_, v___x_1389_);
                        leanh::lean_dec(v_j_1382_);
                        v_j_1382_ = v___x_1390_;
                        state = 0;
                        continue;
                    } else {
                        v___x_1392_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1392_, 0, v_j_1382_);
                        return v___x_1392_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_findIdx_x3f_loop___at___00Std_Time_TimeZone_Transition_findTransitionIndexForTimestamp_spec__0___boxed(
    mut v_value_1393_: *mut leanh::LeanObject,
    mut v_as_1394_: *mut leanh::LeanObject,
    mut v_j_1395_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1396_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1396_ = l_Array_findIdx_x3f_loop___at___00Std_Time_TimeZone_Transition_findTransitionIndexForTimestamp_spec__0(v_value_1393_, v_as_1394_, v_j_1395_);
    leanh::lean_dec_ref(v_as_1394_);
    leanh::lean_dec(v_value_1393_);
    return v_res_1396_;
}
pub unsafe fn l_Std_Time_TimeZone_Transition_findTransitionIndexForTimestamp(
    mut v_transitions_1397_: *mut leanh::LeanObject,
    mut v_timestamp_1398_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_second_1399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_second_1399_ = leanh::lean_ctor_get(v_timestamp_1398_, 0);
    v___x_1400_ = leanh::lean_unsigned_to_nat(0);
    v___x_1401_ = l_Array_findIdx_x3f_loop___at___00Std_Time_TimeZone_Transition_findTransitionIndexForTimestamp_spec__0(v_second_1399_, v_transitions_1397_, v___x_1400_);
    return v___x_1401_;
}
pub unsafe fn l_Std_Time_TimeZone_Transition_findTransitionIndexForTimestamp___boxed(
    mut v_transitions_1402_: *mut leanh::LeanObject,
    mut v_timestamp_1403_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1404_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1404_ = l_Std_Time_TimeZone_Transition_findTransitionIndexForTimestamp(
        v_transitions_1402_,
        v_timestamp_1403_,
    );
    leanh::lean_dec_ref(v_timestamp_1403_);
    leanh::lean_dec_ref(v_transitions_1402_);
    return v_res_1404_;
}
pub unsafe fn l_Std_Time_TimeZone_Transition_findTransitionForTimestamp(
    mut v_transitions_1405_: *mut leanh::LeanObject,
    mut v_timestamp_1406_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1411_: u8 = 0;
    let mut v___x_1412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: u8 = 0;
    let mut v___x_1416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1421_: u8 = 0;
    let mut v___x_1422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: u8 = 0;
    let mut v___x_1426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1407_ = l_Std_Time_TimeZone_Transition_findTransitionIndexForTimestamp(
                    v_transitions_1405_,
                    v_timestamp_1406_,
                );
                if leanh::lean_obj_tag(v___x_1407_) == 1 {
                    v_val_1408_ = leanh::lean_ctor_get(v___x_1407_, 0);
                    v_isSharedCheck_1421_ = (!leanh::lean_is_exclusive(v___x_1407_)) as u8;
                    if v_isSharedCheck_1421_ == 0 {
                        v___x_1410_ = v___x_1407_;
                        v_isShared_1411_ = v_isSharedCheck_1421_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1408_);
                        leanh::lean_dec(v___x_1407_);
                        v___x_1410_ = leanh::lean_box(0);
                        v_isShared_1411_ = v_isSharedCheck_1421_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_1407_);
                    v___x_1422_ = lean_array_get_size(v_transitions_1405_);
                    v___x_1423_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1424_ = lean_nat_sub(v___x_1422_, v___x_1423_);
                    v___x_1425_ = lean_nat_dec_lt(v___x_1424_, v___x_1422_);
                    if v___x_1425_ == 0 {
                        leanh::lean_dec(v___x_1424_);
                        v___x_1426_ = leanh::lean_box(0);
                        return v___x_1426_;
                    } else {
                        v___x_1427_ = lean_array_fget_borrowed(v_transitions_1405_, v___x_1424_);
                        leanh::lean_dec(v___x_1424_);
                        leanh::lean_inc(v___x_1427_);
                        v___x_1428_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1428_, 0, v___x_1427_);
                        return v___x_1428_;
                    }
                }
            }
            1 => {
                v___x_1412_ = leanh::lean_unsigned_to_nat(1);
                v___x_1413_ = lean_nat_sub(v_val_1408_, v___x_1412_);
                leanh::lean_dec(v_val_1408_);
                v___x_1414_ = lean_array_get_size(v_transitions_1405_);
                v___x_1415_ = lean_nat_dec_lt(v___x_1413_, v___x_1414_);
                if v___x_1415_ == 0 {
                    leanh::lean_dec(v___x_1413_);
                    leanh::lean_del_object(v___x_1410_);
                    v___x_1416_ = leanh::lean_box(0);
                    return v___x_1416_;
                } else {
                    v___x_1417_ = lean_array_fget_borrowed(v_transitions_1405_, v___x_1413_);
                    leanh::lean_dec(v___x_1413_);
                    leanh::lean_inc(v___x_1417_);
                    if v_isShared_1411_ == 0 {
                        leanh::lean_ctor_set(v___x_1410_, 0, v___x_1417_);
                        v___x_1419_ = v___x_1410_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1420_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1420_, 0, v___x_1417_);
                        v___x_1419_ = v_reuseFailAlloc_1420_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1419_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_TimeZone_Transition_findTransitionForTimestamp___boxed(
    mut v_transitions_1429_: *mut leanh::LeanObject,
    mut v_timestamp_1430_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1431_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1431_ = l_Std_Time_TimeZone_Transition_findTransitionForTimestamp(
        v_transitions_1429_,
        v_timestamp_1430_,
    );
    leanh::lean_dec_ref(v_timestamp_1430_);
    leanh::lean_dec_ref(v_transitions_1429_);
    return v_res_1431_;
}
pub unsafe fn l_Std_Time_TimeZone_Transition_timezoneAt(
    mut v_transitions_1435_: *mut leanh::LeanObject,
    mut v_tm_1436_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1441_: u8 = 0;
    let mut v___x_1442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1446_: u8 = 0;
    let mut v___x_1447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1437_ = l_Std_Time_TimeZone_Transition_findTransitionForTimestamp(
                    v_transitions_1435_,
                    v_tm_1436_,
                );
                if leanh::lean_obj_tag(v___x_1437_) == 1 {
                    v_val_1438_ = leanh::lean_ctor_get(v___x_1437_, 0);
                    v_isSharedCheck_1446_ = (!leanh::lean_is_exclusive(v___x_1437_)) as u8;
                    if v_isSharedCheck_1446_ == 0 {
                        v___x_1440_ = v___x_1437_;
                        v_isShared_1441_ = v_isSharedCheck_1446_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1438_);
                        leanh::lean_dec(v___x_1437_);
                        v___x_1440_ = leanh::lean_box(0);
                        v_isShared_1441_ = v_isSharedCheck_1446_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_1437_);
                    v___x_1447_ = l_Std_Time_TimeZone_Transition_timezoneAt___closed__1;
                    return v___x_1447_;
                }
            }
            1 => {
                v___x_1442_ =
                    l_Std_Time_TimeZone_Transition_createTimeZoneFromTransition(v_val_1438_);
                leanh::lean_dec(v_val_1438_);
                if v_isShared_1441_ == 0 {
                    leanh::lean_ctor_set(v___x_1440_, 0, v___x_1442_);
                    v___x_1444_ = v___x_1440_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1445_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1445_, 0, v___x_1442_);
                    v___x_1444_ = v_reuseFailAlloc_1445_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1444_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_TimeZone_Transition_timezoneAt___boxed(
    mut v_transitions_1448_: *mut leanh::LeanObject,
    mut v_tm_1449_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1450_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1450_ = l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_1448_, v_tm_1449_);
    leanh::lean_dec_ref(v_tm_1449_);
    leanh::lean_dec_ref(v_transitions_1448_);
    return v_res_1450_;
}
pub unsafe fn l_Std_Time_TimeZone_ZoneRules_fixedOffsetZone___lam__0(
    mut v_second_1451_: *mut leanh::LeanObject,
    mut v_00___1452_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1453_: u8 = 0;
    let mut v___x_1454_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1453_ = 1;
    v___x_1454_ = l_Std_Time_TimeZone_Offset_toIsoString(v_second_1451_, v___x_1453_);
    return v___x_1454_;
}
pub unsafe fn l_Std_Time_TimeZone_ZoneRules_fixedOffsetZone(
    mut v_second_1457_: *mut leanh::LeanObject,
    mut v_identifier_1458_: *mut leanh::LeanObject,
    mut v_abbreviation_1459_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1460_: u8 = 0;
    let mut v___y_1462_: u8 = 0;
    let mut v___y_1463_: u8 = 0;
    let mut v___y_1464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: u8 = 0;
    let mut v___x_1472_: u8 = 0;
    let mut v___x_1473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1460_ = 0;
                if leanh::lean_obj_tag(v_abbreviation_1459_) == 0 {
                    v___x_1476_ = leanh::lean_box(0);
                    leanh::lean_inc(v_second_1457_);
                    v___x_1477_ = l_Std_Time_TimeZone_ZoneRules_fixedOffsetZone___lam__0(
                        v_second_1457_,
                        v___x_1476_,
                    );
                    v___y_1470_ = v___x_1477_;
                    state = 2;
                    continue;
                } else {
                    v_val_1478_ = leanh::lean_ctor_get(v_abbreviation_1459_, 0);
                    leanh::lean_inc(v_val_1478_);
                    leanh::lean_dec_ref_known(v_abbreviation_1459_, 1);
                    v___y_1470_ = v_val_1478_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_1466_ = leanh::lean_alloc_ctor(0, 3, (3) as u32);
                leanh::lean_ctor_set(v___x_1466_, 0, v_second_1457_);
                leanh::lean_ctor_set(v___x_1466_, 1, v___y_1464_);
                leanh::lean_ctor_set(v___x_1466_, 2, v___y_1465_);
                leanh::lean_ctor_set_uint8(
                    v___x_1466_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_1460_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_1466_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 1) as u32,
                    v___y_1462_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_1466_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 2) as u32,
                    v___y_1463_,
                );
                v___x_1467_ = l_Std_Time_TimeZone_ZoneRules_fixedOffsetZone___closed__0;
                v___x_1468_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1468_, 0, v___x_1466_);
                leanh::lean_ctor_set(v___x_1468_, 1, v___x_1467_);
                return v___x_1468_;
            }
            2 => {
                v___x_1471_ = 1;
                v___x_1472_ = 0;
                if leanh::lean_obj_tag(v_identifier_1458_) == 0 {
                    v___x_1473_ = leanh::lean_box(0);
                    leanh::lean_inc(v_second_1457_);
                    v___x_1474_ = l_Std_Time_TimeZone_ZoneRules_fixedOffsetZone___lam__0(
                        v_second_1457_,
                        v___x_1473_,
                    );
                    v___y_1462_ = v___x_1471_;
                    v___y_1463_ = v___x_1472_;
                    v___y_1464_ = v___y_1470_;
                    v___y_1465_ = v___x_1474_;
                    state = 1;
                    continue;
                } else {
                    v_val_1475_ = leanh::lean_ctor_get(v_identifier_1458_, 0);
                    leanh::lean_inc(v_val_1475_);
                    leanh::lean_dec_ref_known(v_identifier_1458_, 1);
                    v___y_1462_ = v___x_1471_;
                    v___y_1463_ = v___x_1472_;
                    v___y_1464_ = v___y_1470_;
                    v___y_1465_ = v_val_1475_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Std_Time_TimeZone_ZoneRules_UTC___closed__0() -> *mut leanh::LeanObject
{
    let mut v___x_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1479_ = leanh::lean_unsigned_to_nat(0);
    v___x_1480_ = lean_nat_to_int(v___x_1479_);
    return v___x_1480_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_ZoneRules_UTC___closed__3() -> *mut leanh::LeanObject
{
    let mut v___x_1484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1484_ = l_Std_Time_TimeZone_ZoneRules_UTC___closed__2;
    v___x_1485_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_TimeZone_ZoneRules_UTC___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_TimeZone_ZoneRules_UTC___closed__0_once),
        _init_l_Std_Time_TimeZone_ZoneRules_UTC___closed__0,
    );
    v___x_1486_ =
        l_Std_Time_TimeZone_ZoneRules_fixedOffsetZone(v___x_1485_, v___x_1484_, v___x_1484_);
    return v___x_1486_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_ZoneRules_UTC() -> *mut leanh::LeanObject {
    let mut v___x_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1487_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_TimeZone_ZoneRules_UTC___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_TimeZone_ZoneRules_UTC___closed__3_once),
        _init_l_Std_Time_TimeZone_ZoneRules_UTC___closed__3,
    );
    return v___x_1487_;
}
pub unsafe fn l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForTimestamp(
    mut v_zr_1488_: *mut leanh::LeanObject,
    mut v_timestamp_1489_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_initialLocalTimeType_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_transitions_1491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_initialLocalTimeType_1490_ = leanh::lean_ctor_get(v_zr_1488_, 0);
    v_transitions_1491_ = leanh::lean_ctor_get(v_zr_1488_, 1);
    v___x_1492_ = l_Std_Time_TimeZone_Transition_findTransitionForTimestamp(
        v_transitions_1491_,
        v_timestamp_1489_,
    );
    if leanh::lean_obj_tag(v___x_1492_) == 0 {
        leanh::lean_inc_ref(v_initialLocalTimeType_1490_);
        return v_initialLocalTimeType_1490_;
    } else {
        let mut v_val_1493_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_localTimeType_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1493_ = leanh::lean_ctor_get(v___x_1492_, 0);
        leanh::lean_inc(v_val_1493_);
        leanh::lean_dec_ref_known(v___x_1492_, 1);
        v_localTimeType_1494_ = leanh::lean_ctor_get(v_val_1493_, 1);
        leanh::lean_inc_ref(v_localTimeType_1494_);
        leanh::lean_dec(v_val_1493_);
        return v_localTimeType_1494_;
    }
}
pub unsafe fn l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForTimestamp___boxed(
    mut v_zr_1495_: *mut leanh::LeanObject,
    mut v_timestamp_1496_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1497_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1497_ =
        l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForTimestamp(v_zr_1495_, v_timestamp_1496_);
    leanh::lean_dec_ref(v_timestamp_1496_);
    leanh::lean_dec_ref(v_zr_1495_);
    return v_res_1497_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime_spec__0(
    mut v_wallTime_1498_: *mut leanh::LeanObject,
    mut v_as_1499_: *mut leanh::LeanObject,
    mut v_sz_1500_: usize,
    mut v_i_1501_: usize,
    mut v_b_1502_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1503_: u8 = 0;
    let mut v_snd_1504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1507_: u8 = 0;
    let mut v_gmtOffset_1508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_1511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: u8 = 0;
    let mut v_localTimeType_1522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: usize = 0;
    let mut v___x_1527_: usize = 0;
    let mut v_reuseFailAlloc_1529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1534_: u8 = 0;
    let mut v_unused_1535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1503_ = lean_usize_dec_lt(v_i_1501_, v_sz_1500_);
                if v___x_1503_ == 0 {
                    return v_b_1502_;
                } else {
                    v_snd_1504_ = leanh::lean_ctor_get(v_b_1502_, 1);
                    v_isSharedCheck_1534_ = (!leanh::lean_is_exclusive(v_b_1502_)) as u8;
                    if v_isSharedCheck_1534_ == 0 {
                        v_unused_1535_ = leanh::lean_ctor_get(v_b_1502_, 0);
                        leanh::lean_dec(v_unused_1535_);
                        v___x_1506_ = v_b_1502_;
                        v_isShared_1507_ = v_isSharedCheck_1534_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_1504_);
                        leanh::lean_dec(v_b_1502_);
                        v___x_1506_ = leanh::lean_box(0);
                        v_isShared_1507_ = v_isSharedCheck_1534_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_gmtOffset_1508_ = leanh::lean_ctor_get(v_snd_1504_, 0);
                v_a_1509_ = lean_array_uget_borrowed(v_as_1499_, v_i_1501_);
                leanh::lean_inc(v_a_1509_);
                v___x_1510_ = l_Std_Time_TimeZone_Transition_timestamp(v_a_1509_);
                v_second_1511_ = leanh::lean_ctor_get(v___x_1510_, 0);
                leanh::lean_inc(v_second_1511_);
                v_nano_1512_ = leanh::lean_ctor_get(v___x_1510_, 1);
                leanh::lean_inc(v_nano_1512_);
                leanh::lean_dec_ref(v___x_1510_);
                v___x_1513_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__0_once
                    ),
                    _init_l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__0,
                );
                v___x_1514_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_TimeZone_Transition_apply___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_TimeZone_Transition_apply___closed__0_once),
                    _init_l_Std_Time_TimeZone_Transition_apply___closed__0,
                );
                v___x_1515_ = lean_int_mul(v_second_1511_, v___x_1514_);
                leanh::lean_dec(v_second_1511_);
                v___x_1516_ = lean_int_add(v___x_1515_, v_nano_1512_);
                leanh::lean_dec(v_nano_1512_);
                leanh::lean_dec(v___x_1515_);
                v___x_1517_ = lean_int_mul(v_gmtOffset_1508_, v___x_1514_);
                v___x_1518_ = lean_int_add(v___x_1517_, v___x_1513_);
                leanh::lean_dec(v___x_1517_);
                v___x_1519_ = lean_int_add(v___x_1516_, v___x_1518_);
                leanh::lean_dec(v___x_1518_);
                leanh::lean_dec(v___x_1516_);
                v___x_1520_ = l_Std_Time_Duration_ofNanoseconds(v___x_1519_);
                leanh::lean_dec(v___x_1519_);
                v___x_1521_ = l_Std_Time_Duration_instDecidableLt(v_wallTime_1498_, v___x_1520_);
                leanh::lean_dec_ref(v___x_1520_);
                if v___x_1521_ == 0 {
                    leanh::lean_dec(v_snd_1504_);
                    v_localTimeType_1522_ = leanh::lean_ctor_get(v_a_1509_, 1);
                    v___x_1523_ = leanh::lean_box(0);
                    leanh::lean_inc_ref(v_localTimeType_1522_);
                    if v_isShared_1507_ == 0 {
                        leanh::lean_ctor_set(v___x_1506_, 1, v_localTimeType_1522_);
                        leanh::lean_ctor_set(v___x_1506_, 0, v___x_1523_);
                        v___x_1525_ = v___x_1506_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1529_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1529_, 0, v___x_1523_);
                        leanh::lean_ctor_set(
                            v_reuseFailAlloc_1529_,
                            1,
                            v_localTimeType_1522_,
                        );
                        v___x_1525_ = v_reuseFailAlloc_1529_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_inc(v_snd_1504_);
                    v___x_1530_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1530_, 0, v_snd_1504_);
                    if v_isShared_1507_ == 0 {
                        leanh::lean_ctor_set(v___x_1506_, 0, v___x_1530_);
                        v___x_1532_ = v___x_1506_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1533_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1533_, 0, v___x_1530_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1533_, 1, v_snd_1504_);
                        v___x_1532_ = v_reuseFailAlloc_1533_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1526_ = 1usize;
                v___x_1527_ = lean_usize_add(v_i_1501_, v___x_1526_);
                v_i_1501_ = v___x_1527_;
                v_b_1502_ = v___x_1525_;
                state = 0;
                continue;
            }
            3 => {
                return v___x_1532_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime_spec__0___boxed(
    mut v_wallTime_1536_: *mut leanh::LeanObject,
    mut v_as_1537_: *mut leanh::LeanObject,
    mut v_sz_1538_: *mut leanh::LeanObject,
    mut v_i_1539_: *mut leanh::LeanObject,
    mut v_b_1540_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1541_: usize = 0;
    let mut v_i_boxed_1542_: usize = 0;
    let mut v_res_1543_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1541_ = leanh::lean_unbox_usize(v_sz_1538_);
    leanh::lean_dec(v_sz_1538_);
    v_i_boxed_1542_ = leanh::lean_unbox_usize(v_i_1539_);
    leanh::lean_dec(v_i_1539_);
    v_res_1543_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime_spec__0(v_wallTime_1536_, v_as_1537_, v_sz_boxed_1541_, v_i_boxed_1542_, v_b_1540_);
    leanh::lean_dec_ref(v_as_1537_);
    leanh::lean_dec_ref(v_wallTime_1536_);
    return v_res_1543_;
}
pub unsafe fn l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(
    mut v_zr_1544_: *mut leanh::LeanObject,
    mut v_wallTime_1545_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_initialLocalTimeType_1546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_transitions_1547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1550_: u8 = 0;
    let mut v___x_1551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1554_: usize = 0;
    let mut v___x_1555_: usize = 0;
    let mut v___x_1556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1561_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_initialLocalTimeType_1546_ = leanh::lean_ctor_get(v_zr_1544_, 0);
                v_transitions_1547_ = leanh::lean_ctor_get(v_zr_1544_, 1);
                v_isSharedCheck_1561_ = (!leanh::lean_is_exclusive(v_zr_1544_)) as u8;
                if v_isSharedCheck_1561_ == 0 {
                    v___x_1549_ = v_zr_1544_;
                    v_isShared_1550_ = v_isSharedCheck_1561_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_transitions_1547_);
                    leanh::lean_inc(v_initialLocalTimeType_1546_);
                    leanh::lean_dec(v_zr_1544_);
                    v___x_1549_ = leanh::lean_box(0);
                    v_isShared_1550_ = v_isSharedCheck_1561_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1551_ = leanh::lean_box(0);
                if v_isShared_1550_ == 0 {
                    leanh::lean_ctor_set(v___x_1549_, 1, v_initialLocalTimeType_1546_);
                    leanh::lean_ctor_set(v___x_1549_, 0, v___x_1551_);
                    v___x_1553_ = v___x_1549_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1560_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1560_, 0, v___x_1551_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_1560_,
                        1,
                        v_initialLocalTimeType_1546_,
                    );
                    v___x_1553_ = v_reuseFailAlloc_1560_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_sz_1554_ = lean_array_size(v_transitions_1547_);
                v___x_1555_ = 0usize;
                v___x_1556_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime_spec__0(v_wallTime_1545_, v_transitions_1547_, v_sz_1554_, v___x_1555_, v___x_1553_);
                leanh::lean_dec_ref(v_transitions_1547_);
                v_fst_1557_ = leanh::lean_ctor_get(v___x_1556_, 0);
                leanh::lean_inc(v_fst_1557_);
                if leanh::lean_obj_tag(v_fst_1557_) == 0 {
                    v_snd_1558_ = leanh::lean_ctor_get(v___x_1556_, 1);
                    leanh::lean_inc(v_snd_1558_);
                    leanh::lean_dec_ref(v___x_1556_);
                    return v_snd_1558_;
                } else {
                    leanh::lean_dec_ref(v___x_1556_);
                    v_val_1559_ = leanh::lean_ctor_get(v_fst_1557_, 0);
                    leanh::lean_inc(v_val_1559_);
                    leanh::lean_dec_ref_known(v_fst_1557_, 1);
                    return v_val_1559_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime___boxed(
    mut v_zr_1562_: *mut leanh::LeanObject,
    mut v_wallTime_1563_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1564_ =
        l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_zr_1562_, v_wallTime_1563_);
    leanh::lean_dec_ref(v_wallTime_1563_);
    return v_res_1564_;
}
pub unsafe fn l_Std_Time_TimeZone_ZoneRules_timezoneAt(
    mut v_zr_1565_: *mut leanh::LeanObject,
    mut v_tm_1566_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_initialLocalTimeType_1567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_transitions_1568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_initialLocalTimeType_1567_ = leanh::lean_ctor_get(v_zr_1565_, 0);
    v_transitions_1568_ = leanh::lean_ctor_get(v_zr_1565_, 1);
    v___x_1569_ = l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_1568_, v_tm_1566_);
    if leanh::lean_obj_tag(v___x_1569_) == 0 {
        let mut v___x_1570_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref_known(v___x_1569_, 1);
        v___x_1570_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_1567_);
        return v___x_1570_;
    } else {
        let mut v_a_1571_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_1571_ = leanh::lean_ctor_get(v___x_1569_, 0);
        leanh::lean_inc(v_a_1571_);
        leanh::lean_dec_ref_known(v___x_1569_, 1);
        return v_a_1571_;
    }
}
pub unsafe fn l_Std_Time_TimeZone_ZoneRules_timezoneAt___boxed(
    mut v_zr_1572_: *mut leanh::LeanObject,
    mut v_tm_1573_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1574_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1574_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v_zr_1572_, v_tm_1573_);
    leanh::lean_dec_ref(v_tm_1573_);
    leanh::lean_dec_ref(v_zr_1572_);
    return v_res_1574_;
}
pub unsafe fn l_Std_Time_TimeZone_ZoneRules_ofTimeZone(
    mut v_tz_1575_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_offset_1576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_abbreviation_1578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isDST_1579_: u8 = 0;
    let mut v___x_1580_: u8 = 0;
    let mut v___x_1581_: u8 = 0;
    let mut v_ltt_1582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_offset_1576_ = leanh::lean_ctor_get(v_tz_1575_, 0);
    v_name_1577_ = leanh::lean_ctor_get(v_tz_1575_, 1);
    v_abbreviation_1578_ = leanh::lean_ctor_get(v_tz_1575_, 2);
    v_isDST_1579_ = leanh::lean_ctor_get_uint8(
        v_tz_1575_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
    );
    v___x_1580_ = 0;
    v___x_1581_ = 1;
    leanh::lean_inc_ref(v_name_1577_);
    leanh::lean_inc_ref(v_abbreviation_1578_);
    leanh::lean_inc(v_offset_1576_);
    v_ltt_1582_ = leanh::lean_alloc_ctor(0, 3, (3) as u32);
    leanh::lean_ctor_set(v_ltt_1582_, 0, v_offset_1576_);
    leanh::lean_ctor_set(v_ltt_1582_, 1, v_abbreviation_1578_);
    leanh::lean_ctor_set(v_ltt_1582_, 2, v_name_1577_);
    leanh::lean_ctor_set_uint8(
        v_ltt_1582_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
        v_isDST_1579_,
    );
    leanh::lean_ctor_set_uint8(
        v_ltt_1582_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 1) as u32,
        v___x_1580_,
    );
    leanh::lean_ctor_set_uint8(
        v_ltt_1582_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 2) as u32,
        v___x_1581_,
    );
    v___x_1583_ = l_Std_Time_TimeZone_ZoneRules_fixedOffsetZone___closed__0;
    v___x_1584_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1584_, 0, v_ltt_1582_);
    leanh::lean_ctor_set(v___x_1584_, 1, v___x_1583_);
    return v___x_1584_;
}
pub unsafe fn l_Std_Time_TimeZone_ZoneRules_ofTimeZone___boxed(
    mut v_tz_1585_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1586_ = l_Std_Time_TimeZone_ZoneRules_ofTimeZone(v_tz_1585_);
    leanh::lean_dec_ref(v_tz_1585_);
    return v_res_1586_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Time_Zoned_ZoneRules(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Time_DateTime(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Zoned_TimeZone(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Std_Time_TimeZone_instInhabitedUTLocal_default =
        _init_l_Std_Time_TimeZone_instInhabitedUTLocal_default();
    l_Std_Time_TimeZone_instInhabitedUTLocal = _init_l_Std_Time_TimeZone_instInhabitedUTLocal();
    l_Std_Time_TimeZone_instInhabitedStdWall_default =
        _init_l_Std_Time_TimeZone_instInhabitedStdWall_default();
    l_Std_Time_TimeZone_instInhabitedStdWall = _init_l_Std_Time_TimeZone_instInhabitedStdWall();
    l_Std_Time_TimeZone_instInhabitedLocalTimeType_default =
        _init_l_Std_Time_TimeZone_instInhabitedLocalTimeType_default();
    leanh::lean_mark_persistent(l_Std_Time_TimeZone_instInhabitedLocalTimeType_default);
    l_Std_Time_TimeZone_instInhabitedLocalTimeType =
        _init_l_Std_Time_TimeZone_instInhabitedLocalTimeType();
    leanh::lean_mark_persistent(l_Std_Time_TimeZone_instInhabitedLocalTimeType);
    l_Std_Time_TimeZone_instInhabitedTransition_default =
        _init_l_Std_Time_TimeZone_instInhabitedTransition_default();
    leanh::lean_mark_persistent(l_Std_Time_TimeZone_instInhabitedTransition_default);
    l_Std_Time_TimeZone_instInhabitedTransition =
        _init_l_Std_Time_TimeZone_instInhabitedTransition();
    leanh::lean_mark_persistent(l_Std_Time_TimeZone_instInhabitedTransition);
    l_Std_Time_TimeZone_instInhabitedZoneRules_default =
        _init_l_Std_Time_TimeZone_instInhabitedZoneRules_default();
    leanh::lean_mark_persistent(l_Std_Time_TimeZone_instInhabitedZoneRules_default);
    l_Std_Time_TimeZone_instInhabitedZoneRules = _init_l_Std_Time_TimeZone_instInhabitedZoneRules();
    leanh::lean_mark_persistent(l_Std_Time_TimeZone_instInhabitedZoneRules);
    l_Std_Time_TimeZone_ZoneRules_UTC = _init_l_Std_Time_TimeZone_ZoneRules_UTC();
    leanh::lean_mark_persistent(l_Std_Time_TimeZone_ZoneRules_UTC);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Time_Zoned_ZoneRules(
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
pub unsafe fn initialize_Std_Time_Zoned_ZoneRules(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Time_DateTime(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Time_Zoned_TimeZone(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Zoned_ZoneRules(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Time_Zoned_ZoneRules(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Time_Zoned_ZoneRules(builtin);
}