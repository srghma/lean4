// Lean compiler output
// Module: Std.Time.Date.PlainDate
// Imports: Std.Time.Date.Basic Std.Time.Date.Unit.Month Std.Time.Date.Unit.Year
use crate::ffi::{
    lean_int_add, lean_int_dec_eq, lean_int_dec_le, lean_int_dec_lt, lean_int_div, lean_int_ediv,
    lean_int_emod, lean_int_mod, lean_int_mul, lean_int_neg, lean_int_sub, lean_nat_to_int,
    lean_string_length,
};
use crate::r#gen::Init::Data::Int::Repr::l_Int_repr;
use crate::r#gen::Init::Data::Ord::Basic::{l_compareLex___boxed, l_compareOn___boxed};
use crate::r#gen::Init::Data::Repr::l_Repr_addAppParen;
use crate::r#gen::Std::Time::Date::Basic::{
    initialize_Std_Time_Date_Basic, runtime_initialize_Std_Time_Date_Basic,
};
use crate::r#gen::Std::Time::Date::Unit::Day::{
    l_Std_Time_Day_instOrdOrdinal___aux__1___boxed, l_Std_Time_Day_instReprOrdinal___lam__0,
};
use crate::r#gen::Std::Time::Date::Unit::Month::{
    initialize_Std_Time_Date_Unit_Month, l_Std_Time_Month_Ordinal_days,
    l_Std_Time_Month_instOrdOrdinal___aux__1___boxed, runtime_initialize_Std_Time_Date_Unit_Month,
};
use crate::r#gen::Std::Time::Date::Unit::Weekday::{
    l_Std_Time_Weekday_ofOrdinal, l_Std_Time_Weekday_toOrdinal,
};
use crate::r#gen::Std::Time::Date::Unit::Year::{
    initialize_Std_Time_Date_Unit_Year, l_Std_Time_Year_Offset_era, l_Std_Time_Year_Offset_weeks,
    l_Std_Time_Year_instOrdOffset___aux__1___boxed, runtime_initialize_Std_Time_Date_Unit_Year,
};
use crate::r#gen::Std::Time::Date::ValidDate::{
    l_Std_Time_ValidDate_dayOfYear, l_Std_Time_ValidDate_ofOrdinal,
};
pub static l_Std_Time_instReprPlainDate_repr___redArg___closed__0_value:
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
static mut l_Std_Time_instReprPlainDate_repr___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainDate_repr___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprPlainDate_repr___redArg___closed__1_value:
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
    m_data: [121, 101, 97, 114, 0],
};
static mut l_Std_Time_instReprPlainDate_repr___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainDate_repr___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprPlainDate_repr___redArg___closed__2_value:
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
        core::ptr::addr_of!(l_Std_Time_instReprPlainDate_repr___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_instReprPlainDate_repr___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainDate_repr___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprPlainDate_repr___redArg___closed__3_value:
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
        core::ptr::addr_of!(l_Std_Time_instReprPlainDate_repr___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_instReprPlainDate_repr___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainDate_repr___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprPlainDate_repr___redArg___closed__4_value:
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
static mut l_Std_Time_instReprPlainDate_repr___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainDate_repr___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprPlainDate_repr___redArg___closed__5_value:
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
        core::ptr::addr_of!(l_Std_Time_instReprPlainDate_repr___redArg___closed__4_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_instReprPlainDate_repr___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainDate_repr___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprPlainDate_repr___redArg___closed__6_value:
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
    m_data: [100, 97, 121, 0],
};
static mut l_Std_Time_instReprPlainDate_repr___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainDate_repr___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprPlainDate_repr___redArg___closed__7_value:
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
        core::ptr::addr_of!(l_Std_Time_instReprPlainDate_repr___redArg___closed__6_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_instReprPlainDate_repr___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainDate_repr___redArg___closed__7_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instReprPlainDate_repr___redArg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_instReprPlainDate_repr___redArg___closed__9_value:
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
    m_data: [118, 97, 108, 105, 100, 0],
};
static mut l_Std_Time_instReprPlainDate_repr___redArg___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainDate_repr___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprPlainDate_repr___redArg___closed__10_value:
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
        core::ptr::addr_of!(l_Std_Time_instReprPlainDate_repr___redArg___closed__9_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_instReprPlainDate_repr___redArg___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainDate_repr___redArg___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprPlainDate_repr___redArg___closed__11_value:
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
static mut l_Std_Time_instReprPlainDate_repr___redArg___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainDate_repr___redArg___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprPlainDate_repr___redArg___closed__12_value:
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
        core::ptr::addr_of!(l_Std_Time_instReprPlainDate_repr___redArg___closed__11_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_instReprPlainDate_repr___redArg___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainDate_repr___redArg___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprPlainDate_repr___redArg___closed__13_value:
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
static mut l_Std_Time_instReprPlainDate_repr___redArg___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainDate_repr___redArg___closed__13_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_instReprPlainDate_repr___redArg___closed__14_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instReprPlainDate_repr___redArg___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instReprPlainDate_repr___redArg___closed__15_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instReprPlainDate_repr___redArg___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_instReprPlainDate_repr___redArg___closed__16_value:
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
        core::ptr::addr_of!(l_Std_Time_instReprPlainDate_repr___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_instReprPlainDate_repr___redArg___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainDate_repr___redArg___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprPlainDate_repr___redArg___closed__17_value:
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
        core::ptr::addr_of!(l_Std_Time_instReprPlainDate_repr___redArg___closed__13_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_instReprPlainDate_repr___redArg___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainDate_repr___redArg___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprPlainDate_repr___redArg___closed__18_value:
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
        core::ptr::addr_of!(l_Std_Time_instReprPlainDate_repr___redArg___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_instReprPlainDate_repr___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_instReprPlainDate_repr___redArg___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainDate_repr___redArg___closed__18_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_instReprPlainDate_repr___redArg___closed__19_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instReprPlainDate_repr___redArg___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_instReprPlainDate_repr___redArg___closed__20_value:
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
static mut l_Std_Time_instReprPlainDate_repr___redArg___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainDate_repr___redArg___closed__20_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprPlainDate_repr___redArg___closed__21_value:
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
        core::ptr::addr_of!(l_Std_Time_instReprPlainDate_repr___redArg___closed__20_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_instReprPlainDate_repr___redArg___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainDate_repr___redArg___closed__21_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprPlainDate_repr___redArg___closed__22_value:
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
    m_data: [109, 111, 110, 116, 104, 0],
};
static mut l_Std_Time_instReprPlainDate_repr___redArg___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainDate_repr___redArg___closed__22_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprPlainDate_repr___redArg___closed__23_value:
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
        core::ptr::addr_of!(l_Std_Time_instReprPlainDate_repr___redArg___closed__22_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_instReprPlainDate_repr___redArg___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainDate_repr___redArg___closed__23_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_instReprPlainDate_repr___redArg___closed__24_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instReprPlainDate_repr___redArg___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instReprPlainDate_repr___redArg___closed__25: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_instReprPlainDate___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instReprPlainDate_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instReprPlainDate___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainDate___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_instReprPlainDate: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainDate___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_instInhabitedPlainDate___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainDate___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDate___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainDate___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDate___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainDate___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDate___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainDate___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDate___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainDate___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDate___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainDate___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDate___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainDate___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDate___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainDate___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDate___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainDate___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDate___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainDate___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDate___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainDate___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDate___closed__11_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainDate___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDate___closed__12_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainDate___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDate___closed__13_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainDate___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDate___closed__14_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainDate___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDate___closed__15_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainDate___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDate___closed__16_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainDate___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDate___closed__17_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainDate___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDate___closed__18_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainDate___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_instInhabitedPlainDate: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_instOrdPlainDate___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instOrdPlainDate___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instOrdPlainDate___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdPlainDate___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instOrdPlainDate___closed__1_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instOrdPlainDate___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instOrdPlainDate___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdPlainDate___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instOrdPlainDate___closed__2_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instOrdPlainDate___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instOrdPlainDate___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdPlainDate___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instOrdPlainDate___closed__3_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_Year_instOrdOffset___aux__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instOrdPlainDate___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdPlainDate___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instOrdPlainDate___closed__4_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_Month_instOrdOrdinal___aux__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instOrdPlainDate___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdPlainDate___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instOrdPlainDate___closed__5_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_Day_instOrdOrdinal___aux__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instOrdPlainDate___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdPlainDate___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instOrdPlainDate___closed__6_value: crate::leanh::LeanClosureObject<4> =
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
            core::ptr::addr_of!(l_Std_Time_instOrdPlainDate___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_instOrdPlainDate___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_instOrdPlainDate___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdPlainDate___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instOrdPlainDate___closed__7_value: crate::leanh::LeanClosureObject<4> =
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
            core::ptr::addr_of!(l_Std_Time_instOrdPlainDate___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_instOrdPlainDate___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_instOrdPlainDate___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdPlainDate___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instOrdPlainDate___closed__8_value: crate::leanh::LeanClosureObject<4> =
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
            core::ptr::addr_of!(l_Std_Time_instOrdPlainDate___closed__5_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_instOrdPlainDate___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_instOrdPlainDate___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdPlainDate___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instOrdPlainDate___closed__9_value: crate::leanh::LeanClosureObject<4> =
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
            core::ptr::addr_of!(l_Std_Time_instOrdPlainDate___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_instOrdPlainDate___closed__8_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_instOrdPlainDate___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdPlainDate___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instOrdPlainDate___closed__10_value: crate::leanh::LeanClosureObject<4> =
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
            core::ptr::addr_of!(l_Std_Time_instOrdPlainDate___closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_instOrdPlainDate___closed__9_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_instOrdPlainDate___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdPlainDate___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_instOrdPlainDate: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdPlainDate___closed__10_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDate_instInhabited___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDate_instInhabited___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_PlainDate_instInhabited: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDate_ofEpochDay___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDate_ofEpochDay___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDate_ofEpochDay___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDate_ofEpochDay___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDate_ofEpochDay___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDate_ofEpochDay___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDate_ofEpochDay___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDate_ofEpochDay___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDate_ofEpochDay___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDate_ofEpochDay___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDate_ofEpochDay___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDate_ofEpochDay___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDate_ofEpochDay___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDate_ofEpochDay___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDate_ofEpochDay___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDate_ofEpochDay___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDate_ofEpochDay___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDate_ofEpochDay___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDate_ofEpochDay___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDate_ofEpochDay___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDate_ofEpochDay___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDate_ofEpochDay___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDate_ofEpochDay___closed__11_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDate_ofEpochDay___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDate_ofEpochDay___closed__12_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDate_ofEpochDay___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDate_ofEpochDay___closed__13_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDate_ofEpochDay___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDate_weekOfMonth___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDate_weekOfMonth___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDate_toEpochDay___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDate_toEpochDay___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDate_toEpochDay___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDate_toEpochDay___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDate_rollOver___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDate_rollOver___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDate_rollOver___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDate_rollOver___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDate_rollOver___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDate_rollOver___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDate_rollOver___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDate_rollOver___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDate_rollOver___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDate_rollOver___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDate_rollOver___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDate_rollOver___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDate_rollOver___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDate_rollOver___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDate_rollOver___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDate_rollOver___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDate_weekday___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDate_weekday___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDate_weekday___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDate_weekday___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDate_weekday___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDate_weekday___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDate_weekday___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDate_weekday___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDate_alignedWeekOfMonth___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDate_alignedWeekOfMonth___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDate_alignedWeekOfMonth___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDate_alignedWeekOfMonth___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_PlainDate_instHAddOffset___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_PlainDate_addDays___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_PlainDate_instHAddOffset___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDate_instHAddOffset___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_PlainDate_instHAddOffset: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDate_instHAddOffset___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_PlainDate_instHSubOffset___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_PlainDate_subDays___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_PlainDate_instHSubOffset___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDate_instHSubOffset___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_PlainDate_instHSubOffset: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDate_instHSubOffset___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_PlainDate_instHAddOffset__1___closed__0_value:
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
    m_fun: l_Std_Time_PlainDate_addWeeks___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_PlainDate_instHAddOffset__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDate_instHAddOffset__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_PlainDate_instHAddOffset__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDate_instHAddOffset__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_PlainDate_instHSubOffset__1___closed__0_value:
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
    m_fun: l_Std_Time_PlainDate_subWeeks___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_PlainDate_instHSubOffset__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDate_instHSubOffset__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_PlainDate_instHSubOffset__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDate_instHSubOffset__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1114_ = crate::leanh::lean_unsigned_to_nat(7);
    v___x_1115_ = lean_nat_to_int(v___x_1114_);
    return v___x_1115_;
}
pub unsafe fn _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1123_ = l_Std_Time_instReprPlainDate_repr___redArg___closed__0;
    v___x_1124_ = lean_string_length(v___x_1123_);
    return v___x_1124_;
}
pub unsafe fn _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1125_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainDate_repr___redArg___closed__14),
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainDate_repr___redArg___closed__14_once),
        _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__14,
    );
    v___x_1126_ = lean_nat_to_int(v___x_1125_);
    return v___x_1126_;
}
pub unsafe fn _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1134_ = crate::leanh::lean_unsigned_to_nat(8);
    v___x_1135_ = lean_nat_to_int(v___x_1134_);
    return v___x_1135_;
}
pub unsafe fn _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__24()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1142_ = crate::leanh::lean_unsigned_to_nat(9);
    v___x_1143_ = lean_nat_to_int(v___x_1142_);
    return v___x_1143_;
}
pub unsafe fn _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1144_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1145_ = lean_nat_to_int(v___x_1144_);
    return v___x_1145_;
}
pub unsafe fn l_Std_Time_instReprPlainDate_repr___redArg(
    mut v_x_1146_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_year_1147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_month_1148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_day_1149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1156_: u8 = 0;
    let mut v___y_1157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1191_: u8 = 0;
    let mut v___x_1192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: u8 = 0;
    let mut v___x_1205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1212_: u8 = 0;
    let mut v___x_1213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_year_1147_ = crate::leanh::lean_ctor_get(v_x_1146_, 0);
                v_month_1148_ = crate::leanh::lean_ctor_get(v_x_1146_, 1);
                v_day_1149_ = crate::leanh::lean_ctor_get(v_x_1146_, 2);
                v___x_1150_ = l_Std_Time_instReprPlainDate_repr___redArg___closed__5;
                v___x_1186_ = l_Std_Time_instReprPlainDate_repr___redArg___closed__18;
                v___x_1187_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDate_repr___redArg___closed__19
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDate_repr___redArg___closed__19_once
                    ),
                    _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__19,
                );
                v___x_1210_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1211_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDate_repr___redArg___closed__25
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once
                    ),
                    _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25,
                );
                v___x_1212_ = lean_int_dec_lt(v_year_1147_, v___x_1211_);
                if v___x_1212_ == 0 {
                    v___x_1213_ = l_Int_repr(v_year_1147_);
                    v___x_1214_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1214_, 0, v___x_1213_);
                    v___y_1189_ = v___x_1214_;
                    state = 2;
                    continue;
                } else {
                    v___x_1215_ = l_Int_repr(v_year_1147_);
                    v___x_1216_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1216_, 0, v___x_1215_);
                    v___x_1217_ = l_Repr_addAppParen(v___x_1216_, v___x_1210_);
                    v___y_1189_ = v___x_1217_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v___y_1153_);
                v___x_1158_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1158_, 0, v___y_1153_);
                crate::leanh::lean_ctor_set(v___x_1158_, 1, v___y_1157_);
                v___x_1159_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1159_, 0, v___x_1158_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1159_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___y_1156_,
                );
                v___x_1160_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1160_, 0, v___y_1154_);
                crate::leanh::lean_ctor_set(v___x_1160_, 1, v___x_1159_);
                crate::leanh::lean_inc_n(v___y_1152_, 2);
                v___x_1161_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1161_, 0, v___x_1160_);
                crate::leanh::lean_ctor_set(v___x_1161_, 1, v___y_1152_);
                crate::leanh::lean_inc_n(v___y_1155_, 2);
                v___x_1162_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1162_, 0, v___x_1161_);
                crate::leanh::lean_ctor_set(v___x_1162_, 1, v___y_1155_);
                v___x_1163_ = l_Std_Time_instReprPlainDate_repr___redArg___closed__7;
                v___x_1164_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1164_, 0, v___x_1162_);
                crate::leanh::lean_ctor_set(v___x_1164_, 1, v___x_1163_);
                v___x_1165_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1165_, 0, v___x_1164_);
                crate::leanh::lean_ctor_set(v___x_1165_, 1, v___x_1150_);
                v___x_1166_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_instReprPlainDate_repr___redArg___closed__8),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once
                    ),
                    _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8,
                );
                v___x_1167_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1168_ = l_Std_Time_Day_instReprOrdinal___lam__0(v_day_1149_, v___x_1167_);
                v___x_1169_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1169_, 0, v___x_1166_);
                crate::leanh::lean_ctor_set(v___x_1169_, 1, v___x_1168_);
                v___x_1170_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1170_, 0, v___x_1169_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1170_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___y_1156_,
                );
                v___x_1171_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1171_, 0, v___x_1165_);
                crate::leanh::lean_ctor_set(v___x_1171_, 1, v___x_1170_);
                v___x_1172_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1172_, 0, v___x_1171_);
                crate::leanh::lean_ctor_set(v___x_1172_, 1, v___y_1152_);
                v___x_1173_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1173_, 0, v___x_1172_);
                crate::leanh::lean_ctor_set(v___x_1173_, 1, v___y_1155_);
                v___x_1174_ = l_Std_Time_instReprPlainDate_repr___redArg___closed__10;
                v___x_1175_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1175_, 0, v___x_1173_);
                crate::leanh::lean_ctor_set(v___x_1175_, 1, v___x_1174_);
                v___x_1176_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1176_, 0, v___x_1175_);
                crate::leanh::lean_ctor_set(v___x_1176_, 1, v___x_1150_);
                v___x_1177_ = l_Std_Time_instReprPlainDate_repr___redArg___closed__12;
                v___x_1178_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1178_, 0, v___x_1176_);
                crate::leanh::lean_ctor_set(v___x_1178_, 1, v___x_1177_);
                v___x_1179_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDate_repr___redArg___closed__15
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDate_repr___redArg___closed__15_once
                    ),
                    _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__15,
                );
                v___x_1180_ = l_Std_Time_instReprPlainDate_repr___redArg___closed__16;
                v___x_1181_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1181_, 0, v___x_1180_);
                crate::leanh::lean_ctor_set(v___x_1181_, 1, v___x_1178_);
                v___x_1182_ = l_Std_Time_instReprPlainDate_repr___redArg___closed__17;
                v___x_1183_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1183_, 0, v___x_1181_);
                crate::leanh::lean_ctor_set(v___x_1183_, 1, v___x_1182_);
                v___x_1184_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1184_, 0, v___x_1179_);
                crate::leanh::lean_ctor_set(v___x_1184_, 1, v___x_1183_);
                v___x_1185_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1185_, 0, v___x_1184_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1185_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___y_1156_,
                );
                return v___x_1185_;
            }
            2 => {
                v___x_1190_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1190_, 0, v___x_1187_);
                crate::leanh::lean_ctor_set(v___x_1190_, 1, v___y_1189_);
                v___x_1191_ = 0;
                v___x_1192_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1192_, 0, v___x_1190_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1192_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1191_,
                );
                v___x_1193_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1193_, 0, v___x_1186_);
                crate::leanh::lean_ctor_set(v___x_1193_, 1, v___x_1192_);
                v___x_1194_ = l_Std_Time_instReprPlainDate_repr___redArg___closed__21;
                v___x_1195_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1195_, 0, v___x_1193_);
                crate::leanh::lean_ctor_set(v___x_1195_, 1, v___x_1194_);
                v___x_1196_ = crate::leanh::lean_box(1);
                v___x_1197_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1197_, 0, v___x_1195_);
                crate::leanh::lean_ctor_set(v___x_1197_, 1, v___x_1196_);
                v___x_1198_ = l_Std_Time_instReprPlainDate_repr___redArg___closed__23;
                v___x_1199_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1199_, 0, v___x_1197_);
                crate::leanh::lean_ctor_set(v___x_1199_, 1, v___x_1198_);
                v___x_1200_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1200_, 0, v___x_1199_);
                crate::leanh::lean_ctor_set(v___x_1200_, 1, v___x_1150_);
                v___x_1201_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDate_repr___redArg___closed__24
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDate_repr___redArg___closed__24_once
                    ),
                    _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__24,
                );
                v___x_1202_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1203_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDate_repr___redArg___closed__25
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once
                    ),
                    _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25,
                );
                v___x_1204_ = lean_int_dec_lt(v_month_1148_, v___x_1203_);
                if v___x_1204_ == 0 {
                    v___x_1205_ = l_Int_repr(v_month_1148_);
                    v___x_1206_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1206_, 0, v___x_1205_);
                    v___y_1152_ = v___x_1194_;
                    v___y_1153_ = v___x_1201_;
                    v___y_1154_ = v___x_1200_;
                    v___y_1155_ = v___x_1196_;
                    v___y_1156_ = v___x_1191_;
                    v___y_1157_ = v___x_1206_;
                    state = 1;
                    continue;
                } else {
                    v___x_1207_ = l_Int_repr(v_month_1148_);
                    v___x_1208_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1208_, 0, v___x_1207_);
                    v___x_1209_ = l_Repr_addAppParen(v___x_1208_, v___x_1202_);
                    v___y_1152_ = v___x_1194_;
                    v___y_1153_ = v___x_1201_;
                    v___y_1154_ = v___x_1200_;
                    v___y_1155_ = v___x_1196_;
                    v___y_1156_ = v___x_1191_;
                    v___y_1157_ = v___x_1209_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_instReprPlainDate_repr___redArg___boxed(
    mut v_x_1218_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1219_ = l_Std_Time_instReprPlainDate_repr___redArg(v_x_1218_);
    crate::leanh::lean_dec_ref(v_x_1218_);
    return v_res_1219_;
}
pub unsafe fn l_Std_Time_instReprPlainDate_repr(
    mut v_x_1220_: *mut crate::leanh::LeanObject,
    mut v_prec_1221_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1222_ = l_Std_Time_instReprPlainDate_repr___redArg(v_x_1220_);
    return v___x_1222_;
}
pub unsafe fn l_Std_Time_instReprPlainDate_repr___boxed(
    mut v_x_1223_: *mut crate::leanh::LeanObject,
    mut v_prec_1224_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1225_ = l_Std_Time_instReprPlainDate_repr(v_x_1223_, v_prec_1224_);
    crate::leanh::lean_dec(v_prec_1224_);
    crate::leanh::lean_dec_ref(v_x_1223_);
    return v_res_1225_;
}
pub unsafe fn l_Std_Time_instDecidableEqPlainDate_decEq(
    mut v_x_1228_: *mut crate::leanh::LeanObject,
    mut v_x_1229_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_year_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_month_1231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_day_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_year_1233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_month_1234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_day_1235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1236_: u8 = 0;
    v_year_1230_ = crate::leanh::lean_ctor_get(v_x_1228_, 0);
    v_month_1231_ = crate::leanh::lean_ctor_get(v_x_1228_, 1);
    v_day_1232_ = crate::leanh::lean_ctor_get(v_x_1228_, 2);
    v_year_1233_ = crate::leanh::lean_ctor_get(v_x_1229_, 0);
    v_month_1234_ = crate::leanh::lean_ctor_get(v_x_1229_, 1);
    v_day_1235_ = crate::leanh::lean_ctor_get(v_x_1229_, 2);
    v___x_1236_ = lean_int_dec_eq(v_year_1230_, v_year_1233_);
    if v___x_1236_ == 0 {
        return v___x_1236_;
    } else {
        let mut v___x_1237_: u8 = 0;
        v___x_1237_ = lean_int_dec_eq(v_month_1231_, v_month_1234_);
        if v___x_1237_ == 0 {
            return v___x_1237_;
        } else {
            let mut v___x_1238_: u8 = 0;
            v___x_1238_ = lean_int_dec_eq(v_day_1232_, v_day_1235_);
            return v___x_1238_;
        }
    }
}
pub unsafe fn l_Std_Time_instDecidableEqPlainDate_decEq___boxed(
    mut v_x_1239_: *mut crate::leanh::LeanObject,
    mut v_x_1240_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1241_: u8 = 0;
    let mut v_r_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1241_ = l_Std_Time_instDecidableEqPlainDate_decEq(v_x_1239_, v_x_1240_);
    crate::leanh::lean_dec_ref(v_x_1240_);
    crate::leanh::lean_dec_ref(v_x_1239_);
    v_r_1242_ = crate::leanh::lean_box((v_res_1241_) as usize);
    return v_r_1242_;
}
pub unsafe fn l_Std_Time_instDecidableEqPlainDate(
    mut v_x_1243_: *mut crate::leanh::LeanObject,
    mut v_x_1244_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1245_: u8 = 0;
    v___x_1245_ = l_Std_Time_instDecidableEqPlainDate_decEq(v_x_1243_, v_x_1244_);
    return v___x_1245_;
}
pub unsafe fn l_Std_Time_instDecidableEqPlainDate___boxed(
    mut v_x_1246_: *mut crate::leanh::LeanObject,
    mut v_x_1247_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1248_: u8 = 0;
    let mut v_r_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1248_ = l_Std_Time_instDecidableEqPlainDate(v_x_1246_, v_x_1247_);
    crate::leanh::lean_dec_ref(v_x_1247_);
    crate::leanh::lean_dec_ref(v_x_1246_);
    v_r_1249_ = crate::leanh::lean_box((v_res_1248_) as usize);
    return v_r_1249_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDate___closed__0() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1250_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_1251_ = lean_nat_to_int(v___x_1250_);
    return v___x_1251_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDate___closed__1() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1252_ = crate::leanh::lean_unsigned_to_nat(11);
    v___x_1253_ = lean_nat_to_int(v___x_1252_);
    return v___x_1253_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDate___closed__2() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1254_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__1_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__1,
    );
    v___x_1255_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__0,
    );
    v___x_1256_ = lean_int_add(v___x_1255_, v___x_1254_);
    return v___x_1256_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDate___closed__3() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1257_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__0,
    );
    v___x_1258_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__2_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__2,
    );
    v___x_1259_ = lean_int_sub(v___x_1258_, v___x_1257_);
    return v___x_1259_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDate___closed__4() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1260_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__0,
    );
    v___x_1261_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__3_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__3,
    );
    v_range_1262_ = lean_int_add(v___x_1261_, v___x_1260_);
    return v_range_1262_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDate___closed__5() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1263_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__0,
    );
    v___x_1264_ = lean_int_sub(v___x_1263_, v___x_1263_);
    return v___x_1264_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDate___closed__6() -> *mut crate::leanh::LeanObject
{
    let mut v_range_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1265_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__4_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__4,
    );
    v___x_1266_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__5),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__5_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__5,
    );
    v___x_1267_ = lean_int_emod(v___x_1266_, v_range_1265_);
    return v___x_1267_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDate___closed__7() -> *mut crate::leanh::LeanObject
{
    let mut v_range_1268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1268_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__4_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__4,
    );
    v___x_1269_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__6),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__6_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__6,
    );
    v___x_1270_ = lean_int_add(v___x_1269_, v_range_1268_);
    return v___x_1270_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDate___closed__8() -> *mut crate::leanh::LeanObject
{
    let mut v_range_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1271_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__4_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__4,
    );
    v___x_1272_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__7),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__7_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__7,
    );
    v___x_1273_ = lean_int_emod(v___x_1272_, v_range_1271_);
    return v___x_1273_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDate___closed__9() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1274_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__0,
    );
    v___x_1275_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__8),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__8_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__8,
    );
    v___x_1276_ = lean_int_add(v___x_1275_, v___x_1274_);
    return v___x_1276_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDate___closed__10() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1277_ = crate::leanh::lean_unsigned_to_nat(30);
    v___x_1278_ = lean_nat_to_int(v___x_1277_);
    return v___x_1278_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDate___closed__11() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1279_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__10),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__10_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__10,
    );
    v___x_1280_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__0,
    );
    v___x_1281_ = lean_int_add(v___x_1280_, v___x_1279_);
    return v___x_1281_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDate___closed__12() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1282_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__0,
    );
    v___x_1283_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__11),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__11_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__11,
    );
    v___x_1284_ = lean_int_sub(v___x_1283_, v___x_1282_);
    return v___x_1284_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDate___closed__13() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_1287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1285_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__0,
    );
    v___x_1286_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__12),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__12_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__12,
    );
    v_range_1287_ = lean_int_add(v___x_1286_, v___x_1285_);
    return v_range_1287_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDate___closed__14() -> *mut crate::leanh::LeanObject
{
    let mut v_range_1288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1288_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__13),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__13_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__13,
    );
    v___x_1289_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__5),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__5_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__5,
    );
    v___x_1290_ = lean_int_emod(v___x_1289_, v_range_1288_);
    return v___x_1290_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDate___closed__15() -> *mut crate::leanh::LeanObject
{
    let mut v_range_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1291_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__13),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__13_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__13,
    );
    v___x_1292_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__14),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__14_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__14,
    );
    v___x_1293_ = lean_int_add(v___x_1292_, v_range_1291_);
    return v___x_1293_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDate___closed__16() -> *mut crate::leanh::LeanObject
{
    let mut v_range_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1294_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__13),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__13_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__13,
    );
    v___x_1295_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__15),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__15_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__15,
    );
    v___x_1296_ = lean_int_emod(v___x_1295_, v_range_1294_);
    return v___x_1296_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDate___closed__17() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1297_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__0,
    );
    v___x_1298_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__16),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__16_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__16,
    );
    v___x_1299_ = lean_int_add(v___x_1298_, v___x_1297_);
    return v___x_1299_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDate___closed__18() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1300_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__17),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__17_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__17,
    );
    v___x_1301_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__9),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__9_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__9,
    );
    v___x_1302_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__0,
    );
    v___x_1303_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1303_, 0, v___x_1302_);
    crate::leanh::lean_ctor_set(v___x_1303_, 1, v___x_1301_);
    crate::leanh::lean_ctor_set(v___x_1303_, 2, v___x_1300_);
    return v___x_1303_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDate() -> *mut crate::leanh::LeanObject {
    let mut v___x_1304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1304_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__18),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__18_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__18,
    );
    return v___x_1304_;
}
pub unsafe fn l_Std_Time_instOrdPlainDate___lam__0(
    mut v_x_1305_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_year_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_year_1306_ = crate::leanh::lean_ctor_get(v_x_1305_, 0);
    crate::leanh::lean_inc(v_year_1306_);
    return v_year_1306_;
}
pub unsafe fn l_Std_Time_instOrdPlainDate___lam__0___boxed(
    mut v_x_1307_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1308_ = l_Std_Time_instOrdPlainDate___lam__0(v_x_1307_);
    crate::leanh::lean_dec_ref(v_x_1307_);
    return v_res_1308_;
}
pub unsafe fn l_Std_Time_instOrdPlainDate___lam__1(
    mut v_x_1309_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_month_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_month_1310_ = crate::leanh::lean_ctor_get(v_x_1309_, 1);
    crate::leanh::lean_inc(v_month_1310_);
    return v_month_1310_;
}
pub unsafe fn l_Std_Time_instOrdPlainDate___lam__1___boxed(
    mut v_x_1311_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1312_ = l_Std_Time_instOrdPlainDate___lam__1(v_x_1311_);
    crate::leanh::lean_dec_ref(v_x_1311_);
    return v_res_1312_;
}
pub unsafe fn l_Std_Time_instOrdPlainDate___lam__2(
    mut v_x_1313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_day_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_day_1314_ = crate::leanh::lean_ctor_get(v_x_1313_, 2);
    crate::leanh::lean_inc(v_day_1314_);
    return v_day_1314_;
}
pub unsafe fn l_Std_Time_instOrdPlainDate___lam__2___boxed(
    mut v_x_1315_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1316_ = l_Std_Time_instOrdPlainDate___lam__2(v_x_1315_);
    crate::leanh::lean_dec_ref(v_x_1315_);
    return v_res_1316_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1339_ = crate::leanh::lean_unsigned_to_nat(4);
    v___x_1340_ = lean_nat_to_int(v___x_1339_);
    return v___x_1340_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1341_ = crate::leanh::lean_unsigned_to_nat(400);
    v___x_1342_ = lean_nat_to_int(v___x_1341_);
    return v___x_1342_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1343_ = crate::leanh::lean_unsigned_to_nat(100);
    v___x_1344_ = lean_nat_to_int(v___x_1343_);
    return v___x_1344_;
}
pub unsafe fn l_Std_Time_PlainDate_ofYearMonthDayClip(
    mut v_year_1345_: *mut crate::leanh::LeanObject,
    mut v_month_1346_: *mut crate::leanh::LeanObject,
    mut v_day_1347_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1349_: u8 = 0;
    let mut v_max_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: u8 = 0;
    let mut v___x_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: u8 = 0;
    let mut v___x_1361_: u8 = 0;
    let mut v___x_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1354_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once
                    ),
                    _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0,
                );
                v___x_1355_ = lean_int_mod(v_year_1345_, v___x_1354_);
                v___x_1356_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDate_repr___redArg___closed__25
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once
                    ),
                    _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25,
                );
                v___x_1361_ = lean_int_dec_eq(v___x_1355_, v___x_1356_);
                crate::leanh::lean_dec(v___x_1355_);
                if v___x_1361_ == 0 {
                    v___y_1349_ = v___x_1361_;
                    state = 1;
                    continue;
                } else {
                    v___x_1362_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once
                        ),
                        _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2,
                    );
                    v___x_1363_ = lean_int_mod(v_year_1345_, v___x_1362_);
                    v___x_1364_ = lean_int_dec_eq(v___x_1363_, v___x_1356_);
                    crate::leanh::lean_dec(v___x_1363_);
                    if v___x_1364_ == 0 {
                        if v___x_1361_ == 0 {
                            state = 2;
                            continue;
                        } else {
                            v___y_1349_ = v___x_1361_;
                            state = 1;
                            continue;
                        }
                    } else {
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v_max_1350_ = l_Std_Time_Month_Ordinal_days(v___y_1349_, v_month_1346_);
                v___x_1351_ = lean_int_dec_lt(v_max_1350_, v_day_1347_);
                if v___x_1351_ == 0 {
                    crate::leanh::lean_dec(v_max_1350_);
                    v___x_1352_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1352_, 0, v_year_1345_);
                    crate::leanh::lean_ctor_set(v___x_1352_, 1, v_month_1346_);
                    crate::leanh::lean_ctor_set(v___x_1352_, 2, v_day_1347_);
                    return v___x_1352_;
                } else {
                    crate::leanh::lean_dec(v_day_1347_);
                    v___x_1353_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1353_, 0, v_year_1345_);
                    crate::leanh::lean_ctor_set(v___x_1353_, 1, v_month_1346_);
                    crate::leanh::lean_ctor_set(v___x_1353_, 2, v_max_1350_);
                    return v___x_1353_;
                }
            }
            2 => {
                v___x_1358_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once
                    ),
                    _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1,
                );
                v___x_1359_ = lean_int_mod(v_year_1345_, v___x_1358_);
                v___x_1360_ = lean_int_dec_eq(v___x_1359_, v___x_1356_);
                crate::leanh::lean_dec(v___x_1359_);
                v___y_1349_ = v___x_1360_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Std_Time_PlainDate_instInhabited___closed__0() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1365_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__17),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__17_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__17,
    );
    v___x_1366_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__9),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__9_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__9,
    );
    v___x_1367_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainDate_repr___redArg___closed__25),
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once),
        _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25,
    );
    v___x_1368_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1368_, 0, v___x_1367_);
    crate::leanh::lean_ctor_set(v___x_1368_, 1, v___x_1366_);
    crate::leanh::lean_ctor_set(v___x_1368_, 2, v___x_1365_);
    return v___x_1368_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_instInhabited() -> *mut crate::leanh::LeanObject {
    let mut v___x_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1369_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_instInhabited___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_instInhabited___closed__0_once),
        _init_l_Std_Time_PlainDate_instInhabited___closed__0,
    );
    return v___x_1369_;
}
pub unsafe fn l_Std_Time_PlainDate_ofYearMonthDay_x3f(
    mut v_year_1370_: *mut crate::leanh::LeanObject,
    mut v_month_1371_: *mut crate::leanh::LeanObject,
    mut v_day_1372_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1374_: u8 = 0;
    let mut v___x_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: u8 = 0;
    let mut v___x_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: u8 = 0;
    let mut v___x_1387_: u8 = 0;
    let mut v___x_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1380_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once
                    ),
                    _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0,
                );
                v___x_1381_ = lean_int_mod(v_year_1370_, v___x_1380_);
                v___x_1382_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDate_repr___redArg___closed__25
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once
                    ),
                    _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25,
                );
                v___x_1387_ = lean_int_dec_eq(v___x_1381_, v___x_1382_);
                crate::leanh::lean_dec(v___x_1381_);
                if v___x_1387_ == 0 {
                    v___y_1374_ = v___x_1387_;
                    state = 1;
                    continue;
                } else {
                    v___x_1388_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once
                        ),
                        _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2,
                    );
                    v___x_1389_ = lean_int_mod(v_year_1370_, v___x_1388_);
                    v___x_1390_ = lean_int_dec_eq(v___x_1389_, v___x_1382_);
                    crate::leanh::lean_dec(v___x_1389_);
                    if v___x_1390_ == 0 {
                        if v___x_1387_ == 0 {
                            state = 2;
                            continue;
                        } else {
                            v___y_1374_ = v___x_1387_;
                            state = 1;
                            continue;
                        }
                    } else {
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1375_ = l_Std_Time_Month_Ordinal_days(v___y_1374_, v_month_1371_);
                v___x_1376_ = lean_int_dec_le(v_day_1372_, v___x_1375_);
                crate::leanh::lean_dec(v___x_1375_);
                if v___x_1376_ == 0 {
                    crate::leanh::lean_dec(v_day_1372_);
                    crate::leanh::lean_dec(v_month_1371_);
                    crate::leanh::lean_dec(v_year_1370_);
                    v___x_1377_ = crate::leanh::lean_box(0);
                    return v___x_1377_;
                } else {
                    v___x_1378_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1378_, 0, v_year_1370_);
                    crate::leanh::lean_ctor_set(v___x_1378_, 1, v_month_1371_);
                    crate::leanh::lean_ctor_set(v___x_1378_, 2, v_day_1372_);
                    v___x_1379_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1379_, 0, v___x_1378_);
                    return v___x_1379_;
                }
            }
            2 => {
                v___x_1384_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once
                    ),
                    _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1,
                );
                v___x_1385_ = lean_int_mod(v_year_1370_, v___x_1384_);
                v___x_1386_ = lean_int_dec_eq(v___x_1385_, v___x_1382_);
                crate::leanh::lean_dec(v___x_1385_);
                v___y_1374_ = v___x_1386_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainDate_ofYearOrdinal(
    mut v_year_1391_: *mut crate::leanh::LeanObject,
    mut v_ordinal_1392_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1394_: u8 = 0;
    let mut v_val_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: u8 = 0;
    let mut v___x_1406_: u8 = 0;
    let mut v___x_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1399_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once
                    ),
                    _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0,
                );
                v___x_1400_ = lean_int_mod(v_year_1391_, v___x_1399_);
                v___x_1401_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDate_repr___redArg___closed__25
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once
                    ),
                    _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25,
                );
                v___x_1406_ = lean_int_dec_eq(v___x_1400_, v___x_1401_);
                crate::leanh::lean_dec(v___x_1400_);
                if v___x_1406_ == 0 {
                    v___y_1394_ = v___x_1406_;
                    state = 1;
                    continue;
                } else {
                    v___x_1407_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once
                        ),
                        _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2,
                    );
                    v___x_1408_ = lean_int_mod(v_year_1391_, v___x_1407_);
                    v___x_1409_ = lean_int_dec_eq(v___x_1408_, v___x_1401_);
                    crate::leanh::lean_dec(v___x_1408_);
                    if v___x_1409_ == 0 {
                        if v___x_1406_ == 0 {
                            state = 2;
                            continue;
                        } else {
                            v___y_1394_ = v___x_1406_;
                            state = 1;
                            continue;
                        }
                    } else {
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v_val_1395_ = l_Std_Time_ValidDate_ofOrdinal(v___y_1394_, v_ordinal_1392_);
                v_fst_1396_ = crate::leanh::lean_ctor_get(v_val_1395_, 0);
                crate::leanh::lean_inc(v_fst_1396_);
                v_snd_1397_ = crate::leanh::lean_ctor_get(v_val_1395_, 1);
                crate::leanh::lean_inc(v_snd_1397_);
                crate::leanh::lean_dec_ref(v_val_1395_);
                v___x_1398_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1398_, 0, v_year_1391_);
                crate::leanh::lean_ctor_set(v___x_1398_, 1, v_fst_1396_);
                crate::leanh::lean_ctor_set(v___x_1398_, 2, v_snd_1397_);
                return v___x_1398_;
            }
            2 => {
                v___x_1403_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once
                    ),
                    _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1,
                );
                v___x_1404_ = lean_int_mod(v_year_1391_, v___x_1403_);
                v___x_1405_ = lean_int_dec_eq(v___x_1404_, v___x_1401_);
                crate::leanh::lean_dec(v___x_1404_);
                v___y_1394_ = v___x_1405_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainDate_ofYearOrdinal___boxed(
    mut v_year_1410_: *mut crate::leanh::LeanObject,
    mut v_ordinal_1411_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1412_ = l_Std_Time_PlainDate_ofYearOrdinal(v_year_1410_, v_ordinal_1411_);
    crate::leanh::lean_dec(v_ordinal_1411_);
    return v_res_1412_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_ofEpochDay___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1413_ = crate::leanh::lean_unsigned_to_nat(719468);
    v___x_1414_ = lean_nat_to_int(v___x_1413_);
    return v___x_1414_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_ofEpochDay___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1415_ = crate::leanh::lean_unsigned_to_nat(31);
    v___x_1416_ = lean_nat_to_int(v___x_1415_);
    return v___x_1416_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_ofEpochDay___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1417_ = crate::leanh::lean_unsigned_to_nat(12);
    v___x_1418_ = lean_nat_to_int(v___x_1417_);
    return v___x_1418_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_ofEpochDay___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1419_ = crate::leanh::lean_unsigned_to_nat(146097);
    v___x_1420_ = lean_nat_to_int(v___x_1419_);
    return v___x_1420_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_ofEpochDay___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1421_ = crate::leanh::lean_unsigned_to_nat(1460);
    v___x_1422_ = lean_nat_to_int(v___x_1421_);
    return v___x_1422_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_ofEpochDay___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1423_ = crate::leanh::lean_unsigned_to_nat(36524);
    v___x_1424_ = lean_nat_to_int(v___x_1423_);
    return v___x_1424_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_ofEpochDay___closed__6() -> *mut crate::leanh::LeanObject {
    let mut v___x_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1425_ = crate::leanh::lean_unsigned_to_nat(146096);
    v___x_1426_ = lean_nat_to_int(v___x_1425_);
    return v___x_1426_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_ofEpochDay___closed__7() -> *mut crate::leanh::LeanObject {
    let mut v___x_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1427_ = crate::leanh::lean_unsigned_to_nat(365);
    v___x_1428_ = lean_nat_to_int(v___x_1427_);
    return v___x_1428_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_ofEpochDay___closed__8() -> *mut crate::leanh::LeanObject {
    let mut v___x_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1429_ = crate::leanh::lean_unsigned_to_nat(5);
    v___x_1430_ = lean_nat_to_int(v___x_1429_);
    return v___x_1430_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_ofEpochDay___closed__9() -> *mut crate::leanh::LeanObject {
    let mut v___x_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1431_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_1432_ = lean_nat_to_int(v___x_1431_);
    return v___x_1432_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_ofEpochDay___closed__10() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1433_ = crate::leanh::lean_unsigned_to_nat(153);
    v___x_1434_ = lean_nat_to_int(v___x_1433_);
    return v___x_1434_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_ofEpochDay___closed__11() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1435_ = crate::leanh::lean_unsigned_to_nat(10);
    v___x_1436_ = lean_nat_to_int(v___x_1435_);
    return v___x_1436_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_ofEpochDay___closed__12() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1437_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainDate_repr___redArg___closed__24),
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainDate_repr___redArg___closed__24_once),
        _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__24,
    );
    v___x_1438_ = lean_int_neg(v___x_1437_);
    return v___x_1438_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_ofEpochDay___closed__13() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1439_ = crate::leanh::lean_unsigned_to_nat(3);
    v___x_1440_ = lean_nat_to_int(v___x_1439_);
    return v___x_1440_;
}
pub unsafe fn l_Std_Time_PlainDate_ofEpochDay(
    mut v_day_1441_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1446_: u8 = 0;
    let mut v_max_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: u8 = 0;
    let mut v___x_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_z_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: u8 = 0;
    let mut v___y_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: u8 = 0;
    let mut v___x_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: u8 = 0;
    let mut v___y_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: u8 = 0;
    let mut v___x_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: u8 = 0;
    let mut v___y_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: u8 = 0;
    let mut v___x_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: u8 = 0;
    let mut v___y_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: u8 = 0;
    let mut v___y_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_era_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_doe_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_yoe_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_doy_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mp_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_d_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: u8 = 0;
    let mut v___x_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: u8 = 0;
    let mut v___x_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1451_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__0_once),
                    _init_l_Std_Time_PlainDate_ofEpochDay___closed__0,
                );
                v_z_1452_ = lean_int_add(v_day_1441_, v___x_1451_);
                v___x_1453_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDate_repr___redArg___closed__25
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once
                    ),
                    _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25,
                );
                v___x_1552_ = lean_int_dec_le(v___x_1453_, v_z_1452_);
                if v___x_1552_ == 0 {
                    v___x_1553_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__6),
                        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__6_once),
                        _init_l_Std_Time_PlainDate_ofEpochDay___closed__6,
                    );
                    v___x_1554_ = lean_int_sub(v_z_1452_, v___x_1553_);
                    v___y_1509_ = v___x_1554_;
                    state = 7;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_z_1452_);
                    v___y_1509_ = v_z_1452_;
                    state = 7;
                    continue;
                }
            }
            1 => {
                v_max_1447_ = l_Std_Time_Month_Ordinal_days(v___y_1446_, v___y_1444_);
                v___x_1448_ = lean_int_dec_lt(v_max_1447_, v___y_1445_);
                if v___x_1448_ == 0 {
                    crate::leanh::lean_dec(v_max_1447_);
                    v___x_1449_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1449_, 0, v___y_1443_);
                    crate::leanh::lean_ctor_set(v___x_1449_, 1, v___y_1444_);
                    crate::leanh::lean_ctor_set(v___x_1449_, 2, v___y_1445_);
                    return v___x_1449_;
                } else {
                    crate::leanh::lean_dec(v___y_1445_);
                    v___x_1450_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1450_, 0, v___y_1443_);
                    crate::leanh::lean_ctor_set(v___x_1450_, 1, v___y_1444_);
                    crate::leanh::lean_ctor_set(v___x_1450_, 2, v_max_1447_);
                    return v___x_1450_;
                }
            }
            2 => {
                v___x_1459_ = lean_int_mod(v___y_1456_, v___y_1455_);
                v___x_1460_ = lean_int_dec_eq(v___x_1459_, v___x_1453_);
                crate::leanh::lean_dec(v___x_1459_);
                v___y_1443_ = v___y_1456_;
                v___y_1444_ = v___y_1457_;
                v___y_1445_ = v___y_1458_;
                v___y_1446_ = v___x_1460_;
                state = 1;
                continue;
            }
            3 => {
                v___x_1468_ = lean_int_mod(v___y_1465_, v___y_1464_);
                v___x_1469_ = lean_int_dec_eq(v___x_1468_, v___x_1453_);
                crate::leanh::lean_dec(v___x_1468_);
                if v___x_1469_ == 0 {
                    v___y_1443_ = v___y_1465_;
                    v___y_1444_ = v___y_1466_;
                    v___y_1445_ = v___y_1467_;
                    v___y_1446_ = v___x_1469_;
                    state = 1;
                    continue;
                } else {
                    v___x_1470_ = lean_int_mod(v___y_1465_, v___y_1463_);
                    v___x_1471_ = lean_int_dec_eq(v___x_1470_, v___x_1453_);
                    crate::leanh::lean_dec(v___x_1470_);
                    if v___x_1471_ == 0 {
                        if v___x_1469_ == 0 {
                            v___y_1455_ = v___y_1462_;
                            v___y_1456_ = v___y_1465_;
                            v___y_1457_ = v___y_1466_;
                            v___y_1458_ = v___y_1467_;
                            state = 2;
                            continue;
                        } else {
                            v___y_1443_ = v___y_1465_;
                            v___y_1444_ = v___y_1466_;
                            v___y_1445_ = v___y_1467_;
                            v___y_1446_ = v___x_1469_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___y_1455_ = v___y_1462_;
                        v___y_1456_ = v___y_1465_;
                        v___y_1457_ = v___y_1466_;
                        v___y_1458_ = v___y_1467_;
                        state = 2;
                        continue;
                    }
                }
            }
            4 => {
                v___x_1480_ = lean_int_dec_le(v___y_1478_, v___y_1477_);
                if v___x_1480_ == 0 {
                    crate::leanh::lean_dec(v___y_1477_);
                    crate::leanh::lean_inc(v___y_1478_);
                    v___y_1462_ = v___y_1473_;
                    v___y_1463_ = v___y_1476_;
                    v___y_1464_ = v___y_1475_;
                    v___y_1465_ = v___y_1474_;
                    v___y_1466_ = v___y_1479_;
                    v___y_1467_ = v___y_1478_;
                    state = 3;
                    continue;
                } else {
                    v___x_1481_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__1),
                        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__1_once),
                        _init_l_Std_Time_PlainDate_ofEpochDay___closed__1,
                    );
                    v___x_1482_ = lean_int_dec_le(v___y_1477_, v___x_1481_);
                    if v___x_1482_ == 0 {
                        crate::leanh::lean_dec(v___y_1477_);
                        v___y_1462_ = v___y_1473_;
                        v___y_1463_ = v___y_1476_;
                        v___y_1464_ = v___y_1475_;
                        v___y_1465_ = v___y_1474_;
                        v___y_1466_ = v___y_1479_;
                        v___y_1467_ = v___x_1481_;
                        state = 3;
                        continue;
                    } else {
                        v___y_1462_ = v___y_1473_;
                        v___y_1463_ = v___y_1476_;
                        v___y_1464_ = v___y_1475_;
                        v___y_1465_ = v___y_1474_;
                        v___y_1466_ = v___y_1479_;
                        v___y_1467_ = v___y_1477_;
                        state = 3;
                        continue;
                    }
                }
            }
            5 => {
                v_y_1492_ = lean_int_add(v___y_1489_, v___y_1491_);
                crate::leanh::lean_dec(v___y_1489_);
                v___x_1493_ = lean_int_dec_le(v___y_1488_, v___y_1490_);
                if v___x_1493_ == 0 {
                    crate::leanh::lean_dec(v___y_1490_);
                    crate::leanh::lean_inc(v___y_1488_);
                    v___y_1473_ = v___y_1484_;
                    v___y_1474_ = v_y_1492_;
                    v___y_1475_ = v___y_1486_;
                    v___y_1476_ = v___y_1485_;
                    v___y_1477_ = v___y_1487_;
                    v___y_1478_ = v___y_1488_;
                    v___y_1479_ = v___y_1488_;
                    state = 4;
                    continue;
                } else {
                    v___x_1494_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__2),
                        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__2_once),
                        _init_l_Std_Time_PlainDate_ofEpochDay___closed__2,
                    );
                    v___x_1495_ = lean_int_dec_le(v___y_1490_, v___x_1494_);
                    if v___x_1495_ == 0 {
                        crate::leanh::lean_dec(v___y_1490_);
                        v___y_1473_ = v___y_1484_;
                        v___y_1474_ = v_y_1492_;
                        v___y_1475_ = v___y_1486_;
                        v___y_1476_ = v___y_1485_;
                        v___y_1477_ = v___y_1487_;
                        v___y_1478_ = v___y_1488_;
                        v___y_1479_ = v___x_1494_;
                        state = 4;
                        continue;
                    } else {
                        v___y_1473_ = v___y_1484_;
                        v___y_1474_ = v_y_1492_;
                        v___y_1475_ = v___y_1486_;
                        v___y_1476_ = v___y_1485_;
                        v___y_1477_ = v___y_1487_;
                        v___y_1478_ = v___y_1488_;
                        v___y_1479_ = v___y_1490_;
                        state = 4;
                        continue;
                    }
                }
            }
            6 => {
                v_m_1506_ = lean_int_add(v___y_1500_, v___y_1505_);
                crate::leanh::lean_dec(v___y_1500_);
                v___x_1507_ = lean_int_dec_le(v_m_1506_, v___y_1501_);
                if v___x_1507_ == 0 {
                    v___y_1484_ = v___y_1497_;
                    v___y_1485_ = v___y_1499_;
                    v___y_1486_ = v___y_1498_;
                    v___y_1487_ = v___y_1502_;
                    v___y_1488_ = v___y_1504_;
                    v___y_1489_ = v___y_1503_;
                    v___y_1490_ = v_m_1506_;
                    v___y_1491_ = v___x_1453_;
                    state = 5;
                    continue;
                } else {
                    v___y_1484_ = v___y_1497_;
                    v___y_1485_ = v___y_1499_;
                    v___y_1486_ = v___y_1498_;
                    v___y_1487_ = v___y_1502_;
                    v___y_1488_ = v___y_1504_;
                    v___y_1489_ = v___y_1503_;
                    v___y_1490_ = v_m_1506_;
                    v___y_1491_ = v___y_1504_;
                    state = 5;
                    continue;
                }
            }
            7 => {
                v___x_1510_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__3),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__3_once),
                    _init_l_Std_Time_PlainDate_ofEpochDay___closed__3,
                );
                v_era_1511_ = lean_int_div(v___y_1509_, v___x_1510_);
                crate::leanh::lean_dec(v___y_1509_);
                v___x_1512_ = lean_int_mul(v_era_1511_, v___x_1510_);
                v_doe_1513_ = lean_int_sub(v_z_1452_, v___x_1512_);
                crate::leanh::lean_dec(v___x_1512_);
                crate::leanh::lean_dec(v_z_1452_);
                v___x_1514_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__4),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__4_once),
                    _init_l_Std_Time_PlainDate_ofEpochDay___closed__4,
                );
                v___x_1515_ = lean_int_div(v_doe_1513_, v___x_1514_);
                v___x_1516_ = lean_int_sub(v_doe_1513_, v___x_1515_);
                crate::leanh::lean_dec(v___x_1515_);
                v___x_1517_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__5),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__5_once),
                    _init_l_Std_Time_PlainDate_ofEpochDay___closed__5,
                );
                v___x_1518_ = lean_int_div(v_doe_1513_, v___x_1517_);
                v___x_1519_ = lean_int_add(v___x_1516_, v___x_1518_);
                crate::leanh::lean_dec(v___x_1518_);
                crate::leanh::lean_dec(v___x_1516_);
                v___x_1520_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__6),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__6_once),
                    _init_l_Std_Time_PlainDate_ofEpochDay___closed__6,
                );
                v___x_1521_ = lean_int_div(v_doe_1513_, v___x_1520_);
                v___x_1522_ = lean_int_sub(v___x_1519_, v___x_1521_);
                crate::leanh::lean_dec(v___x_1521_);
                crate::leanh::lean_dec(v___x_1519_);
                v___x_1523_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__7),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__7_once),
                    _init_l_Std_Time_PlainDate_ofEpochDay___closed__7,
                );
                v_yoe_1524_ = lean_int_div(v___x_1522_, v___x_1523_);
                crate::leanh::lean_dec(v___x_1522_);
                v___x_1525_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once
                    ),
                    _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1,
                );
                v___x_1526_ = lean_int_mul(v_era_1511_, v___x_1525_);
                crate::leanh::lean_dec(v_era_1511_);
                v_y_1527_ = lean_int_add(v_yoe_1524_, v___x_1526_);
                crate::leanh::lean_dec(v___x_1526_);
                v___x_1528_ = lean_int_mul(v___x_1523_, v_yoe_1524_);
                v___x_1529_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once
                    ),
                    _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0,
                );
                v___x_1530_ = lean_int_div(v_yoe_1524_, v___x_1529_);
                v___x_1531_ = lean_int_add(v___x_1528_, v___x_1530_);
                crate::leanh::lean_dec(v___x_1530_);
                crate::leanh::lean_dec(v___x_1528_);
                v___x_1532_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once
                    ),
                    _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2,
                );
                v___x_1533_ = lean_int_div(v_yoe_1524_, v___x_1532_);
                crate::leanh::lean_dec(v_yoe_1524_);
                v___x_1534_ = lean_int_sub(v___x_1531_, v___x_1533_);
                crate::leanh::lean_dec(v___x_1533_);
                crate::leanh::lean_dec(v___x_1531_);
                v_doy_1535_ = lean_int_sub(v_doe_1513_, v___x_1534_);
                crate::leanh::lean_dec(v___x_1534_);
                crate::leanh::lean_dec(v_doe_1513_);
                v___x_1536_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__8),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__8_once),
                    _init_l_Std_Time_PlainDate_ofEpochDay___closed__8,
                );
                v___x_1537_ = lean_int_mul(v___x_1536_, v_doy_1535_);
                v___x_1538_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__9),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__9_once),
                    _init_l_Std_Time_PlainDate_ofEpochDay___closed__9,
                );
                v___x_1539_ = lean_int_add(v___x_1537_, v___x_1538_);
                crate::leanh::lean_dec(v___x_1537_);
                v___x_1540_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__10),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__10_once),
                    _init_l_Std_Time_PlainDate_ofEpochDay___closed__10,
                );
                v_mp_1541_ = lean_int_div(v___x_1539_, v___x_1540_);
                crate::leanh::lean_dec(v___x_1539_);
                v___x_1542_ = lean_int_mul(v___x_1540_, v_mp_1541_);
                v___x_1543_ = lean_int_add(v___x_1542_, v___x_1538_);
                crate::leanh::lean_dec(v___x_1542_);
                v___x_1544_ = lean_int_div(v___x_1543_, v___x_1536_);
                crate::leanh::lean_dec(v___x_1543_);
                v___x_1545_ = lean_int_sub(v_doy_1535_, v___x_1544_);
                crate::leanh::lean_dec(v___x_1544_);
                crate::leanh::lean_dec(v_doy_1535_);
                v___x_1546_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0_once),
                    _init_l_Std_Time_instInhabitedPlainDate___closed__0,
                );
                v_d_1547_ = lean_int_add(v___x_1545_, v___x_1546_);
                crate::leanh::lean_dec(v___x_1545_);
                v___x_1548_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__11),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__11_once),
                    _init_l_Std_Time_PlainDate_ofEpochDay___closed__11,
                );
                v___x_1549_ = lean_int_dec_lt(v_mp_1541_, v___x_1548_);
                if v___x_1549_ == 0 {
                    v___x_1550_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__12),
                        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__12_once),
                        _init_l_Std_Time_PlainDate_ofEpochDay___closed__12,
                    );
                    v___y_1497_ = v___x_1525_;
                    v___y_1498_ = v___x_1529_;
                    v___y_1499_ = v___x_1532_;
                    v___y_1500_ = v_mp_1541_;
                    v___y_1501_ = v___x_1538_;
                    v___y_1502_ = v_d_1547_;
                    v___y_1503_ = v_y_1527_;
                    v___y_1504_ = v___x_1546_;
                    v___y_1505_ = v___x_1550_;
                    state = 6;
                    continue;
                } else {
                    v___x_1551_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__13),
                        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__13_once),
                        _init_l_Std_Time_PlainDate_ofEpochDay___closed__13,
                    );
                    v___y_1497_ = v___x_1525_;
                    v___y_1498_ = v___x_1529_;
                    v___y_1499_ = v___x_1532_;
                    v___y_1500_ = v_mp_1541_;
                    v___y_1501_ = v___x_1538_;
                    v___y_1502_ = v_d_1547_;
                    v___y_1503_ = v_y_1527_;
                    v___y_1504_ = v___x_1546_;
                    v___y_1505_ = v___x_1551_;
                    state = 6;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainDate_ofEpochDay___boxed(
    mut v_day_1555_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1556_ = l_Std_Time_PlainDate_ofEpochDay(v_day_1555_);
    crate::leanh::lean_dec(v_day_1555_);
    return v_res_1556_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_weekOfMonth___closed__0() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1557_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__0,
    );
    v___x_1558_ = lean_int_neg(v___x_1557_);
    return v___x_1558_;
}
pub unsafe fn l_Std_Time_PlainDate_weekOfMonth(
    mut v_date_1559_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_day_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_day_1560_ = crate::leanh::lean_ctor_get(v_date_1559_, 2);
    v___x_1561_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__0,
    );
    v___x_1562_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainDate_repr___redArg___closed__8),
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once),
        _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8,
    );
    v___x_1563_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_weekOfMonth___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_weekOfMonth___closed__0_once),
        _init_l_Std_Time_PlainDate_weekOfMonth___closed__0,
    );
    v___x_1564_ = lean_int_add(v_day_1560_, v___x_1563_);
    v___x_1565_ = lean_int_ediv(v___x_1564_, v___x_1562_);
    crate::leanh::lean_dec(v___x_1564_);
    v___x_1566_ = lean_int_add(v___x_1565_, v___x_1561_);
    crate::leanh::lean_dec(v___x_1565_);
    return v___x_1566_;
}
pub unsafe fn l_Std_Time_PlainDate_weekOfMonth___boxed(
    mut v_date_1567_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1568_ = l_Std_Time_PlainDate_weekOfMonth(v_date_1567_);
    crate::leanh::lean_dec_ref(v_date_1567_);
    return v_res_1568_;
}
pub unsafe fn l_Std_Time_PlainDate_quarter(
    mut v_date_1569_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_month_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_month_1570_ = crate::leanh::lean_ctor_get(v_date_1569_, 1);
    v___x_1571_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__0,
    );
    v___x_1572_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__13),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__13_once),
        _init_l_Std_Time_PlainDate_ofEpochDay___closed__13,
    );
    v___x_1573_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_weekOfMonth___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_weekOfMonth___closed__0_once),
        _init_l_Std_Time_PlainDate_weekOfMonth___closed__0,
    );
    v___x_1574_ = lean_int_add(v_month_1570_, v___x_1573_);
    v___x_1575_ = lean_int_ediv(v___x_1574_, v___x_1572_);
    crate::leanh::lean_dec(v___x_1574_);
    v___x_1576_ = lean_int_add(v___x_1575_, v___x_1571_);
    crate::leanh::lean_dec(v___x_1575_);
    return v___x_1576_;
}
pub unsafe fn l_Std_Time_PlainDate_quarter___boxed(
    mut v_date_1577_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1578_ = l_Std_Time_PlainDate_quarter(v_date_1577_);
    crate::leanh::lean_dec_ref(v_date_1577_);
    return v_res_1578_;
}
pub unsafe fn l_Std_Time_PlainDate_dayOfYear(
    mut v_date_1579_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_year_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_month_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_day_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1584_: u8 = 0;
    let mut v___x_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: u8 = 0;
    let mut v___x_1594_: u8 = 0;
    let mut v___x_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_year_1580_ = crate::leanh::lean_ctor_get(v_date_1579_, 0);
                v_month_1581_ = crate::leanh::lean_ctor_get(v_date_1579_, 1);
                v_day_1582_ = crate::leanh::lean_ctor_get(v_date_1579_, 2);
                v___x_1587_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once
                    ),
                    _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0,
                );
                v___x_1588_ = lean_int_mod(v_year_1580_, v___x_1587_);
                v___x_1589_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDate_repr___redArg___closed__25
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once
                    ),
                    _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25,
                );
                v___x_1594_ = lean_int_dec_eq(v___x_1588_, v___x_1589_);
                crate::leanh::lean_dec(v___x_1588_);
                if v___x_1594_ == 0 {
                    v___y_1584_ = v___x_1594_;
                    state = 1;
                    continue;
                } else {
                    v___x_1595_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once
                        ),
                        _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2,
                    );
                    v___x_1596_ = lean_int_mod(v_year_1580_, v___x_1595_);
                    v___x_1597_ = lean_int_dec_eq(v___x_1596_, v___x_1589_);
                    crate::leanh::lean_dec(v___x_1596_);
                    if v___x_1597_ == 0 {
                        if v___x_1594_ == 0 {
                            state = 2;
                            continue;
                        } else {
                            v___y_1584_ = v___x_1594_;
                            state = 1;
                            continue;
                        }
                    } else {
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_day_1582_);
                crate::leanh::lean_inc(v_month_1581_);
                v___x_1585_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1585_, 0, v_month_1581_);
                crate::leanh::lean_ctor_set(v___x_1585_, 1, v_day_1582_);
                v___x_1586_ = l_Std_Time_ValidDate_dayOfYear(v___y_1584_, v___x_1585_);
                crate::leanh::lean_dec_ref_known(v___x_1585_, 2);
                return v___x_1586_;
            }
            2 => {
                v___x_1591_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once
                    ),
                    _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1,
                );
                v___x_1592_ = lean_int_mod(v_year_1580_, v___x_1591_);
                v___x_1593_ = lean_int_dec_eq(v___x_1592_, v___x_1589_);
                crate::leanh::lean_dec(v___x_1592_);
                v___y_1584_ = v___x_1593_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainDate_dayOfYear___boxed(
    mut v_date_1598_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1599_ = l_Std_Time_PlainDate_dayOfYear(v_date_1598_);
    crate::leanh::lean_dec_ref(v_date_1598_);
    return v_res_1599_;
}
pub unsafe fn l_Std_Time_PlainDate_era(mut v_date_1600_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v_year_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: u8 = 0;
    v_year_1601_ = crate::leanh::lean_ctor_get(v_date_1600_, 0);
    v___x_1602_ = l_Std_Time_Year_Offset_era(v_year_1601_);
    return v___x_1602_;
}
pub unsafe fn l_Std_Time_PlainDate_era___boxed(
    mut v_date_1603_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1604_: u8 = 0;
    let mut v_r_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1604_ = l_Std_Time_PlainDate_era(v_date_1603_);
    crate::leanh::lean_dec_ref(v_date_1603_);
    v_r_1605_ = crate::leanh::lean_box((v_res_1604_) as usize);
    return v_r_1605_;
}
pub unsafe fn l_Std_Time_PlainDate_inLeapYear(
    mut v_date_1606_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_year_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1614_: u8 = 0;
    let mut v___x_1615_: u8 = 0;
    let mut v___x_1616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_year_1607_ = crate::leanh::lean_ctor_get(v_date_1606_, 0);
                v___x_1608_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once
                    ),
                    _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0,
                );
                v___x_1609_ = lean_int_mod(v_year_1607_, v___x_1608_);
                v___x_1610_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDate_repr___redArg___closed__25
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once
                    ),
                    _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25,
                );
                v___x_1615_ = lean_int_dec_eq(v___x_1609_, v___x_1610_);
                crate::leanh::lean_dec(v___x_1609_);
                if v___x_1615_ == 0 {
                    return v___x_1615_;
                } else {
                    v___x_1616_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once
                        ),
                        _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2,
                    );
                    v___x_1617_ = lean_int_mod(v_year_1607_, v___x_1616_);
                    v___x_1618_ = lean_int_dec_eq(v___x_1617_, v___x_1610_);
                    crate::leanh::lean_dec(v___x_1617_);
                    if v___x_1618_ == 0 {
                        if v___x_1615_ == 0 {
                            state = 1;
                            continue;
                        } else {
                            return v___x_1615_;
                        }
                    } else {
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1612_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once
                    ),
                    _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1,
                );
                v___x_1613_ = lean_int_mod(v_year_1607_, v___x_1612_);
                v___x_1614_ = lean_int_dec_eq(v___x_1613_, v___x_1610_);
                crate::leanh::lean_dec(v___x_1613_);
                return v___x_1614_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainDate_inLeapYear___boxed(
    mut v_date_1619_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1620_: u8 = 0;
    let mut v_r_1621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1620_ = l_Std_Time_PlainDate_inLeapYear(v_date_1619_);
    crate::leanh::lean_dec_ref(v_date_1619_);
    v_r_1621_ = crate::leanh::lean_box((v_res_1620_) as usize);
    return v_r_1621_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_toEpochDay___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1622_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__13),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__13_once),
        _init_l_Std_Time_PlainDate_ofEpochDay___closed__13,
    );
    v___x_1623_ = lean_int_neg(v___x_1622_);
    return v___x_1623_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_toEpochDay___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1624_ = crate::leanh::lean_unsigned_to_nat(399);
    v___x_1625_ = lean_nat_to_int(v___x_1624_);
    return v___x_1625_;
}
pub unsafe fn l_Std_Time_PlainDate_toEpochDay(
    mut v_date_1626_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_year_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_month_1628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_day_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_doy_1643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_doe_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_era_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_yoe_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: u8 = 0;
    let mut v___x_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: u8 = 0;
    let mut v___x_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: u8 = 0;
    let mut v___x_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_year_1627_ = crate::leanh::lean_ctor_get(v_date_1626_, 0);
                crate::leanh::lean_inc(v_year_1627_);
                v_month_1628_ = crate::leanh::lean_ctor_get(v_date_1626_, 1);
                crate::leanh::lean_inc(v_month_1628_);
                v_day_1629_ = crate::leanh::lean_ctor_get(v_date_1626_, 2);
                crate::leanh::lean_inc(v_day_1629_);
                crate::leanh::lean_dec_ref(v_date_1626_);
                v___x_1630_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__9),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__9_once),
                    _init_l_Std_Time_PlainDate_ofEpochDay___closed__9,
                );
                v___x_1631_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0_once),
                    _init_l_Std_Time_instInhabitedPlainDate___closed__0,
                );
                v___x_1675_ = lean_int_dec_lt(v___x_1630_, v_month_1628_);
                if v___x_1675_ == 0 {
                    v___x_1676_ = lean_int_sub(v_year_1627_, v___x_1631_);
                    crate::leanh::lean_dec(v_year_1627_);
                    v___y_1670_ = v___x_1676_;
                    state = 3;
                    continue;
                } else {
                    v___y_1670_ = v_year_1627_;
                    state = 3;
                    continue;
                }
            }
            1 => {
                v___x_1637_ = lean_int_add(v_month_1628_, v___y_1636_);
                crate::leanh::lean_dec(v_month_1628_);
                v___x_1638_ = lean_int_mul(v___y_1635_, v___x_1637_);
                crate::leanh::lean_dec(v___x_1637_);
                v___x_1639_ = lean_int_add(v___x_1638_, v___x_1630_);
                crate::leanh::lean_dec(v___x_1638_);
                v___x_1640_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__8),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__8_once),
                    _init_l_Std_Time_PlainDate_ofEpochDay___closed__8,
                );
                v___x_1641_ = lean_int_div(v___x_1639_, v___x_1640_);
                crate::leanh::lean_dec(v___x_1639_);
                v___x_1642_ = lean_int_add(v___x_1641_, v_day_1629_);
                crate::leanh::lean_dec(v_day_1629_);
                crate::leanh::lean_dec(v___x_1641_);
                v_doy_1643_ = lean_int_sub(v___x_1642_, v___x_1631_);
                crate::leanh::lean_dec(v___x_1642_);
                v___x_1644_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__7),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__7_once),
                    _init_l_Std_Time_PlainDate_ofEpochDay___closed__7,
                );
                v___x_1645_ = lean_int_mul(v___y_1633_, v___x_1644_);
                v___x_1646_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once
                    ),
                    _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0,
                );
                v___x_1647_ = lean_int_div(v___y_1633_, v___x_1646_);
                v___x_1648_ = lean_int_add(v___x_1645_, v___x_1647_);
                crate::leanh::lean_dec(v___x_1647_);
                crate::leanh::lean_dec(v___x_1645_);
                v___x_1649_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once
                    ),
                    _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2,
                );
                v___x_1650_ = lean_int_div(v___y_1633_, v___x_1649_);
                crate::leanh::lean_dec(v___y_1633_);
                v___x_1651_ = lean_int_sub(v___x_1648_, v___x_1650_);
                crate::leanh::lean_dec(v___x_1650_);
                crate::leanh::lean_dec(v___x_1648_);
                v_doe_1652_ = lean_int_add(v___x_1651_, v_doy_1643_);
                crate::leanh::lean_dec(v_doy_1643_);
                crate::leanh::lean_dec(v___x_1651_);
                v___x_1653_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__3),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__3_once),
                    _init_l_Std_Time_PlainDate_ofEpochDay___closed__3,
                );
                v___x_1654_ = lean_int_mul(v___y_1634_, v___x_1653_);
                crate::leanh::lean_dec(v___y_1634_);
                v___x_1655_ = lean_int_add(v___x_1654_, v_doe_1652_);
                crate::leanh::lean_dec(v_doe_1652_);
                crate::leanh::lean_dec(v___x_1654_);
                v___x_1656_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__0_once),
                    _init_l_Std_Time_PlainDate_ofEpochDay___closed__0,
                );
                v___x_1657_ = lean_int_sub(v___x_1655_, v___x_1656_);
                crate::leanh::lean_dec(v___x_1655_);
                return v___x_1657_;
            }
            2 => {
                v___x_1661_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once
                    ),
                    _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1,
                );
                v_era_1662_ = lean_int_div(v___y_1660_, v___x_1661_);
                crate::leanh::lean_dec(v___y_1660_);
                v___x_1663_ = lean_int_mul(v_era_1662_, v___x_1661_);
                v_yoe_1664_ = lean_int_sub(v___y_1659_, v___x_1663_);
                crate::leanh::lean_dec(v___x_1663_);
                crate::leanh::lean_dec(v___y_1659_);
                v___x_1665_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__10),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__10_once),
                    _init_l_Std_Time_PlainDate_ofEpochDay___closed__10,
                );
                v___x_1666_ = lean_int_dec_lt(v___x_1630_, v_month_1628_);
                if v___x_1666_ == 0 {
                    v___x_1667_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Time_instReprPlainDate_repr___redArg___closed__24
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Time_instReprPlainDate_repr___redArg___closed__24_once
                        ),
                        _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__24,
                    );
                    v___y_1633_ = v_yoe_1664_;
                    v___y_1634_ = v_era_1662_;
                    v___y_1635_ = v___x_1665_;
                    v___y_1636_ = v___x_1667_;
                    state = 1;
                    continue;
                } else {
                    v___x_1668_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_toEpochDay___closed__0),
                        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_toEpochDay___closed__0_once),
                        _init_l_Std_Time_PlainDate_toEpochDay___closed__0,
                    );
                    v___y_1633_ = v_yoe_1664_;
                    v___y_1634_ = v_era_1662_;
                    v___y_1635_ = v___x_1665_;
                    v___y_1636_ = v___x_1668_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_1671_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDate_repr___redArg___closed__25
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once
                    ),
                    _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25,
                );
                v___x_1672_ = lean_int_dec_le(v___x_1671_, v___y_1670_);
                if v___x_1672_ == 0 {
                    v___x_1673_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_toEpochDay___closed__1),
                        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_toEpochDay___closed__1_once),
                        _init_l_Std_Time_PlainDate_toEpochDay___closed__1,
                    );
                    v___x_1674_ = lean_int_sub(v___y_1670_, v___x_1673_);
                    v___y_1659_ = v___y_1670_;
                    v___y_1660_ = v___x_1674_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v___y_1670_);
                    v___y_1659_ = v___y_1670_;
                    v___y_1660_ = v___y_1670_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainDate_addDays(
    mut v_date_1677_: *mut crate::leanh::LeanObject,
    mut v_days_1678_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_dateDays_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_dateDays_1679_ = l_Std_Time_PlainDate_toEpochDay(v_date_1677_);
    v___x_1680_ = lean_int_add(v_dateDays_1679_, v_days_1678_);
    crate::leanh::lean_dec(v_dateDays_1679_);
    v___x_1681_ = l_Std_Time_PlainDate_ofEpochDay(v___x_1680_);
    crate::leanh::lean_dec(v___x_1680_);
    return v___x_1681_;
}
pub unsafe fn l_Std_Time_PlainDate_addDays___boxed(
    mut v_date_1682_: *mut crate::leanh::LeanObject,
    mut v_days_1683_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1684_ = l_Std_Time_PlainDate_addDays(v_date_1682_, v_days_1683_);
    crate::leanh::lean_dec(v_days_1683_);
    return v_res_1684_;
}
pub unsafe fn l_Std_Time_PlainDate_subDays(
    mut v_date_1685_: *mut crate::leanh::LeanObject,
    mut v_days_1686_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dateDays_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1687_ = lean_int_neg(v_days_1686_);
    v_dateDays_1688_ = l_Std_Time_PlainDate_toEpochDay(v_date_1685_);
    v___x_1689_ = lean_int_add(v_dateDays_1688_, v___x_1687_);
    crate::leanh::lean_dec(v___x_1687_);
    crate::leanh::lean_dec(v_dateDays_1688_);
    v___x_1690_ = l_Std_Time_PlainDate_ofEpochDay(v___x_1689_);
    crate::leanh::lean_dec(v___x_1689_);
    return v___x_1690_;
}
pub unsafe fn l_Std_Time_PlainDate_subDays___boxed(
    mut v_date_1691_: *mut crate::leanh::LeanObject,
    mut v_days_1692_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1693_ = l_Std_Time_PlainDate_subDays(v_date_1691_, v_days_1692_);
    crate::leanh::lean_dec(v_days_1692_);
    return v_res_1693_;
}
pub unsafe fn l_Std_Time_PlainDate_addWeeks(
    mut v_date_1694_: *mut crate::leanh::LeanObject,
    mut v_weeks_1695_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_dateDays_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_daysToAdd_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_dateDays_1696_ = l_Std_Time_PlainDate_toEpochDay(v_date_1694_);
    v___x_1697_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainDate_repr___redArg___closed__8),
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once),
        _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8,
    );
    v_daysToAdd_1698_ = lean_int_mul(v_weeks_1695_, v___x_1697_);
    v___x_1699_ = lean_int_add(v_dateDays_1696_, v_daysToAdd_1698_);
    crate::leanh::lean_dec(v_daysToAdd_1698_);
    crate::leanh::lean_dec(v_dateDays_1696_);
    v___x_1700_ = l_Std_Time_PlainDate_ofEpochDay(v___x_1699_);
    crate::leanh::lean_dec(v___x_1699_);
    return v___x_1700_;
}
pub unsafe fn l_Std_Time_PlainDate_addWeeks___boxed(
    mut v_date_1701_: *mut crate::leanh::LeanObject,
    mut v_weeks_1702_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1703_ = l_Std_Time_PlainDate_addWeeks(v_date_1701_, v_weeks_1702_);
    crate::leanh::lean_dec(v_weeks_1702_);
    return v_res_1703_;
}
pub unsafe fn l_Std_Time_PlainDate_subWeeks(
    mut v_date_1704_: *mut crate::leanh::LeanObject,
    mut v_weeks_1705_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dateDays_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_daysToAdd_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1706_ = lean_int_neg(v_weeks_1705_);
    v_dateDays_1707_ = l_Std_Time_PlainDate_toEpochDay(v_date_1704_);
    v___x_1708_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainDate_repr___redArg___closed__8),
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once),
        _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8,
    );
    v_daysToAdd_1709_ = lean_int_mul(v___x_1706_, v___x_1708_);
    crate::leanh::lean_dec(v___x_1706_);
    v___x_1710_ = lean_int_add(v_dateDays_1707_, v_daysToAdd_1709_);
    crate::leanh::lean_dec(v_daysToAdd_1709_);
    crate::leanh::lean_dec(v_dateDays_1707_);
    v___x_1711_ = l_Std_Time_PlainDate_ofEpochDay(v___x_1710_);
    crate::leanh::lean_dec(v___x_1710_);
    return v___x_1711_;
}
pub unsafe fn l_Std_Time_PlainDate_subWeeks___boxed(
    mut v_date_1712_: *mut crate::leanh::LeanObject,
    mut v_weeks_1713_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1714_ = l_Std_Time_PlainDate_subWeeks(v_date_1712_, v_weeks_1713_);
    crate::leanh::lean_dec(v_weeks_1713_);
    return v_res_1714_;
}
pub unsafe fn l_Std_Time_PlainDate_addMonthsClip(
    mut v_date_1715_: *mut crate::leanh::LeanObject,
    mut v_months_1716_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_year_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_month_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_day_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1722_: u8 = 0;
    let mut v___x_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_totalMonths_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_wrappedMonths_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_yearsOffset_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1732_: u8 = 0;
    let mut v_max_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: u8 = 0;
    let mut v___x_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: u8 = 0;
    let mut v___x_1748_: u8 = 0;
    let mut v___x_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: u8 = 0;
    let mut v_isSharedCheck_1752_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_year_1717_ = crate::leanh::lean_ctor_get(v_date_1715_, 0);
                v_month_1718_ = crate::leanh::lean_ctor_get(v_date_1715_, 1);
                v_day_1719_ = crate::leanh::lean_ctor_get(v_date_1715_, 2);
                v_isSharedCheck_1752_ = (!crate::leanh::lean_is_exclusive(v_date_1715_)) as u8;
                if v_isSharedCheck_1752_ == 0 {
                    v___x_1721_ = v_date_1715_;
                    v_isShared_1722_ = v_isSharedCheck_1752_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_day_1719_);
                    crate::leanh::lean_inc(v_month_1718_);
                    crate::leanh::lean_inc(v_year_1717_);
                    crate::leanh::lean_dec(v_date_1715_);
                    v___x_1721_ = crate::leanh::lean_box(0);
                    v_isShared_1722_ = v_isSharedCheck_1752_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1723_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0_once),
                    _init_l_Std_Time_instInhabitedPlainDate___closed__0,
                );
                v___x_1724_ = lean_int_sub(v_month_1718_, v___x_1723_);
                crate::leanh::lean_dec(v_month_1718_);
                v_totalMonths_1725_ = lean_int_add(v___x_1724_, v_months_1716_);
                crate::leanh::lean_dec(v___x_1724_);
                v___x_1726_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__2),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__2_once),
                    _init_l_Std_Time_PlainDate_ofEpochDay___closed__2,
                );
                v___x_1727_ = lean_int_emod(v_totalMonths_1725_, v___x_1726_);
                v_wrappedMonths_1728_ = lean_int_add(v___x_1727_, v___x_1723_);
                crate::leanh::lean_dec(v___x_1727_);
                v_yearsOffset_1729_ = lean_int_ediv(v_totalMonths_1725_, v___x_1726_);
                crate::leanh::lean_dec(v_totalMonths_1725_);
                v___x_1730_ = lean_int_add(v_year_1717_, v_yearsOffset_1729_);
                crate::leanh::lean_dec(v_yearsOffset_1729_);
                crate::leanh::lean_dec(v_year_1717_);
                v___x_1741_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once
                    ),
                    _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0,
                );
                v___x_1742_ = lean_int_mod(v___x_1730_, v___x_1741_);
                v___x_1743_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDate_repr___redArg___closed__25
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once
                    ),
                    _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25,
                );
                v___x_1748_ = lean_int_dec_eq(v___x_1742_, v___x_1743_);
                crate::leanh::lean_dec(v___x_1742_);
                if v___x_1748_ == 0 {
                    v___y_1732_ = v___x_1748_;
                    state = 2;
                    continue;
                } else {
                    v___x_1749_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once
                        ),
                        _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2,
                    );
                    v___x_1750_ = lean_int_mod(v___x_1730_, v___x_1749_);
                    v___x_1751_ = lean_int_dec_eq(v___x_1750_, v___x_1743_);
                    crate::leanh::lean_dec(v___x_1750_);
                    if v___x_1751_ == 0 {
                        if v___x_1748_ == 0 {
                            state = 5;
                            continue;
                        } else {
                            v___y_1732_ = v___x_1748_;
                            state = 2;
                            continue;
                        }
                    } else {
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v_max_1733_ = l_Std_Time_Month_Ordinal_days(v___y_1732_, v_wrappedMonths_1728_);
                v___x_1734_ = lean_int_dec_lt(v_max_1733_, v_day_1719_);
                if v___x_1734_ == 0 {
                    crate::leanh::lean_dec(v_max_1733_);
                    if v_isShared_1722_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1721_, 1, v_wrappedMonths_1728_);
                        crate::leanh::lean_ctor_set(v___x_1721_, 0, v___x_1730_);
                        v___x_1736_ = v___x_1721_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1737_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1737_, 0, v___x_1730_);
                        crate::leanh::lean_ctor_set(
                            v_reuseFailAlloc_1737_,
                            1,
                            v_wrappedMonths_1728_,
                        );
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1737_, 2, v_day_1719_);
                        v___x_1736_ = v_reuseFailAlloc_1737_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_day_1719_);
                    if v_isShared_1722_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1721_, 2, v_max_1733_);
                        crate::leanh::lean_ctor_set(v___x_1721_, 1, v_wrappedMonths_1728_);
                        crate::leanh::lean_ctor_set(v___x_1721_, 0, v___x_1730_);
                        v___x_1739_ = v___x_1721_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1740_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1740_, 0, v___x_1730_);
                        crate::leanh::lean_ctor_set(
                            v_reuseFailAlloc_1740_,
                            1,
                            v_wrappedMonths_1728_,
                        );
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1740_, 2, v_max_1733_);
                        v___x_1739_ = v_reuseFailAlloc_1740_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_1736_;
            }
            4 => {
                return v___x_1739_;
            }
            5 => {
                v___x_1745_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once
                    ),
                    _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1,
                );
                v___x_1746_ = lean_int_mod(v___x_1730_, v___x_1745_);
                v___x_1747_ = lean_int_dec_eq(v___x_1746_, v___x_1743_);
                crate::leanh::lean_dec(v___x_1746_);
                v___y_1732_ = v___x_1747_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainDate_addMonthsClip___boxed(
    mut v_date_1753_: *mut crate::leanh::LeanObject,
    mut v_months_1754_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1755_ = l_Std_Time_PlainDate_addMonthsClip(v_date_1753_, v_months_1754_);
    crate::leanh::lean_dec(v_months_1754_);
    return v_res_1755_;
}
pub unsafe fn l_Std_Time_PlainDate_subMonthsClip(
    mut v_date_1756_: *mut crate::leanh::LeanObject,
    mut v_months_1757_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1758_ = lean_int_neg(v_months_1757_);
    v___x_1759_ = l_Std_Time_PlainDate_addMonthsClip(v_date_1756_, v___x_1758_);
    crate::leanh::lean_dec(v___x_1758_);
    return v___x_1759_;
}
pub unsafe fn l_Std_Time_PlainDate_subMonthsClip___boxed(
    mut v_date_1760_: *mut crate::leanh::LeanObject,
    mut v_months_1761_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1762_ = l_Std_Time_PlainDate_subMonthsClip(v_date_1760_, v_months_1761_);
    crate::leanh::lean_dec(v_months_1761_);
    return v_res_1762_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_rollOver___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1763_ = crate::leanh::lean_unsigned_to_nat(30);
    v___x_1764_ = lean_nat_to_int(v___x_1763_);
    return v___x_1764_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_rollOver___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1765_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_rollOver___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_rollOver___closed__0_once),
        _init_l_Std_Time_PlainDate_rollOver___closed__0,
    );
    v___x_1766_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__0,
    );
    v___x_1767_ = lean_int_add(v___x_1766_, v___x_1765_);
    return v___x_1767_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_rollOver___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1768_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__0,
    );
    v___x_1769_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_rollOver___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_rollOver___closed__1_once),
        _init_l_Std_Time_PlainDate_rollOver___closed__1,
    );
    v___x_1770_ = lean_int_sub(v___x_1769_, v___x_1768_);
    return v___x_1770_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_rollOver___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1771_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__0,
    );
    v___x_1772_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_rollOver___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_rollOver___closed__2_once),
        _init_l_Std_Time_PlainDate_rollOver___closed__2,
    );
    v_range_1773_ = lean_int_add(v___x_1772_, v___x_1771_);
    return v_range_1773_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_rollOver___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v_range_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1774_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_rollOver___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_rollOver___closed__3_once),
        _init_l_Std_Time_PlainDate_rollOver___closed__3,
    );
    v___x_1775_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__5),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__5_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__5,
    );
    v___x_1776_ = lean_int_emod(v___x_1775_, v_range_1774_);
    return v___x_1776_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_rollOver___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v_range_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1777_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_rollOver___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_rollOver___closed__3_once),
        _init_l_Std_Time_PlainDate_rollOver___closed__3,
    );
    v___x_1778_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_rollOver___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_rollOver___closed__4_once),
        _init_l_Std_Time_PlainDate_rollOver___closed__4,
    );
    v___x_1779_ = lean_int_add(v___x_1778_, v_range_1777_);
    return v___x_1779_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_rollOver___closed__6() -> *mut crate::leanh::LeanObject {
    let mut v_range_1780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1780_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_rollOver___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_rollOver___closed__3_once),
        _init_l_Std_Time_PlainDate_rollOver___closed__3,
    );
    v___x_1781_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_rollOver___closed__5),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_rollOver___closed__5_once),
        _init_l_Std_Time_PlainDate_rollOver___closed__5,
    );
    v___x_1782_ = lean_int_emod(v___x_1781_, v_range_1780_);
    return v___x_1782_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_rollOver___closed__7() -> *mut crate::leanh::LeanObject {
    let mut v___x_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1783_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__0,
    );
    v___x_1784_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_rollOver___closed__6),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_rollOver___closed__6_once),
        _init_l_Std_Time_PlainDate_rollOver___closed__6,
    );
    v___x_1785_ = lean_int_add(v___x_1784_, v___x_1783_);
    return v___x_1785_;
}
pub unsafe fn l_Std_Time_PlainDate_rollOver(
    mut v_year_1786_: *mut crate::leanh::LeanObject,
    mut v_month_1787_: *mut crate::leanh::LeanObject,
    mut v_day_1788_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dateDays_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1798_: u8 = 0;
    let mut v_max_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: u8 = 0;
    let mut v___x_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: u8 = 0;
    let mut v___x_1810_: u8 = 0;
    let mut v___x_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1796_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_rollOver___closed__7),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_rollOver___closed__7_once),
                    _init_l_Std_Time_PlainDate_rollOver___closed__7,
                );
                v___x_1803_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once
                    ),
                    _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0,
                );
                v___x_1804_ = lean_int_mod(v_year_1786_, v___x_1803_);
                v___x_1805_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDate_repr___redArg___closed__25
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once
                    ),
                    _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25,
                );
                v___x_1810_ = lean_int_dec_eq(v___x_1804_, v___x_1805_);
                crate::leanh::lean_dec(v___x_1804_);
                if v___x_1810_ == 0 {
                    v___y_1798_ = v___x_1810_;
                    state = 2;
                    continue;
                } else {
                    v___x_1811_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once
                        ),
                        _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2,
                    );
                    v___x_1812_ = lean_int_mod(v_year_1786_, v___x_1811_);
                    v___x_1813_ = lean_int_dec_eq(v___x_1812_, v___x_1805_);
                    crate::leanh::lean_dec(v___x_1812_);
                    if v___x_1813_ == 0 {
                        if v___x_1810_ == 0 {
                            state = 3;
                            continue;
                        } else {
                            v___y_1798_ = v___x_1810_;
                            state = 2;
                            continue;
                        }
                    } else {
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1791_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0_once),
                    _init_l_Std_Time_instInhabitedPlainDate___closed__0,
                );
                v___x_1792_ = lean_int_sub(v_day_1788_, v___x_1791_);
                v_dateDays_1793_ = l_Std_Time_PlainDate_toEpochDay(v___y_1790_);
                v___x_1794_ = lean_int_add(v_dateDays_1793_, v___x_1792_);
                crate::leanh::lean_dec(v___x_1792_);
                crate::leanh::lean_dec(v_dateDays_1793_);
                v___x_1795_ = l_Std_Time_PlainDate_ofEpochDay(v___x_1794_);
                crate::leanh::lean_dec(v___x_1794_);
                return v___x_1795_;
            }
            2 => {
                v_max_1799_ = l_Std_Time_Month_Ordinal_days(v___y_1798_, v_month_1787_);
                v___x_1800_ = lean_int_dec_lt(v_max_1799_, v___x_1796_);
                if v___x_1800_ == 0 {
                    crate::leanh::lean_dec(v_max_1799_);
                    v___x_1801_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1801_, 0, v_year_1786_);
                    crate::leanh::lean_ctor_set(v___x_1801_, 1, v_month_1787_);
                    crate::leanh::lean_ctor_set(v___x_1801_, 2, v___x_1796_);
                    v___y_1790_ = v___x_1801_;
                    state = 1;
                    continue;
                } else {
                    v___x_1802_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1802_, 0, v_year_1786_);
                    crate::leanh::lean_ctor_set(v___x_1802_, 1, v_month_1787_);
                    crate::leanh::lean_ctor_set(v___x_1802_, 2, v_max_1799_);
                    v___y_1790_ = v___x_1802_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_1807_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once
                    ),
                    _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1,
                );
                v___x_1808_ = lean_int_mod(v_year_1786_, v___x_1807_);
                v___x_1809_ = lean_int_dec_eq(v___x_1808_, v___x_1805_);
                crate::leanh::lean_dec(v___x_1808_);
                v___y_1798_ = v___x_1809_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainDate_rollOver___boxed(
    mut v_year_1814_: *mut crate::leanh::LeanObject,
    mut v_month_1815_: *mut crate::leanh::LeanObject,
    mut v_day_1816_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1817_ = l_Std_Time_PlainDate_rollOver(v_year_1814_, v_month_1815_, v_day_1816_);
    crate::leanh::lean_dec(v_day_1816_);
    return v_res_1817_;
}
pub unsafe fn l_Std_Time_PlainDate_withYearClip(
    mut v_dt_1818_: *mut crate::leanh::LeanObject,
    mut v_year_1819_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_month_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_day_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1824_: u8 = 0;
    let mut v___y_1826_: u8 = 0;
    let mut v_max_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: u8 = 0;
    let mut v___x_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: u8 = 0;
    let mut v___x_1842_: u8 = 0;
    let mut v___x_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: u8 = 0;
    let mut v_isSharedCheck_1846_: u8 = 0;
    let mut v_unused_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_month_1820_ = crate::leanh::lean_ctor_get(v_dt_1818_, 1);
                v_day_1821_ = crate::leanh::lean_ctor_get(v_dt_1818_, 2);
                v_isSharedCheck_1846_ = (!crate::leanh::lean_is_exclusive(v_dt_1818_)) as u8;
                if v_isSharedCheck_1846_ == 0 {
                    v_unused_1847_ = crate::leanh::lean_ctor_get(v_dt_1818_, 0);
                    crate::leanh::lean_dec(v_unused_1847_);
                    v___x_1823_ = v_dt_1818_;
                    v_isShared_1824_ = v_isSharedCheck_1846_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_day_1821_);
                    crate::leanh::lean_inc(v_month_1820_);
                    crate::leanh::lean_dec(v_dt_1818_);
                    v___x_1823_ = crate::leanh::lean_box(0);
                    v_isShared_1824_ = v_isSharedCheck_1846_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1835_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once
                    ),
                    _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0,
                );
                v___x_1836_ = lean_int_mod(v_year_1819_, v___x_1835_);
                v___x_1837_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDate_repr___redArg___closed__25
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once
                    ),
                    _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25,
                );
                v___x_1842_ = lean_int_dec_eq(v___x_1836_, v___x_1837_);
                crate::leanh::lean_dec(v___x_1836_);
                if v___x_1842_ == 0 {
                    v___y_1826_ = v___x_1842_;
                    state = 2;
                    continue;
                } else {
                    v___x_1843_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once
                        ),
                        _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2,
                    );
                    v___x_1844_ = lean_int_mod(v_year_1819_, v___x_1843_);
                    v___x_1845_ = lean_int_dec_eq(v___x_1844_, v___x_1837_);
                    crate::leanh::lean_dec(v___x_1844_);
                    if v___x_1845_ == 0 {
                        if v___x_1842_ == 0 {
                            state = 5;
                            continue;
                        } else {
                            v___y_1826_ = v___x_1842_;
                            state = 2;
                            continue;
                        }
                    } else {
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v_max_1827_ = l_Std_Time_Month_Ordinal_days(v___y_1826_, v_month_1820_);
                v___x_1828_ = lean_int_dec_lt(v_max_1827_, v_day_1821_);
                if v___x_1828_ == 0 {
                    crate::leanh::lean_dec(v_max_1827_);
                    if v_isShared_1824_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1823_, 0, v_year_1819_);
                        v___x_1830_ = v___x_1823_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1831_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1831_, 0, v_year_1819_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1831_, 1, v_month_1820_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1831_, 2, v_day_1821_);
                        v___x_1830_ = v_reuseFailAlloc_1831_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_day_1821_);
                    if v_isShared_1824_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1823_, 2, v_max_1827_);
                        crate::leanh::lean_ctor_set(v___x_1823_, 0, v_year_1819_);
                        v___x_1833_ = v___x_1823_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1834_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1834_, 0, v_year_1819_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1834_, 1, v_month_1820_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1834_, 2, v_max_1827_);
                        v___x_1833_ = v_reuseFailAlloc_1834_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_1830_;
            }
            4 => {
                return v___x_1833_;
            }
            5 => {
                v___x_1839_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once
                    ),
                    _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1,
                );
                v___x_1840_ = lean_int_mod(v_year_1819_, v___x_1839_);
                v___x_1841_ = lean_int_dec_eq(v___x_1840_, v___x_1837_);
                crate::leanh::lean_dec(v___x_1840_);
                v___y_1826_ = v___x_1841_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainDate_withYearRollOver(
    mut v_dt_1848_: *mut crate::leanh::LeanObject,
    mut v_year_1849_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_month_1850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_day_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_month_1850_ = crate::leanh::lean_ctor_get(v_dt_1848_, 1);
    crate::leanh::lean_inc(v_month_1850_);
    v_day_1851_ = crate::leanh::lean_ctor_get(v_dt_1848_, 2);
    crate::leanh::lean_inc(v_day_1851_);
    crate::leanh::lean_dec_ref(v_dt_1848_);
    v___x_1852_ = l_Std_Time_PlainDate_rollOver(v_year_1849_, v_month_1850_, v_day_1851_);
    crate::leanh::lean_dec(v_day_1851_);
    return v___x_1852_;
}
pub unsafe fn l_Std_Time_PlainDate_addMonthsRollOver(
    mut v_date_1853_: *mut crate::leanh::LeanObject,
    mut v_months_1854_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_year_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_month_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_day_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1860_: u8 = 0;
    let mut v___y_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dateDays_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1871_: u8 = 0;
    let mut v_max_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: u8 = 0;
    let mut v___x_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: u8 = 0;
    let mut v___x_1887_: u8 = 0;
    let mut v___x_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: u8 = 0;
    let mut v_isSharedCheck_1891_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_year_1855_ = crate::leanh::lean_ctor_get(v_date_1853_, 0);
                v_month_1856_ = crate::leanh::lean_ctor_get(v_date_1853_, 1);
                v_day_1857_ = crate::leanh::lean_ctor_get(v_date_1853_, 2);
                v_isSharedCheck_1891_ = (!crate::leanh::lean_is_exclusive(v_date_1853_)) as u8;
                if v_isSharedCheck_1891_ == 0 {
                    v___x_1859_ = v_date_1853_;
                    v_isShared_1860_ = v_isSharedCheck_1891_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_day_1857_);
                    crate::leanh::lean_inc(v_month_1856_);
                    crate::leanh::lean_inc(v_year_1855_);
                    crate::leanh::lean_dec(v_date_1853_);
                    v___x_1859_ = crate::leanh::lean_box(0);
                    v_isShared_1860_ = v_isSharedCheck_1891_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1869_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_rollOver___closed__7),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_rollOver___closed__7_once),
                    _init_l_Std_Time_PlainDate_rollOver___closed__7,
                );
                v___x_1880_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once
                    ),
                    _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0,
                );
                v___x_1881_ = lean_int_mod(v_year_1855_, v___x_1880_);
                v___x_1882_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDate_repr___redArg___closed__25
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once
                    ),
                    _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25,
                );
                v___x_1887_ = lean_int_dec_eq(v___x_1881_, v___x_1882_);
                crate::leanh::lean_dec(v___x_1881_);
                if v___x_1887_ == 0 {
                    v___y_1871_ = v___x_1887_;
                    state = 3;
                    continue;
                } else {
                    v___x_1888_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once
                        ),
                        _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2,
                    );
                    v___x_1889_ = lean_int_mod(v_year_1855_, v___x_1888_);
                    v___x_1890_ = lean_int_dec_eq(v___x_1889_, v___x_1882_);
                    crate::leanh::lean_dec(v___x_1889_);
                    if v___x_1890_ == 0 {
                        if v___x_1887_ == 0 {
                            state = 6;
                            continue;
                        } else {
                            v___y_1871_ = v___x_1887_;
                            state = 3;
                            continue;
                        }
                    } else {
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1863_ = l_Std_Time_PlainDate_addMonthsClip(v___y_1862_, v_months_1854_);
                v___x_1864_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0_once),
                    _init_l_Std_Time_instInhabitedPlainDate___closed__0,
                );
                v___x_1865_ = lean_int_sub(v_day_1857_, v___x_1864_);
                crate::leanh::lean_dec(v_day_1857_);
                v_dateDays_1866_ = l_Std_Time_PlainDate_toEpochDay(v___x_1863_);
                v___x_1867_ = lean_int_add(v_dateDays_1866_, v___x_1865_);
                crate::leanh::lean_dec(v___x_1865_);
                crate::leanh::lean_dec(v_dateDays_1866_);
                v___x_1868_ = l_Std_Time_PlainDate_ofEpochDay(v___x_1867_);
                crate::leanh::lean_dec(v___x_1867_);
                return v___x_1868_;
            }
            3 => {
                v_max_1872_ = l_Std_Time_Month_Ordinal_days(v___y_1871_, v_month_1856_);
                v___x_1873_ = lean_int_dec_lt(v_max_1872_, v___x_1869_);
                if v___x_1873_ == 0 {
                    crate::leanh::lean_dec(v_max_1872_);
                    if v_isShared_1860_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1859_, 2, v___x_1869_);
                        v___x_1875_ = v___x_1859_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1876_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1876_, 0, v_year_1855_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1876_, 1, v_month_1856_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1876_, 2, v___x_1869_);
                        v___x_1875_ = v_reuseFailAlloc_1876_;
                        state = 4;
                        continue;
                    }
                } else {
                    if v_isShared_1860_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1859_, 2, v_max_1872_);
                        v___x_1878_ = v___x_1859_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1879_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1879_, 0, v_year_1855_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1879_, 1, v_month_1856_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1879_, 2, v_max_1872_);
                        v___x_1878_ = v_reuseFailAlloc_1879_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                v___y_1862_ = v___x_1875_;
                state = 2;
                continue;
            }
            5 => {
                v___y_1862_ = v___x_1878_;
                state = 2;
                continue;
            }
            6 => {
                v___x_1884_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once
                    ),
                    _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1,
                );
                v___x_1885_ = lean_int_mod(v_year_1855_, v___x_1884_);
                v___x_1886_ = lean_int_dec_eq(v___x_1885_, v___x_1882_);
                crate::leanh::lean_dec(v___x_1885_);
                v___y_1871_ = v___x_1886_;
                state = 3;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainDate_addMonthsRollOver___boxed(
    mut v_date_1892_: *mut crate::leanh::LeanObject,
    mut v_months_1893_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1894_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_1892_, v_months_1893_);
    crate::leanh::lean_dec(v_months_1893_);
    return v_res_1894_;
}
pub unsafe fn l_Std_Time_PlainDate_subMonthsRollOver(
    mut v_date_1895_: *mut crate::leanh::LeanObject,
    mut v_months_1896_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1897_ = lean_int_neg(v_months_1896_);
    v___x_1898_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_1895_, v___x_1897_);
    crate::leanh::lean_dec(v___x_1897_);
    return v___x_1898_;
}
pub unsafe fn l_Std_Time_PlainDate_subMonthsRollOver___boxed(
    mut v_date_1899_: *mut crate::leanh::LeanObject,
    mut v_months_1900_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1901_ = l_Std_Time_PlainDate_subMonthsRollOver(v_date_1899_, v_months_1900_);
    crate::leanh::lean_dec(v_months_1900_);
    return v_res_1901_;
}
pub unsafe fn l_Std_Time_PlainDate_addYearsRollOver(
    mut v_date_1902_: *mut crate::leanh::LeanObject,
    mut v_years_1903_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1904_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__2_once),
        _init_l_Std_Time_PlainDate_ofEpochDay___closed__2,
    );
    v___x_1905_ = lean_int_mul(v_years_1903_, v___x_1904_);
    v___x_1906_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_1902_, v___x_1905_);
    crate::leanh::lean_dec(v___x_1905_);
    return v___x_1906_;
}
pub unsafe fn l_Std_Time_PlainDate_addYearsRollOver___boxed(
    mut v_date_1907_: *mut crate::leanh::LeanObject,
    mut v_years_1908_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1909_ = l_Std_Time_PlainDate_addYearsRollOver(v_date_1907_, v_years_1908_);
    crate::leanh::lean_dec(v_years_1908_);
    return v_res_1909_;
}
pub unsafe fn l_Std_Time_PlainDate_subYearsRollOver(
    mut v_date_1910_: *mut crate::leanh::LeanObject,
    mut v_years_1911_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1912_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__2_once),
        _init_l_Std_Time_PlainDate_ofEpochDay___closed__2,
    );
    v___x_1913_ = lean_int_mul(v_years_1911_, v___x_1912_);
    v___x_1914_ = lean_int_neg(v___x_1913_);
    crate::leanh::lean_dec(v___x_1913_);
    v___x_1915_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_1910_, v___x_1914_);
    crate::leanh::lean_dec(v___x_1914_);
    return v___x_1915_;
}
pub unsafe fn l_Std_Time_PlainDate_subYearsRollOver___boxed(
    mut v_date_1916_: *mut crate::leanh::LeanObject,
    mut v_years_1917_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1918_ = l_Std_Time_PlainDate_subYearsRollOver(v_date_1916_, v_years_1917_);
    crate::leanh::lean_dec(v_years_1917_);
    return v_res_1918_;
}
pub unsafe fn l_Std_Time_PlainDate_addYearsClip(
    mut v_date_1919_: *mut crate::leanh::LeanObject,
    mut v_years_1920_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1921_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__2_once),
        _init_l_Std_Time_PlainDate_ofEpochDay___closed__2,
    );
    v___x_1922_ = lean_int_mul(v_years_1920_, v___x_1921_);
    v___x_1923_ = l_Std_Time_PlainDate_addMonthsClip(v_date_1919_, v___x_1922_);
    crate::leanh::lean_dec(v___x_1922_);
    return v___x_1923_;
}
pub unsafe fn l_Std_Time_PlainDate_addYearsClip___boxed(
    mut v_date_1924_: *mut crate::leanh::LeanObject,
    mut v_years_1925_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1926_ = l_Std_Time_PlainDate_addYearsClip(v_date_1924_, v_years_1925_);
    crate::leanh::lean_dec(v_years_1925_);
    return v_res_1926_;
}
pub unsafe fn l_Std_Time_PlainDate_subYearsClip(
    mut v_date_1927_: *mut crate::leanh::LeanObject,
    mut v_years_1928_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1929_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__2_once),
        _init_l_Std_Time_PlainDate_ofEpochDay___closed__2,
    );
    v___x_1930_ = lean_int_mul(v_years_1928_, v___x_1929_);
    v___x_1931_ = lean_int_neg(v___x_1930_);
    crate::leanh::lean_dec(v___x_1930_);
    v___x_1932_ = l_Std_Time_PlainDate_addMonthsClip(v_date_1927_, v___x_1931_);
    crate::leanh::lean_dec(v___x_1931_);
    return v___x_1932_;
}
pub unsafe fn l_Std_Time_PlainDate_subYearsClip___boxed(
    mut v_date_1933_: *mut crate::leanh::LeanObject,
    mut v_years_1934_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1935_ = l_Std_Time_PlainDate_subYearsClip(v_date_1933_, v_years_1934_);
    crate::leanh::lean_dec(v_years_1934_);
    return v_res_1935_;
}
pub unsafe fn l_Std_Time_PlainDate_withDaysClip(
    mut v_dt_1936_: *mut crate::leanh::LeanObject,
    mut v_days_1937_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_year_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_month_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1942_: u8 = 0;
    let mut v___y_1944_: u8 = 0;
    let mut v_max_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: u8 = 0;
    let mut v___x_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: u8 = 0;
    let mut v___x_1960_: u8 = 0;
    let mut v___x_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: u8 = 0;
    let mut v_isSharedCheck_1964_: u8 = 0;
    let mut v_unused_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_year_1938_ = crate::leanh::lean_ctor_get(v_dt_1936_, 0);
                v_month_1939_ = crate::leanh::lean_ctor_get(v_dt_1936_, 1);
                v_isSharedCheck_1964_ = (!crate::leanh::lean_is_exclusive(v_dt_1936_)) as u8;
                if v_isSharedCheck_1964_ == 0 {
                    v_unused_1965_ = crate::leanh::lean_ctor_get(v_dt_1936_, 2);
                    crate::leanh::lean_dec(v_unused_1965_);
                    v___x_1941_ = v_dt_1936_;
                    v_isShared_1942_ = v_isSharedCheck_1964_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_month_1939_);
                    crate::leanh::lean_inc(v_year_1938_);
                    crate::leanh::lean_dec(v_dt_1936_);
                    v___x_1941_ = crate::leanh::lean_box(0);
                    v_isShared_1942_ = v_isSharedCheck_1964_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1953_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once
                    ),
                    _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0,
                );
                v___x_1954_ = lean_int_mod(v_year_1938_, v___x_1953_);
                v___x_1955_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDate_repr___redArg___closed__25
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once
                    ),
                    _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25,
                );
                v___x_1960_ = lean_int_dec_eq(v___x_1954_, v___x_1955_);
                crate::leanh::lean_dec(v___x_1954_);
                if v___x_1960_ == 0 {
                    v___y_1944_ = v___x_1960_;
                    state = 2;
                    continue;
                } else {
                    v___x_1961_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once
                        ),
                        _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2,
                    );
                    v___x_1962_ = lean_int_mod(v_year_1938_, v___x_1961_);
                    v___x_1963_ = lean_int_dec_eq(v___x_1962_, v___x_1955_);
                    crate::leanh::lean_dec(v___x_1962_);
                    if v___x_1963_ == 0 {
                        if v___x_1960_ == 0 {
                            state = 5;
                            continue;
                        } else {
                            v___y_1944_ = v___x_1960_;
                            state = 2;
                            continue;
                        }
                    } else {
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v_max_1945_ = l_Std_Time_Month_Ordinal_days(v___y_1944_, v_month_1939_);
                v___x_1946_ = lean_int_dec_lt(v_max_1945_, v_days_1937_);
                if v___x_1946_ == 0 {
                    crate::leanh::lean_dec(v_max_1945_);
                    if v_isShared_1942_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1941_, 2, v_days_1937_);
                        v___x_1948_ = v___x_1941_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1949_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1949_, 0, v_year_1938_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1949_, 1, v_month_1939_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1949_, 2, v_days_1937_);
                        v___x_1948_ = v_reuseFailAlloc_1949_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_days_1937_);
                    if v_isShared_1942_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1941_, 2, v_max_1945_);
                        v___x_1951_ = v___x_1941_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1952_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1952_, 0, v_year_1938_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1952_, 1, v_month_1939_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1952_, 2, v_max_1945_);
                        v___x_1951_ = v_reuseFailAlloc_1952_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_1948_;
            }
            4 => {
                return v___x_1951_;
            }
            5 => {
                v___x_1957_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once
                    ),
                    _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1,
                );
                v___x_1958_ = lean_int_mod(v_year_1938_, v___x_1957_);
                v___x_1959_ = lean_int_dec_eq(v___x_1958_, v___x_1955_);
                crate::leanh::lean_dec(v___x_1958_);
                v___y_1944_ = v___x_1959_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainDate_withDaysRollOver(
    mut v_dt_1966_: *mut crate::leanh::LeanObject,
    mut v_days_1967_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_year_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_month_1969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_year_1968_ = crate::leanh::lean_ctor_get(v_dt_1966_, 0);
    crate::leanh::lean_inc(v_year_1968_);
    v_month_1969_ = crate::leanh::lean_ctor_get(v_dt_1966_, 1);
    crate::leanh::lean_inc(v_month_1969_);
    crate::leanh::lean_dec_ref(v_dt_1966_);
    v___x_1970_ = l_Std_Time_PlainDate_rollOver(v_year_1968_, v_month_1969_, v_days_1967_);
    return v___x_1970_;
}
pub unsafe fn l_Std_Time_PlainDate_withDaysRollOver___boxed(
    mut v_dt_1971_: *mut crate::leanh::LeanObject,
    mut v_days_1972_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1973_ = l_Std_Time_PlainDate_withDaysRollOver(v_dt_1971_, v_days_1972_);
    crate::leanh::lean_dec(v_days_1972_);
    return v_res_1973_;
}
pub unsafe fn l_Std_Time_PlainDate_withMonthClip(
    mut v_dt_1974_: *mut crate::leanh::LeanObject,
    mut v_month_1975_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_year_1976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_day_1977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1980_: u8 = 0;
    let mut v___y_1982_: u8 = 0;
    let mut v_max_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: u8 = 0;
    let mut v___x_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: u8 = 0;
    let mut v___x_1998_: u8 = 0;
    let mut v___x_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2001_: u8 = 0;
    let mut v_isSharedCheck_2002_: u8 = 0;
    let mut v_unused_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_year_1976_ = crate::leanh::lean_ctor_get(v_dt_1974_, 0);
                v_day_1977_ = crate::leanh::lean_ctor_get(v_dt_1974_, 2);
                v_isSharedCheck_2002_ = (!crate::leanh::lean_is_exclusive(v_dt_1974_)) as u8;
                if v_isSharedCheck_2002_ == 0 {
                    v_unused_2003_ = crate::leanh::lean_ctor_get(v_dt_1974_, 1);
                    crate::leanh::lean_dec(v_unused_2003_);
                    v___x_1979_ = v_dt_1974_;
                    v_isShared_1980_ = v_isSharedCheck_2002_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_day_1977_);
                    crate::leanh::lean_inc(v_year_1976_);
                    crate::leanh::lean_dec(v_dt_1974_);
                    v___x_1979_ = crate::leanh::lean_box(0);
                    v_isShared_1980_ = v_isSharedCheck_2002_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1991_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once
                    ),
                    _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0,
                );
                v___x_1992_ = lean_int_mod(v_year_1976_, v___x_1991_);
                v___x_1993_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDate_repr___redArg___closed__25
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once
                    ),
                    _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25,
                );
                v___x_1998_ = lean_int_dec_eq(v___x_1992_, v___x_1993_);
                crate::leanh::lean_dec(v___x_1992_);
                if v___x_1998_ == 0 {
                    v___y_1982_ = v___x_1998_;
                    state = 2;
                    continue;
                } else {
                    v___x_1999_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once
                        ),
                        _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2,
                    );
                    v___x_2000_ = lean_int_mod(v_year_1976_, v___x_1999_);
                    v___x_2001_ = lean_int_dec_eq(v___x_2000_, v___x_1993_);
                    crate::leanh::lean_dec(v___x_2000_);
                    if v___x_2001_ == 0 {
                        if v___x_1998_ == 0 {
                            state = 5;
                            continue;
                        } else {
                            v___y_1982_ = v___x_1998_;
                            state = 2;
                            continue;
                        }
                    } else {
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v_max_1983_ = l_Std_Time_Month_Ordinal_days(v___y_1982_, v_month_1975_);
                v___x_1984_ = lean_int_dec_lt(v_max_1983_, v_day_1977_);
                if v___x_1984_ == 0 {
                    crate::leanh::lean_dec(v_max_1983_);
                    if v_isShared_1980_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1979_, 1, v_month_1975_);
                        v___x_1986_ = v___x_1979_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1987_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1987_, 0, v_year_1976_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1987_, 1, v_month_1975_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1987_, 2, v_day_1977_);
                        v___x_1986_ = v_reuseFailAlloc_1987_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_day_1977_);
                    if v_isShared_1980_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1979_, 2, v_max_1983_);
                        crate::leanh::lean_ctor_set(v___x_1979_, 1, v_month_1975_);
                        v___x_1989_ = v___x_1979_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1990_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1990_, 0, v_year_1976_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1990_, 1, v_month_1975_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1990_, 2, v_max_1983_);
                        v___x_1989_ = v_reuseFailAlloc_1990_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_1986_;
            }
            4 => {
                return v___x_1989_;
            }
            5 => {
                v___x_1995_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once
                    ),
                    _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1,
                );
                v___x_1996_ = lean_int_mod(v_year_1976_, v___x_1995_);
                v___x_1997_ = lean_int_dec_eq(v___x_1996_, v___x_1993_);
                crate::leanh::lean_dec(v___x_1996_);
                v___y_1982_ = v___x_1997_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainDate_withMonthRollOver(
    mut v_dt_2004_: *mut crate::leanh::LeanObject,
    mut v_month_2005_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_year_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_day_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_year_2006_ = crate::leanh::lean_ctor_get(v_dt_2004_, 0);
    crate::leanh::lean_inc(v_year_2006_);
    v_day_2007_ = crate::leanh::lean_ctor_get(v_dt_2004_, 2);
    crate::leanh::lean_inc(v_day_2007_);
    crate::leanh::lean_dec_ref(v_dt_2004_);
    v___x_2008_ = l_Std_Time_PlainDate_rollOver(v_year_2006_, v_month_2005_, v_day_2007_);
    crate::leanh::lean_dec(v_day_2007_);
    return v___x_2008_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_weekday___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2009_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__0,
    );
    v___x_2010_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainDate_repr___redArg___closed__8),
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once),
        _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8,
    );
    v___x_2011_ = lean_int_sub(v___x_2010_, v___x_2009_);
    return v___x_2011_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_weekday___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2012_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__0,
    );
    v___x_2013_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_weekday___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_weekday___closed__0_once),
        _init_l_Std_Time_PlainDate_weekday___closed__0,
    );
    v_range_2014_ = lean_int_add(v___x_2013_, v___x_2012_);
    return v_range_2014_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_weekday___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2015_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once),
        _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0,
    );
    v___x_2016_ = lean_int_neg(v___x_2015_);
    return v___x_2016_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_weekday___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_2017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2017_ = crate::leanh::lean_unsigned_to_nat(6);
    v___x_2018_ = lean_nat_to_int(v___x_2017_);
    return v___x_2018_;
}
pub unsafe fn l_Std_Time_PlainDate_weekday(mut v_date_2019_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___y_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2029_: u8 = 0;
    let mut v_days_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: u8 = 0;
    let mut v___x_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_days_2030_ = l_Std_Time_PlainDate_toEpochDay(v_date_2019_);
                v___x_2031_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once
                    ),
                    _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0,
                );
                v___x_2032_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_weekday___closed__2),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_weekday___closed__2_once),
                    _init_l_Std_Time_PlainDate_weekday___closed__2,
                );
                v___x_2033_ = lean_int_dec_le(v___x_2032_, v_days_2030_);
                if v___x_2033_ == 0 {
                    v___x_2034_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__8),
                        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__8_once),
                        _init_l_Std_Time_PlainDate_ofEpochDay___closed__8,
                    );
                    v___x_2035_ = lean_int_add(v_days_2030_, v___x_2034_);
                    crate::leanh::lean_dec(v_days_2030_);
                    v___x_2036_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Time_instReprPlainDate_repr___redArg___closed__8
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once
                        ),
                        _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8,
                    );
                    v___x_2037_ = lean_int_emod(v___x_2035_, v___x_2036_);
                    crate::leanh::lean_dec(v___x_2035_);
                    v___x_2038_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_weekday___closed__3),
                        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_weekday___closed__3_once),
                        _init_l_Std_Time_PlainDate_weekday___closed__3,
                    );
                    v___x_2039_ = lean_int_add(v___x_2037_, v___x_2038_);
                    crate::leanh::lean_dec(v___x_2037_);
                    v___y_2021_ = v___x_2039_;
                    state = 1;
                    continue;
                } else {
                    v___x_2040_ = lean_int_add(v_days_2030_, v___x_2031_);
                    crate::leanh::lean_dec(v_days_2030_);
                    v___x_2041_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Time_instReprPlainDate_repr___redArg___closed__8
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once
                        ),
                        _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8,
                    );
                    v___x_2042_ = lean_int_emod(v___x_2040_, v___x_2041_);
                    crate::leanh::lean_dec(v___x_2040_);
                    v___y_2021_ = v___x_2042_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2022_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0_once),
                    _init_l_Std_Time_instInhabitedPlainDate___closed__0,
                );
                v_range_2023_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_weekday___closed__1),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_weekday___closed__1_once),
                    _init_l_Std_Time_PlainDate_weekday___closed__1,
                );
                v___x_2024_ = lean_int_sub(v___y_2021_, v___x_2022_);
                crate::leanh::lean_dec(v___y_2021_);
                v___x_2025_ = lean_int_emod(v___x_2024_, v_range_2023_);
                crate::leanh::lean_dec(v___x_2024_);
                v___x_2026_ = lean_int_add(v___x_2025_, v_range_2023_);
                crate::leanh::lean_dec(v___x_2025_);
                v___x_2027_ = lean_int_emod(v___x_2026_, v_range_2023_);
                crate::leanh::lean_dec(v___x_2026_);
                v___x_2028_ = lean_int_add(v___x_2027_, v___x_2022_);
                crate::leanh::lean_dec(v___x_2027_);
                v___x_2029_ = l_Std_Time_Weekday_ofOrdinal(v___x_2028_);
                crate::leanh::lean_dec(v___x_2028_);
                return v___x_2029_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainDate_weekday___boxed(
    mut v_date_2043_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2044_: u8 = 0;
    let mut v_r_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2044_ = l_Std_Time_PlainDate_weekday(v_date_2043_);
    v_r_2045_ = crate::leanh::lean_box((v_res_2044_) as usize);
    return v_r_2045_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_alignedWeekOfMonth___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2046_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__0,
    );
    v___x_2047_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_weekday___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_weekday___closed__3_once),
        _init_l_Std_Time_PlainDate_weekday___closed__3,
    );
    v___x_2048_ = lean_int_sub(v___x_2047_, v___x_2046_);
    return v___x_2048_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_alignedWeekOfMonth___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2049_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__0,
    );
    v___x_2050_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_alignedWeekOfMonth___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_alignedWeekOfMonth___closed__0_once),
        _init_l_Std_Time_PlainDate_alignedWeekOfMonth___closed__0,
    );
    v_range_2051_ = lean_int_add(v___x_2050_, v___x_2049_);
    return v_range_2051_;
}
pub unsafe fn l_Std_Time_PlainDate_alignedWeekOfMonth(
    mut v_date_2052_: *mut crate::leanh::LeanObject,
    mut v_firstDay_2053_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v_year_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_month_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_day_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2059_: u8 = 0;
    let mut v___y_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: u8 = 0;
    let mut v_day1Ord_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2082_: u8 = 0;
    let mut v_max_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: u8 = 0;
    let mut v___x_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: u8 = 0;
    let mut v___x_2098_: u8 = 0;
    let mut v___x_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: u8 = 0;
    let mut v_isSharedCheck_2102_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_year_2054_ = crate::leanh::lean_ctor_get(v_date_2052_, 0);
                v_month_2055_ = crate::leanh::lean_ctor_get(v_date_2052_, 1);
                v_day_2056_ = crate::leanh::lean_ctor_get(v_date_2052_, 2);
                v_isSharedCheck_2102_ = (!crate::leanh::lean_is_exclusive(v_date_2052_)) as u8;
                if v_isSharedCheck_2102_ == 0 {
                    v___x_2058_ = v_date_2052_;
                    v_isShared_2059_ = v_isSharedCheck_2102_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_day_2056_);
                    crate::leanh::lean_inc(v_month_2055_);
                    crate::leanh::lean_inc(v_year_2054_);
                    crate::leanh::lean_dec(v_date_2052_);
                    v___x_2058_ = crate::leanh::lean_box(0);
                    v_isShared_2059_ = v_isSharedCheck_2102_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2080_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_rollOver___closed__7),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_rollOver___closed__7_once),
                    _init_l_Std_Time_PlainDate_rollOver___closed__7,
                );
                v___x_2091_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once
                    ),
                    _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0,
                );
                v___x_2092_ = lean_int_mod(v_year_2054_, v___x_2091_);
                v___x_2093_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDate_repr___redArg___closed__25
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once
                    ),
                    _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25,
                );
                v___x_2098_ = lean_int_dec_eq(v___x_2092_, v___x_2093_);
                crate::leanh::lean_dec(v___x_2092_);
                if v___x_2098_ == 0 {
                    v___y_2082_ = v___x_2098_;
                    state = 3;
                    continue;
                } else {
                    v___x_2099_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once
                        ),
                        _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2,
                    );
                    v___x_2100_ = lean_int_mod(v_year_2054_, v___x_2099_);
                    v___x_2101_ = lean_int_dec_eq(v___x_2100_, v___x_2093_);
                    crate::leanh::lean_dec(v___x_2100_);
                    if v___x_2101_ == 0 {
                        if v___x_2098_ == 0 {
                            state = 6;
                            continue;
                        } else {
                            v___y_2082_ = v___x_2098_;
                            state = 3;
                            continue;
                        }
                    } else {
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2062_ = l_Std_Time_PlainDate_weekday(v___y_2061_);
                v_day1Ord_2063_ = l_Std_Time_Weekday_toOrdinal(v___x_2062_);
                v___x_2064_ = l_Std_Time_Weekday_toOrdinal(v_firstDay_2053_);
                v___x_2065_ = lean_int_sub(v_day1Ord_2063_, v___x_2064_);
                crate::leanh::lean_dec(v___x_2064_);
                crate::leanh::lean_dec(v_day1Ord_2063_);
                v___x_2066_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_instReprPlainDate_repr___redArg___closed__8),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once
                    ),
                    _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8,
                );
                v___x_2067_ = lean_int_add(v___x_2065_, v___x_2066_);
                crate::leanh::lean_dec(v___x_2065_);
                v_offset_2068_ = lean_int_emod(v___x_2067_, v___x_2066_);
                crate::leanh::lean_dec(v___x_2067_);
                v___x_2069_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0_once),
                    _init_l_Std_Time_instInhabitedPlainDate___closed__0,
                );
                v___x_2070_ = lean_int_sub(v_day_2056_, v___x_2069_);
                crate::leanh::lean_dec(v_day_2056_);
                v___x_2071_ = lean_int_add(v___x_2070_, v_offset_2068_);
                crate::leanh::lean_dec(v_offset_2068_);
                crate::leanh::lean_dec(v___x_2070_);
                v___x_2072_ = lean_int_ediv(v___x_2071_, v___x_2066_);
                crate::leanh::lean_dec(v___x_2071_);
                v___x_2073_ = lean_int_add(v___x_2072_, v___x_2069_);
                crate::leanh::lean_dec(v___x_2072_);
                v_range_2074_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_alignedWeekOfMonth___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDate_alignedWeekOfMonth___closed__1_once
                    ),
                    _init_l_Std_Time_PlainDate_alignedWeekOfMonth___closed__1,
                );
                v___x_2075_ = lean_int_sub(v___x_2073_, v___x_2069_);
                crate::leanh::lean_dec(v___x_2073_);
                v___x_2076_ = lean_int_emod(v___x_2075_, v_range_2074_);
                crate::leanh::lean_dec(v___x_2075_);
                v___x_2077_ = lean_int_add(v___x_2076_, v_range_2074_);
                crate::leanh::lean_dec(v___x_2076_);
                v___x_2078_ = lean_int_emod(v___x_2077_, v_range_2074_);
                crate::leanh::lean_dec(v___x_2077_);
                v___x_2079_ = lean_int_add(v___x_2078_, v___x_2069_);
                crate::leanh::lean_dec(v___x_2078_);
                return v___x_2079_;
            }
            3 => {
                v_max_2083_ = l_Std_Time_Month_Ordinal_days(v___y_2082_, v_month_2055_);
                v___x_2084_ = lean_int_dec_lt(v_max_2083_, v___x_2080_);
                if v___x_2084_ == 0 {
                    crate::leanh::lean_dec(v_max_2083_);
                    if v_isShared_2059_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2058_, 2, v___x_2080_);
                        v___x_2086_ = v___x_2058_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2087_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2087_, 0, v_year_2054_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2087_, 1, v_month_2055_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2087_, 2, v___x_2080_);
                        v___x_2086_ = v_reuseFailAlloc_2087_;
                        state = 4;
                        continue;
                    }
                } else {
                    if v_isShared_2059_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2058_, 2, v_max_2083_);
                        v___x_2089_ = v___x_2058_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2090_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2090_, 0, v_year_2054_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2090_, 1, v_month_2055_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2090_, 2, v_max_2083_);
                        v___x_2089_ = v_reuseFailAlloc_2090_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                v___y_2061_ = v___x_2086_;
                state = 2;
                continue;
            }
            5 => {
                v___y_2061_ = v___x_2089_;
                state = 2;
                continue;
            }
            6 => {
                v___x_2095_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once
                    ),
                    _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1,
                );
                v___x_2096_ = lean_int_mod(v_year_2054_, v___x_2095_);
                v___x_2097_ = lean_int_dec_eq(v___x_2096_, v___x_2093_);
                crate::leanh::lean_dec(v___x_2096_);
                v___y_2082_ = v___x_2097_;
                state = 3;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainDate_alignedWeekOfMonth___boxed(
    mut v_date_2103_: *mut crate::leanh::LeanObject,
    mut v_firstDay_2104_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_firstDay_boxed_2105_: u8 = 0;
    let mut v_res_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_firstDay_boxed_2105_ = (crate::leanh::lean_unbox(v_firstDay_2104_) as u8);
    v_res_2106_ = l_Std_Time_PlainDate_alignedWeekOfMonth(v_date_2103_, v_firstDay_boxed_2105_);
    return v_res_2106_;
}
pub unsafe fn l_Std_Time_PlainDate_withWeekday(
    mut v_date_2107_: *mut crate::leanh::LeanObject,
    mut v_desiredWeekday_2108_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dateDays_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: u8 = 0;
    let mut v_weekday_2115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: u8 = 0;
    let mut v___x_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_date_2107_);
                v___x_2114_ = l_Std_Time_PlainDate_weekday(v_date_2107_);
                v_weekday_2115_ = l_Std_Time_Weekday_toOrdinal(v___x_2114_);
                v___x_2116_ = l_Std_Time_Weekday_toOrdinal(v_desiredWeekday_2108_);
                v___x_2117_ = lean_int_neg(v_weekday_2115_);
                crate::leanh::lean_dec(v_weekday_2115_);
                v___x_2118_ = lean_int_add(v___x_2116_, v___x_2117_);
                crate::leanh::lean_dec(v___x_2117_);
                crate::leanh::lean_dec(v___x_2116_);
                v___x_2119_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDate_repr___redArg___closed__25
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once
                    ),
                    _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25,
                );
                v___x_2120_ = lean_int_dec_lt(v___x_2118_, v___x_2119_);
                if v___x_2120_ == 0 {
                    v___y_2110_ = v___x_2118_;
                    state = 1;
                    continue;
                } else {
                    v___x_2121_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Time_instReprPlainDate_repr___redArg___closed__8
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once
                        ),
                        _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8,
                    );
                    v___x_2122_ = lean_int_add(v___x_2118_, v___x_2121_);
                    crate::leanh::lean_dec(v___x_2118_);
                    v___y_2110_ = v___x_2122_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_dateDays_2111_ = l_Std_Time_PlainDate_toEpochDay(v_date_2107_);
                v___x_2112_ = lean_int_add(v_dateDays_2111_, v___y_2110_);
                crate::leanh::lean_dec(v___y_2110_);
                crate::leanh::lean_dec(v_dateDays_2111_);
                v___x_2113_ = l_Std_Time_PlainDate_ofEpochDay(v___x_2112_);
                crate::leanh::lean_dec(v___x_2112_);
                return v___x_2113_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainDate_withWeekday___boxed(
    mut v_date_2123_: *mut crate::leanh::LeanObject,
    mut v_desiredWeekday_2124_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_desiredWeekday_boxed_2125_: u8 = 0;
    let mut v_res_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_desiredWeekday_boxed_2125_ = (crate::leanh::lean_unbox(v_desiredWeekday_2124_) as u8);
    v_res_2126_ = l_Std_Time_PlainDate_withWeekday(v_date_2123_, v_desiredWeekday_boxed_2125_);
    return v_res_2126_;
}
pub unsafe fn l_Std_Time_PlainDate_weekOfYear(
    mut v_date_2127_: *mut crate::leanh::LeanObject,
    mut v_firstDay_2128_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v_year_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: u8 = 0;
    let mut v___x_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_w_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: u8 = 0;
    v_year_2129_ = crate::leanh::lean_ctor_get(v_date_2127_, 0);
    crate::leanh::lean_inc(v_year_2129_);
    v___x_2130_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__0,
    );
    v___x_2131_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainDate_repr___redArg___closed__8),
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once),
        _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8,
    );
    crate::leanh::lean_inc_ref(v_date_2127_);
    v___x_2132_ = l_Std_Time_PlainDate_weekday(v_date_2127_);
    v___x_2133_ = l_Std_Time_Weekday_toOrdinal(v___x_2132_);
    v___x_2134_ = l_Std_Time_Weekday_toOrdinal(v_firstDay_2128_);
    v___x_2135_ = lean_int_sub(v___x_2133_, v___x_2134_);
    crate::leanh::lean_dec(v___x_2134_);
    crate::leanh::lean_dec(v___x_2133_);
    v___x_2136_ = lean_int_add(v___x_2135_, v___x_2131_);
    crate::leanh::lean_dec(v___x_2135_);
    v___x_2137_ = lean_int_emod(v___x_2136_, v___x_2131_);
    crate::leanh::lean_dec(v___x_2136_);
    v___x_2138_ = lean_int_add(v___x_2137_, v___x_2130_);
    crate::leanh::lean_dec(v___x_2137_);
    v_range_2139_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_weekday___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_weekday___closed__1_once),
        _init_l_Std_Time_PlainDate_weekday___closed__1,
    );
    v___x_2140_ = lean_int_sub(v___x_2138_, v___x_2130_);
    crate::leanh::lean_dec(v___x_2138_);
    v___x_2141_ = lean_int_emod(v___x_2140_, v_range_2139_);
    crate::leanh::lean_dec(v___x_2140_);
    v___x_2142_ = lean_int_add(v___x_2141_, v_range_2139_);
    crate::leanh::lean_dec(v___x_2141_);
    v___x_2143_ = lean_int_emod(v___x_2142_, v_range_2139_);
    crate::leanh::lean_dec(v___x_2142_);
    v___x_2144_ = lean_int_add(v___x_2143_, v___x_2130_);
    crate::leanh::lean_dec(v___x_2143_);
    v___x_2145_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__11),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__11_once),
        _init_l_Std_Time_PlainDate_ofEpochDay___closed__11,
    );
    v___x_2146_ = l_Std_Time_PlainDate_dayOfYear(v_date_2127_);
    crate::leanh::lean_dec_ref(v_date_2127_);
    v___x_2147_ = lean_int_add(v___x_2145_, v___x_2146_);
    crate::leanh::lean_dec(v___x_2146_);
    v___x_2148_ = lean_int_neg(v___x_2144_);
    crate::leanh::lean_dec(v___x_2144_);
    v___x_2149_ = lean_int_add(v___x_2147_, v___x_2148_);
    crate::leanh::lean_dec(v___x_2148_);
    crate::leanh::lean_dec(v___x_2147_);
    v_w_2150_ = lean_int_ediv(v___x_2149_, v___x_2131_);
    crate::leanh::lean_dec(v___x_2149_);
    v___x_2151_ = lean_int_dec_lt(v_w_2150_, v___x_2130_);
    if v___x_2151_ == 0 {
        let mut v___x_2152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2153_: u8 = 0;
        v___x_2152_ = l_Std_Time_Year_Offset_weeks(v_year_2129_);
        crate::leanh::lean_dec(v_year_2129_);
        v___x_2153_ = lean_int_dec_lt(v___x_2152_, v_w_2150_);
        crate::leanh::lean_dec(v___x_2152_);
        if v___x_2153_ == 0 {
            return v_w_2150_;
        } else {
            crate::leanh::lean_dec(v_w_2150_);
            return v___x_2130_;
        }
    } else {
        let mut v___x_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_w_2150_);
        v___x_2154_ = lean_int_sub(v_year_2129_, v___x_2130_);
        crate::leanh::lean_dec(v_year_2129_);
        v___x_2155_ = l_Std_Time_Year_Offset_weeks(v___x_2154_);
        crate::leanh::lean_dec(v___x_2154_);
        return v___x_2155_;
    }
}
pub unsafe fn l_Std_Time_PlainDate_weekOfYear___boxed(
    mut v_date_2156_: *mut crate::leanh::LeanObject,
    mut v_firstDay_2157_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_firstDay_boxed_2158_: u8 = 0;
    let mut v_res_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_firstDay_boxed_2158_ = (crate::leanh::lean_unbox(v_firstDay_2157_) as u8);
    v_res_2159_ = l_Std_Time_PlainDate_weekOfYear(v_date_2156_, v_firstDay_boxed_2158_);
    return v_res_2159_;
}
pub unsafe fn l_Std_Time_PlainDate_weekYear(
    mut v_date_2160_: *mut crate::leanh::LeanObject,
    mut v_firstDay_2161_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v_year_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: u8 = 0;
    let mut v___x_2166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: u8 = 0;
    v_year_2162_ = crate::leanh::lean_ctor_get(v_date_2160_, 0);
    crate::leanh::lean_inc(v_year_2162_);
    v___x_2163_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__0,
    );
    v___x_2164_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainDate_repr___redArg___closed__8),
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once),
        _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8,
    );
    crate::leanh::lean_inc_ref(v_date_2160_);
    v___x_2165_ = l_Std_Time_PlainDate_weekday(v_date_2160_);
    v___x_2166_ = l_Std_Time_Weekday_toOrdinal(v___x_2165_);
    v___x_2167_ = l_Std_Time_Weekday_toOrdinal(v_firstDay_2161_);
    v___x_2168_ = lean_int_sub(v___x_2166_, v___x_2167_);
    crate::leanh::lean_dec(v___x_2167_);
    crate::leanh::lean_dec(v___x_2166_);
    v___x_2169_ = lean_int_add(v___x_2168_, v___x_2164_);
    crate::leanh::lean_dec(v___x_2168_);
    v___x_2170_ = lean_int_emod(v___x_2169_, v___x_2164_);
    crate::leanh::lean_dec(v___x_2169_);
    v___x_2171_ = lean_int_add(v___x_2170_, v___x_2163_);
    crate::leanh::lean_dec(v___x_2170_);
    v_range_2172_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_weekday___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_weekday___closed__1_once),
        _init_l_Std_Time_PlainDate_weekday___closed__1,
    );
    v___x_2173_ = lean_int_sub(v___x_2171_, v___x_2163_);
    crate::leanh::lean_dec(v___x_2171_);
    v___x_2174_ = lean_int_emod(v___x_2173_, v_range_2172_);
    crate::leanh::lean_dec(v___x_2173_);
    v___x_2175_ = lean_int_add(v___x_2174_, v_range_2172_);
    crate::leanh::lean_dec(v___x_2174_);
    v___x_2176_ = lean_int_emod(v___x_2175_, v_range_2172_);
    crate::leanh::lean_dec(v___x_2175_);
    v___x_2177_ = lean_int_add(v___x_2176_, v___x_2163_);
    crate::leanh::lean_dec(v___x_2176_);
    v___x_2178_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__11),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__11_once),
        _init_l_Std_Time_PlainDate_ofEpochDay___closed__11,
    );
    v___x_2179_ = l_Std_Time_PlainDate_dayOfYear(v_date_2160_);
    crate::leanh::lean_dec_ref(v_date_2160_);
    v___x_2180_ = lean_int_add(v___x_2178_, v___x_2179_);
    crate::leanh::lean_dec(v___x_2179_);
    v___x_2181_ = lean_int_neg(v___x_2177_);
    crate::leanh::lean_dec(v___x_2177_);
    v___x_2182_ = lean_int_add(v___x_2180_, v___x_2181_);
    crate::leanh::lean_dec(v___x_2181_);
    crate::leanh::lean_dec(v___x_2180_);
    v___x_2183_ = lean_int_ediv(v___x_2182_, v___x_2164_);
    crate::leanh::lean_dec(v___x_2182_);
    v___x_2184_ = lean_int_dec_lt(v___x_2183_, v___x_2163_);
    if v___x_2184_ == 0 {
        let mut v___x_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2186_: u8 = 0;
        v___x_2185_ = l_Std_Time_Year_Offset_weeks(v_year_2162_);
        v___x_2186_ = lean_int_dec_lt(v___x_2185_, v___x_2183_);
        crate::leanh::lean_dec(v___x_2183_);
        crate::leanh::lean_dec(v___x_2185_);
        if v___x_2186_ == 0 {
            return v_year_2162_;
        } else {
            let mut v___x_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2187_ = lean_int_add(v_year_2162_, v___x_2163_);
            crate::leanh::lean_dec(v_year_2162_);
            return v___x_2187_;
        }
    } else {
        let mut v___x_2188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___x_2183_);
        v___x_2188_ = lean_int_sub(v_year_2162_, v___x_2163_);
        crate::leanh::lean_dec(v_year_2162_);
        return v___x_2188_;
    }
}
pub unsafe fn l_Std_Time_PlainDate_weekYear___boxed(
    mut v_date_2189_: *mut crate::leanh::LeanObject,
    mut v_firstDay_2190_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_firstDay_boxed_2191_: u8 = 0;
    let mut v_res_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_firstDay_boxed_2191_ = (crate::leanh::lean_unbox(v_firstDay_2190_) as u8);
    v_res_2192_ = l_Std_Time_PlainDate_weekYear(v_date_2189_, v_firstDay_boxed_2191_);
    return v_res_2192_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Time_Date_PlainDate(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Time_Date_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Date_Unit_Month(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Date_Unit_Year(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Std_Time_instInhabitedPlainDate = _init_l_Std_Time_instInhabitedPlainDate();
    crate::leanh::lean_mark_persistent(l_Std_Time_instInhabitedPlainDate);
    l_Std_Time_PlainDate_instInhabited = _init_l_Std_Time_PlainDate_instInhabited();
    crate::leanh::lean_mark_persistent(l_Std_Time_PlainDate_instInhabited);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Time_Date_PlainDate(
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
pub unsafe fn initialize_Std_Time_Date_PlainDate(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Time_Date_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Time_Date_Unit_Month(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Time_Date_Unit_Year(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Date_PlainDate(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Time_Date_PlainDate(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Time_Date_PlainDate(builtin);
}
