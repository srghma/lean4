// Lean compiler output
// Module: Std.Time.Zoned.ZonedDateTime
// Imports: Std.Time.Zoned.DateTime Std.Time.Zoned.ZoneRules Std.Time.DateTime.PlainDateTime
use crate::r#gen::Std::Time::Date::PlainDate::{
    l_Std_Time_PlainDate_addMonthsClip, l_Std_Time_PlainDate_addMonthsRollOver,
    l_Std_Time_PlainDate_alignedWeekOfMonth, l_Std_Time_PlainDate_ofEpochDay,
    l_Std_Time_PlainDate_quarter, l_Std_Time_PlainDate_rollOver, l_Std_Time_PlainDate_toEpochDay,
    l_Std_Time_PlainDate_weekOfYear, l_Std_Time_PlainDate_weekYear, l_Std_Time_PlainDate_weekday,
};
use crate::r#gen::Std::Time::Date::Unit::Month::l_Std_Time_Month_Ordinal_days;
use crate::r#gen::Std::Time::Date::Unit::Year::l_Std_Time_Year_Offset_era;
use crate::r#gen::Std::Time::Date::ValidDate::l_Std_Time_ValidDate_dayOfYear;
use crate::r#gen::Std::Time::DateTime::PlainDateTime::{
    initialize_Std_Time_DateTime_PlainDateTime, l_Std_Time_PlainDateTime_addMonthsClip,
    l_Std_Time_PlainDateTime_addMonthsRollOver, l_Std_Time_PlainDateTime_ofWallTime,
    l_Std_Time_PlainDateTime_toWallTime, l_Std_Time_PlainDateTime_weekOfMonth,
    l_Std_Time_PlainDateTime_withWeekday, l_Std_Time_instInhabitedPlainDateTime_default,
    runtime_initialize_Std_Time_DateTime_PlainDateTime,
};
use crate::r#gen::Std::Time::DateTime::Timestamp::l_Std_Time_instInhabitedTimestamp_default;
use crate::r#gen::Std::Time::Duration::l_Std_Time_Duration_ofNanoseconds;
use crate::r#gen::Std::Time::Zoned::DateTime::{
    initialize_Std_Time_Zoned_DateTime, runtime_initialize_Std_Time_Zoned_DateTime,
};
use crate::r#gen::Std::Time::Zoned::TimeZone::l_Std_Time_instInhabitedTimeZone_default;
use crate::r#gen::Std::Time::Zoned::ZoneRules::{
    initialize_Std_Time_Zoned_ZoneRules, l_Std_Time_TimeZone_LocalTimeType_getTimeZone,
    l_Std_Time_TimeZone_Transition_timezoneAt,
    l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime,
    l_Std_Time_TimeZone_instInhabitedZoneRules_default,
    runtime_initialize_Std_Time_Zoned_ZoneRules,
};
use crate::ffi::{lean_mk_thunk, lean_thunk_get_own};
use crate::ffi::{
    lean_int_add, lean_int_dec_eq, lean_int_dec_lt, lean_int_mul, lean_int_neg, lean_nat_to_int,
};
use crate::ffi::{
    lean_int_ediv, lean_int_emod, lean_int_mod,
};
pub static l_Std_Time_instInhabitedZonedDateTime___private__1___closed__0_value:
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
    m_fun: l_Std_Time_instInhabitedZonedDateTime___private__1___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instInhabitedZonedDateTime___private__1___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instInhabitedZonedDateTime___private__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_instInhabitedZonedDateTime___private__1___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedZonedDateTime___private__1___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instInhabitedZonedDateTime___private__1___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedZonedDateTime___private__1___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Std_Time_instInhabitedZonedDateTime___private__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_instInhabitedZonedDateTime: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_ZonedDateTime_ofTimestampWithZone___closed__0_value:
    crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Std_Time_ZonedDateTime_ofTimestampWithZone___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_ofTimestampWithZone___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_ZonedDateTime_millisecond___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_ZonedDateTime_millisecond___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_ZonedDateTime_dayOfYear___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_ZonedDateTime_dayOfYear___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_ZonedDateTime_dayOfYear___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_ZonedDateTime_dayOfYear___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_ZonedDateTime_dayOfYear___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_ZonedDateTime_dayOfYear___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_ZonedDateTime_addDays___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_ZonedDateTime_addDays___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_ZonedDateTime_addWeeks___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_ZonedDateTime_addWeeks___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_ZonedDateTime_addHours___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_ZonedDateTime_addHours___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_ZonedDateTime_addMinutes___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_ZonedDateTime_addMinutes___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_ZonedDateTime_withMilliseconds___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_ZonedDateTime_withMilliseconds___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_ZonedDateTime_instHAddOffset___closed__0_value:
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
    m_fun: l_Std_Time_ZonedDateTime_addDays___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_ZonedDateTime_instHAddOffset___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHAddOffset___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_ZonedDateTime_instHAddOffset: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHAddOffset___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_ZonedDateTime_instHSubOffset___closed__0_value:
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
    m_fun: l_Std_Time_ZonedDateTime_subDays___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_ZonedDateTime_instHSubOffset___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHSubOffset___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_ZonedDateTime_instHSubOffset: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHSubOffset___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_ZonedDateTime_instHAddOffset__1___closed__0_value:
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
    m_fun: l_Std_Time_ZonedDateTime_addWeeks___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_ZonedDateTime_instHAddOffset__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHAddOffset__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_ZonedDateTime_instHAddOffset__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHAddOffset__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_ZonedDateTime_instHSubOffset__1___closed__0_value:
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
    m_fun: l_Std_Time_ZonedDateTime_subWeeks___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_ZonedDateTime_instHSubOffset__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHSubOffset__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_ZonedDateTime_instHSubOffset__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHSubOffset__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_ZonedDateTime_instHAddOffset__2___closed__0_value:
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
    m_fun: l_Std_Time_ZonedDateTime_addHours___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_ZonedDateTime_instHAddOffset__2___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHAddOffset__2___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_ZonedDateTime_instHAddOffset__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHAddOffset__2___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_ZonedDateTime_instHSubOffset__2___closed__0_value:
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
    m_fun: l_Std_Time_ZonedDateTime_subHours___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_ZonedDateTime_instHSubOffset__2___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHSubOffset__2___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_ZonedDateTime_instHSubOffset__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHSubOffset__2___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_ZonedDateTime_instHAddOffset__3___closed__0_value:
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
    m_fun: l_Std_Time_ZonedDateTime_addMinutes___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_ZonedDateTime_instHAddOffset__3___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHAddOffset__3___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_ZonedDateTime_instHAddOffset__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHAddOffset__3___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_ZonedDateTime_instHSubOffset__3___closed__0_value:
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
    m_fun: l_Std_Time_ZonedDateTime_subMinutes___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_ZonedDateTime_instHSubOffset__3___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHSubOffset__3___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_ZonedDateTime_instHSubOffset__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHSubOffset__3___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_ZonedDateTime_instHAddOffset__4___closed__0_value:
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
    m_fun: l_Std_Time_ZonedDateTime_addSeconds___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_ZonedDateTime_instHAddOffset__4___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHAddOffset__4___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_ZonedDateTime_instHAddOffset__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHAddOffset__4___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_ZonedDateTime_instHSubOffset__4___closed__0_value:
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
    m_fun: l_Std_Time_ZonedDateTime_subSeconds___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_ZonedDateTime_instHSubOffset__4___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHSubOffset__4___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_ZonedDateTime_instHSubOffset__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHSubOffset__4___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_ZonedDateTime_instHAddOffset__5___closed__0_value:
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
    m_fun: l_Std_Time_ZonedDateTime_addMilliseconds___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_ZonedDateTime_instHAddOffset__5___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHAddOffset__5___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_ZonedDateTime_instHAddOffset__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHAddOffset__5___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_ZonedDateTime_instHSubOffset__5___closed__0_value:
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
    m_fun: l_Std_Time_ZonedDateTime_subMilliseconds___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_ZonedDateTime_instHSubOffset__5___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHSubOffset__5___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_ZonedDateTime_instHSubOffset__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHSubOffset__5___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_ZonedDateTime_instHAddOffset__6___closed__0_value:
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
    m_fun: l_Std_Time_ZonedDateTime_addNanoseconds___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_ZonedDateTime_instHAddOffset__6___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHAddOffset__6___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_ZonedDateTime_instHAddOffset__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHAddOffset__6___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_ZonedDateTime_instHSubOffset__6___closed__0_value:
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
    m_fun: l_Std_Time_ZonedDateTime_subNanoseconds___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_ZonedDateTime_instHSubOffset__6___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHSubOffset__6___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_ZonedDateTime_instHSubOffset__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHSubOffset__6___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_ZonedDateTime_instHSubDuration___closed__0_value:
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
    m_fun: l_Std_Time_ZonedDateTime_instHSubDuration___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_ZonedDateTime_instHSubDuration___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHSubDuration___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_ZonedDateTime_instHSubDuration: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHSubDuration___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_ZonedDateTime_instHAddDuration___closed__0_value:
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
    m_fun: l_Std_Time_ZonedDateTime_instHAddDuration___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_ZonedDateTime_instHAddDuration___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHAddDuration___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_ZonedDateTime_instHAddDuration: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHAddDuration___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_ZonedDateTime_instHSubDuration__1___closed__0_value:
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
    m_fun: l_Std_Time_ZonedDateTime_instHSubDuration__1___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_ZonedDateTime_instHSubDuration__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHSubDuration__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_ZonedDateTime_instHSubDuration__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHSubDuration__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Std_Time_instInhabitedZonedDateTime___private__1___lam__0(
    mut v_x_2116_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2117_ = l_Std_Time_instInhabitedPlainDateTime_default;
    return v___x_2117_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedZonedDateTime___private__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___f_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2119_ = l_Std_Time_instInhabitedZonedDateTime___private__1___closed__0;
    v___x_2120_ = lean_mk_thunk(v___f_2119_);
    return v___x_2120_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedZonedDateTime___private__1___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2121_ = l_Std_Time_instInhabitedTimeZone_default;
    v___x_2122_ = l_Std_Time_TimeZone_instInhabitedZoneRules_default;
    v___x_2123_ = l_Std_Time_instInhabitedTimestamp_default;
    v___x_2124_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedZonedDateTime___private__1___closed__1),
        core::ptr::addr_of_mut!(
            l_Std_Time_instInhabitedZonedDateTime___private__1___closed__1_once
        ),
        _init_l_Std_Time_instInhabitedZonedDateTime___private__1___closed__1,
    );
    v___x_2125_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2125_, 0, v___x_2124_);
    crate::leanh::lean_ctor_set(v___x_2125_, 1, v___x_2123_);
    crate::leanh::lean_ctor_set(v___x_2125_, 2, v___x_2122_);
    crate::leanh::lean_ctor_set(v___x_2125_, 3, v___x_2121_);
    return v___x_2125_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedZonedDateTime___private__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2126_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedZonedDateTime___private__1___closed__2),
        core::ptr::addr_of_mut!(
            l_Std_Time_instInhabitedZonedDateTime___private__1___closed__2_once
        ),
        _init_l_Std_Time_instInhabitedZonedDateTime___private__1___closed__2,
    );
    return v___x_2126_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedZonedDateTime() -> *mut crate::leanh::LeanObject {
    let mut v___x_2127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2127_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedZonedDateTime___private__1___closed__2),
        core::ptr::addr_of_mut!(
            l_Std_Time_instInhabitedZonedDateTime___private__1___closed__2_once
        ),
        _init_l_Std_Time_instInhabitedZonedDateTime___private__1___closed__2,
    );
    return v___x_2127_;
}
pub unsafe fn _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2128_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2129_ = lean_nat_to_int(v___x_2128_);
    return v___x_2129_;
}
pub unsafe fn _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2130_ = crate::leanh::lean_unsigned_to_nat(1000000000);
    v___x_2131_ = lean_nat_to_int(v___x_2130_);
    return v___x_2131_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_ofTimestamp___lam__0(
    mut v___y_2132_: *mut crate::leanh::LeanObject,
    mut v_tm_2133_: *mut crate::leanh::LeanObject,
    mut v_x_2134_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_offset_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_offset_2135_ = crate::leanh::lean_ctor_get(v___y_2132_, 0);
    v_second_2136_ = crate::leanh::lean_ctor_get(v_tm_2133_, 0);
    v_nano_2137_ = crate::leanh::lean_ctor_get(v_tm_2133_, 1);
    v___x_2138_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once),
        _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0,
    );
    v___x_2139_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once),
        _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
    );
    v___x_2140_ = lean_int_mul(v_second_2136_, v___x_2139_);
    v___x_2141_ = lean_int_add(v___x_2140_, v_nano_2137_);
    crate::leanh::lean_dec(v___x_2140_);
    v___x_2142_ = lean_int_mul(v_offset_2135_, v___x_2139_);
    v___x_2143_ = lean_int_add(v___x_2142_, v___x_2138_);
    crate::leanh::lean_dec(v___x_2142_);
    v___x_2144_ = lean_int_add(v___x_2141_, v___x_2143_);
    crate::leanh::lean_dec(v___x_2143_);
    crate::leanh::lean_dec(v___x_2141_);
    v___x_2145_ = l_Std_Time_Duration_ofNanoseconds(v___x_2144_);
    crate::leanh::lean_dec(v___x_2144_);
    v___x_2146_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_2145_);
    return v___x_2146_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___boxed(
    mut v___y_2147_: *mut crate::leanh::LeanObject,
    mut v_tm_2148_: *mut crate::leanh::LeanObject,
    mut v_x_2149_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2150_ = l_Std_Time_ZonedDateTime_ofTimestamp___lam__0(v___y_2147_, v_tm_2148_, v_x_2149_);
    crate::leanh::lean_dec_ref(v_tm_2148_);
    crate::leanh::lean_dec_ref(v___y_2147_);
    return v_res_2150_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_ofTimestamp(
    mut v_tm_2151_: *mut crate::leanh::LeanObject,
    mut v_rules_2152_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initialLocalTimeType_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_transitions_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_initialLocalTimeType_2158_ = crate::leanh::lean_ctor_get(v_rules_2152_, 0);
                v_transitions_2159_ = crate::leanh::lean_ctor_get(v_rules_2152_, 1);
                v___x_2160_ =
                    l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_2159_, v_tm_2151_);
                if crate::leanh::lean_obj_tag(v___x_2160_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_2160_, 1);
                    v___x_2161_ =
                        l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_2158_);
                    v___y_2154_ = v___x_2161_;
                    state = 1;
                    continue;
                } else {
                    v_a_2162_ = crate::leanh::lean_ctor_get(v___x_2160_, 0);
                    crate::leanh::lean_inc(v_a_2162_);
                    crate::leanh::lean_dec_ref_known(v___x_2160_, 1);
                    v___y_2154_ = v_a_2162_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_tm_2151_);
                crate::leanh::lean_inc_ref(v___y_2154_);
                v___f_2155_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___boxed as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_2155_, 0, v___y_2154_);
                crate::leanh::lean_closure_set(v___f_2155_, 1, v_tm_2151_);
                v___x_2156_ = lean_mk_thunk(v___f_2155_);
                v___x_2157_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2157_, 0, v___x_2156_);
                crate::leanh::lean_ctor_set(v___x_2157_, 1, v_tm_2151_);
                crate::leanh::lean_ctor_set(v___x_2157_, 2, v_rules_2152_);
                crate::leanh::lean_ctor_set(v___x_2157_, 3, v___y_2154_);
                return v___x_2157_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__0(
    mut v_pdt_2163_: *mut crate::leanh::LeanObject,
    mut v_x_2164_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_pdt_2163_);
    return v_pdt_2163_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__0___boxed(
    mut v_pdt_2165_: *mut crate::leanh::LeanObject,
    mut v_x_2166_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2167_ = l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__0(v_pdt_2165_, v_x_2166_);
    crate::leanh::lean_dec_ref(v_pdt_2165_);
    return v_res_2167_;
}
pub unsafe fn _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2168_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once),
        _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0,
    );
    v___x_2169_ = lean_int_neg(v___x_2168_);
    return v___x_2169_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_ofPlainDateTime(
    mut v_pdt_2170_: *mut crate::leanh::LeanObject,
    mut v_zr_2171_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_wt_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ltt_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tz_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_2175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_pdt_2170_);
    v_wt_2172_ = l_Std_Time_PlainDateTime_toWallTime(v_pdt_2170_);
    crate::leanh::lean_inc_ref(v_zr_2171_);
    v_ltt_2173_ =
        l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_zr_2171_, v_wt_2172_);
    v_tz_2174_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_2173_);
    crate::leanh::lean_dec_ref(v_ltt_2173_);
    v_offset_2175_ = crate::leanh::lean_ctor_get(v_tz_2174_, 0);
    crate::leanh::lean_inc(v_offset_2175_);
    v_second_2176_ = crate::leanh::lean_ctor_get(v_wt_2172_, 0);
    crate::leanh::lean_inc(v_second_2176_);
    v_nano_2177_ = crate::leanh::lean_ctor_get(v_wt_2172_, 1);
    crate::leanh::lean_inc(v_nano_2177_);
    crate::leanh::lean_dec_ref(v_wt_2172_);
    v___f_2178_ = crate::leanh::lean_alloc_closure(
        l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2178_, 0, v_pdt_2170_);
    v___x_2179_ = lean_mk_thunk(v___f_2178_);
    v___x_2180_ = lean_int_neg(v_offset_2175_);
    crate::leanh::lean_dec(v_offset_2175_);
    v___x_2181_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once),
        _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
    );
    v___x_2182_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once),
        _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
    );
    v___x_2183_ = lean_int_mul(v_second_2176_, v___x_2182_);
    crate::leanh::lean_dec(v_second_2176_);
    v___x_2184_ = lean_int_add(v___x_2183_, v_nano_2177_);
    crate::leanh::lean_dec(v_nano_2177_);
    crate::leanh::lean_dec(v___x_2183_);
    v___x_2185_ = lean_int_mul(v___x_2180_, v___x_2182_);
    crate::leanh::lean_dec(v___x_2180_);
    v___x_2186_ = lean_int_add(v___x_2185_, v___x_2181_);
    crate::leanh::lean_dec(v___x_2185_);
    v___x_2187_ = lean_int_add(v___x_2184_, v___x_2186_);
    crate::leanh::lean_dec(v___x_2186_);
    crate::leanh::lean_dec(v___x_2184_);
    v___x_2188_ = l_Std_Time_Duration_ofNanoseconds(v___x_2187_);
    crate::leanh::lean_dec(v___x_2187_);
    v___x_2189_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2189_, 0, v___x_2179_);
    crate::leanh::lean_ctor_set(v___x_2189_, 1, v___x_2188_);
    crate::leanh::lean_ctor_set(v___x_2189_, 2, v_zr_2171_);
    crate::leanh::lean_ctor_set(v___x_2189_, 3, v_tz_2174_);
    return v___x_2189_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_ofTimestampWithZone___lam__0(
    mut v___y_2190_: *mut crate::leanh::LeanObject,
    mut v_tm_2191_: *mut crate::leanh::LeanObject,
    mut v___x_2192_: *mut crate::leanh::LeanObject,
    mut v_x_2193_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_offset_2194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_offset_2194_ = crate::leanh::lean_ctor_get(v___y_2190_, 0);
    v_second_2195_ = crate::leanh::lean_ctor_get(v_tm_2191_, 0);
    v_nano_2196_ = crate::leanh::lean_ctor_get(v_tm_2191_, 1);
    v___x_2197_ = lean_nat_to_int(v___x_2192_);
    v___x_2198_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once),
        _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
    );
    v___x_2199_ = lean_int_mul(v_second_2195_, v___x_2198_);
    v___x_2200_ = lean_int_add(v___x_2199_, v_nano_2196_);
    crate::leanh::lean_dec(v___x_2199_);
    v___x_2201_ = lean_int_mul(v_offset_2194_, v___x_2198_);
    v___x_2202_ = lean_int_add(v___x_2201_, v___x_2197_);
    crate::leanh::lean_dec(v___x_2197_);
    crate::leanh::lean_dec(v___x_2201_);
    v___x_2203_ = lean_int_add(v___x_2200_, v___x_2202_);
    crate::leanh::lean_dec(v___x_2202_);
    crate::leanh::lean_dec(v___x_2200_);
    v___x_2204_ = l_Std_Time_Duration_ofNanoseconds(v___x_2203_);
    crate::leanh::lean_dec(v___x_2203_);
    v___x_2205_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_2204_);
    return v___x_2205_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_ofTimestampWithZone___lam__0___boxed(
    mut v___y_2206_: *mut crate::leanh::LeanObject,
    mut v_tm_2207_: *mut crate::leanh::LeanObject,
    mut v___x_2208_: *mut crate::leanh::LeanObject,
    mut v_x_2209_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2210_ = l_Std_Time_ZonedDateTime_ofTimestampWithZone___lam__0(
        v___y_2206_,
        v_tm_2207_,
        v___x_2208_,
        v_x_2209_,
    );
    crate::leanh::lean_dec_ref(v_tm_2207_);
    crate::leanh::lean_dec_ref(v___y_2206_);
    return v_res_2210_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_ofTimestampWithZone(
    mut v_tm_2213_: *mut crate::leanh::LeanObject,
    mut v_tz_2214_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_offset_2215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_abbreviation_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isDST_2218_: u8 = 0;
    let mut v___x_2219_: u8 = 0;
    let mut v___x_2220_: u8 = 0;
    let mut v_ltt_2221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_offset_2215_ = crate::leanh::lean_ctor_get(v_tz_2214_, 0);
                v_name_2216_ = crate::leanh::lean_ctor_get(v_tz_2214_, 1);
                v_abbreviation_2217_ = crate::leanh::lean_ctor_get(v_tz_2214_, 2);
                v_isDST_2218_ = crate::leanh::lean_ctor_get_uint8(
                    v_tz_2214_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v___x_2219_ = 0;
                v___x_2220_ = 1;
                crate::leanh::lean_inc_ref(v_name_2216_);
                crate::leanh::lean_inc_ref(v_abbreviation_2217_);
                crate::leanh::lean_inc(v_offset_2215_);
                v_ltt_2221_ = crate::leanh::lean_alloc_ctor(0, 3, (3) as u32);
                crate::leanh::lean_ctor_set(v_ltt_2221_, 0, v_offset_2215_);
                crate::leanh::lean_ctor_set(v_ltt_2221_, 1, v_abbreviation_2217_);
                crate::leanh::lean_ctor_set(v_ltt_2221_, 2, v_name_2216_);
                crate::leanh::lean_ctor_set_uint8(
                    v_ltt_2221_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v_isDST_2218_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v_ltt_2221_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                    v___x_2219_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v_ltt_2221_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 2) as u32,
                    v___x_2220_,
                );
                v___x_2222_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2223_ = l_Std_Time_ZonedDateTime_ofTimestampWithZone___closed__0;
                crate::leanh::lean_inc_ref(v_ltt_2221_);
                v___x_2224_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2224_, 0, v_ltt_2221_);
                crate::leanh::lean_ctor_set(v___x_2224_, 1, v___x_2223_);
                v___x_2230_ = l_Std_Time_TimeZone_Transition_timezoneAt(v___x_2223_, v_tm_2213_);
                if crate::leanh::lean_obj_tag(v___x_2230_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_2230_, 1);
                    v___x_2231_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_2221_);
                    crate::leanh::lean_dec_ref_known(v_ltt_2221_, 3);
                    v___y_2226_ = v___x_2231_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref_known(v_ltt_2221_, 3);
                    v_a_2232_ = crate::leanh::lean_ctor_get(v___x_2230_, 0);
                    crate::leanh::lean_inc(v_a_2232_);
                    crate::leanh::lean_dec_ref_known(v___x_2230_, 1);
                    v___y_2226_ = v_a_2232_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_tm_2213_);
                crate::leanh::lean_inc_ref(v___y_2226_);
                v___f_2227_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_ofTimestampWithZone___lam__0___boxed
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_2227_, 0, v___y_2226_);
                crate::leanh::lean_closure_set(v___f_2227_, 1, v_tm_2213_);
                crate::leanh::lean_closure_set(v___f_2227_, 2, v___x_2222_);
                v___x_2228_ = lean_mk_thunk(v___f_2227_);
                v___x_2229_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2229_, 0, v___x_2228_);
                crate::leanh::lean_ctor_set(v___x_2229_, 1, v_tm_2213_);
                crate::leanh::lean_ctor_set(v___x_2229_, 2, v___x_2224_);
                crate::leanh::lean_ctor_set(v___x_2229_, 3, v___y_2226_);
                return v___x_2229_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_ZonedDateTime_ofTimestampWithZone___boxed(
    mut v_tm_2233_: *mut crate::leanh::LeanObject,
    mut v_tz_2234_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2235_ = l_Std_Time_ZonedDateTime_ofTimestampWithZone(v_tm_2233_, v_tz_2234_);
    crate::leanh::lean_dec_ref(v_tz_2234_);
    return v_res_2235_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone___lam__0(
    mut v_tm_2236_: *mut crate::leanh::LeanObject,
    mut v_x_2237_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_tm_2236_);
    return v_tm_2236_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone___lam__0___boxed(
    mut v_tm_2238_: *mut crate::leanh::LeanObject,
    mut v_x_2239_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2240_ = l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone___lam__0(v_tm_2238_, v_x_2239_);
    crate::leanh::lean_dec_ref(v_tm_2238_);
    return v_res_2240_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone(
    mut v_tm_2241_: *mut crate::leanh::LeanObject,
    mut v_tz_2242_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_offset_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_abbreviation_2245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isDST_2246_: u8 = 0;
    let mut v___x_2247_: u8 = 0;
    let mut v___x_2248_: u8 = 0;
    let mut v_ltt_2249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_wt_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ltt_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tz_2254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_2255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_offset_2243_ = crate::leanh::lean_ctor_get(v_tz_2242_, 0);
    v_name_2244_ = crate::leanh::lean_ctor_get(v_tz_2242_, 1);
    v_abbreviation_2245_ = crate::leanh::lean_ctor_get(v_tz_2242_, 2);
    v_isDST_2246_ = crate::leanh::lean_ctor_get_uint8(
        v_tz_2242_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
    );
    v___x_2247_ = 0;
    v___x_2248_ = 1;
    crate::leanh::lean_inc_ref(v_name_2244_);
    crate::leanh::lean_inc_ref(v_abbreviation_2245_);
    crate::leanh::lean_inc(v_offset_2243_);
    v_ltt_2249_ = crate::leanh::lean_alloc_ctor(0, 3, (3) as u32);
    crate::leanh::lean_ctor_set(v_ltt_2249_, 0, v_offset_2243_);
    crate::leanh::lean_ctor_set(v_ltt_2249_, 1, v_abbreviation_2245_);
    crate::leanh::lean_ctor_set(v_ltt_2249_, 2, v_name_2244_);
    crate::leanh::lean_ctor_set_uint8(
        v_ltt_2249_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v_isDST_2246_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v_ltt_2249_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
        v___x_2247_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v_ltt_2249_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 2) as u32,
        v___x_2248_,
    );
    v___x_2250_ = l_Std_Time_ZonedDateTime_ofTimestampWithZone___closed__0;
    v___x_2251_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2251_, 0, v_ltt_2249_);
    crate::leanh::lean_ctor_set(v___x_2251_, 1, v___x_2250_);
    crate::leanh::lean_inc_ref(v_tm_2241_);
    v_wt_2252_ = l_Std_Time_PlainDateTime_toWallTime(v_tm_2241_);
    crate::leanh::lean_inc_ref(v___x_2251_);
    v_ltt_2253_ =
        l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v___x_2251_, v_wt_2252_);
    v_tz_2254_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_2253_);
    crate::leanh::lean_dec_ref(v_ltt_2253_);
    v_offset_2255_ = crate::leanh::lean_ctor_get(v_tz_2254_, 0);
    crate::leanh::lean_inc(v_offset_2255_);
    v_second_2256_ = crate::leanh::lean_ctor_get(v_wt_2252_, 0);
    crate::leanh::lean_inc(v_second_2256_);
    v_nano_2257_ = crate::leanh::lean_ctor_get(v_wt_2252_, 1);
    crate::leanh::lean_inc(v_nano_2257_);
    crate::leanh::lean_dec_ref(v_wt_2252_);
    v___f_2258_ = crate::leanh::lean_alloc_closure(
        l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2258_, 0, v_tm_2241_);
    v___x_2259_ = lean_mk_thunk(v___f_2258_);
    v___x_2260_ = lean_int_neg(v_offset_2255_);
    crate::leanh::lean_dec(v_offset_2255_);
    v___x_2261_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once),
        _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
    );
    v___x_2262_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once),
        _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
    );
    v___x_2263_ = lean_int_mul(v_second_2256_, v___x_2262_);
    crate::leanh::lean_dec(v_second_2256_);
    v___x_2264_ = lean_int_add(v___x_2263_, v_nano_2257_);
    crate::leanh::lean_dec(v_nano_2257_);
    crate::leanh::lean_dec(v___x_2263_);
    v___x_2265_ = lean_int_mul(v___x_2260_, v___x_2262_);
    crate::leanh::lean_dec(v___x_2260_);
    v___x_2266_ = lean_int_add(v___x_2265_, v___x_2261_);
    crate::leanh::lean_dec(v___x_2265_);
    v___x_2267_ = lean_int_add(v___x_2264_, v___x_2266_);
    crate::leanh::lean_dec(v___x_2266_);
    crate::leanh::lean_dec(v___x_2264_);
    v___x_2268_ = l_Std_Time_Duration_ofNanoseconds(v___x_2267_);
    crate::leanh::lean_dec(v___x_2267_);
    v___x_2269_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2269_, 0, v___x_2259_);
    crate::leanh::lean_ctor_set(v___x_2269_, 1, v___x_2268_);
    crate::leanh::lean_ctor_set(v___x_2269_, 2, v___x_2251_);
    crate::leanh::lean_ctor_set(v___x_2269_, 3, v_tz_2254_);
    return v___x_2269_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone___boxed(
    mut v_tm_2270_: *mut crate::leanh::LeanObject,
    mut v_tz_2271_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2272_ = l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone(v_tm_2270_, v_tz_2271_);
    crate::leanh::lean_dec_ref(v_tz_2271_);
    return v_res_2272_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_toTimestamp(
    mut v_date_2273_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_timestamp_2274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_timestamp_2274_ = crate::leanh::lean_ctor_get(v_date_2273_, 1);
    crate::leanh::lean_inc_ref(v_timestamp_2274_);
    return v_timestamp_2274_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_toTimestamp___boxed(
    mut v_date_2275_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2276_ = l_Std_Time_ZonedDateTime_toTimestamp(v_date_2275_);
    crate::leanh::lean_dec_ref(v_date_2275_);
    return v_res_2276_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_convertZoneRules___lam__0(
    mut v___y_2277_: *mut crate::leanh::LeanObject,
    mut v_timestamp_2278_: *mut crate::leanh::LeanObject,
    mut v_x_2279_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_offset_2280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_2281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_offset_2280_ = crate::leanh::lean_ctor_get(v___y_2277_, 0);
    v_second_2281_ = crate::leanh::lean_ctor_get(v_timestamp_2278_, 0);
    v_nano_2282_ = crate::leanh::lean_ctor_get(v_timestamp_2278_, 1);
    v___x_2283_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once),
        _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0,
    );
    v___x_2284_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once),
        _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
    );
    v___x_2285_ = lean_int_mul(v_second_2281_, v___x_2284_);
    v___x_2286_ = lean_int_add(v___x_2285_, v_nano_2282_);
    crate::leanh::lean_dec(v___x_2285_);
    v___x_2287_ = lean_int_mul(v_offset_2280_, v___x_2284_);
    v___x_2288_ = lean_int_add(v___x_2287_, v___x_2283_);
    crate::leanh::lean_dec(v___x_2287_);
    v___x_2289_ = lean_int_add(v___x_2286_, v___x_2288_);
    crate::leanh::lean_dec(v___x_2288_);
    crate::leanh::lean_dec(v___x_2286_);
    v___x_2290_ = l_Std_Time_Duration_ofNanoseconds(v___x_2289_);
    crate::leanh::lean_dec(v___x_2289_);
    v___x_2291_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_2290_);
    return v___x_2291_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_convertZoneRules___lam__0___boxed(
    mut v___y_2292_: *mut crate::leanh::LeanObject,
    mut v_timestamp_2293_: *mut crate::leanh::LeanObject,
    mut v_x_2294_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2295_ = l_Std_Time_ZonedDateTime_convertZoneRules___lam__0(
        v___y_2292_,
        v_timestamp_2293_,
        v_x_2294_,
    );
    crate::leanh::lean_dec_ref(v_timestamp_2293_);
    crate::leanh::lean_dec_ref(v___y_2292_);
    return v_res_2295_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_convertZoneRules(
    mut v_date_2296_: *mut crate::leanh::LeanObject,
    mut v_tz_u2081_2297_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_timestamp_2298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2301_: u8 = 0;
    let mut v___y_2303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initialLocalTimeType_2309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_transitions_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2314_: u8 = 0;
    let mut v_unused_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_2298_ = crate::leanh::lean_ctor_get(v_date_2296_, 1);
                v_isSharedCheck_2314_ = (!crate::leanh::lean_is_exclusive(v_date_2296_)) as u8;
                if v_isSharedCheck_2314_ == 0 {
                    v_unused_2315_ = crate::leanh::lean_ctor_get(v_date_2296_, 3);
                    crate::leanh::lean_dec(v_unused_2315_);
                    v_unused_2316_ = crate::leanh::lean_ctor_get(v_date_2296_, 2);
                    crate::leanh::lean_dec(v_unused_2316_);
                    v_unused_2317_ = crate::leanh::lean_ctor_get(v_date_2296_, 0);
                    crate::leanh::lean_dec(v_unused_2317_);
                    v___x_2300_ = v_date_2296_;
                    v_isShared_2301_ = v_isSharedCheck_2314_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_timestamp_2298_);
                    crate::leanh::lean_dec(v_date_2296_);
                    v___x_2300_ = crate::leanh::lean_box(0);
                    v_isShared_2301_ = v_isSharedCheck_2314_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_initialLocalTimeType_2309_ = crate::leanh::lean_ctor_get(v_tz_u2081_2297_, 0);
                v_transitions_2310_ = crate::leanh::lean_ctor_get(v_tz_u2081_2297_, 1);
                v___x_2311_ = l_Std_Time_TimeZone_Transition_timezoneAt(
                    v_transitions_2310_,
                    v_timestamp_2298_,
                );
                if crate::leanh::lean_obj_tag(v___x_2311_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_2311_, 1);
                    v___x_2312_ =
                        l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_2309_);
                    v___y_2303_ = v___x_2312_;
                    state = 2;
                    continue;
                } else {
                    v_a_2313_ = crate::leanh::lean_ctor_get(v___x_2311_, 0);
                    crate::leanh::lean_inc(v_a_2313_);
                    crate::leanh::lean_dec_ref_known(v___x_2311_, 1);
                    v___y_2303_ = v_a_2313_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc_ref(v_timestamp_2298_);
                crate::leanh::lean_inc_ref(v___y_2303_);
                v___f_2304_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_convertZoneRules___lam__0___boxed
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_2304_, 0, v___y_2303_);
                crate::leanh::lean_closure_set(v___f_2304_, 1, v_timestamp_2298_);
                v___x_2305_ = lean_mk_thunk(v___f_2304_);
                if v_isShared_2301_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2300_, 3, v___y_2303_);
                    crate::leanh::lean_ctor_set(v___x_2300_, 2, v_tz_u2081_2297_);
                    crate::leanh::lean_ctor_set(v___x_2300_, 0, v___x_2305_);
                    v___x_2307_ = v___x_2300_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2308_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2308_, 0, v___x_2305_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2308_, 1, v_timestamp_2298_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2308_, 2, v_tz_u2081_2297_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2308_, 3, v___y_2303_);
                    v___x_2307_ = v_reuseFailAlloc_2308_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2307_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_ZonedDateTime_toPlainDateTime(
    mut v_dt_2318_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_2319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_date_2319_ = crate::leanh::lean_ctor_get(v_dt_2318_, 0);
    v___x_2320_ = lean_thunk_get_own(v_date_2319_);
    return v___x_2320_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_toPlainDateTime___boxed(
    mut v_dt_2321_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2322_ = l_Std_Time_ZonedDateTime_toPlainDateTime(v_dt_2321_);
    crate::leanh::lean_dec_ref(v_dt_2321_);
    return v_res_2322_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_toDateTime___lam__0(
    mut v_timezone_2323_: *mut crate::leanh::LeanObject,
    mut v_timestamp_2324_: *mut crate::leanh::LeanObject,
    mut v_x_2325_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_offset_2326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_2327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_offset_2326_ = crate::leanh::lean_ctor_get(v_timezone_2323_, 0);
    v_second_2327_ = crate::leanh::lean_ctor_get(v_timestamp_2324_, 0);
    v_nano_2328_ = crate::leanh::lean_ctor_get(v_timestamp_2324_, 1);
    v___x_2329_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once),
        _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0,
    );
    v___x_2330_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once),
        _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
    );
    v___x_2331_ = lean_int_mul(v_second_2327_, v___x_2330_);
    v___x_2332_ = lean_int_add(v___x_2331_, v_nano_2328_);
    crate::leanh::lean_dec(v___x_2331_);
    v___x_2333_ = lean_int_mul(v_offset_2326_, v___x_2330_);
    v___x_2334_ = lean_int_add(v___x_2333_, v___x_2329_);
    crate::leanh::lean_dec(v___x_2333_);
    v___x_2335_ = lean_int_add(v___x_2332_, v___x_2334_);
    crate::leanh::lean_dec(v___x_2334_);
    crate::leanh::lean_dec(v___x_2332_);
    v___x_2336_ = l_Std_Time_Duration_ofNanoseconds(v___x_2335_);
    crate::leanh::lean_dec(v___x_2335_);
    v___x_2337_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_2336_);
    return v___x_2337_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_toDateTime___lam__0___boxed(
    mut v_timezone_2338_: *mut crate::leanh::LeanObject,
    mut v_timestamp_2339_: *mut crate::leanh::LeanObject,
    mut v_x_2340_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2341_ = l_Std_Time_ZonedDateTime_toDateTime___lam__0(
        v_timezone_2338_,
        v_timestamp_2339_,
        v_x_2340_,
    );
    crate::leanh::lean_dec_ref(v_timestamp_2339_);
    crate::leanh::lean_dec_ref(v_timezone_2338_);
    return v_res_2341_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_toDateTime(
    mut v_dt_2342_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_timestamp_2343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_timezone_2344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_timestamp_2343_ = crate::leanh::lean_ctor_get(v_dt_2342_, 1);
    crate::leanh::lean_inc_ref_n(v_timestamp_2343_, 2);
    v_timezone_2344_ = crate::leanh::lean_ctor_get(v_dt_2342_, 3);
    crate::leanh::lean_inc_ref(v_timezone_2344_);
    crate::leanh::lean_dec_ref(v_dt_2342_);
    v___f_2345_ = crate::leanh::lean_alloc_closure(
        l_Std_Time_ZonedDateTime_toDateTime___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2345_, 0, v_timezone_2344_);
    crate::leanh::lean_closure_set(v___f_2345_, 1, v_timestamp_2343_);
    v___x_2346_ = lean_mk_thunk(v___f_2345_);
    v___x_2347_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2347_, 0, v_timestamp_2343_);
    crate::leanh::lean_ctor_set(v___x_2347_, 1, v___x_2346_);
    return v___x_2347_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_time(
    mut v_zdt_2348_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_2349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_2351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_date_2349_ = crate::leanh::lean_ctor_get(v_zdt_2348_, 0);
    v___x_2350_ = lean_thunk_get_own(v_date_2349_);
    v_time_2351_ = crate::leanh::lean_ctor_get(v___x_2350_, 1);
    crate::leanh::lean_inc_ref(v_time_2351_);
    crate::leanh::lean_dec(v___x_2350_);
    return v_time_2351_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_time___boxed(
    mut v_zdt_2352_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2353_ = l_Std_Time_ZonedDateTime_time(v_zdt_2352_);
    crate::leanh::lean_dec_ref(v_zdt_2352_);
    return v_res_2353_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_year(
    mut v_zdt_2354_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_2357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_year_2358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_date_2355_ = crate::leanh::lean_ctor_get(v_zdt_2354_, 0);
    v___x_2356_ = lean_thunk_get_own(v_date_2355_);
    v_date_2357_ = crate::leanh::lean_ctor_get(v___x_2356_, 0);
    crate::leanh::lean_inc_ref(v_date_2357_);
    crate::leanh::lean_dec(v___x_2356_);
    v_year_2358_ = crate::leanh::lean_ctor_get(v_date_2357_, 0);
    crate::leanh::lean_inc(v_year_2358_);
    crate::leanh::lean_dec_ref(v_date_2357_);
    return v_year_2358_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_year___boxed(
    mut v_zdt_2359_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2360_ = l_Std_Time_ZonedDateTime_year(v_zdt_2359_);
    crate::leanh::lean_dec_ref(v_zdt_2359_);
    return v_res_2360_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_month(
    mut v_zdt_2361_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_2362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_month_2365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_date_2362_ = crate::leanh::lean_ctor_get(v_zdt_2361_, 0);
    v___x_2363_ = lean_thunk_get_own(v_date_2362_);
    v_date_2364_ = crate::leanh::lean_ctor_get(v___x_2363_, 0);
    crate::leanh::lean_inc_ref(v_date_2364_);
    crate::leanh::lean_dec(v___x_2363_);
    v_month_2365_ = crate::leanh::lean_ctor_get(v_date_2364_, 1);
    crate::leanh::lean_inc(v_month_2365_);
    crate::leanh::lean_dec_ref(v_date_2364_);
    return v_month_2365_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_month___boxed(
    mut v_zdt_2366_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2367_ = l_Std_Time_ZonedDateTime_month(v_zdt_2366_);
    crate::leanh::lean_dec_ref(v_zdt_2366_);
    return v_res_2367_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_day(
    mut v_zdt_2368_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_2371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_day_2372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_date_2369_ = crate::leanh::lean_ctor_get(v_zdt_2368_, 0);
    v___x_2370_ = lean_thunk_get_own(v_date_2369_);
    v_date_2371_ = crate::leanh::lean_ctor_get(v___x_2370_, 0);
    crate::leanh::lean_inc_ref(v_date_2371_);
    crate::leanh::lean_dec(v___x_2370_);
    v_day_2372_ = crate::leanh::lean_ctor_get(v_date_2371_, 2);
    crate::leanh::lean_inc(v_day_2372_);
    crate::leanh::lean_dec_ref(v_date_2371_);
    return v_day_2372_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_day___boxed(
    mut v_zdt_2373_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2374_ = l_Std_Time_ZonedDateTime_day(v_zdt_2373_);
    crate::leanh::lean_dec_ref(v_zdt_2373_);
    return v_res_2374_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_hour(
    mut v_zdt_2375_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_2376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_2378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hour_2379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_date_2376_ = crate::leanh::lean_ctor_get(v_zdt_2375_, 0);
    v___x_2377_ = lean_thunk_get_own(v_date_2376_);
    v_time_2378_ = crate::leanh::lean_ctor_get(v___x_2377_, 1);
    crate::leanh::lean_inc_ref(v_time_2378_);
    crate::leanh::lean_dec(v___x_2377_);
    v_hour_2379_ = crate::leanh::lean_ctor_get(v_time_2378_, 0);
    crate::leanh::lean_inc(v_hour_2379_);
    crate::leanh::lean_dec_ref(v_time_2378_);
    return v_hour_2379_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_hour___boxed(
    mut v_zdt_2380_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2381_ = l_Std_Time_ZonedDateTime_hour(v_zdt_2380_);
    crate::leanh::lean_dec_ref(v_zdt_2380_);
    return v_res_2381_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_minute(
    mut v_zdt_2382_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_2383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_2385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_minute_2386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_date_2383_ = crate::leanh::lean_ctor_get(v_zdt_2382_, 0);
    v___x_2384_ = lean_thunk_get_own(v_date_2383_);
    v_time_2385_ = crate::leanh::lean_ctor_get(v___x_2384_, 1);
    crate::leanh::lean_inc_ref(v_time_2385_);
    crate::leanh::lean_dec(v___x_2384_);
    v_minute_2386_ = crate::leanh::lean_ctor_get(v_time_2385_, 1);
    crate::leanh::lean_inc(v_minute_2386_);
    crate::leanh::lean_dec_ref(v_time_2385_);
    return v_minute_2386_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_minute___boxed(
    mut v_zdt_2387_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2388_ = l_Std_Time_ZonedDateTime_minute(v_zdt_2387_);
    crate::leanh::lean_dec_ref(v_zdt_2387_);
    return v_res_2388_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_second(
    mut v_zdt_2389_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_2390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_2392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_2393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_date_2390_ = crate::leanh::lean_ctor_get(v_zdt_2389_, 0);
    v___x_2391_ = lean_thunk_get_own(v_date_2390_);
    v_time_2392_ = crate::leanh::lean_ctor_get(v___x_2391_, 1);
    crate::leanh::lean_inc_ref(v_time_2392_);
    crate::leanh::lean_dec(v___x_2391_);
    v_second_2393_ = crate::leanh::lean_ctor_get(v_time_2392_, 2);
    crate::leanh::lean_inc(v_second_2393_);
    crate::leanh::lean_dec_ref(v_time_2392_);
    return v_second_2393_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_second___boxed(
    mut v_zdt_2394_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2395_ = l_Std_Time_ZonedDateTime_second(v_zdt_2394_);
    crate::leanh::lean_dec_ref(v_zdt_2394_);
    return v_res_2395_;
}
pub unsafe fn _init_l_Std_Time_ZonedDateTime_millisecond___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2396_ = crate::leanh::lean_unsigned_to_nat(1000000);
    v___x_2397_ = lean_nat_to_int(v___x_2396_);
    return v___x_2397_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_millisecond(
    mut v_dt_2398_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_2399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_2401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_2402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_date_2399_ = crate::leanh::lean_ctor_get(v_dt_2398_, 0);
    v___x_2400_ = lean_thunk_get_own(v_date_2399_);
    v_time_2401_ = crate::leanh::lean_ctor_get(v___x_2400_, 1);
    crate::leanh::lean_inc_ref(v_time_2401_);
    crate::leanh::lean_dec(v___x_2400_);
    v_nanosecond_2402_ = crate::leanh::lean_ctor_get(v_time_2401_, 3);
    crate::leanh::lean_inc(v_nanosecond_2402_);
    crate::leanh::lean_dec_ref(v_time_2401_);
    v___x_2403_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_millisecond___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_millisecond___closed__0_once),
        _init_l_Std_Time_ZonedDateTime_millisecond___closed__0,
    );
    v___x_2404_ = lean_int_ediv(v_nanosecond_2402_, v___x_2403_);
    crate::leanh::lean_dec(v_nanosecond_2402_);
    return v___x_2404_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_millisecond___boxed(
    mut v_dt_2405_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2406_ = l_Std_Time_ZonedDateTime_millisecond(v_dt_2405_);
    crate::leanh::lean_dec_ref(v_dt_2405_);
    return v_res_2406_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_nanosecond(
    mut v_zdt_2407_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_2408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_2410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_2411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_date_2408_ = crate::leanh::lean_ctor_get(v_zdt_2407_, 0);
    v___x_2409_ = lean_thunk_get_own(v_date_2408_);
    v_time_2410_ = crate::leanh::lean_ctor_get(v___x_2409_, 1);
    crate::leanh::lean_inc_ref(v_time_2410_);
    crate::leanh::lean_dec(v___x_2409_);
    v_nanosecond_2411_ = crate::leanh::lean_ctor_get(v_time_2410_, 3);
    crate::leanh::lean_inc(v_nanosecond_2411_);
    crate::leanh::lean_dec_ref(v_time_2410_);
    return v_nanosecond_2411_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_nanosecond___boxed(
    mut v_zdt_2412_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2413_ = l_Std_Time_ZonedDateTime_nanosecond(v_zdt_2412_);
    crate::leanh::lean_dec_ref(v_zdt_2412_);
    return v_res_2413_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_offset(
    mut v_zdt_2414_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_timezone_2415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_2416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_timezone_2415_ = crate::leanh::lean_ctor_get(v_zdt_2414_, 3);
    v_offset_2416_ = crate::leanh::lean_ctor_get(v_timezone_2415_, 0);
    crate::leanh::lean_inc(v_offset_2416_);
    return v_offset_2416_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_offset___boxed(
    mut v_zdt_2417_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2418_ = l_Std_Time_ZonedDateTime_offset(v_zdt_2417_);
    crate::leanh::lean_dec_ref(v_zdt_2417_);
    return v_res_2418_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_weekday(
    mut v_zdt_2419_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_date_2420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_2422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2423_: u8 = 0;
    v_date_2420_ = crate::leanh::lean_ctor_get(v_zdt_2419_, 0);
    v___x_2421_ = lean_thunk_get_own(v_date_2420_);
    v_date_2422_ = crate::leanh::lean_ctor_get(v___x_2421_, 0);
    crate::leanh::lean_inc_ref(v_date_2422_);
    crate::leanh::lean_dec(v___x_2421_);
    v___x_2423_ = l_Std_Time_PlainDate_weekday(v_date_2422_);
    return v___x_2423_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_weekday___boxed(
    mut v_zdt_2424_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2425_: u8 = 0;
    let mut v_r_2426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2425_ = l_Std_Time_ZonedDateTime_weekday(v_zdt_2424_);
    crate::leanh::lean_dec_ref(v_zdt_2424_);
    v_r_2426_ = crate::leanh::lean_box((v_res_2425_) as usize);
    return v_r_2426_;
}
pub unsafe fn _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__0() -> *mut crate::leanh::LeanObject
{
    let mut v___x_2427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2427_ = crate::leanh::lean_unsigned_to_nat(4);
    v___x_2428_ = lean_nat_to_int(v___x_2427_);
    return v___x_2428_;
}
pub unsafe fn _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__1() -> *mut crate::leanh::LeanObject
{
    let mut v___x_2429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2429_ = crate::leanh::lean_unsigned_to_nat(400);
    v___x_2430_ = lean_nat_to_int(v___x_2429_);
    return v___x_2430_;
}
pub unsafe fn _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__2() -> *mut crate::leanh::LeanObject
{
    let mut v___x_2431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2431_ = crate::leanh::lean_unsigned_to_nat(100);
    v___x_2432_ = lean_nat_to_int(v___x_2431_);
    return v___x_2432_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_dayOfYear(
    mut v_date_2433_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_2434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2436_: u8 = 0;
    let mut v___x_2437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_2438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2441_: u8 = 0;
    let mut v_month_2442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_day_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2448_: u8 = 0;
    let mut v_unused_2449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_2451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_year_2452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: u8 = 0;
    let mut v___x_2460_: u8 = 0;
    let mut v___x_2461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_2434_ = crate::leanh::lean_ctor_get(v_date_2433_, 0);
                v___x_2450_ = lean_thunk_get_own(v_date_2434_);
                v_date_2451_ = crate::leanh::lean_ctor_get(v___x_2450_, 0);
                crate::leanh::lean_inc_ref(v_date_2451_);
                crate::leanh::lean_dec(v___x_2450_);
                v_year_2452_ = crate::leanh::lean_ctor_get(v_date_2451_, 0);
                crate::leanh::lean_inc(v_year_2452_);
                crate::leanh::lean_dec_ref(v_date_2451_);
                v___x_2453_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_dayOfYear___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_dayOfYear___closed__0_once),
                    _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__0,
                );
                v___x_2454_ = lean_int_mod(v_year_2452_, v___x_2453_);
                v___x_2455_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0,
                );
                v___x_2460_ = lean_int_dec_eq(v___x_2454_, v___x_2455_);
                crate::leanh::lean_dec(v___x_2454_);
                if v___x_2460_ == 0 {
                    crate::leanh::lean_dec(v_year_2452_);
                    v___y_2436_ = v___x_2460_;
                    state = 1;
                    continue;
                } else {
                    v___x_2461_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_dayOfYear___closed__2),
                        core::ptr::addr_of_mut!(
                            l_Std_Time_ZonedDateTime_dayOfYear___closed__2_once
                        ),
                        _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__2,
                    );
                    v___x_2462_ = lean_int_mod(v_year_2452_, v___x_2461_);
                    v___x_2463_ = lean_int_dec_eq(v___x_2462_, v___x_2455_);
                    crate::leanh::lean_dec(v___x_2462_);
                    if v___x_2463_ == 0 {
                        if v___x_2460_ == 0 {
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_year_2452_);
                            v___y_2436_ = v___x_2460_;
                            state = 1;
                            continue;
                        }
                    } else {
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2437_ = lean_thunk_get_own(v_date_2434_);
                v_date_2438_ = crate::leanh::lean_ctor_get(v___x_2437_, 0);
                v_isSharedCheck_2448_ = (!crate::leanh::lean_is_exclusive(v___x_2437_)) as u8;
                if v_isSharedCheck_2448_ == 0 {
                    v_unused_2449_ = crate::leanh::lean_ctor_get(v___x_2437_, 1);
                    crate::leanh::lean_dec(v_unused_2449_);
                    v___x_2440_ = v___x_2437_;
                    v_isShared_2441_ = v_isSharedCheck_2448_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_date_2438_);
                    crate::leanh::lean_dec(v___x_2437_);
                    v___x_2440_ = crate::leanh::lean_box(0);
                    v_isShared_2441_ = v_isSharedCheck_2448_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_month_2442_ = crate::leanh::lean_ctor_get(v_date_2438_, 1);
                crate::leanh::lean_inc(v_month_2442_);
                v_day_2443_ = crate::leanh::lean_ctor_get(v_date_2438_, 2);
                crate::leanh::lean_inc(v_day_2443_);
                crate::leanh::lean_dec_ref(v_date_2438_);
                if v_isShared_2441_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2440_, 1, v_day_2443_);
                    crate::leanh::lean_ctor_set(v___x_2440_, 0, v_month_2442_);
                    v___x_2445_ = v___x_2440_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2447_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2447_, 0, v_month_2442_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2447_, 1, v_day_2443_);
                    v___x_2445_ = v_reuseFailAlloc_2447_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2446_ = l_Std_Time_ValidDate_dayOfYear(v___y_2436_, v___x_2445_);
                crate::leanh::lean_dec_ref(v___x_2445_);
                return v___x_2446_;
            }
            4 => {
                v___x_2457_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_dayOfYear___closed__1),
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_dayOfYear___closed__1_once),
                    _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__1,
                );
                v___x_2458_ = lean_int_mod(v_year_2452_, v___x_2457_);
                crate::leanh::lean_dec(v_year_2452_);
                v___x_2459_ = lean_int_dec_eq(v___x_2458_, v___x_2455_);
                crate::leanh::lean_dec(v___x_2458_);
                v___y_2436_ = v___x_2459_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_ZonedDateTime_dayOfYear___boxed(
    mut v_date_2464_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2465_ = l_Std_Time_ZonedDateTime_dayOfYear(v_date_2464_);
    crate::leanh::lean_dec_ref(v_date_2464_);
    return v_res_2465_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_weekOfYear(
    mut v_date_2466_: *mut crate::leanh::LeanObject,
    mut v_firstDay_2467_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_2468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_2470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_date_2468_ = crate::leanh::lean_ctor_get(v_date_2466_, 0);
    v___x_2469_ = lean_thunk_get_own(v_date_2468_);
    v_date_2470_ = crate::leanh::lean_ctor_get(v___x_2469_, 0);
    crate::leanh::lean_inc_ref(v_date_2470_);
    crate::leanh::lean_dec(v___x_2469_);
    v___x_2471_ = l_Std_Time_PlainDate_weekOfYear(v_date_2470_, v_firstDay_2467_);
    return v___x_2471_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_weekOfYear___boxed(
    mut v_date_2472_: *mut crate::leanh::LeanObject,
    mut v_firstDay_2473_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_firstDay_boxed_2474_: u8 = 0;
    let mut v_res_2475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_firstDay_boxed_2474_ = (crate::leanh::lean_unbox(v_firstDay_2473_) as u8);
    v_res_2475_ = l_Std_Time_ZonedDateTime_weekOfYear(v_date_2472_, v_firstDay_boxed_2474_);
    crate::leanh::lean_dec_ref(v_date_2472_);
    return v_res_2475_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_weekYear(
    mut v_date_2476_: *mut crate::leanh::LeanObject,
    mut v_firstDay_2477_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_2478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_2480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_date_2478_ = crate::leanh::lean_ctor_get(v_date_2476_, 0);
    v___x_2479_ = lean_thunk_get_own(v_date_2478_);
    v_date_2480_ = crate::leanh::lean_ctor_get(v___x_2479_, 0);
    crate::leanh::lean_inc_ref(v_date_2480_);
    crate::leanh::lean_dec(v___x_2479_);
    v___x_2481_ = l_Std_Time_PlainDate_weekYear(v_date_2480_, v_firstDay_2477_);
    return v___x_2481_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_weekYear___boxed(
    mut v_date_2482_: *mut crate::leanh::LeanObject,
    mut v_firstDay_2483_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_firstDay_boxed_2484_: u8 = 0;
    let mut v_res_2485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_firstDay_boxed_2484_ = (crate::leanh::lean_unbox(v_firstDay_2483_) as u8);
    v_res_2485_ = l_Std_Time_ZonedDateTime_weekYear(v_date_2482_, v_firstDay_boxed_2484_);
    crate::leanh::lean_dec_ref(v_date_2482_);
    return v_res_2485_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_weekOfMonth(
    mut v_date_2486_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_2487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_date_2487_ = crate::leanh::lean_ctor_get(v_date_2486_, 0);
    v___x_2488_ = lean_thunk_get_own(v_date_2487_);
    v___x_2489_ = l_Std_Time_PlainDateTime_weekOfMonth(v___x_2488_);
    crate::leanh::lean_dec(v___x_2488_);
    return v___x_2489_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_weekOfMonth___boxed(
    mut v_date_2490_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2491_ = l_Std_Time_ZonedDateTime_weekOfMonth(v_date_2490_);
    crate::leanh::lean_dec_ref(v_date_2490_);
    return v_res_2491_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_alignedWeekOfMonth(
    mut v_date_2492_: *mut crate::leanh::LeanObject,
    mut v_firstDay_2493_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_2494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_2496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_date_2494_ = crate::leanh::lean_ctor_get(v_date_2492_, 0);
    v___x_2495_ = lean_thunk_get_own(v_date_2494_);
    v_date_2496_ = crate::leanh::lean_ctor_get(v___x_2495_, 0);
    crate::leanh::lean_inc_ref(v_date_2496_);
    crate::leanh::lean_dec(v___x_2495_);
    v___x_2497_ = l_Std_Time_PlainDate_alignedWeekOfMonth(v_date_2496_, v_firstDay_2493_);
    return v___x_2497_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_alignedWeekOfMonth___boxed(
    mut v_date_2498_: *mut crate::leanh::LeanObject,
    mut v_firstDay_2499_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_firstDay_boxed_2500_: u8 = 0;
    let mut v_res_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_firstDay_boxed_2500_ = (crate::leanh::lean_unbox(v_firstDay_2499_) as u8);
    v_res_2501_ = l_Std_Time_ZonedDateTime_alignedWeekOfMonth(v_date_2498_, v_firstDay_boxed_2500_);
    crate::leanh::lean_dec_ref(v_date_2498_);
    return v_res_2501_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_quarter(
    mut v_date_2502_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_2503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_2505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_date_2503_ = crate::leanh::lean_ctor_get(v_date_2502_, 0);
    v___x_2504_ = lean_thunk_get_own(v_date_2503_);
    v_date_2505_ = crate::leanh::lean_ctor_get(v___x_2504_, 0);
    crate::leanh::lean_inc_ref(v_date_2505_);
    crate::leanh::lean_dec(v___x_2504_);
    v___x_2506_ = l_Std_Time_PlainDate_quarter(v_date_2505_);
    crate::leanh::lean_dec_ref(v_date_2505_);
    return v___x_2506_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_quarter___boxed(
    mut v_date_2507_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2508_ = l_Std_Time_ZonedDateTime_quarter(v_date_2507_);
    crate::leanh::lean_dec_ref(v_date_2507_);
    return v_res_2508_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_addDays___lam__0(
    mut v___y_2509_: *mut crate::leanh::LeanObject,
    mut v___x_2510_: *mut crate::leanh::LeanObject,
    mut v___x_2511_: *mut crate::leanh::LeanObject,
    mut v___x_2512_: *mut crate::leanh::LeanObject,
    mut v_x_2513_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_offset_2514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_offset_2514_ = crate::leanh::lean_ctor_get(v___y_2509_, 0);
    v_second_2515_ = crate::leanh::lean_ctor_get(v___x_2510_, 0);
    v_nano_2516_ = crate::leanh::lean_ctor_get(v___x_2510_, 1);
    v___x_2517_ = lean_int_mul(v_second_2515_, v___x_2511_);
    v___x_2518_ = lean_int_add(v___x_2517_, v_nano_2516_);
    crate::leanh::lean_dec(v___x_2517_);
    v___x_2519_ = lean_int_mul(v_offset_2514_, v___x_2511_);
    v___x_2520_ = lean_int_add(v___x_2519_, v___x_2512_);
    crate::leanh::lean_dec(v___x_2519_);
    v___x_2521_ = lean_int_add(v___x_2518_, v___x_2520_);
    crate::leanh::lean_dec(v___x_2520_);
    crate::leanh::lean_dec(v___x_2518_);
    v___x_2522_ = l_Std_Time_Duration_ofNanoseconds(v___x_2521_);
    crate::leanh::lean_dec(v___x_2521_);
    v___x_2523_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_2522_);
    return v___x_2523_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_addDays___lam__0___boxed(
    mut v___y_2524_: *mut crate::leanh::LeanObject,
    mut v___x_2525_: *mut crate::leanh::LeanObject,
    mut v___x_2526_: *mut crate::leanh::LeanObject,
    mut v___x_2527_: *mut crate::leanh::LeanObject,
    mut v_x_2528_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2529_ = l_Std_Time_ZonedDateTime_addDays___lam__0(
        v___y_2524_,
        v___x_2525_,
        v___x_2526_,
        v___x_2527_,
        v_x_2528_,
    );
    crate::leanh::lean_dec(v___x_2527_);
    crate::leanh::lean_dec(v___x_2526_);
    crate::leanh::lean_dec_ref(v___x_2525_);
    crate::leanh::lean_dec_ref(v___y_2524_);
    return v_res_2529_;
}
pub unsafe fn _init_l_Std_Time_ZonedDateTime_addDays___closed__0() -> *mut crate::leanh::LeanObject
{
    let mut v___x_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2530_ = crate::leanh::lean_unsigned_to_nat(86400);
    v___x_2531_ = lean_nat_to_int(v___x_2530_);
    return v___x_2531_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_addDays(
    mut v_dt_2532_: *mut crate::leanh::LeanObject,
    mut v_days_2533_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_timestamp_2534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rules_2535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2538_: u8 = 0;
    let mut v_second_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initialLocalTimeType_2541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_transitions_2542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2563_: u8 = 0;
    let mut v_unused_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_2534_ = crate::leanh::lean_ctor_get(v_dt_2532_, 1);
                v_rules_2535_ = crate::leanh::lean_ctor_get(v_dt_2532_, 2);
                v_isSharedCheck_2563_ = (!crate::leanh::lean_is_exclusive(v_dt_2532_)) as u8;
                if v_isSharedCheck_2563_ == 0 {
                    v_unused_2564_ = crate::leanh::lean_ctor_get(v_dt_2532_, 3);
                    crate::leanh::lean_dec(v_unused_2564_);
                    v_unused_2565_ = crate::leanh::lean_ctor_get(v_dt_2532_, 0);
                    crate::leanh::lean_dec(v_unused_2565_);
                    v___x_2537_ = v_dt_2532_;
                    v_isShared_2538_ = v_isSharedCheck_2563_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_rules_2535_);
                    crate::leanh::lean_inc(v_timestamp_2534_);
                    crate::leanh::lean_dec(v_dt_2532_);
                    v___x_2537_ = crate::leanh::lean_box(0);
                    v_isShared_2538_ = v_isSharedCheck_2563_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_second_2539_ = crate::leanh::lean_ctor_get(v_timestamp_2534_, 0);
                crate::leanh::lean_inc(v_second_2539_);
                v_nano_2540_ = crate::leanh::lean_ctor_get(v_timestamp_2534_, 1);
                crate::leanh::lean_inc(v_nano_2540_);
                crate::leanh::lean_dec_ref(v_timestamp_2534_);
                v_initialLocalTimeType_2541_ = crate::leanh::lean_ctor_get(v_rules_2535_, 0);
                v_transitions_2542_ = crate::leanh::lean_ctor_get(v_rules_2535_, 1);
                v___x_2543_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_addDays___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_addDays___closed__0_once),
                    _init_l_Std_Time_ZonedDateTime_addDays___closed__0,
                );
                v___x_2544_ = lean_int_mul(v_days_2533_, v___x_2543_);
                v___x_2545_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0,
                );
                v___x_2546_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_2547_ = lean_int_mul(v_second_2539_, v___x_2546_);
                crate::leanh::lean_dec(v_second_2539_);
                v___x_2548_ = lean_int_add(v___x_2547_, v_nano_2540_);
                crate::leanh::lean_dec(v_nano_2540_);
                crate::leanh::lean_dec(v___x_2547_);
                v___x_2549_ = lean_int_mul(v___x_2544_, v___x_2546_);
                crate::leanh::lean_dec(v___x_2544_);
                v___x_2550_ = lean_int_add(v___x_2549_, v___x_2545_);
                crate::leanh::lean_dec(v___x_2549_);
                v___x_2551_ = lean_int_add(v___x_2548_, v___x_2550_);
                crate::leanh::lean_dec(v___x_2550_);
                crate::leanh::lean_dec(v___x_2548_);
                v___x_2552_ = l_Std_Time_Duration_ofNanoseconds(v___x_2551_);
                crate::leanh::lean_dec(v___x_2551_);
                v___x_2560_ =
                    l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_2542_, v___x_2552_);
                if crate::leanh::lean_obj_tag(v___x_2560_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_2560_, 1);
                    v___x_2561_ =
                        l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_2541_);
                    v___y_2554_ = v___x_2561_;
                    state = 2;
                    continue;
                } else {
                    v_a_2562_ = crate::leanh::lean_ctor_get(v___x_2560_, 0);
                    crate::leanh::lean_inc(v_a_2562_);
                    crate::leanh::lean_dec_ref_known(v___x_2560_, 1);
                    v___y_2554_ = v_a_2562_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc_ref(v___x_2552_);
                crate::leanh::lean_inc_ref(v___y_2554_);
                v___f_2555_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addDays___lam__0___boxed as *mut core::ffi::c_void,
                    5,
                    4,
                );
                crate::leanh::lean_closure_set(v___f_2555_, 0, v___y_2554_);
                crate::leanh::lean_closure_set(v___f_2555_, 1, v___x_2552_);
                crate::leanh::lean_closure_set(v___f_2555_, 2, v___x_2546_);
                crate::leanh::lean_closure_set(v___f_2555_, 3, v___x_2545_);
                v___x_2556_ = lean_mk_thunk(v___f_2555_);
                if v_isShared_2538_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2537_, 3, v___y_2554_);
                    crate::leanh::lean_ctor_set(v___x_2537_, 1, v___x_2552_);
                    crate::leanh::lean_ctor_set(v___x_2537_, 0, v___x_2556_);
                    v___x_2558_ = v___x_2537_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2559_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2559_, 0, v___x_2556_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2559_, 1, v___x_2552_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2559_, 2, v_rules_2535_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2559_, 3, v___y_2554_);
                    v___x_2558_ = v_reuseFailAlloc_2559_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2558_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_ZonedDateTime_addDays___boxed(
    mut v_dt_2566_: *mut crate::leanh::LeanObject,
    mut v_days_2567_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2568_ = l_Std_Time_ZonedDateTime_addDays(v_dt_2566_, v_days_2567_);
    crate::leanh::lean_dec(v_days_2567_);
    return v_res_2568_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_subDays(
    mut v_dt_2569_: *mut crate::leanh::LeanObject,
    mut v_days_2570_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_timestamp_2571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rules_2572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2575_: u8 = 0;
    let mut v_second_2576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initialLocalTimeType_2578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_transitions_2579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2602_: u8 = 0;
    let mut v_unused_2603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_2571_ = crate::leanh::lean_ctor_get(v_dt_2569_, 1);
                v_rules_2572_ = crate::leanh::lean_ctor_get(v_dt_2569_, 2);
                v_isSharedCheck_2602_ = (!crate::leanh::lean_is_exclusive(v_dt_2569_)) as u8;
                if v_isSharedCheck_2602_ == 0 {
                    v_unused_2603_ = crate::leanh::lean_ctor_get(v_dt_2569_, 3);
                    crate::leanh::lean_dec(v_unused_2603_);
                    v_unused_2604_ = crate::leanh::lean_ctor_get(v_dt_2569_, 0);
                    crate::leanh::lean_dec(v_unused_2604_);
                    v___x_2574_ = v_dt_2569_;
                    v_isShared_2575_ = v_isSharedCheck_2602_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_rules_2572_);
                    crate::leanh::lean_inc(v_timestamp_2571_);
                    crate::leanh::lean_dec(v_dt_2569_);
                    v___x_2574_ = crate::leanh::lean_box(0);
                    v_isShared_2575_ = v_isSharedCheck_2602_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_second_2576_ = crate::leanh::lean_ctor_get(v_timestamp_2571_, 0);
                crate::leanh::lean_inc(v_second_2576_);
                v_nano_2577_ = crate::leanh::lean_ctor_get(v_timestamp_2571_, 1);
                crate::leanh::lean_inc(v_nano_2577_);
                crate::leanh::lean_dec_ref(v_timestamp_2571_);
                v_initialLocalTimeType_2578_ = crate::leanh::lean_ctor_get(v_rules_2572_, 0);
                v_transitions_2579_ = crate::leanh::lean_ctor_get(v_rules_2572_, 1);
                v___x_2580_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_addDays___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_addDays___closed__0_once),
                    _init_l_Std_Time_ZonedDateTime_addDays___closed__0,
                );
                v___x_2581_ = lean_int_mul(v_days_2570_, v___x_2580_);
                v___x_2582_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0,
                );
                v___x_2583_ = lean_int_neg(v___x_2581_);
                crate::leanh::lean_dec(v___x_2581_);
                v___x_2584_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
                );
                v___x_2585_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_2586_ = lean_int_mul(v_second_2576_, v___x_2585_);
                crate::leanh::lean_dec(v_second_2576_);
                v___x_2587_ = lean_int_add(v___x_2586_, v_nano_2577_);
                crate::leanh::lean_dec(v_nano_2577_);
                crate::leanh::lean_dec(v___x_2586_);
                v___x_2588_ = lean_int_mul(v___x_2583_, v___x_2585_);
                crate::leanh::lean_dec(v___x_2583_);
                v___x_2589_ = lean_int_add(v___x_2588_, v___x_2584_);
                crate::leanh::lean_dec(v___x_2588_);
                v___x_2590_ = lean_int_add(v___x_2587_, v___x_2589_);
                crate::leanh::lean_dec(v___x_2589_);
                crate::leanh::lean_dec(v___x_2587_);
                v___x_2591_ = l_Std_Time_Duration_ofNanoseconds(v___x_2590_);
                crate::leanh::lean_dec(v___x_2590_);
                v___x_2599_ =
                    l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_2579_, v___x_2591_);
                if crate::leanh::lean_obj_tag(v___x_2599_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_2599_, 1);
                    v___x_2600_ =
                        l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_2578_);
                    v___y_2593_ = v___x_2600_;
                    state = 2;
                    continue;
                } else {
                    v_a_2601_ = crate::leanh::lean_ctor_get(v___x_2599_, 0);
                    crate::leanh::lean_inc(v_a_2601_);
                    crate::leanh::lean_dec_ref_known(v___x_2599_, 1);
                    v___y_2593_ = v_a_2601_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc_ref(v___x_2591_);
                crate::leanh::lean_inc_ref(v___y_2593_);
                v___f_2594_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addDays___lam__0___boxed as *mut core::ffi::c_void,
                    5,
                    4,
                );
                crate::leanh::lean_closure_set(v___f_2594_, 0, v___y_2593_);
                crate::leanh::lean_closure_set(v___f_2594_, 1, v___x_2591_);
                crate::leanh::lean_closure_set(v___f_2594_, 2, v___x_2585_);
                crate::leanh::lean_closure_set(v___f_2594_, 3, v___x_2582_);
                v___x_2595_ = lean_mk_thunk(v___f_2594_);
                if v_isShared_2575_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2574_, 3, v___y_2593_);
                    crate::leanh::lean_ctor_set(v___x_2574_, 1, v___x_2591_);
                    crate::leanh::lean_ctor_set(v___x_2574_, 0, v___x_2595_);
                    v___x_2597_ = v___x_2574_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2598_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2598_, 0, v___x_2595_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2598_, 1, v___x_2591_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2598_, 2, v_rules_2572_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2598_, 3, v___y_2593_);
                    v___x_2597_ = v_reuseFailAlloc_2598_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2597_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_ZonedDateTime_subDays___boxed(
    mut v_dt_2605_: *mut crate::leanh::LeanObject,
    mut v_days_2606_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2607_ = l_Std_Time_ZonedDateTime_subDays(v_dt_2605_, v_days_2606_);
    crate::leanh::lean_dec(v_days_2606_);
    return v_res_2607_;
}
pub unsafe fn _init_l_Std_Time_ZonedDateTime_addWeeks___closed__0() -> *mut crate::leanh::LeanObject
{
    let mut v___x_2608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2608_ = crate::leanh::lean_unsigned_to_nat(7);
    v___x_2609_ = lean_nat_to_int(v___x_2608_);
    return v___x_2609_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_addWeeks(
    mut v_dt_2610_: *mut crate::leanh::LeanObject,
    mut v_weeks_2611_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_timestamp_2612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rules_2613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2616_: u8 = 0;
    let mut v_second_2617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initialLocalTimeType_2619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_transitions_2620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2643_: u8 = 0;
    let mut v_unused_2644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_2612_ = crate::leanh::lean_ctor_get(v_dt_2610_, 1);
                v_rules_2613_ = crate::leanh::lean_ctor_get(v_dt_2610_, 2);
                v_isSharedCheck_2643_ = (!crate::leanh::lean_is_exclusive(v_dt_2610_)) as u8;
                if v_isSharedCheck_2643_ == 0 {
                    v_unused_2644_ = crate::leanh::lean_ctor_get(v_dt_2610_, 3);
                    crate::leanh::lean_dec(v_unused_2644_);
                    v_unused_2645_ = crate::leanh::lean_ctor_get(v_dt_2610_, 0);
                    crate::leanh::lean_dec(v_unused_2645_);
                    v___x_2615_ = v_dt_2610_;
                    v_isShared_2616_ = v_isSharedCheck_2643_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_rules_2613_);
                    crate::leanh::lean_inc(v_timestamp_2612_);
                    crate::leanh::lean_dec(v_dt_2610_);
                    v___x_2615_ = crate::leanh::lean_box(0);
                    v_isShared_2616_ = v_isSharedCheck_2643_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_second_2617_ = crate::leanh::lean_ctor_get(v_timestamp_2612_, 0);
                crate::leanh::lean_inc(v_second_2617_);
                v_nano_2618_ = crate::leanh::lean_ctor_get(v_timestamp_2612_, 1);
                crate::leanh::lean_inc(v_nano_2618_);
                crate::leanh::lean_dec_ref(v_timestamp_2612_);
                v_initialLocalTimeType_2619_ = crate::leanh::lean_ctor_get(v_rules_2613_, 0);
                v_transitions_2620_ = crate::leanh::lean_ctor_get(v_rules_2613_, 1);
                v___x_2621_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_addWeeks___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_addWeeks___closed__0_once),
                    _init_l_Std_Time_ZonedDateTime_addWeeks___closed__0,
                );
                v___x_2622_ = lean_int_mul(v_weeks_2611_, v___x_2621_);
                v___x_2623_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_addDays___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_addDays___closed__0_once),
                    _init_l_Std_Time_ZonedDateTime_addDays___closed__0,
                );
                v___x_2624_ = lean_int_mul(v___x_2622_, v___x_2623_);
                crate::leanh::lean_dec(v___x_2622_);
                v___x_2625_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0,
                );
                v___x_2626_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_2627_ = lean_int_mul(v_second_2617_, v___x_2626_);
                crate::leanh::lean_dec(v_second_2617_);
                v___x_2628_ = lean_int_add(v___x_2627_, v_nano_2618_);
                crate::leanh::lean_dec(v_nano_2618_);
                crate::leanh::lean_dec(v___x_2627_);
                v___x_2629_ = lean_int_mul(v___x_2624_, v___x_2626_);
                crate::leanh::lean_dec(v___x_2624_);
                v___x_2630_ = lean_int_add(v___x_2629_, v___x_2625_);
                crate::leanh::lean_dec(v___x_2629_);
                v___x_2631_ = lean_int_add(v___x_2628_, v___x_2630_);
                crate::leanh::lean_dec(v___x_2630_);
                crate::leanh::lean_dec(v___x_2628_);
                v___x_2632_ = l_Std_Time_Duration_ofNanoseconds(v___x_2631_);
                crate::leanh::lean_dec(v___x_2631_);
                v___x_2640_ =
                    l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_2620_, v___x_2632_);
                if crate::leanh::lean_obj_tag(v___x_2640_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_2640_, 1);
                    v___x_2641_ =
                        l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_2619_);
                    v___y_2634_ = v___x_2641_;
                    state = 2;
                    continue;
                } else {
                    v_a_2642_ = crate::leanh::lean_ctor_get(v___x_2640_, 0);
                    crate::leanh::lean_inc(v_a_2642_);
                    crate::leanh::lean_dec_ref_known(v___x_2640_, 1);
                    v___y_2634_ = v_a_2642_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc_ref(v___x_2632_);
                crate::leanh::lean_inc_ref(v___y_2634_);
                v___f_2635_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addDays___lam__0___boxed as *mut core::ffi::c_void,
                    5,
                    4,
                );
                crate::leanh::lean_closure_set(v___f_2635_, 0, v___y_2634_);
                crate::leanh::lean_closure_set(v___f_2635_, 1, v___x_2632_);
                crate::leanh::lean_closure_set(v___f_2635_, 2, v___x_2626_);
                crate::leanh::lean_closure_set(v___f_2635_, 3, v___x_2625_);
                v___x_2636_ = lean_mk_thunk(v___f_2635_);
                if v_isShared_2616_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2615_, 3, v___y_2634_);
                    crate::leanh::lean_ctor_set(v___x_2615_, 1, v___x_2632_);
                    crate::leanh::lean_ctor_set(v___x_2615_, 0, v___x_2636_);
                    v___x_2638_ = v___x_2615_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2639_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2639_, 0, v___x_2636_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2639_, 1, v___x_2632_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2639_, 2, v_rules_2613_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2639_, 3, v___y_2634_);
                    v___x_2638_ = v_reuseFailAlloc_2639_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2638_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_ZonedDateTime_addWeeks___boxed(
    mut v_dt_2646_: *mut crate::leanh::LeanObject,
    mut v_weeks_2647_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2648_ = l_Std_Time_ZonedDateTime_addWeeks(v_dt_2646_, v_weeks_2647_);
    crate::leanh::lean_dec(v_weeks_2647_);
    return v_res_2648_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_subWeeks(
    mut v_dt_2649_: *mut crate::leanh::LeanObject,
    mut v_weeks_2650_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_timestamp_2651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rules_2652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2655_: u8 = 0;
    let mut v_second_2656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initialLocalTimeType_2658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_transitions_2659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2684_: u8 = 0;
    let mut v_unused_2685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_2651_ = crate::leanh::lean_ctor_get(v_dt_2649_, 1);
                v_rules_2652_ = crate::leanh::lean_ctor_get(v_dt_2649_, 2);
                v_isSharedCheck_2684_ = (!crate::leanh::lean_is_exclusive(v_dt_2649_)) as u8;
                if v_isSharedCheck_2684_ == 0 {
                    v_unused_2685_ = crate::leanh::lean_ctor_get(v_dt_2649_, 3);
                    crate::leanh::lean_dec(v_unused_2685_);
                    v_unused_2686_ = crate::leanh::lean_ctor_get(v_dt_2649_, 0);
                    crate::leanh::lean_dec(v_unused_2686_);
                    v___x_2654_ = v_dt_2649_;
                    v_isShared_2655_ = v_isSharedCheck_2684_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_rules_2652_);
                    crate::leanh::lean_inc(v_timestamp_2651_);
                    crate::leanh::lean_dec(v_dt_2649_);
                    v___x_2654_ = crate::leanh::lean_box(0);
                    v_isShared_2655_ = v_isSharedCheck_2684_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_second_2656_ = crate::leanh::lean_ctor_get(v_timestamp_2651_, 0);
                crate::leanh::lean_inc(v_second_2656_);
                v_nano_2657_ = crate::leanh::lean_ctor_get(v_timestamp_2651_, 1);
                crate::leanh::lean_inc(v_nano_2657_);
                crate::leanh::lean_dec_ref(v_timestamp_2651_);
                v_initialLocalTimeType_2658_ = crate::leanh::lean_ctor_get(v_rules_2652_, 0);
                v_transitions_2659_ = crate::leanh::lean_ctor_get(v_rules_2652_, 1);
                v___x_2660_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_addWeeks___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_addWeeks___closed__0_once),
                    _init_l_Std_Time_ZonedDateTime_addWeeks___closed__0,
                );
                v___x_2661_ = lean_int_mul(v_weeks_2650_, v___x_2660_);
                v___x_2662_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_addDays___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_addDays___closed__0_once),
                    _init_l_Std_Time_ZonedDateTime_addDays___closed__0,
                );
                v___x_2663_ = lean_int_mul(v___x_2661_, v___x_2662_);
                crate::leanh::lean_dec(v___x_2661_);
                v___x_2664_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0,
                );
                v___x_2665_ = lean_int_neg(v___x_2663_);
                crate::leanh::lean_dec(v___x_2663_);
                v___x_2666_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
                );
                v___x_2667_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_2668_ = lean_int_mul(v_second_2656_, v___x_2667_);
                crate::leanh::lean_dec(v_second_2656_);
                v___x_2669_ = lean_int_add(v___x_2668_, v_nano_2657_);
                crate::leanh::lean_dec(v_nano_2657_);
                crate::leanh::lean_dec(v___x_2668_);
                v___x_2670_ = lean_int_mul(v___x_2665_, v___x_2667_);
                crate::leanh::lean_dec(v___x_2665_);
                v___x_2671_ = lean_int_add(v___x_2670_, v___x_2666_);
                crate::leanh::lean_dec(v___x_2670_);
                v___x_2672_ = lean_int_add(v___x_2669_, v___x_2671_);
                crate::leanh::lean_dec(v___x_2671_);
                crate::leanh::lean_dec(v___x_2669_);
                v___x_2673_ = l_Std_Time_Duration_ofNanoseconds(v___x_2672_);
                crate::leanh::lean_dec(v___x_2672_);
                v___x_2681_ =
                    l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_2659_, v___x_2673_);
                if crate::leanh::lean_obj_tag(v___x_2681_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_2681_, 1);
                    v___x_2682_ =
                        l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_2658_);
                    v___y_2675_ = v___x_2682_;
                    state = 2;
                    continue;
                } else {
                    v_a_2683_ = crate::leanh::lean_ctor_get(v___x_2681_, 0);
                    crate::leanh::lean_inc(v_a_2683_);
                    crate::leanh::lean_dec_ref_known(v___x_2681_, 1);
                    v___y_2675_ = v_a_2683_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc_ref(v___x_2673_);
                crate::leanh::lean_inc_ref(v___y_2675_);
                v___f_2676_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addDays___lam__0___boxed as *mut core::ffi::c_void,
                    5,
                    4,
                );
                crate::leanh::lean_closure_set(v___f_2676_, 0, v___y_2675_);
                crate::leanh::lean_closure_set(v___f_2676_, 1, v___x_2673_);
                crate::leanh::lean_closure_set(v___f_2676_, 2, v___x_2667_);
                crate::leanh::lean_closure_set(v___f_2676_, 3, v___x_2664_);
                v___x_2677_ = lean_mk_thunk(v___f_2676_);
                if v_isShared_2655_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2654_, 3, v___y_2675_);
                    crate::leanh::lean_ctor_set(v___x_2654_, 1, v___x_2673_);
                    crate::leanh::lean_ctor_set(v___x_2654_, 0, v___x_2677_);
                    v___x_2679_ = v___x_2654_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2680_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2680_, 0, v___x_2677_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2680_, 1, v___x_2673_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2680_, 2, v_rules_2652_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2680_, 3, v___y_2675_);
                    v___x_2679_ = v_reuseFailAlloc_2680_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2679_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_ZonedDateTime_subWeeks___boxed(
    mut v_dt_2687_: *mut crate::leanh::LeanObject,
    mut v_weeks_2688_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2689_ = l_Std_Time_ZonedDateTime_subWeeks(v_dt_2687_, v_weeks_2688_);
    crate::leanh::lean_dec(v_weeks_2688_);
    return v_res_2689_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_addMonthsClip___lam__0(
    mut v___x_2690_: *mut crate::leanh::LeanObject,
    mut v_x_2691_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v___x_2690_);
    return v___x_2690_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed(
    mut v___x_2692_: *mut crate::leanh::LeanObject,
    mut v_x_2693_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2694_ = l_Std_Time_ZonedDateTime_addMonthsClip___lam__0(v___x_2692_, v_x_2693_);
    crate::leanh::lean_dec_ref(v___x_2692_);
    return v_res_2694_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_addMonthsClip(
    mut v_dt_2695_: *mut crate::leanh::LeanObject,
    mut v_months_2696_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_2697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rules_2698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2701_: u8 = 0;
    let mut v___x_2702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_wt_2704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ltt_2705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tz_2706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_2707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_2708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2724_: u8 = 0;
    let mut v_unused_2725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_2697_ = crate::leanh::lean_ctor_get(v_dt_2695_, 0);
                v_rules_2698_ = crate::leanh::lean_ctor_get(v_dt_2695_, 2);
                v_isSharedCheck_2724_ = (!crate::leanh::lean_is_exclusive(v_dt_2695_)) as u8;
                if v_isSharedCheck_2724_ == 0 {
                    v_unused_2725_ = crate::leanh::lean_ctor_get(v_dt_2695_, 3);
                    crate::leanh::lean_dec(v_unused_2725_);
                    v_unused_2726_ = crate::leanh::lean_ctor_get(v_dt_2695_, 1);
                    crate::leanh::lean_dec(v_unused_2726_);
                    v___x_2700_ = v_dt_2695_;
                    v_isShared_2701_ = v_isSharedCheck_2724_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_rules_2698_);
                    crate::leanh::lean_inc(v_date_2697_);
                    crate::leanh::lean_dec(v_dt_2695_);
                    v___x_2700_ = crate::leanh::lean_box(0);
                    v_isShared_2701_ = v_isSharedCheck_2724_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2702_ = lean_thunk_get_own(v_date_2697_);
                crate::leanh::lean_dec_ref(v_date_2697_);
                v___x_2703_ = l_Std_Time_PlainDateTime_addMonthsClip(v___x_2702_, v_months_2696_);
                crate::leanh::lean_inc_ref(v___x_2703_);
                v_wt_2704_ = l_Std_Time_PlainDateTime_toWallTime(v___x_2703_);
                crate::leanh::lean_inc_ref(v_rules_2698_);
                v_ltt_2705_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(
                    v_rules_2698_,
                    v_wt_2704_,
                );
                v_tz_2706_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_2705_);
                crate::leanh::lean_dec_ref(v_ltt_2705_);
                v_offset_2707_ = crate::leanh::lean_ctor_get(v_tz_2706_, 0);
                crate::leanh::lean_inc(v_offset_2707_);
                v_second_2708_ = crate::leanh::lean_ctor_get(v_wt_2704_, 0);
                crate::leanh::lean_inc(v_second_2708_);
                v_nano_2709_ = crate::leanh::lean_ctor_get(v_wt_2704_, 1);
                crate::leanh::lean_inc(v_nano_2709_);
                crate::leanh::lean_dec_ref(v_wt_2704_);
                v___f_2710_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2710_, 0, v___x_2703_);
                v___x_2711_ = lean_mk_thunk(v___f_2710_);
                v___x_2712_ = lean_int_neg(v_offset_2707_);
                crate::leanh::lean_dec(v_offset_2707_);
                v___x_2713_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
                );
                v___x_2714_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_2715_ = lean_int_mul(v_second_2708_, v___x_2714_);
                crate::leanh::lean_dec(v_second_2708_);
                v___x_2716_ = lean_int_add(v___x_2715_, v_nano_2709_);
                crate::leanh::lean_dec(v_nano_2709_);
                crate::leanh::lean_dec(v___x_2715_);
                v___x_2717_ = lean_int_mul(v___x_2712_, v___x_2714_);
                crate::leanh::lean_dec(v___x_2712_);
                v___x_2718_ = lean_int_add(v___x_2717_, v___x_2713_);
                crate::leanh::lean_dec(v___x_2717_);
                v___x_2719_ = lean_int_add(v___x_2716_, v___x_2718_);
                crate::leanh::lean_dec(v___x_2718_);
                crate::leanh::lean_dec(v___x_2716_);
                v___x_2720_ = l_Std_Time_Duration_ofNanoseconds(v___x_2719_);
                crate::leanh::lean_dec(v___x_2719_);
                if v_isShared_2701_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2700_, 3, v_tz_2706_);
                    crate::leanh::lean_ctor_set(v___x_2700_, 1, v___x_2720_);
                    crate::leanh::lean_ctor_set(v___x_2700_, 0, v___x_2711_);
                    v___x_2722_ = v___x_2700_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2723_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2723_, 0, v___x_2711_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2723_, 1, v___x_2720_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2723_, 2, v_rules_2698_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2723_, 3, v_tz_2706_);
                    v___x_2722_ = v_reuseFailAlloc_2723_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2722_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_ZonedDateTime_addMonthsClip___boxed(
    mut v_dt_2727_: *mut crate::leanh::LeanObject,
    mut v_months_2728_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2729_ = l_Std_Time_ZonedDateTime_addMonthsClip(v_dt_2727_, v_months_2728_);
    crate::leanh::lean_dec(v_months_2728_);
    return v_res_2729_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_subMonthsClip(
    mut v_dt_2730_: *mut crate::leanh::LeanObject,
    mut v_months_2731_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_2732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rules_2733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2736_: u8 = 0;
    let mut v___x_2737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_2738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_2739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2742_: u8 = 0;
    let mut v___x_2743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_wt_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ltt_2748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tz_2749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_2750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_2751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2768_: u8 = 0;
    let mut v_isSharedCheck_2769_: u8 = 0;
    let mut v_unused_2770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_2732_ = crate::leanh::lean_ctor_get(v_dt_2730_, 0);
                v_rules_2733_ = crate::leanh::lean_ctor_get(v_dt_2730_, 2);
                v_isSharedCheck_2769_ = (!crate::leanh::lean_is_exclusive(v_dt_2730_)) as u8;
                if v_isSharedCheck_2769_ == 0 {
                    v_unused_2770_ = crate::leanh::lean_ctor_get(v_dt_2730_, 3);
                    crate::leanh::lean_dec(v_unused_2770_);
                    v_unused_2771_ = crate::leanh::lean_ctor_get(v_dt_2730_, 1);
                    crate::leanh::lean_dec(v_unused_2771_);
                    v___x_2735_ = v_dt_2730_;
                    v_isShared_2736_ = v_isSharedCheck_2769_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_rules_2733_);
                    crate::leanh::lean_inc(v_date_2732_);
                    crate::leanh::lean_dec(v_dt_2730_);
                    v___x_2735_ = crate::leanh::lean_box(0);
                    v_isShared_2736_ = v_isSharedCheck_2769_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2737_ = lean_thunk_get_own(v_date_2732_);
                crate::leanh::lean_dec_ref(v_date_2732_);
                v_date_2738_ = crate::leanh::lean_ctor_get(v___x_2737_, 0);
                v_time_2739_ = crate::leanh::lean_ctor_get(v___x_2737_, 1);
                v_isSharedCheck_2768_ = (!crate::leanh::lean_is_exclusive(v___x_2737_)) as u8;
                if v_isSharedCheck_2768_ == 0 {
                    v___x_2741_ = v___x_2737_;
                    v_isShared_2742_ = v_isSharedCheck_2768_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_time_2739_);
                    crate::leanh::lean_inc(v_date_2738_);
                    crate::leanh::lean_dec(v___x_2737_);
                    v___x_2741_ = crate::leanh::lean_box(0);
                    v_isShared_2742_ = v_isSharedCheck_2768_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2743_ = lean_int_neg(v_months_2731_);
                v___x_2744_ = l_Std_Time_PlainDate_addMonthsClip(v_date_2738_, v___x_2743_);
                crate::leanh::lean_dec(v___x_2743_);
                if v_isShared_2742_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2741_, 0, v___x_2744_);
                    v___x_2746_ = v___x_2741_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2767_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2767_, 0, v___x_2744_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2767_, 1, v_time_2739_);
                    v___x_2746_ = v_reuseFailAlloc_2767_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_inc_ref(v___x_2746_);
                v_wt_2747_ = l_Std_Time_PlainDateTime_toWallTime(v___x_2746_);
                crate::leanh::lean_inc_ref(v_rules_2733_);
                v_ltt_2748_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(
                    v_rules_2733_,
                    v_wt_2747_,
                );
                v_tz_2749_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_2748_);
                crate::leanh::lean_dec_ref(v_ltt_2748_);
                v_offset_2750_ = crate::leanh::lean_ctor_get(v_tz_2749_, 0);
                crate::leanh::lean_inc(v_offset_2750_);
                v_second_2751_ = crate::leanh::lean_ctor_get(v_wt_2747_, 0);
                crate::leanh::lean_inc(v_second_2751_);
                v_nano_2752_ = crate::leanh::lean_ctor_get(v_wt_2747_, 1);
                crate::leanh::lean_inc(v_nano_2752_);
                crate::leanh::lean_dec_ref(v_wt_2747_);
                v___f_2753_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2753_, 0, v___x_2746_);
                v___x_2754_ = lean_mk_thunk(v___f_2753_);
                v___x_2755_ = lean_int_neg(v_offset_2750_);
                crate::leanh::lean_dec(v_offset_2750_);
                v___x_2756_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
                );
                v___x_2757_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_2758_ = lean_int_mul(v_second_2751_, v___x_2757_);
                crate::leanh::lean_dec(v_second_2751_);
                v___x_2759_ = lean_int_add(v___x_2758_, v_nano_2752_);
                crate::leanh::lean_dec(v_nano_2752_);
                crate::leanh::lean_dec(v___x_2758_);
                v___x_2760_ = lean_int_mul(v___x_2755_, v___x_2757_);
                crate::leanh::lean_dec(v___x_2755_);
                v___x_2761_ = lean_int_add(v___x_2760_, v___x_2756_);
                crate::leanh::lean_dec(v___x_2760_);
                v___x_2762_ = lean_int_add(v___x_2759_, v___x_2761_);
                crate::leanh::lean_dec(v___x_2761_);
                crate::leanh::lean_dec(v___x_2759_);
                v___x_2763_ = l_Std_Time_Duration_ofNanoseconds(v___x_2762_);
                crate::leanh::lean_dec(v___x_2762_);
                if v_isShared_2736_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2735_, 3, v_tz_2749_);
                    crate::leanh::lean_ctor_set(v___x_2735_, 1, v___x_2763_);
                    crate::leanh::lean_ctor_set(v___x_2735_, 0, v___x_2754_);
                    v___x_2765_ = v___x_2735_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2766_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2766_, 0, v___x_2754_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2766_, 1, v___x_2763_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2766_, 2, v_rules_2733_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2766_, 3, v_tz_2749_);
                    v___x_2765_ = v_reuseFailAlloc_2766_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2765_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_ZonedDateTime_subMonthsClip___boxed(
    mut v_dt_2772_: *mut crate::leanh::LeanObject,
    mut v_months_2773_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2774_ = l_Std_Time_ZonedDateTime_subMonthsClip(v_dt_2772_, v_months_2773_);
    crate::leanh::lean_dec(v_months_2773_);
    return v_res_2774_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_addMonthsRollOver(
    mut v_dt_2775_: *mut crate::leanh::LeanObject,
    mut v_months_2776_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_2777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rules_2778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2781_: u8 = 0;
    let mut v___x_2782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_wt_2784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ltt_2785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tz_2786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_2787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_2788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2804_: u8 = 0;
    let mut v_unused_2805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_2777_ = crate::leanh::lean_ctor_get(v_dt_2775_, 0);
                v_rules_2778_ = crate::leanh::lean_ctor_get(v_dt_2775_, 2);
                v_isSharedCheck_2804_ = (!crate::leanh::lean_is_exclusive(v_dt_2775_)) as u8;
                if v_isSharedCheck_2804_ == 0 {
                    v_unused_2805_ = crate::leanh::lean_ctor_get(v_dt_2775_, 3);
                    crate::leanh::lean_dec(v_unused_2805_);
                    v_unused_2806_ = crate::leanh::lean_ctor_get(v_dt_2775_, 1);
                    crate::leanh::lean_dec(v_unused_2806_);
                    v___x_2780_ = v_dt_2775_;
                    v_isShared_2781_ = v_isSharedCheck_2804_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_rules_2778_);
                    crate::leanh::lean_inc(v_date_2777_);
                    crate::leanh::lean_dec(v_dt_2775_);
                    v___x_2780_ = crate::leanh::lean_box(0);
                    v_isShared_2781_ = v_isSharedCheck_2804_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2782_ = lean_thunk_get_own(v_date_2777_);
                crate::leanh::lean_dec_ref(v_date_2777_);
                v___x_2783_ =
                    l_Std_Time_PlainDateTime_addMonthsRollOver(v___x_2782_, v_months_2776_);
                crate::leanh::lean_inc_ref(v___x_2783_);
                v_wt_2784_ = l_Std_Time_PlainDateTime_toWallTime(v___x_2783_);
                crate::leanh::lean_inc_ref(v_rules_2778_);
                v_ltt_2785_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(
                    v_rules_2778_,
                    v_wt_2784_,
                );
                v_tz_2786_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_2785_);
                crate::leanh::lean_dec_ref(v_ltt_2785_);
                v_offset_2787_ = crate::leanh::lean_ctor_get(v_tz_2786_, 0);
                crate::leanh::lean_inc(v_offset_2787_);
                v_second_2788_ = crate::leanh::lean_ctor_get(v_wt_2784_, 0);
                crate::leanh::lean_inc(v_second_2788_);
                v_nano_2789_ = crate::leanh::lean_ctor_get(v_wt_2784_, 1);
                crate::leanh::lean_inc(v_nano_2789_);
                crate::leanh::lean_dec_ref(v_wt_2784_);
                v___f_2790_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2790_, 0, v___x_2783_);
                v___x_2791_ = lean_mk_thunk(v___f_2790_);
                v___x_2792_ = lean_int_neg(v_offset_2787_);
                crate::leanh::lean_dec(v_offset_2787_);
                v___x_2793_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
                );
                v___x_2794_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_2795_ = lean_int_mul(v_second_2788_, v___x_2794_);
                crate::leanh::lean_dec(v_second_2788_);
                v___x_2796_ = lean_int_add(v___x_2795_, v_nano_2789_);
                crate::leanh::lean_dec(v_nano_2789_);
                crate::leanh::lean_dec(v___x_2795_);
                v___x_2797_ = lean_int_mul(v___x_2792_, v___x_2794_);
                crate::leanh::lean_dec(v___x_2792_);
                v___x_2798_ = lean_int_add(v___x_2797_, v___x_2793_);
                crate::leanh::lean_dec(v___x_2797_);
                v___x_2799_ = lean_int_add(v___x_2796_, v___x_2798_);
                crate::leanh::lean_dec(v___x_2798_);
                crate::leanh::lean_dec(v___x_2796_);
                v___x_2800_ = l_Std_Time_Duration_ofNanoseconds(v___x_2799_);
                crate::leanh::lean_dec(v___x_2799_);
                if v_isShared_2781_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2780_, 3, v_tz_2786_);
                    crate::leanh::lean_ctor_set(v___x_2780_, 1, v___x_2800_);
                    crate::leanh::lean_ctor_set(v___x_2780_, 0, v___x_2791_);
                    v___x_2802_ = v___x_2780_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2803_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2803_, 0, v___x_2791_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2803_, 1, v___x_2800_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2803_, 2, v_rules_2778_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2803_, 3, v_tz_2786_);
                    v___x_2802_ = v_reuseFailAlloc_2803_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2802_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_ZonedDateTime_addMonthsRollOver___boxed(
    mut v_dt_2807_: *mut crate::leanh::LeanObject,
    mut v_months_2808_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2809_ = l_Std_Time_ZonedDateTime_addMonthsRollOver(v_dt_2807_, v_months_2808_);
    crate::leanh::lean_dec(v_months_2808_);
    return v_res_2809_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_subMonthsRollOver(
    mut v_dt_2810_: *mut crate::leanh::LeanObject,
    mut v_months_2811_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_2812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rules_2813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2816_: u8 = 0;
    let mut v___x_2817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_2818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_2819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2822_: u8 = 0;
    let mut v___x_2823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_wt_2827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ltt_2828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tz_2829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_2830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_2831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2848_: u8 = 0;
    let mut v_isSharedCheck_2849_: u8 = 0;
    let mut v_unused_2850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_2812_ = crate::leanh::lean_ctor_get(v_dt_2810_, 0);
                v_rules_2813_ = crate::leanh::lean_ctor_get(v_dt_2810_, 2);
                v_isSharedCheck_2849_ = (!crate::leanh::lean_is_exclusive(v_dt_2810_)) as u8;
                if v_isSharedCheck_2849_ == 0 {
                    v_unused_2850_ = crate::leanh::lean_ctor_get(v_dt_2810_, 3);
                    crate::leanh::lean_dec(v_unused_2850_);
                    v_unused_2851_ = crate::leanh::lean_ctor_get(v_dt_2810_, 1);
                    crate::leanh::lean_dec(v_unused_2851_);
                    v___x_2815_ = v_dt_2810_;
                    v_isShared_2816_ = v_isSharedCheck_2849_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_rules_2813_);
                    crate::leanh::lean_inc(v_date_2812_);
                    crate::leanh::lean_dec(v_dt_2810_);
                    v___x_2815_ = crate::leanh::lean_box(0);
                    v_isShared_2816_ = v_isSharedCheck_2849_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2817_ = lean_thunk_get_own(v_date_2812_);
                crate::leanh::lean_dec_ref(v_date_2812_);
                v_date_2818_ = crate::leanh::lean_ctor_get(v___x_2817_, 0);
                v_time_2819_ = crate::leanh::lean_ctor_get(v___x_2817_, 1);
                v_isSharedCheck_2848_ = (!crate::leanh::lean_is_exclusive(v___x_2817_)) as u8;
                if v_isSharedCheck_2848_ == 0 {
                    v___x_2821_ = v___x_2817_;
                    v_isShared_2822_ = v_isSharedCheck_2848_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_time_2819_);
                    crate::leanh::lean_inc(v_date_2818_);
                    crate::leanh::lean_dec(v___x_2817_);
                    v___x_2821_ = crate::leanh::lean_box(0);
                    v_isShared_2822_ = v_isSharedCheck_2848_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2823_ = lean_int_neg(v_months_2811_);
                v___x_2824_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_2818_, v___x_2823_);
                crate::leanh::lean_dec(v___x_2823_);
                if v_isShared_2822_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2821_, 0, v___x_2824_);
                    v___x_2826_ = v___x_2821_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2847_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2847_, 0, v___x_2824_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2847_, 1, v_time_2819_);
                    v___x_2826_ = v_reuseFailAlloc_2847_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_inc_ref(v___x_2826_);
                v_wt_2827_ = l_Std_Time_PlainDateTime_toWallTime(v___x_2826_);
                crate::leanh::lean_inc_ref(v_rules_2813_);
                v_ltt_2828_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(
                    v_rules_2813_,
                    v_wt_2827_,
                );
                v_tz_2829_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_2828_);
                crate::leanh::lean_dec_ref(v_ltt_2828_);
                v_offset_2830_ = crate::leanh::lean_ctor_get(v_tz_2829_, 0);
                crate::leanh::lean_inc(v_offset_2830_);
                v_second_2831_ = crate::leanh::lean_ctor_get(v_wt_2827_, 0);
                crate::leanh::lean_inc(v_second_2831_);
                v_nano_2832_ = crate::leanh::lean_ctor_get(v_wt_2827_, 1);
                crate::leanh::lean_inc(v_nano_2832_);
                crate::leanh::lean_dec_ref(v_wt_2827_);
                v___f_2833_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2833_, 0, v___x_2826_);
                v___x_2834_ = lean_mk_thunk(v___f_2833_);
                v___x_2835_ = lean_int_neg(v_offset_2830_);
                crate::leanh::lean_dec(v_offset_2830_);
                v___x_2836_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
                );
                v___x_2837_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_2838_ = lean_int_mul(v_second_2831_, v___x_2837_);
                crate::leanh::lean_dec(v_second_2831_);
                v___x_2839_ = lean_int_add(v___x_2838_, v_nano_2832_);
                crate::leanh::lean_dec(v_nano_2832_);
                crate::leanh::lean_dec(v___x_2838_);
                v___x_2840_ = lean_int_mul(v___x_2835_, v___x_2837_);
                crate::leanh::lean_dec(v___x_2835_);
                v___x_2841_ = lean_int_add(v___x_2840_, v___x_2836_);
                crate::leanh::lean_dec(v___x_2840_);
                v___x_2842_ = lean_int_add(v___x_2839_, v___x_2841_);
                crate::leanh::lean_dec(v___x_2841_);
                crate::leanh::lean_dec(v___x_2839_);
                v___x_2843_ = l_Std_Time_Duration_ofNanoseconds(v___x_2842_);
                crate::leanh::lean_dec(v___x_2842_);
                if v_isShared_2816_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2815_, 3, v_tz_2829_);
                    crate::leanh::lean_ctor_set(v___x_2815_, 1, v___x_2843_);
                    crate::leanh::lean_ctor_set(v___x_2815_, 0, v___x_2834_);
                    v___x_2845_ = v___x_2815_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2846_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2846_, 0, v___x_2834_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2846_, 1, v___x_2843_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2846_, 2, v_rules_2813_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2846_, 3, v_tz_2829_);
                    v___x_2845_ = v_reuseFailAlloc_2846_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2845_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_ZonedDateTime_subMonthsRollOver___boxed(
    mut v_dt_2852_: *mut crate::leanh::LeanObject,
    mut v_months_2853_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2854_ = l_Std_Time_ZonedDateTime_subMonthsRollOver(v_dt_2852_, v_months_2853_);
    crate::leanh::lean_dec(v_months_2853_);
    return v_res_2854_;
}
pub unsafe fn _init_l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2855_ = crate::leanh::lean_unsigned_to_nat(12);
    v___x_2856_ = lean_nat_to_int(v___x_2855_);
    return v___x_2856_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_addYearsRollOver(
    mut v_dt_2857_: *mut crate::leanh::LeanObject,
    mut v_years_2858_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_2859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rules_2860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2863_: u8 = 0;
    let mut v___x_2864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_2865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_2866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2869_: u8 = 0;
    let mut v___x_2870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_wt_2875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ltt_2876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tz_2877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_2878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_2879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2896_: u8 = 0;
    let mut v_isSharedCheck_2897_: u8 = 0;
    let mut v_unused_2898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_2859_ = crate::leanh::lean_ctor_get(v_dt_2857_, 0);
                v_rules_2860_ = crate::leanh::lean_ctor_get(v_dt_2857_, 2);
                v_isSharedCheck_2897_ = (!crate::leanh::lean_is_exclusive(v_dt_2857_)) as u8;
                if v_isSharedCheck_2897_ == 0 {
                    v_unused_2898_ = crate::leanh::lean_ctor_get(v_dt_2857_, 3);
                    crate::leanh::lean_dec(v_unused_2898_);
                    v_unused_2899_ = crate::leanh::lean_ctor_get(v_dt_2857_, 1);
                    crate::leanh::lean_dec(v_unused_2899_);
                    v___x_2862_ = v_dt_2857_;
                    v_isShared_2863_ = v_isSharedCheck_2897_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_rules_2860_);
                    crate::leanh::lean_inc(v_date_2859_);
                    crate::leanh::lean_dec(v_dt_2857_);
                    v___x_2862_ = crate::leanh::lean_box(0);
                    v_isShared_2863_ = v_isSharedCheck_2897_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2864_ = lean_thunk_get_own(v_date_2859_);
                crate::leanh::lean_dec_ref(v_date_2859_);
                v_date_2865_ = crate::leanh::lean_ctor_get(v___x_2864_, 0);
                v_time_2866_ = crate::leanh::lean_ctor_get(v___x_2864_, 1);
                v_isSharedCheck_2896_ = (!crate::leanh::lean_is_exclusive(v___x_2864_)) as u8;
                if v_isSharedCheck_2896_ == 0 {
                    v___x_2868_ = v___x_2864_;
                    v_isShared_2869_ = v_isSharedCheck_2896_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_time_2866_);
                    crate::leanh::lean_inc(v_date_2865_);
                    crate::leanh::lean_dec(v___x_2864_);
                    v___x_2868_ = crate::leanh::lean_box(0);
                    v_isShared_2869_ = v_isSharedCheck_2896_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2870_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0,
                );
                v___x_2871_ = lean_int_mul(v_years_2858_, v___x_2870_);
                v___x_2872_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_2865_, v___x_2871_);
                crate::leanh::lean_dec(v___x_2871_);
                if v_isShared_2869_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2868_, 0, v___x_2872_);
                    v___x_2874_ = v___x_2868_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2895_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2895_, 0, v___x_2872_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2895_, 1, v_time_2866_);
                    v___x_2874_ = v_reuseFailAlloc_2895_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_inc_ref(v___x_2874_);
                v_wt_2875_ = l_Std_Time_PlainDateTime_toWallTime(v___x_2874_);
                crate::leanh::lean_inc_ref(v_rules_2860_);
                v_ltt_2876_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(
                    v_rules_2860_,
                    v_wt_2875_,
                );
                v_tz_2877_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_2876_);
                crate::leanh::lean_dec_ref(v_ltt_2876_);
                v_offset_2878_ = crate::leanh::lean_ctor_get(v_tz_2877_, 0);
                crate::leanh::lean_inc(v_offset_2878_);
                v_second_2879_ = crate::leanh::lean_ctor_get(v_wt_2875_, 0);
                crate::leanh::lean_inc(v_second_2879_);
                v_nano_2880_ = crate::leanh::lean_ctor_get(v_wt_2875_, 1);
                crate::leanh::lean_inc(v_nano_2880_);
                crate::leanh::lean_dec_ref(v_wt_2875_);
                v___f_2881_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2881_, 0, v___x_2874_);
                v___x_2882_ = lean_mk_thunk(v___f_2881_);
                v___x_2883_ = lean_int_neg(v_offset_2878_);
                crate::leanh::lean_dec(v_offset_2878_);
                v___x_2884_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
                );
                v___x_2885_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_2886_ = lean_int_mul(v_second_2879_, v___x_2885_);
                crate::leanh::lean_dec(v_second_2879_);
                v___x_2887_ = lean_int_add(v___x_2886_, v_nano_2880_);
                crate::leanh::lean_dec(v_nano_2880_);
                crate::leanh::lean_dec(v___x_2886_);
                v___x_2888_ = lean_int_mul(v___x_2883_, v___x_2885_);
                crate::leanh::lean_dec(v___x_2883_);
                v___x_2889_ = lean_int_add(v___x_2888_, v___x_2884_);
                crate::leanh::lean_dec(v___x_2888_);
                v___x_2890_ = lean_int_add(v___x_2887_, v___x_2889_);
                crate::leanh::lean_dec(v___x_2889_);
                crate::leanh::lean_dec(v___x_2887_);
                v___x_2891_ = l_Std_Time_Duration_ofNanoseconds(v___x_2890_);
                crate::leanh::lean_dec(v___x_2890_);
                if v_isShared_2863_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2862_, 3, v_tz_2877_);
                    crate::leanh::lean_ctor_set(v___x_2862_, 1, v___x_2891_);
                    crate::leanh::lean_ctor_set(v___x_2862_, 0, v___x_2882_);
                    v___x_2893_ = v___x_2862_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2894_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2894_, 0, v___x_2882_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2894_, 1, v___x_2891_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2894_, 2, v_rules_2860_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2894_, 3, v_tz_2877_);
                    v___x_2893_ = v_reuseFailAlloc_2894_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2893_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_ZonedDateTime_addYearsRollOver___boxed(
    mut v_dt_2900_: *mut crate::leanh::LeanObject,
    mut v_years_2901_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2902_ = l_Std_Time_ZonedDateTime_addYearsRollOver(v_dt_2900_, v_years_2901_);
    crate::leanh::lean_dec(v_years_2901_);
    return v_res_2902_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_addYearsClip(
    mut v_dt_2903_: *mut crate::leanh::LeanObject,
    mut v_years_2904_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_2905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rules_2906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2909_: u8 = 0;
    let mut v___x_2910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_2911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_2912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2915_: u8 = 0;
    let mut v___x_2916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_wt_2921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ltt_2922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tz_2923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_2924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_2925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2942_: u8 = 0;
    let mut v_isSharedCheck_2943_: u8 = 0;
    let mut v_unused_2944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_2905_ = crate::leanh::lean_ctor_get(v_dt_2903_, 0);
                v_rules_2906_ = crate::leanh::lean_ctor_get(v_dt_2903_, 2);
                v_isSharedCheck_2943_ = (!crate::leanh::lean_is_exclusive(v_dt_2903_)) as u8;
                if v_isSharedCheck_2943_ == 0 {
                    v_unused_2944_ = crate::leanh::lean_ctor_get(v_dt_2903_, 3);
                    crate::leanh::lean_dec(v_unused_2944_);
                    v_unused_2945_ = crate::leanh::lean_ctor_get(v_dt_2903_, 1);
                    crate::leanh::lean_dec(v_unused_2945_);
                    v___x_2908_ = v_dt_2903_;
                    v_isShared_2909_ = v_isSharedCheck_2943_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_rules_2906_);
                    crate::leanh::lean_inc(v_date_2905_);
                    crate::leanh::lean_dec(v_dt_2903_);
                    v___x_2908_ = crate::leanh::lean_box(0);
                    v_isShared_2909_ = v_isSharedCheck_2943_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2910_ = lean_thunk_get_own(v_date_2905_);
                crate::leanh::lean_dec_ref(v_date_2905_);
                v_date_2911_ = crate::leanh::lean_ctor_get(v___x_2910_, 0);
                v_time_2912_ = crate::leanh::lean_ctor_get(v___x_2910_, 1);
                v_isSharedCheck_2942_ = (!crate::leanh::lean_is_exclusive(v___x_2910_)) as u8;
                if v_isSharedCheck_2942_ == 0 {
                    v___x_2914_ = v___x_2910_;
                    v_isShared_2915_ = v_isSharedCheck_2942_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_time_2912_);
                    crate::leanh::lean_inc(v_date_2911_);
                    crate::leanh::lean_dec(v___x_2910_);
                    v___x_2914_ = crate::leanh::lean_box(0);
                    v_isShared_2915_ = v_isSharedCheck_2942_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2916_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0,
                );
                v___x_2917_ = lean_int_mul(v_years_2904_, v___x_2916_);
                v___x_2918_ = l_Std_Time_PlainDate_addMonthsClip(v_date_2911_, v___x_2917_);
                crate::leanh::lean_dec(v___x_2917_);
                if v_isShared_2915_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2914_, 0, v___x_2918_);
                    v___x_2920_ = v___x_2914_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2941_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2941_, 0, v___x_2918_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2941_, 1, v_time_2912_);
                    v___x_2920_ = v_reuseFailAlloc_2941_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_inc_ref(v___x_2920_);
                v_wt_2921_ = l_Std_Time_PlainDateTime_toWallTime(v___x_2920_);
                crate::leanh::lean_inc_ref(v_rules_2906_);
                v_ltt_2922_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(
                    v_rules_2906_,
                    v_wt_2921_,
                );
                v_tz_2923_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_2922_);
                crate::leanh::lean_dec_ref(v_ltt_2922_);
                v_offset_2924_ = crate::leanh::lean_ctor_get(v_tz_2923_, 0);
                crate::leanh::lean_inc(v_offset_2924_);
                v_second_2925_ = crate::leanh::lean_ctor_get(v_wt_2921_, 0);
                crate::leanh::lean_inc(v_second_2925_);
                v_nano_2926_ = crate::leanh::lean_ctor_get(v_wt_2921_, 1);
                crate::leanh::lean_inc(v_nano_2926_);
                crate::leanh::lean_dec_ref(v_wt_2921_);
                v___f_2927_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2927_, 0, v___x_2920_);
                v___x_2928_ = lean_mk_thunk(v___f_2927_);
                v___x_2929_ = lean_int_neg(v_offset_2924_);
                crate::leanh::lean_dec(v_offset_2924_);
                v___x_2930_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
                );
                v___x_2931_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_2932_ = lean_int_mul(v_second_2925_, v___x_2931_);
                crate::leanh::lean_dec(v_second_2925_);
                v___x_2933_ = lean_int_add(v___x_2932_, v_nano_2926_);
                crate::leanh::lean_dec(v_nano_2926_);
                crate::leanh::lean_dec(v___x_2932_);
                v___x_2934_ = lean_int_mul(v___x_2929_, v___x_2931_);
                crate::leanh::lean_dec(v___x_2929_);
                v___x_2935_ = lean_int_add(v___x_2934_, v___x_2930_);
                crate::leanh::lean_dec(v___x_2934_);
                v___x_2936_ = lean_int_add(v___x_2933_, v___x_2935_);
                crate::leanh::lean_dec(v___x_2935_);
                crate::leanh::lean_dec(v___x_2933_);
                v___x_2937_ = l_Std_Time_Duration_ofNanoseconds(v___x_2936_);
                crate::leanh::lean_dec(v___x_2936_);
                if v_isShared_2909_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2908_, 3, v_tz_2923_);
                    crate::leanh::lean_ctor_set(v___x_2908_, 1, v___x_2937_);
                    crate::leanh::lean_ctor_set(v___x_2908_, 0, v___x_2928_);
                    v___x_2939_ = v___x_2908_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2940_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2940_, 0, v___x_2928_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2940_, 1, v___x_2937_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2940_, 2, v_rules_2906_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2940_, 3, v_tz_2923_);
                    v___x_2939_ = v_reuseFailAlloc_2940_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2939_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_ZonedDateTime_addYearsClip___boxed(
    mut v_dt_2946_: *mut crate::leanh::LeanObject,
    mut v_years_2947_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2948_ = l_Std_Time_ZonedDateTime_addYearsClip(v_dt_2946_, v_years_2947_);
    crate::leanh::lean_dec(v_years_2947_);
    return v_res_2948_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_subYearsClip(
    mut v_dt_2949_: *mut crate::leanh::LeanObject,
    mut v_years_2950_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_2951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rules_2952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2955_: u8 = 0;
    let mut v___x_2956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_2957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_2958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2961_: u8 = 0;
    let mut v___x_2962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_wt_2968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ltt_2969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tz_2970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_2971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_2972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2989_: u8 = 0;
    let mut v_isSharedCheck_2990_: u8 = 0;
    let mut v_unused_2991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_2951_ = crate::leanh::lean_ctor_get(v_dt_2949_, 0);
                v_rules_2952_ = crate::leanh::lean_ctor_get(v_dt_2949_, 2);
                v_isSharedCheck_2990_ = (!crate::leanh::lean_is_exclusive(v_dt_2949_)) as u8;
                if v_isSharedCheck_2990_ == 0 {
                    v_unused_2991_ = crate::leanh::lean_ctor_get(v_dt_2949_, 3);
                    crate::leanh::lean_dec(v_unused_2991_);
                    v_unused_2992_ = crate::leanh::lean_ctor_get(v_dt_2949_, 1);
                    crate::leanh::lean_dec(v_unused_2992_);
                    v___x_2954_ = v_dt_2949_;
                    v_isShared_2955_ = v_isSharedCheck_2990_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_rules_2952_);
                    crate::leanh::lean_inc(v_date_2951_);
                    crate::leanh::lean_dec(v_dt_2949_);
                    v___x_2954_ = crate::leanh::lean_box(0);
                    v_isShared_2955_ = v_isSharedCheck_2990_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2956_ = lean_thunk_get_own(v_date_2951_);
                crate::leanh::lean_dec_ref(v_date_2951_);
                v_date_2957_ = crate::leanh::lean_ctor_get(v___x_2956_, 0);
                v_time_2958_ = crate::leanh::lean_ctor_get(v___x_2956_, 1);
                v_isSharedCheck_2989_ = (!crate::leanh::lean_is_exclusive(v___x_2956_)) as u8;
                if v_isSharedCheck_2989_ == 0 {
                    v___x_2960_ = v___x_2956_;
                    v_isShared_2961_ = v_isSharedCheck_2989_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_time_2958_);
                    crate::leanh::lean_inc(v_date_2957_);
                    crate::leanh::lean_dec(v___x_2956_);
                    v___x_2960_ = crate::leanh::lean_box(0);
                    v_isShared_2961_ = v_isSharedCheck_2989_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2962_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0,
                );
                v___x_2963_ = lean_int_mul(v_years_2950_, v___x_2962_);
                v___x_2964_ = lean_int_neg(v___x_2963_);
                crate::leanh::lean_dec(v___x_2963_);
                v___x_2965_ = l_Std_Time_PlainDate_addMonthsClip(v_date_2957_, v___x_2964_);
                crate::leanh::lean_dec(v___x_2964_);
                if v_isShared_2961_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2960_, 0, v___x_2965_);
                    v___x_2967_ = v___x_2960_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2988_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2988_, 0, v___x_2965_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2988_, 1, v_time_2958_);
                    v___x_2967_ = v_reuseFailAlloc_2988_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_inc_ref(v___x_2967_);
                v_wt_2968_ = l_Std_Time_PlainDateTime_toWallTime(v___x_2967_);
                crate::leanh::lean_inc_ref(v_rules_2952_);
                v_ltt_2969_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(
                    v_rules_2952_,
                    v_wt_2968_,
                );
                v_tz_2970_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_2969_);
                crate::leanh::lean_dec_ref(v_ltt_2969_);
                v_offset_2971_ = crate::leanh::lean_ctor_get(v_tz_2970_, 0);
                crate::leanh::lean_inc(v_offset_2971_);
                v_second_2972_ = crate::leanh::lean_ctor_get(v_wt_2968_, 0);
                crate::leanh::lean_inc(v_second_2972_);
                v_nano_2973_ = crate::leanh::lean_ctor_get(v_wt_2968_, 1);
                crate::leanh::lean_inc(v_nano_2973_);
                crate::leanh::lean_dec_ref(v_wt_2968_);
                v___f_2974_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2974_, 0, v___x_2967_);
                v___x_2975_ = lean_mk_thunk(v___f_2974_);
                v___x_2976_ = lean_int_neg(v_offset_2971_);
                crate::leanh::lean_dec(v_offset_2971_);
                v___x_2977_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
                );
                v___x_2978_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_2979_ = lean_int_mul(v_second_2972_, v___x_2978_);
                crate::leanh::lean_dec(v_second_2972_);
                v___x_2980_ = lean_int_add(v___x_2979_, v_nano_2973_);
                crate::leanh::lean_dec(v_nano_2973_);
                crate::leanh::lean_dec(v___x_2979_);
                v___x_2981_ = lean_int_mul(v___x_2976_, v___x_2978_);
                crate::leanh::lean_dec(v___x_2976_);
                v___x_2982_ = lean_int_add(v___x_2981_, v___x_2977_);
                crate::leanh::lean_dec(v___x_2981_);
                v___x_2983_ = lean_int_add(v___x_2980_, v___x_2982_);
                crate::leanh::lean_dec(v___x_2982_);
                crate::leanh::lean_dec(v___x_2980_);
                v___x_2984_ = l_Std_Time_Duration_ofNanoseconds(v___x_2983_);
                crate::leanh::lean_dec(v___x_2983_);
                if v_isShared_2955_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2954_, 3, v_tz_2970_);
                    crate::leanh::lean_ctor_set(v___x_2954_, 1, v___x_2984_);
                    crate::leanh::lean_ctor_set(v___x_2954_, 0, v___x_2975_);
                    v___x_2986_ = v___x_2954_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2987_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2987_, 0, v___x_2975_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2987_, 1, v___x_2984_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2987_, 2, v_rules_2952_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2987_, 3, v_tz_2970_);
                    v___x_2986_ = v_reuseFailAlloc_2987_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2986_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_ZonedDateTime_subYearsClip___boxed(
    mut v_dt_2993_: *mut crate::leanh::LeanObject,
    mut v_years_2994_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2995_ = l_Std_Time_ZonedDateTime_subYearsClip(v_dt_2993_, v_years_2994_);
    crate::leanh::lean_dec(v_years_2994_);
    return v_res_2995_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_subYearsRollOver(
    mut v_dt_2996_: *mut crate::leanh::LeanObject,
    mut v_years_2997_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_2998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rules_2999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3002_: u8 = 0;
    let mut v___x_3003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_3004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_3005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3008_: u8 = 0;
    let mut v___x_3009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_wt_3015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ltt_3016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tz_3017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_3018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_3020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3036_: u8 = 0;
    let mut v_isSharedCheck_3037_: u8 = 0;
    let mut v_unused_3038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_2998_ = crate::leanh::lean_ctor_get(v_dt_2996_, 0);
                v_rules_2999_ = crate::leanh::lean_ctor_get(v_dt_2996_, 2);
                v_isSharedCheck_3037_ = (!crate::leanh::lean_is_exclusive(v_dt_2996_)) as u8;
                if v_isSharedCheck_3037_ == 0 {
                    v_unused_3038_ = crate::leanh::lean_ctor_get(v_dt_2996_, 3);
                    crate::leanh::lean_dec(v_unused_3038_);
                    v_unused_3039_ = crate::leanh::lean_ctor_get(v_dt_2996_, 1);
                    crate::leanh::lean_dec(v_unused_3039_);
                    v___x_3001_ = v_dt_2996_;
                    v_isShared_3002_ = v_isSharedCheck_3037_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_rules_2999_);
                    crate::leanh::lean_inc(v_date_2998_);
                    crate::leanh::lean_dec(v_dt_2996_);
                    v___x_3001_ = crate::leanh::lean_box(0);
                    v_isShared_3002_ = v_isSharedCheck_3037_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3003_ = lean_thunk_get_own(v_date_2998_);
                crate::leanh::lean_dec_ref(v_date_2998_);
                v_date_3004_ = crate::leanh::lean_ctor_get(v___x_3003_, 0);
                v_time_3005_ = crate::leanh::lean_ctor_get(v___x_3003_, 1);
                v_isSharedCheck_3036_ = (!crate::leanh::lean_is_exclusive(v___x_3003_)) as u8;
                if v_isSharedCheck_3036_ == 0 {
                    v___x_3007_ = v___x_3003_;
                    v_isShared_3008_ = v_isSharedCheck_3036_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_time_3005_);
                    crate::leanh::lean_inc(v_date_3004_);
                    crate::leanh::lean_dec(v___x_3003_);
                    v___x_3007_ = crate::leanh::lean_box(0);
                    v_isShared_3008_ = v_isSharedCheck_3036_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3009_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0,
                );
                v___x_3010_ = lean_int_mul(v_years_2997_, v___x_3009_);
                v___x_3011_ = lean_int_neg(v___x_3010_);
                crate::leanh::lean_dec(v___x_3010_);
                v___x_3012_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_3004_, v___x_3011_);
                crate::leanh::lean_dec(v___x_3011_);
                if v_isShared_3008_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3007_, 0, v___x_3012_);
                    v___x_3014_ = v___x_3007_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3035_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3035_, 0, v___x_3012_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3035_, 1, v_time_3005_);
                    v___x_3014_ = v_reuseFailAlloc_3035_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_inc_ref(v___x_3014_);
                v_wt_3015_ = l_Std_Time_PlainDateTime_toWallTime(v___x_3014_);
                crate::leanh::lean_inc_ref(v_rules_2999_);
                v_ltt_3016_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(
                    v_rules_2999_,
                    v_wt_3015_,
                );
                v_tz_3017_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_3016_);
                crate::leanh::lean_dec_ref(v_ltt_3016_);
                v_offset_3018_ = crate::leanh::lean_ctor_get(v_tz_3017_, 0);
                crate::leanh::lean_inc(v_offset_3018_);
                v_second_3019_ = crate::leanh::lean_ctor_get(v_wt_3015_, 0);
                crate::leanh::lean_inc(v_second_3019_);
                v_nano_3020_ = crate::leanh::lean_ctor_get(v_wt_3015_, 1);
                crate::leanh::lean_inc(v_nano_3020_);
                crate::leanh::lean_dec_ref(v_wt_3015_);
                v___f_3021_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3021_, 0, v___x_3014_);
                v___x_3022_ = lean_mk_thunk(v___f_3021_);
                v___x_3023_ = lean_int_neg(v_offset_3018_);
                crate::leanh::lean_dec(v_offset_3018_);
                v___x_3024_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
                );
                v___x_3025_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3026_ = lean_int_mul(v_second_3019_, v___x_3025_);
                crate::leanh::lean_dec(v_second_3019_);
                v___x_3027_ = lean_int_add(v___x_3026_, v_nano_3020_);
                crate::leanh::lean_dec(v_nano_3020_);
                crate::leanh::lean_dec(v___x_3026_);
                v___x_3028_ = lean_int_mul(v___x_3023_, v___x_3025_);
                crate::leanh::lean_dec(v___x_3023_);
                v___x_3029_ = lean_int_add(v___x_3028_, v___x_3024_);
                crate::leanh::lean_dec(v___x_3028_);
                v___x_3030_ = lean_int_add(v___x_3027_, v___x_3029_);
                crate::leanh::lean_dec(v___x_3029_);
                crate::leanh::lean_dec(v___x_3027_);
                v___x_3031_ = l_Std_Time_Duration_ofNanoseconds(v___x_3030_);
                crate::leanh::lean_dec(v___x_3030_);
                if v_isShared_3002_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3001_, 3, v_tz_3017_);
                    crate::leanh::lean_ctor_set(v___x_3001_, 1, v___x_3031_);
                    crate::leanh::lean_ctor_set(v___x_3001_, 0, v___x_3022_);
                    v___x_3033_ = v___x_3001_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3034_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3034_, 0, v___x_3022_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3034_, 1, v___x_3031_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3034_, 2, v_rules_2999_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3034_, 3, v_tz_3017_);
                    v___x_3033_ = v_reuseFailAlloc_3034_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3033_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_ZonedDateTime_subYearsRollOver___boxed(
    mut v_dt_3040_: *mut crate::leanh::LeanObject,
    mut v_years_3041_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3042_ = l_Std_Time_ZonedDateTime_subYearsRollOver(v_dt_3040_, v_years_3041_);
    crate::leanh::lean_dec(v_years_3041_);
    return v_res_3042_;
}
pub unsafe fn _init_l_Std_Time_ZonedDateTime_addHours___closed__0() -> *mut crate::leanh::LeanObject
{
    let mut v___x_3043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3043_ = crate::leanh::lean_unsigned_to_nat(3600);
    v___x_3044_ = lean_nat_to_int(v___x_3043_);
    return v___x_3044_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_addHours(
    mut v_dt_3045_: *mut crate::leanh::LeanObject,
    mut v_hours_3046_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_timestamp_3047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rules_3048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3051_: u8 = 0;
    let mut v_second_3052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_3053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initialLocalTimeType_3054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_transitions_3055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3076_: u8 = 0;
    let mut v_unused_3077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_3047_ = crate::leanh::lean_ctor_get(v_dt_3045_, 1);
                v_rules_3048_ = crate::leanh::lean_ctor_get(v_dt_3045_, 2);
                v_isSharedCheck_3076_ = (!crate::leanh::lean_is_exclusive(v_dt_3045_)) as u8;
                if v_isSharedCheck_3076_ == 0 {
                    v_unused_3077_ = crate::leanh::lean_ctor_get(v_dt_3045_, 3);
                    crate::leanh::lean_dec(v_unused_3077_);
                    v_unused_3078_ = crate::leanh::lean_ctor_get(v_dt_3045_, 0);
                    crate::leanh::lean_dec(v_unused_3078_);
                    v___x_3050_ = v_dt_3045_;
                    v_isShared_3051_ = v_isSharedCheck_3076_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_rules_3048_);
                    crate::leanh::lean_inc(v_timestamp_3047_);
                    crate::leanh::lean_dec(v_dt_3045_);
                    v___x_3050_ = crate::leanh::lean_box(0);
                    v_isShared_3051_ = v_isSharedCheck_3076_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_second_3052_ = crate::leanh::lean_ctor_get(v_timestamp_3047_, 0);
                crate::leanh::lean_inc(v_second_3052_);
                v_nano_3053_ = crate::leanh::lean_ctor_get(v_timestamp_3047_, 1);
                crate::leanh::lean_inc(v_nano_3053_);
                crate::leanh::lean_dec_ref(v_timestamp_3047_);
                v_initialLocalTimeType_3054_ = crate::leanh::lean_ctor_get(v_rules_3048_, 0);
                v_transitions_3055_ = crate::leanh::lean_ctor_get(v_rules_3048_, 1);
                v___x_3056_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_addHours___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_addHours___closed__0_once),
                    _init_l_Std_Time_ZonedDateTime_addHours___closed__0,
                );
                v___x_3057_ = lean_int_mul(v_hours_3046_, v___x_3056_);
                v___x_3058_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0,
                );
                v___x_3059_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3060_ = lean_int_mul(v_second_3052_, v___x_3059_);
                crate::leanh::lean_dec(v_second_3052_);
                v___x_3061_ = lean_int_add(v___x_3060_, v_nano_3053_);
                crate::leanh::lean_dec(v_nano_3053_);
                crate::leanh::lean_dec(v___x_3060_);
                v___x_3062_ = lean_int_mul(v___x_3057_, v___x_3059_);
                crate::leanh::lean_dec(v___x_3057_);
                v___x_3063_ = lean_int_add(v___x_3062_, v___x_3058_);
                crate::leanh::lean_dec(v___x_3062_);
                v___x_3064_ = lean_int_add(v___x_3061_, v___x_3063_);
                crate::leanh::lean_dec(v___x_3063_);
                crate::leanh::lean_dec(v___x_3061_);
                v___x_3065_ = l_Std_Time_Duration_ofNanoseconds(v___x_3064_);
                crate::leanh::lean_dec(v___x_3064_);
                v___x_3073_ =
                    l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_3055_, v___x_3065_);
                if crate::leanh::lean_obj_tag(v___x_3073_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_3073_, 1);
                    v___x_3074_ =
                        l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_3054_);
                    v___y_3067_ = v___x_3074_;
                    state = 2;
                    continue;
                } else {
                    v_a_3075_ = crate::leanh::lean_ctor_get(v___x_3073_, 0);
                    crate::leanh::lean_inc(v_a_3075_);
                    crate::leanh::lean_dec_ref_known(v___x_3073_, 1);
                    v___y_3067_ = v_a_3075_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc_ref(v___x_3065_);
                crate::leanh::lean_inc_ref(v___y_3067_);
                v___f_3068_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addDays___lam__0___boxed as *mut core::ffi::c_void,
                    5,
                    4,
                );
                crate::leanh::lean_closure_set(v___f_3068_, 0, v___y_3067_);
                crate::leanh::lean_closure_set(v___f_3068_, 1, v___x_3065_);
                crate::leanh::lean_closure_set(v___f_3068_, 2, v___x_3059_);
                crate::leanh::lean_closure_set(v___f_3068_, 3, v___x_3058_);
                v___x_3069_ = lean_mk_thunk(v___f_3068_);
                if v_isShared_3051_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3050_, 3, v___y_3067_);
                    crate::leanh::lean_ctor_set(v___x_3050_, 1, v___x_3065_);
                    crate::leanh::lean_ctor_set(v___x_3050_, 0, v___x_3069_);
                    v___x_3071_ = v___x_3050_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3072_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3072_, 0, v___x_3069_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3072_, 1, v___x_3065_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3072_, 2, v_rules_3048_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3072_, 3, v___y_3067_);
                    v___x_3071_ = v_reuseFailAlloc_3072_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3071_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_ZonedDateTime_addHours___boxed(
    mut v_dt_3079_: *mut crate::leanh::LeanObject,
    mut v_hours_3080_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3081_ = l_Std_Time_ZonedDateTime_addHours(v_dt_3079_, v_hours_3080_);
    crate::leanh::lean_dec(v_hours_3080_);
    return v_res_3081_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_subHours(
    mut v_dt_3082_: *mut crate::leanh::LeanObject,
    mut v_hours_3083_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_timestamp_3084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rules_3085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3088_: u8 = 0;
    let mut v_second_3089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_3090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initialLocalTimeType_3091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_transitions_3092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3115_: u8 = 0;
    let mut v_unused_3116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_3084_ = crate::leanh::lean_ctor_get(v_dt_3082_, 1);
                v_rules_3085_ = crate::leanh::lean_ctor_get(v_dt_3082_, 2);
                v_isSharedCheck_3115_ = (!crate::leanh::lean_is_exclusive(v_dt_3082_)) as u8;
                if v_isSharedCheck_3115_ == 0 {
                    v_unused_3116_ = crate::leanh::lean_ctor_get(v_dt_3082_, 3);
                    crate::leanh::lean_dec(v_unused_3116_);
                    v_unused_3117_ = crate::leanh::lean_ctor_get(v_dt_3082_, 0);
                    crate::leanh::lean_dec(v_unused_3117_);
                    v___x_3087_ = v_dt_3082_;
                    v_isShared_3088_ = v_isSharedCheck_3115_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_rules_3085_);
                    crate::leanh::lean_inc(v_timestamp_3084_);
                    crate::leanh::lean_dec(v_dt_3082_);
                    v___x_3087_ = crate::leanh::lean_box(0);
                    v_isShared_3088_ = v_isSharedCheck_3115_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_second_3089_ = crate::leanh::lean_ctor_get(v_timestamp_3084_, 0);
                crate::leanh::lean_inc(v_second_3089_);
                v_nano_3090_ = crate::leanh::lean_ctor_get(v_timestamp_3084_, 1);
                crate::leanh::lean_inc(v_nano_3090_);
                crate::leanh::lean_dec_ref(v_timestamp_3084_);
                v_initialLocalTimeType_3091_ = crate::leanh::lean_ctor_get(v_rules_3085_, 0);
                v_transitions_3092_ = crate::leanh::lean_ctor_get(v_rules_3085_, 1);
                v___x_3093_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_addHours___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_addHours___closed__0_once),
                    _init_l_Std_Time_ZonedDateTime_addHours___closed__0,
                );
                v___x_3094_ = lean_int_mul(v_hours_3083_, v___x_3093_);
                v___x_3095_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0,
                );
                v___x_3096_ = lean_int_neg(v___x_3094_);
                crate::leanh::lean_dec(v___x_3094_);
                v___x_3097_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
                );
                v___x_3098_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3099_ = lean_int_mul(v_second_3089_, v___x_3098_);
                crate::leanh::lean_dec(v_second_3089_);
                v___x_3100_ = lean_int_add(v___x_3099_, v_nano_3090_);
                crate::leanh::lean_dec(v_nano_3090_);
                crate::leanh::lean_dec(v___x_3099_);
                v___x_3101_ = lean_int_mul(v___x_3096_, v___x_3098_);
                crate::leanh::lean_dec(v___x_3096_);
                v___x_3102_ = lean_int_add(v___x_3101_, v___x_3097_);
                crate::leanh::lean_dec(v___x_3101_);
                v___x_3103_ = lean_int_add(v___x_3100_, v___x_3102_);
                crate::leanh::lean_dec(v___x_3102_);
                crate::leanh::lean_dec(v___x_3100_);
                v___x_3104_ = l_Std_Time_Duration_ofNanoseconds(v___x_3103_);
                crate::leanh::lean_dec(v___x_3103_);
                v___x_3112_ =
                    l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_3092_, v___x_3104_);
                if crate::leanh::lean_obj_tag(v___x_3112_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_3112_, 1);
                    v___x_3113_ =
                        l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_3091_);
                    v___y_3106_ = v___x_3113_;
                    state = 2;
                    continue;
                } else {
                    v_a_3114_ = crate::leanh::lean_ctor_get(v___x_3112_, 0);
                    crate::leanh::lean_inc(v_a_3114_);
                    crate::leanh::lean_dec_ref_known(v___x_3112_, 1);
                    v___y_3106_ = v_a_3114_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc_ref(v___x_3104_);
                crate::leanh::lean_inc_ref(v___y_3106_);
                v___f_3107_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addDays___lam__0___boxed as *mut core::ffi::c_void,
                    5,
                    4,
                );
                crate::leanh::lean_closure_set(v___f_3107_, 0, v___y_3106_);
                crate::leanh::lean_closure_set(v___f_3107_, 1, v___x_3104_);
                crate::leanh::lean_closure_set(v___f_3107_, 2, v___x_3098_);
                crate::leanh::lean_closure_set(v___f_3107_, 3, v___x_3095_);
                v___x_3108_ = lean_mk_thunk(v___f_3107_);
                if v_isShared_3088_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3087_, 3, v___y_3106_);
                    crate::leanh::lean_ctor_set(v___x_3087_, 1, v___x_3104_);
                    crate::leanh::lean_ctor_set(v___x_3087_, 0, v___x_3108_);
                    v___x_3110_ = v___x_3087_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3111_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3111_, 0, v___x_3108_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3111_, 1, v___x_3104_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3111_, 2, v_rules_3085_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3111_, 3, v___y_3106_);
                    v___x_3110_ = v_reuseFailAlloc_3111_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3110_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_ZonedDateTime_subHours___boxed(
    mut v_dt_3118_: *mut crate::leanh::LeanObject,
    mut v_hours_3119_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3120_ = l_Std_Time_ZonedDateTime_subHours(v_dt_3118_, v_hours_3119_);
    crate::leanh::lean_dec(v_hours_3119_);
    return v_res_3120_;
}
pub unsafe fn _init_l_Std_Time_ZonedDateTime_addMinutes___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3121_ = crate::leanh::lean_unsigned_to_nat(60);
    v___x_3122_ = lean_nat_to_int(v___x_3121_);
    return v___x_3122_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_addMinutes(
    mut v_dt_3123_: *mut crate::leanh::LeanObject,
    mut v_minutes_3124_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_timestamp_3125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rules_3126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3129_: u8 = 0;
    let mut v_second_3130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_3131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initialLocalTimeType_3132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_transitions_3133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3154_: u8 = 0;
    let mut v_unused_3155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_3125_ = crate::leanh::lean_ctor_get(v_dt_3123_, 1);
                v_rules_3126_ = crate::leanh::lean_ctor_get(v_dt_3123_, 2);
                v_isSharedCheck_3154_ = (!crate::leanh::lean_is_exclusive(v_dt_3123_)) as u8;
                if v_isSharedCheck_3154_ == 0 {
                    v_unused_3155_ = crate::leanh::lean_ctor_get(v_dt_3123_, 3);
                    crate::leanh::lean_dec(v_unused_3155_);
                    v_unused_3156_ = crate::leanh::lean_ctor_get(v_dt_3123_, 0);
                    crate::leanh::lean_dec(v_unused_3156_);
                    v___x_3128_ = v_dt_3123_;
                    v_isShared_3129_ = v_isSharedCheck_3154_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_rules_3126_);
                    crate::leanh::lean_inc(v_timestamp_3125_);
                    crate::leanh::lean_dec(v_dt_3123_);
                    v___x_3128_ = crate::leanh::lean_box(0);
                    v_isShared_3129_ = v_isSharedCheck_3154_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_second_3130_ = crate::leanh::lean_ctor_get(v_timestamp_3125_, 0);
                crate::leanh::lean_inc(v_second_3130_);
                v_nano_3131_ = crate::leanh::lean_ctor_get(v_timestamp_3125_, 1);
                crate::leanh::lean_inc(v_nano_3131_);
                crate::leanh::lean_dec_ref(v_timestamp_3125_);
                v_initialLocalTimeType_3132_ = crate::leanh::lean_ctor_get(v_rules_3126_, 0);
                v_transitions_3133_ = crate::leanh::lean_ctor_get(v_rules_3126_, 1);
                v___x_3134_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_addMinutes___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_addMinutes___closed__0_once),
                    _init_l_Std_Time_ZonedDateTime_addMinutes___closed__0,
                );
                v___x_3135_ = lean_int_mul(v_minutes_3124_, v___x_3134_);
                v___x_3136_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0,
                );
                v___x_3137_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3138_ = lean_int_mul(v_second_3130_, v___x_3137_);
                crate::leanh::lean_dec(v_second_3130_);
                v___x_3139_ = lean_int_add(v___x_3138_, v_nano_3131_);
                crate::leanh::lean_dec(v_nano_3131_);
                crate::leanh::lean_dec(v___x_3138_);
                v___x_3140_ = lean_int_mul(v___x_3135_, v___x_3137_);
                crate::leanh::lean_dec(v___x_3135_);
                v___x_3141_ = lean_int_add(v___x_3140_, v___x_3136_);
                crate::leanh::lean_dec(v___x_3140_);
                v___x_3142_ = lean_int_add(v___x_3139_, v___x_3141_);
                crate::leanh::lean_dec(v___x_3141_);
                crate::leanh::lean_dec(v___x_3139_);
                v___x_3143_ = l_Std_Time_Duration_ofNanoseconds(v___x_3142_);
                crate::leanh::lean_dec(v___x_3142_);
                v___x_3151_ =
                    l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_3133_, v___x_3143_);
                if crate::leanh::lean_obj_tag(v___x_3151_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_3151_, 1);
                    v___x_3152_ =
                        l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_3132_);
                    v___y_3145_ = v___x_3152_;
                    state = 2;
                    continue;
                } else {
                    v_a_3153_ = crate::leanh::lean_ctor_get(v___x_3151_, 0);
                    crate::leanh::lean_inc(v_a_3153_);
                    crate::leanh::lean_dec_ref_known(v___x_3151_, 1);
                    v___y_3145_ = v_a_3153_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc_ref(v___x_3143_);
                crate::leanh::lean_inc_ref(v___y_3145_);
                v___f_3146_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addDays___lam__0___boxed as *mut core::ffi::c_void,
                    5,
                    4,
                );
                crate::leanh::lean_closure_set(v___f_3146_, 0, v___y_3145_);
                crate::leanh::lean_closure_set(v___f_3146_, 1, v___x_3143_);
                crate::leanh::lean_closure_set(v___f_3146_, 2, v___x_3137_);
                crate::leanh::lean_closure_set(v___f_3146_, 3, v___x_3136_);
                v___x_3147_ = lean_mk_thunk(v___f_3146_);
                if v_isShared_3129_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3128_, 3, v___y_3145_);
                    crate::leanh::lean_ctor_set(v___x_3128_, 1, v___x_3143_);
                    crate::leanh::lean_ctor_set(v___x_3128_, 0, v___x_3147_);
                    v___x_3149_ = v___x_3128_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3150_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3150_, 0, v___x_3147_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3150_, 1, v___x_3143_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3150_, 2, v_rules_3126_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3150_, 3, v___y_3145_);
                    v___x_3149_ = v_reuseFailAlloc_3150_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3149_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_ZonedDateTime_addMinutes___boxed(
    mut v_dt_3157_: *mut crate::leanh::LeanObject,
    mut v_minutes_3158_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3159_ = l_Std_Time_ZonedDateTime_addMinutes(v_dt_3157_, v_minutes_3158_);
    crate::leanh::lean_dec(v_minutes_3158_);
    return v_res_3159_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_subMinutes(
    mut v_dt_3160_: *mut crate::leanh::LeanObject,
    mut v_minutes_3161_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_timestamp_3162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rules_3163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3166_: u8 = 0;
    let mut v_second_3167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_3168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initialLocalTimeType_3169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_transitions_3170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3193_: u8 = 0;
    let mut v_unused_3194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_3162_ = crate::leanh::lean_ctor_get(v_dt_3160_, 1);
                v_rules_3163_ = crate::leanh::lean_ctor_get(v_dt_3160_, 2);
                v_isSharedCheck_3193_ = (!crate::leanh::lean_is_exclusive(v_dt_3160_)) as u8;
                if v_isSharedCheck_3193_ == 0 {
                    v_unused_3194_ = crate::leanh::lean_ctor_get(v_dt_3160_, 3);
                    crate::leanh::lean_dec(v_unused_3194_);
                    v_unused_3195_ = crate::leanh::lean_ctor_get(v_dt_3160_, 0);
                    crate::leanh::lean_dec(v_unused_3195_);
                    v___x_3165_ = v_dt_3160_;
                    v_isShared_3166_ = v_isSharedCheck_3193_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_rules_3163_);
                    crate::leanh::lean_inc(v_timestamp_3162_);
                    crate::leanh::lean_dec(v_dt_3160_);
                    v___x_3165_ = crate::leanh::lean_box(0);
                    v_isShared_3166_ = v_isSharedCheck_3193_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_second_3167_ = crate::leanh::lean_ctor_get(v_timestamp_3162_, 0);
                crate::leanh::lean_inc(v_second_3167_);
                v_nano_3168_ = crate::leanh::lean_ctor_get(v_timestamp_3162_, 1);
                crate::leanh::lean_inc(v_nano_3168_);
                crate::leanh::lean_dec_ref(v_timestamp_3162_);
                v_initialLocalTimeType_3169_ = crate::leanh::lean_ctor_get(v_rules_3163_, 0);
                v_transitions_3170_ = crate::leanh::lean_ctor_get(v_rules_3163_, 1);
                v___x_3171_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_addMinutes___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_addMinutes___closed__0_once),
                    _init_l_Std_Time_ZonedDateTime_addMinutes___closed__0,
                );
                v___x_3172_ = lean_int_mul(v_minutes_3161_, v___x_3171_);
                v___x_3173_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0,
                );
                v___x_3174_ = lean_int_neg(v___x_3172_);
                crate::leanh::lean_dec(v___x_3172_);
                v___x_3175_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
                );
                v___x_3176_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3177_ = lean_int_mul(v_second_3167_, v___x_3176_);
                crate::leanh::lean_dec(v_second_3167_);
                v___x_3178_ = lean_int_add(v___x_3177_, v_nano_3168_);
                crate::leanh::lean_dec(v_nano_3168_);
                crate::leanh::lean_dec(v___x_3177_);
                v___x_3179_ = lean_int_mul(v___x_3174_, v___x_3176_);
                crate::leanh::lean_dec(v___x_3174_);
                v___x_3180_ = lean_int_add(v___x_3179_, v___x_3175_);
                crate::leanh::lean_dec(v___x_3179_);
                v___x_3181_ = lean_int_add(v___x_3178_, v___x_3180_);
                crate::leanh::lean_dec(v___x_3180_);
                crate::leanh::lean_dec(v___x_3178_);
                v___x_3182_ = l_Std_Time_Duration_ofNanoseconds(v___x_3181_);
                crate::leanh::lean_dec(v___x_3181_);
                v___x_3190_ =
                    l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_3170_, v___x_3182_);
                if crate::leanh::lean_obj_tag(v___x_3190_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_3190_, 1);
                    v___x_3191_ =
                        l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_3169_);
                    v___y_3184_ = v___x_3191_;
                    state = 2;
                    continue;
                } else {
                    v_a_3192_ = crate::leanh::lean_ctor_get(v___x_3190_, 0);
                    crate::leanh::lean_inc(v_a_3192_);
                    crate::leanh::lean_dec_ref_known(v___x_3190_, 1);
                    v___y_3184_ = v_a_3192_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc_ref(v___x_3182_);
                crate::leanh::lean_inc_ref(v___y_3184_);
                v___f_3185_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addDays___lam__0___boxed as *mut core::ffi::c_void,
                    5,
                    4,
                );
                crate::leanh::lean_closure_set(v___f_3185_, 0, v___y_3184_);
                crate::leanh::lean_closure_set(v___f_3185_, 1, v___x_3182_);
                crate::leanh::lean_closure_set(v___f_3185_, 2, v___x_3176_);
                crate::leanh::lean_closure_set(v___f_3185_, 3, v___x_3173_);
                v___x_3186_ = lean_mk_thunk(v___f_3185_);
                if v_isShared_3166_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3165_, 3, v___y_3184_);
                    crate::leanh::lean_ctor_set(v___x_3165_, 1, v___x_3182_);
                    crate::leanh::lean_ctor_set(v___x_3165_, 0, v___x_3186_);
                    v___x_3188_ = v___x_3165_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3189_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3189_, 0, v___x_3186_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3189_, 1, v___x_3182_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3189_, 2, v_rules_3163_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3189_, 3, v___y_3184_);
                    v___x_3188_ = v_reuseFailAlloc_3189_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3188_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_ZonedDateTime_subMinutes___boxed(
    mut v_dt_3196_: *mut crate::leanh::LeanObject,
    mut v_minutes_3197_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3198_ = l_Std_Time_ZonedDateTime_subMinutes(v_dt_3196_, v_minutes_3197_);
    crate::leanh::lean_dec(v_minutes_3197_);
    return v_res_3198_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_addMilliseconds___lam__0(
    mut v___y_3199_: *mut crate::leanh::LeanObject,
    mut v___x_3200_: *mut crate::leanh::LeanObject,
    mut v___x_3201_: *mut crate::leanh::LeanObject,
    mut v_x_3202_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_offset_3203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_3205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_offset_3203_ = crate::leanh::lean_ctor_get(v___y_3199_, 0);
    v_second_3204_ = crate::leanh::lean_ctor_get(v___x_3200_, 0);
    v_nano_3205_ = crate::leanh::lean_ctor_get(v___x_3200_, 1);
    v___x_3206_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once),
        _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0,
    );
    v___x_3207_ = lean_int_mul(v_second_3204_, v___x_3201_);
    v___x_3208_ = lean_int_add(v___x_3207_, v_nano_3205_);
    crate::leanh::lean_dec(v___x_3207_);
    v___x_3209_ = lean_int_mul(v_offset_3203_, v___x_3201_);
    v___x_3210_ = lean_int_add(v___x_3209_, v___x_3206_);
    crate::leanh::lean_dec(v___x_3209_);
    v___x_3211_ = lean_int_add(v___x_3208_, v___x_3210_);
    crate::leanh::lean_dec(v___x_3210_);
    crate::leanh::lean_dec(v___x_3208_);
    v___x_3212_ = l_Std_Time_Duration_ofNanoseconds(v___x_3211_);
    crate::leanh::lean_dec(v___x_3211_);
    v___x_3213_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_3212_);
    return v___x_3213_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_addMilliseconds___lam__0___boxed(
    mut v___y_3214_: *mut crate::leanh::LeanObject,
    mut v___x_3215_: *mut crate::leanh::LeanObject,
    mut v___x_3216_: *mut crate::leanh::LeanObject,
    mut v_x_3217_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3218_ = l_Std_Time_ZonedDateTime_addMilliseconds___lam__0(
        v___y_3214_,
        v___x_3215_,
        v___x_3216_,
        v_x_3217_,
    );
    crate::leanh::lean_dec(v___x_3216_);
    crate::leanh::lean_dec_ref(v___x_3215_);
    crate::leanh::lean_dec_ref(v___y_3214_);
    return v_res_3218_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_addMilliseconds(
    mut v_dt_3219_: *mut crate::leanh::LeanObject,
    mut v_milliseconds_3220_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_timestamp_3221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rules_3222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3225_: u8 = 0;
    let mut v_second_3226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_3227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_3232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initialLocalTimeType_3233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_transitions_3234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3252_: u8 = 0;
    let mut v_unused_3253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_3221_ = crate::leanh::lean_ctor_get(v_dt_3219_, 1);
                v_rules_3222_ = crate::leanh::lean_ctor_get(v_dt_3219_, 2);
                v_isSharedCheck_3252_ = (!crate::leanh::lean_is_exclusive(v_dt_3219_)) as u8;
                if v_isSharedCheck_3252_ == 0 {
                    v_unused_3253_ = crate::leanh::lean_ctor_get(v_dt_3219_, 3);
                    crate::leanh::lean_dec(v_unused_3253_);
                    v_unused_3254_ = crate::leanh::lean_ctor_get(v_dt_3219_, 0);
                    crate::leanh::lean_dec(v_unused_3254_);
                    v___x_3224_ = v_dt_3219_;
                    v_isShared_3225_ = v_isSharedCheck_3252_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_rules_3222_);
                    crate::leanh::lean_inc(v_timestamp_3221_);
                    crate::leanh::lean_dec(v_dt_3219_);
                    v___x_3224_ = crate::leanh::lean_box(0);
                    v_isShared_3225_ = v_isSharedCheck_3252_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_second_3226_ = crate::leanh::lean_ctor_get(v_timestamp_3221_, 0);
                crate::leanh::lean_inc(v_second_3226_);
                v_nano_3227_ = crate::leanh::lean_ctor_get(v_timestamp_3221_, 1);
                crate::leanh::lean_inc(v_nano_3227_);
                crate::leanh::lean_dec_ref(v_timestamp_3221_);
                v___x_3228_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_millisecond___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_millisecond___closed__0_once),
                    _init_l_Std_Time_ZonedDateTime_millisecond___closed__0,
                );
                v___x_3229_ = lean_int_mul(v_milliseconds_3220_, v___x_3228_);
                v___x_3230_ = l_Std_Time_Duration_ofNanoseconds(v___x_3229_);
                crate::leanh::lean_dec(v___x_3229_);
                v_second_3231_ = crate::leanh::lean_ctor_get(v___x_3230_, 0);
                crate::leanh::lean_inc(v_second_3231_);
                v_nano_3232_ = crate::leanh::lean_ctor_get(v___x_3230_, 1);
                crate::leanh::lean_inc(v_nano_3232_);
                crate::leanh::lean_dec_ref(v___x_3230_);
                v_initialLocalTimeType_3233_ = crate::leanh::lean_ctor_get(v_rules_3222_, 0);
                v_transitions_3234_ = crate::leanh::lean_ctor_get(v_rules_3222_, 1);
                v___x_3235_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3236_ = lean_int_mul(v_second_3226_, v___x_3235_);
                crate::leanh::lean_dec(v_second_3226_);
                v___x_3237_ = lean_int_add(v___x_3236_, v_nano_3227_);
                crate::leanh::lean_dec(v_nano_3227_);
                crate::leanh::lean_dec(v___x_3236_);
                v___x_3238_ = lean_int_mul(v_second_3231_, v___x_3235_);
                crate::leanh::lean_dec(v_second_3231_);
                v___x_3239_ = lean_int_add(v___x_3238_, v_nano_3232_);
                crate::leanh::lean_dec(v_nano_3232_);
                crate::leanh::lean_dec(v___x_3238_);
                v___x_3240_ = lean_int_add(v___x_3237_, v___x_3239_);
                crate::leanh::lean_dec(v___x_3239_);
                crate::leanh::lean_dec(v___x_3237_);
                v___x_3241_ = l_Std_Time_Duration_ofNanoseconds(v___x_3240_);
                crate::leanh::lean_dec(v___x_3240_);
                v___x_3249_ =
                    l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_3234_, v___x_3241_);
                if crate::leanh::lean_obj_tag(v___x_3249_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_3249_, 1);
                    v___x_3250_ =
                        l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_3233_);
                    v___y_3243_ = v___x_3250_;
                    state = 2;
                    continue;
                } else {
                    v_a_3251_ = crate::leanh::lean_ctor_get(v___x_3249_, 0);
                    crate::leanh::lean_inc(v_a_3251_);
                    crate::leanh::lean_dec_ref_known(v___x_3249_, 1);
                    v___y_3243_ = v_a_3251_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc_ref(v___x_3241_);
                crate::leanh::lean_inc_ref(v___y_3243_);
                v___f_3244_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addMilliseconds___lam__0___boxed
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_3244_, 0, v___y_3243_);
                crate::leanh::lean_closure_set(v___f_3244_, 1, v___x_3241_);
                crate::leanh::lean_closure_set(v___f_3244_, 2, v___x_3235_);
                v___x_3245_ = lean_mk_thunk(v___f_3244_);
                if v_isShared_3225_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3224_, 3, v___y_3243_);
                    crate::leanh::lean_ctor_set(v___x_3224_, 1, v___x_3241_);
                    crate::leanh::lean_ctor_set(v___x_3224_, 0, v___x_3245_);
                    v___x_3247_ = v___x_3224_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3248_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3248_, 0, v___x_3245_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3248_, 1, v___x_3241_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3248_, 2, v_rules_3222_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3248_, 3, v___y_3243_);
                    v___x_3247_ = v_reuseFailAlloc_3248_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3247_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_ZonedDateTime_addMilliseconds___boxed(
    mut v_dt_3255_: *mut crate::leanh::LeanObject,
    mut v_milliseconds_3256_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3257_ = l_Std_Time_ZonedDateTime_addMilliseconds(v_dt_3255_, v_milliseconds_3256_);
    crate::leanh::lean_dec(v_milliseconds_3256_);
    return v_res_3257_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_subMilliseconds(
    mut v_dt_3258_: *mut crate::leanh::LeanObject,
    mut v_milliseconds_3259_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_timestamp_3260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rules_3261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3264_: u8 = 0;
    let mut v___x_3265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_3269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_3271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initialLocalTimeType_3272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_transitions_3273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3293_: u8 = 0;
    let mut v_unused_3294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_3260_ = crate::leanh::lean_ctor_get(v_dt_3258_, 1);
                v_rules_3261_ = crate::leanh::lean_ctor_get(v_dt_3258_, 2);
                v_isSharedCheck_3293_ = (!crate::leanh::lean_is_exclusive(v_dt_3258_)) as u8;
                if v_isSharedCheck_3293_ == 0 {
                    v_unused_3294_ = crate::leanh::lean_ctor_get(v_dt_3258_, 3);
                    crate::leanh::lean_dec(v_unused_3294_);
                    v_unused_3295_ = crate::leanh::lean_ctor_get(v_dt_3258_, 0);
                    crate::leanh::lean_dec(v_unused_3295_);
                    v___x_3263_ = v_dt_3258_;
                    v_isShared_3264_ = v_isSharedCheck_3293_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_rules_3261_);
                    crate::leanh::lean_inc(v_timestamp_3260_);
                    crate::leanh::lean_dec(v_dt_3258_);
                    v___x_3263_ = crate::leanh::lean_box(0);
                    v_isShared_3264_ = v_isSharedCheck_3293_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3265_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_millisecond___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_millisecond___closed__0_once),
                    _init_l_Std_Time_ZonedDateTime_millisecond___closed__0,
                );
                v___x_3266_ = lean_int_mul(v_milliseconds_3259_, v___x_3265_);
                v___x_3267_ = l_Std_Time_Duration_ofNanoseconds(v___x_3266_);
                crate::leanh::lean_dec(v___x_3266_);
                v_second_3268_ = crate::leanh::lean_ctor_get(v___x_3267_, 0);
                crate::leanh::lean_inc(v_second_3268_);
                v_nano_3269_ = crate::leanh::lean_ctor_get(v___x_3267_, 1);
                crate::leanh::lean_inc(v_nano_3269_);
                crate::leanh::lean_dec_ref(v___x_3267_);
                v_second_3270_ = crate::leanh::lean_ctor_get(v_timestamp_3260_, 0);
                crate::leanh::lean_inc(v_second_3270_);
                v_nano_3271_ = crate::leanh::lean_ctor_get(v_timestamp_3260_, 1);
                crate::leanh::lean_inc(v_nano_3271_);
                crate::leanh::lean_dec_ref(v_timestamp_3260_);
                v_initialLocalTimeType_3272_ = crate::leanh::lean_ctor_get(v_rules_3261_, 0);
                v_transitions_3273_ = crate::leanh::lean_ctor_get(v_rules_3261_, 1);
                v___x_3274_ = lean_int_neg(v_second_3268_);
                crate::leanh::lean_dec(v_second_3268_);
                v___x_3275_ = lean_int_neg(v_nano_3269_);
                crate::leanh::lean_dec(v_nano_3269_);
                v___x_3276_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3277_ = lean_int_mul(v_second_3270_, v___x_3276_);
                crate::leanh::lean_dec(v_second_3270_);
                v___x_3278_ = lean_int_add(v___x_3277_, v_nano_3271_);
                crate::leanh::lean_dec(v_nano_3271_);
                crate::leanh::lean_dec(v___x_3277_);
                v___x_3279_ = lean_int_mul(v___x_3274_, v___x_3276_);
                crate::leanh::lean_dec(v___x_3274_);
                v___x_3280_ = lean_int_add(v___x_3279_, v___x_3275_);
                crate::leanh::lean_dec(v___x_3275_);
                crate::leanh::lean_dec(v___x_3279_);
                v___x_3281_ = lean_int_add(v___x_3278_, v___x_3280_);
                crate::leanh::lean_dec(v___x_3280_);
                crate::leanh::lean_dec(v___x_3278_);
                v___x_3282_ = l_Std_Time_Duration_ofNanoseconds(v___x_3281_);
                crate::leanh::lean_dec(v___x_3281_);
                v___x_3290_ =
                    l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_3273_, v___x_3282_);
                if crate::leanh::lean_obj_tag(v___x_3290_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_3290_, 1);
                    v___x_3291_ =
                        l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_3272_);
                    v___y_3284_ = v___x_3291_;
                    state = 2;
                    continue;
                } else {
                    v_a_3292_ = crate::leanh::lean_ctor_get(v___x_3290_, 0);
                    crate::leanh::lean_inc(v_a_3292_);
                    crate::leanh::lean_dec_ref_known(v___x_3290_, 1);
                    v___y_3284_ = v_a_3292_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc_ref(v___x_3282_);
                crate::leanh::lean_inc_ref(v___y_3284_);
                v___f_3285_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addMilliseconds___lam__0___boxed
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_3285_, 0, v___y_3284_);
                crate::leanh::lean_closure_set(v___f_3285_, 1, v___x_3282_);
                crate::leanh::lean_closure_set(v___f_3285_, 2, v___x_3276_);
                v___x_3286_ = lean_mk_thunk(v___f_3285_);
                if v_isShared_3264_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3263_, 3, v___y_3284_);
                    crate::leanh::lean_ctor_set(v___x_3263_, 1, v___x_3282_);
                    crate::leanh::lean_ctor_set(v___x_3263_, 0, v___x_3286_);
                    v___x_3288_ = v___x_3263_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3289_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3289_, 0, v___x_3286_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3289_, 1, v___x_3282_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3289_, 2, v_rules_3261_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3289_, 3, v___y_3284_);
                    v___x_3288_ = v_reuseFailAlloc_3289_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3288_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_ZonedDateTime_subMilliseconds___boxed(
    mut v_dt_3296_: *mut crate::leanh::LeanObject,
    mut v_milliseconds_3297_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3298_ = l_Std_Time_ZonedDateTime_subMilliseconds(v_dt_3296_, v_milliseconds_3297_);
    crate::leanh::lean_dec(v_milliseconds_3297_);
    return v_res_3298_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_addSeconds(
    mut v_dt_3299_: *mut crate::leanh::LeanObject,
    mut v_seconds_3300_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_timestamp_3301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rules_3302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3305_: u8 = 0;
    let mut v_second_3306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_3307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initialLocalTimeType_3308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_transitions_3309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3328_: u8 = 0;
    let mut v_unused_3329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_3301_ = crate::leanh::lean_ctor_get(v_dt_3299_, 1);
                v_rules_3302_ = crate::leanh::lean_ctor_get(v_dt_3299_, 2);
                v_isSharedCheck_3328_ = (!crate::leanh::lean_is_exclusive(v_dt_3299_)) as u8;
                if v_isSharedCheck_3328_ == 0 {
                    v_unused_3329_ = crate::leanh::lean_ctor_get(v_dt_3299_, 3);
                    crate::leanh::lean_dec(v_unused_3329_);
                    v_unused_3330_ = crate::leanh::lean_ctor_get(v_dt_3299_, 0);
                    crate::leanh::lean_dec(v_unused_3330_);
                    v___x_3304_ = v_dt_3299_;
                    v_isShared_3305_ = v_isSharedCheck_3328_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_rules_3302_);
                    crate::leanh::lean_inc(v_timestamp_3301_);
                    crate::leanh::lean_dec(v_dt_3299_);
                    v___x_3304_ = crate::leanh::lean_box(0);
                    v_isShared_3305_ = v_isSharedCheck_3328_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_second_3306_ = crate::leanh::lean_ctor_get(v_timestamp_3301_, 0);
                crate::leanh::lean_inc(v_second_3306_);
                v_nano_3307_ = crate::leanh::lean_ctor_get(v_timestamp_3301_, 1);
                crate::leanh::lean_inc(v_nano_3307_);
                crate::leanh::lean_dec_ref(v_timestamp_3301_);
                v_initialLocalTimeType_3308_ = crate::leanh::lean_ctor_get(v_rules_3302_, 0);
                v_transitions_3309_ = crate::leanh::lean_ctor_get(v_rules_3302_, 1);
                v___x_3310_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0,
                );
                v___x_3311_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3312_ = lean_int_mul(v_second_3306_, v___x_3311_);
                crate::leanh::lean_dec(v_second_3306_);
                v___x_3313_ = lean_int_add(v___x_3312_, v_nano_3307_);
                crate::leanh::lean_dec(v_nano_3307_);
                crate::leanh::lean_dec(v___x_3312_);
                v___x_3314_ = lean_int_mul(v_seconds_3300_, v___x_3311_);
                v___x_3315_ = lean_int_add(v___x_3314_, v___x_3310_);
                crate::leanh::lean_dec(v___x_3314_);
                v___x_3316_ = lean_int_add(v___x_3313_, v___x_3315_);
                crate::leanh::lean_dec(v___x_3315_);
                crate::leanh::lean_dec(v___x_3313_);
                v___x_3317_ = l_Std_Time_Duration_ofNanoseconds(v___x_3316_);
                crate::leanh::lean_dec(v___x_3316_);
                v___x_3325_ =
                    l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_3309_, v___x_3317_);
                if crate::leanh::lean_obj_tag(v___x_3325_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_3325_, 1);
                    v___x_3326_ =
                        l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_3308_);
                    v___y_3319_ = v___x_3326_;
                    state = 2;
                    continue;
                } else {
                    v_a_3327_ = crate::leanh::lean_ctor_get(v___x_3325_, 0);
                    crate::leanh::lean_inc(v_a_3327_);
                    crate::leanh::lean_dec_ref_known(v___x_3325_, 1);
                    v___y_3319_ = v_a_3327_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc_ref(v___x_3317_);
                crate::leanh::lean_inc_ref(v___y_3319_);
                v___f_3320_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addDays___lam__0___boxed as *mut core::ffi::c_void,
                    5,
                    4,
                );
                crate::leanh::lean_closure_set(v___f_3320_, 0, v___y_3319_);
                crate::leanh::lean_closure_set(v___f_3320_, 1, v___x_3317_);
                crate::leanh::lean_closure_set(v___f_3320_, 2, v___x_3311_);
                crate::leanh::lean_closure_set(v___f_3320_, 3, v___x_3310_);
                v___x_3321_ = lean_mk_thunk(v___f_3320_);
                if v_isShared_3305_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3304_, 3, v___y_3319_);
                    crate::leanh::lean_ctor_set(v___x_3304_, 1, v___x_3317_);
                    crate::leanh::lean_ctor_set(v___x_3304_, 0, v___x_3321_);
                    v___x_3323_ = v___x_3304_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3324_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3324_, 0, v___x_3321_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3324_, 1, v___x_3317_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3324_, 2, v_rules_3302_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3324_, 3, v___y_3319_);
                    v___x_3323_ = v_reuseFailAlloc_3324_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3323_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_ZonedDateTime_addSeconds___boxed(
    mut v_dt_3331_: *mut crate::leanh::LeanObject,
    mut v_seconds_3332_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3333_ = l_Std_Time_ZonedDateTime_addSeconds(v_dt_3331_, v_seconds_3332_);
    crate::leanh::lean_dec(v_seconds_3332_);
    return v_res_3333_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_subSeconds(
    mut v_dt_3334_: *mut crate::leanh::LeanObject,
    mut v_seconds_3335_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_timestamp_3336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rules_3337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3340_: u8 = 0;
    let mut v_second_3341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_3342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initialLocalTimeType_3343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_transitions_3344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3365_: u8 = 0;
    let mut v_unused_3366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_3336_ = crate::leanh::lean_ctor_get(v_dt_3334_, 1);
                v_rules_3337_ = crate::leanh::lean_ctor_get(v_dt_3334_, 2);
                v_isSharedCheck_3365_ = (!crate::leanh::lean_is_exclusive(v_dt_3334_)) as u8;
                if v_isSharedCheck_3365_ == 0 {
                    v_unused_3366_ = crate::leanh::lean_ctor_get(v_dt_3334_, 3);
                    crate::leanh::lean_dec(v_unused_3366_);
                    v_unused_3367_ = crate::leanh::lean_ctor_get(v_dt_3334_, 0);
                    crate::leanh::lean_dec(v_unused_3367_);
                    v___x_3339_ = v_dt_3334_;
                    v_isShared_3340_ = v_isSharedCheck_3365_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_rules_3337_);
                    crate::leanh::lean_inc(v_timestamp_3336_);
                    crate::leanh::lean_dec(v_dt_3334_);
                    v___x_3339_ = crate::leanh::lean_box(0);
                    v_isShared_3340_ = v_isSharedCheck_3365_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_second_3341_ = crate::leanh::lean_ctor_get(v_timestamp_3336_, 0);
                crate::leanh::lean_inc(v_second_3341_);
                v_nano_3342_ = crate::leanh::lean_ctor_get(v_timestamp_3336_, 1);
                crate::leanh::lean_inc(v_nano_3342_);
                crate::leanh::lean_dec_ref(v_timestamp_3336_);
                v_initialLocalTimeType_3343_ = crate::leanh::lean_ctor_get(v_rules_3337_, 0);
                v_transitions_3344_ = crate::leanh::lean_ctor_get(v_rules_3337_, 1);
                v___x_3345_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0,
                );
                v___x_3346_ = lean_int_neg(v_seconds_3335_);
                v___x_3347_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
                );
                v___x_3348_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3349_ = lean_int_mul(v_second_3341_, v___x_3348_);
                crate::leanh::lean_dec(v_second_3341_);
                v___x_3350_ = lean_int_add(v___x_3349_, v_nano_3342_);
                crate::leanh::lean_dec(v_nano_3342_);
                crate::leanh::lean_dec(v___x_3349_);
                v___x_3351_ = lean_int_mul(v___x_3346_, v___x_3348_);
                crate::leanh::lean_dec(v___x_3346_);
                v___x_3352_ = lean_int_add(v___x_3351_, v___x_3347_);
                crate::leanh::lean_dec(v___x_3351_);
                v___x_3353_ = lean_int_add(v___x_3350_, v___x_3352_);
                crate::leanh::lean_dec(v___x_3352_);
                crate::leanh::lean_dec(v___x_3350_);
                v___x_3354_ = l_Std_Time_Duration_ofNanoseconds(v___x_3353_);
                crate::leanh::lean_dec(v___x_3353_);
                v___x_3362_ =
                    l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_3344_, v___x_3354_);
                if crate::leanh::lean_obj_tag(v___x_3362_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_3362_, 1);
                    v___x_3363_ =
                        l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_3343_);
                    v___y_3356_ = v___x_3363_;
                    state = 2;
                    continue;
                } else {
                    v_a_3364_ = crate::leanh::lean_ctor_get(v___x_3362_, 0);
                    crate::leanh::lean_inc(v_a_3364_);
                    crate::leanh::lean_dec_ref_known(v___x_3362_, 1);
                    v___y_3356_ = v_a_3364_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc_ref(v___x_3354_);
                crate::leanh::lean_inc_ref(v___y_3356_);
                v___f_3357_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addDays___lam__0___boxed as *mut core::ffi::c_void,
                    5,
                    4,
                );
                crate::leanh::lean_closure_set(v___f_3357_, 0, v___y_3356_);
                crate::leanh::lean_closure_set(v___f_3357_, 1, v___x_3354_);
                crate::leanh::lean_closure_set(v___f_3357_, 2, v___x_3348_);
                crate::leanh::lean_closure_set(v___f_3357_, 3, v___x_3345_);
                v___x_3358_ = lean_mk_thunk(v___f_3357_);
                if v_isShared_3340_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3339_, 3, v___y_3356_);
                    crate::leanh::lean_ctor_set(v___x_3339_, 1, v___x_3354_);
                    crate::leanh::lean_ctor_set(v___x_3339_, 0, v___x_3358_);
                    v___x_3360_ = v___x_3339_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3361_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3361_, 0, v___x_3358_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3361_, 1, v___x_3354_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3361_, 2, v_rules_3337_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3361_, 3, v___y_3356_);
                    v___x_3360_ = v_reuseFailAlloc_3361_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3360_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_ZonedDateTime_subSeconds___boxed(
    mut v_dt_3368_: *mut crate::leanh::LeanObject,
    mut v_seconds_3369_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3370_ = l_Std_Time_ZonedDateTime_subSeconds(v_dt_3368_, v_seconds_3369_);
    crate::leanh::lean_dec(v_seconds_3369_);
    return v_res_3370_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_addNanoseconds(
    mut v_dt_3371_: *mut crate::leanh::LeanObject,
    mut v_nanoseconds_3372_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_timestamp_3373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rules_3374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3377_: u8 = 0;
    let mut v_second_3378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_3379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_3382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initialLocalTimeType_3383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_transitions_3384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3402_: u8 = 0;
    let mut v_unused_3403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_3373_ = crate::leanh::lean_ctor_get(v_dt_3371_, 1);
                v_rules_3374_ = crate::leanh::lean_ctor_get(v_dt_3371_, 2);
                v_isSharedCheck_3402_ = (!crate::leanh::lean_is_exclusive(v_dt_3371_)) as u8;
                if v_isSharedCheck_3402_ == 0 {
                    v_unused_3403_ = crate::leanh::lean_ctor_get(v_dt_3371_, 3);
                    crate::leanh::lean_dec(v_unused_3403_);
                    v_unused_3404_ = crate::leanh::lean_ctor_get(v_dt_3371_, 0);
                    crate::leanh::lean_dec(v_unused_3404_);
                    v___x_3376_ = v_dt_3371_;
                    v_isShared_3377_ = v_isSharedCheck_3402_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_rules_3374_);
                    crate::leanh::lean_inc(v_timestamp_3373_);
                    crate::leanh::lean_dec(v_dt_3371_);
                    v___x_3376_ = crate::leanh::lean_box(0);
                    v_isShared_3377_ = v_isSharedCheck_3402_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_second_3378_ = crate::leanh::lean_ctor_get(v_timestamp_3373_, 0);
                crate::leanh::lean_inc(v_second_3378_);
                v_nano_3379_ = crate::leanh::lean_ctor_get(v_timestamp_3373_, 1);
                crate::leanh::lean_inc(v_nano_3379_);
                crate::leanh::lean_dec_ref(v_timestamp_3373_);
                v___x_3380_ = l_Std_Time_Duration_ofNanoseconds(v_nanoseconds_3372_);
                v_second_3381_ = crate::leanh::lean_ctor_get(v___x_3380_, 0);
                crate::leanh::lean_inc(v_second_3381_);
                v_nano_3382_ = crate::leanh::lean_ctor_get(v___x_3380_, 1);
                crate::leanh::lean_inc(v_nano_3382_);
                crate::leanh::lean_dec_ref(v___x_3380_);
                v_initialLocalTimeType_3383_ = crate::leanh::lean_ctor_get(v_rules_3374_, 0);
                v_transitions_3384_ = crate::leanh::lean_ctor_get(v_rules_3374_, 1);
                v___x_3385_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3386_ = lean_int_mul(v_second_3378_, v___x_3385_);
                crate::leanh::lean_dec(v_second_3378_);
                v___x_3387_ = lean_int_add(v___x_3386_, v_nano_3379_);
                crate::leanh::lean_dec(v_nano_3379_);
                crate::leanh::lean_dec(v___x_3386_);
                v___x_3388_ = lean_int_mul(v_second_3381_, v___x_3385_);
                crate::leanh::lean_dec(v_second_3381_);
                v___x_3389_ = lean_int_add(v___x_3388_, v_nano_3382_);
                crate::leanh::lean_dec(v_nano_3382_);
                crate::leanh::lean_dec(v___x_3388_);
                v___x_3390_ = lean_int_add(v___x_3387_, v___x_3389_);
                crate::leanh::lean_dec(v___x_3389_);
                crate::leanh::lean_dec(v___x_3387_);
                v___x_3391_ = l_Std_Time_Duration_ofNanoseconds(v___x_3390_);
                crate::leanh::lean_dec(v___x_3390_);
                v___x_3399_ =
                    l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_3384_, v___x_3391_);
                if crate::leanh::lean_obj_tag(v___x_3399_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_3399_, 1);
                    v___x_3400_ =
                        l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_3383_);
                    v___y_3393_ = v___x_3400_;
                    state = 2;
                    continue;
                } else {
                    v_a_3401_ = crate::leanh::lean_ctor_get(v___x_3399_, 0);
                    crate::leanh::lean_inc(v_a_3401_);
                    crate::leanh::lean_dec_ref_known(v___x_3399_, 1);
                    v___y_3393_ = v_a_3401_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc_ref(v___x_3391_);
                crate::leanh::lean_inc_ref(v___y_3393_);
                v___f_3394_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addMilliseconds___lam__0___boxed
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_3394_, 0, v___y_3393_);
                crate::leanh::lean_closure_set(v___f_3394_, 1, v___x_3391_);
                crate::leanh::lean_closure_set(v___f_3394_, 2, v___x_3385_);
                v___x_3395_ = lean_mk_thunk(v___f_3394_);
                if v_isShared_3377_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3376_, 3, v___y_3393_);
                    crate::leanh::lean_ctor_set(v___x_3376_, 1, v___x_3391_);
                    crate::leanh::lean_ctor_set(v___x_3376_, 0, v___x_3395_);
                    v___x_3397_ = v___x_3376_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3398_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3398_, 0, v___x_3395_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3398_, 1, v___x_3391_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3398_, 2, v_rules_3374_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3398_, 3, v___y_3393_);
                    v___x_3397_ = v_reuseFailAlloc_3398_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3397_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_ZonedDateTime_addNanoseconds___boxed(
    mut v_dt_3405_: *mut crate::leanh::LeanObject,
    mut v_nanoseconds_3406_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3407_ = l_Std_Time_ZonedDateTime_addNanoseconds(v_dt_3405_, v_nanoseconds_3406_);
    crate::leanh::lean_dec(v_nanoseconds_3406_);
    return v_res_3407_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_subNanoseconds(
    mut v_dt_3408_: *mut crate::leanh::LeanObject,
    mut v_nanoseconds_3409_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_timestamp_3410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rules_3411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3414_: u8 = 0;
    let mut v___x_3415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_3417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_3419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initialLocalTimeType_3420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_transitions_3421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3441_: u8 = 0;
    let mut v_unused_3442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_3410_ = crate::leanh::lean_ctor_get(v_dt_3408_, 1);
                v_rules_3411_ = crate::leanh::lean_ctor_get(v_dt_3408_, 2);
                v_isSharedCheck_3441_ = (!crate::leanh::lean_is_exclusive(v_dt_3408_)) as u8;
                if v_isSharedCheck_3441_ == 0 {
                    v_unused_3442_ = crate::leanh::lean_ctor_get(v_dt_3408_, 3);
                    crate::leanh::lean_dec(v_unused_3442_);
                    v_unused_3443_ = crate::leanh::lean_ctor_get(v_dt_3408_, 0);
                    crate::leanh::lean_dec(v_unused_3443_);
                    v___x_3413_ = v_dt_3408_;
                    v_isShared_3414_ = v_isSharedCheck_3441_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_rules_3411_);
                    crate::leanh::lean_inc(v_timestamp_3410_);
                    crate::leanh::lean_dec(v_dt_3408_);
                    v___x_3413_ = crate::leanh::lean_box(0);
                    v_isShared_3414_ = v_isSharedCheck_3441_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3415_ = l_Std_Time_Duration_ofNanoseconds(v_nanoseconds_3409_);
                v_second_3416_ = crate::leanh::lean_ctor_get(v___x_3415_, 0);
                crate::leanh::lean_inc(v_second_3416_);
                v_nano_3417_ = crate::leanh::lean_ctor_get(v___x_3415_, 1);
                crate::leanh::lean_inc(v_nano_3417_);
                crate::leanh::lean_dec_ref(v___x_3415_);
                v_second_3418_ = crate::leanh::lean_ctor_get(v_timestamp_3410_, 0);
                crate::leanh::lean_inc(v_second_3418_);
                v_nano_3419_ = crate::leanh::lean_ctor_get(v_timestamp_3410_, 1);
                crate::leanh::lean_inc(v_nano_3419_);
                crate::leanh::lean_dec_ref(v_timestamp_3410_);
                v_initialLocalTimeType_3420_ = crate::leanh::lean_ctor_get(v_rules_3411_, 0);
                v_transitions_3421_ = crate::leanh::lean_ctor_get(v_rules_3411_, 1);
                v___x_3422_ = lean_int_neg(v_second_3416_);
                crate::leanh::lean_dec(v_second_3416_);
                v___x_3423_ = lean_int_neg(v_nano_3417_);
                crate::leanh::lean_dec(v_nano_3417_);
                v___x_3424_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3425_ = lean_int_mul(v_second_3418_, v___x_3424_);
                crate::leanh::lean_dec(v_second_3418_);
                v___x_3426_ = lean_int_add(v___x_3425_, v_nano_3419_);
                crate::leanh::lean_dec(v_nano_3419_);
                crate::leanh::lean_dec(v___x_3425_);
                v___x_3427_ = lean_int_mul(v___x_3422_, v___x_3424_);
                crate::leanh::lean_dec(v___x_3422_);
                v___x_3428_ = lean_int_add(v___x_3427_, v___x_3423_);
                crate::leanh::lean_dec(v___x_3423_);
                crate::leanh::lean_dec(v___x_3427_);
                v___x_3429_ = lean_int_add(v___x_3426_, v___x_3428_);
                crate::leanh::lean_dec(v___x_3428_);
                crate::leanh::lean_dec(v___x_3426_);
                v___x_3430_ = l_Std_Time_Duration_ofNanoseconds(v___x_3429_);
                crate::leanh::lean_dec(v___x_3429_);
                v___x_3438_ =
                    l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_3421_, v___x_3430_);
                if crate::leanh::lean_obj_tag(v___x_3438_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_3438_, 1);
                    v___x_3439_ =
                        l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_3420_);
                    v___y_3432_ = v___x_3439_;
                    state = 2;
                    continue;
                } else {
                    v_a_3440_ = crate::leanh::lean_ctor_get(v___x_3438_, 0);
                    crate::leanh::lean_inc(v_a_3440_);
                    crate::leanh::lean_dec_ref_known(v___x_3438_, 1);
                    v___y_3432_ = v_a_3440_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc_ref(v___x_3430_);
                crate::leanh::lean_inc_ref(v___y_3432_);
                v___f_3433_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addMilliseconds___lam__0___boxed
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_3433_, 0, v___y_3432_);
                crate::leanh::lean_closure_set(v___f_3433_, 1, v___x_3430_);
                crate::leanh::lean_closure_set(v___f_3433_, 2, v___x_3424_);
                v___x_3434_ = lean_mk_thunk(v___f_3433_);
                if v_isShared_3414_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3413_, 3, v___y_3432_);
                    crate::leanh::lean_ctor_set(v___x_3413_, 1, v___x_3430_);
                    crate::leanh::lean_ctor_set(v___x_3413_, 0, v___x_3434_);
                    v___x_3436_ = v___x_3413_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3437_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3437_, 0, v___x_3434_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3437_, 1, v___x_3430_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3437_, 2, v_rules_3411_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3437_, 3, v___y_3432_);
                    v___x_3436_ = v_reuseFailAlloc_3437_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3436_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_ZonedDateTime_subNanoseconds___boxed(
    mut v_dt_3444_: *mut crate::leanh::LeanObject,
    mut v_nanoseconds_3445_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3446_ = l_Std_Time_ZonedDateTime_subNanoseconds(v_dt_3444_, v_nanoseconds_3445_);
    crate::leanh::lean_dec(v_nanoseconds_3445_);
    return v_res_3446_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_era(mut v_date_3447_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v_date_3448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_3450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_year_3451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: u8 = 0;
    v_date_3448_ = crate::leanh::lean_ctor_get(v_date_3447_, 0);
    v___x_3449_ = lean_thunk_get_own(v_date_3448_);
    v_date_3450_ = crate::leanh::lean_ctor_get(v___x_3449_, 0);
    crate::leanh::lean_inc_ref(v_date_3450_);
    crate::leanh::lean_dec(v___x_3449_);
    v_year_3451_ = crate::leanh::lean_ctor_get(v_date_3450_, 0);
    crate::leanh::lean_inc(v_year_3451_);
    crate::leanh::lean_dec_ref(v_date_3450_);
    v___x_3452_ = l_Std_Time_Year_Offset_era(v_year_3451_);
    crate::leanh::lean_dec(v_year_3451_);
    return v___x_3452_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_era___boxed(
    mut v_date_3453_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3454_: u8 = 0;
    let mut v_r_3455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3454_ = l_Std_Time_ZonedDateTime_era(v_date_3453_);
    crate::leanh::lean_dec_ref(v_date_3453_);
    v_r_3455_ = crate::leanh::lean_box((v_res_3454_) as usize);
    return v_r_3455_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_withWeekday(
    mut v_dt_3456_: *mut crate::leanh::LeanObject,
    mut v_desiredWeekday_3457_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_3458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rules_3459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3462_: u8 = 0;
    let mut v_date_3463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_wt_3465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ltt_3466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tz_3467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_3470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3485_: u8 = 0;
    let mut v_unused_3486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_3458_ = crate::leanh::lean_ctor_get(v_dt_3456_, 0);
                v_rules_3459_ = crate::leanh::lean_ctor_get(v_dt_3456_, 2);
                v_isSharedCheck_3485_ = (!crate::leanh::lean_is_exclusive(v_dt_3456_)) as u8;
                if v_isSharedCheck_3485_ == 0 {
                    v_unused_3486_ = crate::leanh::lean_ctor_get(v_dt_3456_, 3);
                    crate::leanh::lean_dec(v_unused_3486_);
                    v_unused_3487_ = crate::leanh::lean_ctor_get(v_dt_3456_, 1);
                    crate::leanh::lean_dec(v_unused_3487_);
                    v___x_3461_ = v_dt_3456_;
                    v_isShared_3462_ = v_isSharedCheck_3485_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_rules_3459_);
                    crate::leanh::lean_inc(v_date_3458_);
                    crate::leanh::lean_dec(v_dt_3456_);
                    v___x_3461_ = crate::leanh::lean_box(0);
                    v_isShared_3462_ = v_isSharedCheck_3485_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_date_3463_ = lean_thunk_get_own(v_date_3458_);
                crate::leanh::lean_dec_ref(v_date_3458_);
                v___x_3464_ =
                    l_Std_Time_PlainDateTime_withWeekday(v_date_3463_, v_desiredWeekday_3457_);
                crate::leanh::lean_inc_ref(v___x_3464_);
                v_wt_3465_ = l_Std_Time_PlainDateTime_toWallTime(v___x_3464_);
                crate::leanh::lean_inc_ref(v_rules_3459_);
                v_ltt_3466_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(
                    v_rules_3459_,
                    v_wt_3465_,
                );
                v_tz_3467_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_3466_);
                crate::leanh::lean_dec_ref(v_ltt_3466_);
                v_offset_3468_ = crate::leanh::lean_ctor_get(v_tz_3467_, 0);
                crate::leanh::lean_inc(v_offset_3468_);
                v_second_3469_ = crate::leanh::lean_ctor_get(v_wt_3465_, 0);
                crate::leanh::lean_inc(v_second_3469_);
                v_nano_3470_ = crate::leanh::lean_ctor_get(v_wt_3465_, 1);
                crate::leanh::lean_inc(v_nano_3470_);
                crate::leanh::lean_dec_ref(v_wt_3465_);
                v___f_3471_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3471_, 0, v___x_3464_);
                v___x_3472_ = lean_mk_thunk(v___f_3471_);
                v___x_3473_ = lean_int_neg(v_offset_3468_);
                crate::leanh::lean_dec(v_offset_3468_);
                v___x_3474_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
                );
                v___x_3475_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3476_ = lean_int_mul(v_second_3469_, v___x_3475_);
                crate::leanh::lean_dec(v_second_3469_);
                v___x_3477_ = lean_int_add(v___x_3476_, v_nano_3470_);
                crate::leanh::lean_dec(v_nano_3470_);
                crate::leanh::lean_dec(v___x_3476_);
                v___x_3478_ = lean_int_mul(v___x_3473_, v___x_3475_);
                crate::leanh::lean_dec(v___x_3473_);
                v___x_3479_ = lean_int_add(v___x_3478_, v___x_3474_);
                crate::leanh::lean_dec(v___x_3478_);
                v___x_3480_ = lean_int_add(v___x_3477_, v___x_3479_);
                crate::leanh::lean_dec(v___x_3479_);
                crate::leanh::lean_dec(v___x_3477_);
                v___x_3481_ = l_Std_Time_Duration_ofNanoseconds(v___x_3480_);
                crate::leanh::lean_dec(v___x_3480_);
                if v_isShared_3462_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3461_, 3, v_tz_3467_);
                    crate::leanh::lean_ctor_set(v___x_3461_, 1, v___x_3481_);
                    crate::leanh::lean_ctor_set(v___x_3461_, 0, v___x_3472_);
                    v___x_3483_ = v___x_3461_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3484_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3484_, 0, v___x_3472_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3484_, 1, v___x_3481_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3484_, 2, v_rules_3459_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3484_, 3, v_tz_3467_);
                    v___x_3483_ = v_reuseFailAlloc_3484_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3483_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_ZonedDateTime_withWeekday___boxed(
    mut v_dt_3488_: *mut crate::leanh::LeanObject,
    mut v_desiredWeekday_3489_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_desiredWeekday_boxed_3490_: u8 = 0;
    let mut v_res_3491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_desiredWeekday_boxed_3490_ = (crate::leanh::lean_unbox(v_desiredWeekday_3489_) as u8);
    v_res_3491_ = l_Std_Time_ZonedDateTime_withWeekday(v_dt_3488_, v_desiredWeekday_boxed_3490_);
    return v_res_3491_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_withDaysClip(
    mut v_dt_3492_: *mut crate::leanh::LeanObject,
    mut v_days_3493_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_3494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rules_3495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3498_: u8 = 0;
    let mut v_date_3499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_3502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3505_: u8 = 0;
    let mut v___x_3507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_wt_3508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ltt_3509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tz_3510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_3511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_3513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3529_: u8 = 0;
    let mut v_unused_3530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_3531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_year_3532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_month_3533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3536_: u8 = 0;
    let mut v___y_3538_: u8 = 0;
    let mut v_max_3539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3540_: u8 = 0;
    let mut v___x_3542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3553_: u8 = 0;
    let mut v___x_3554_: u8 = 0;
    let mut v___x_3555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3557_: u8 = 0;
    let mut v_isSharedCheck_3558_: u8 = 0;
    let mut v_unused_3559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3560_: u8 = 0;
    let mut v_unused_3561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_3494_ = crate::leanh::lean_ctor_get(v_dt_3492_, 0);
                v_rules_3495_ = crate::leanh::lean_ctor_get(v_dt_3492_, 2);
                v_isSharedCheck_3560_ = (!crate::leanh::lean_is_exclusive(v_dt_3492_)) as u8;
                if v_isSharedCheck_3560_ == 0 {
                    v_unused_3561_ = crate::leanh::lean_ctor_get(v_dt_3492_, 3);
                    crate::leanh::lean_dec(v_unused_3561_);
                    v_unused_3562_ = crate::leanh::lean_ctor_get(v_dt_3492_, 1);
                    crate::leanh::lean_dec(v_unused_3562_);
                    v___x_3497_ = v_dt_3492_;
                    v_isShared_3498_ = v_isSharedCheck_3560_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_rules_3495_);
                    crate::leanh::lean_inc(v_date_3494_);
                    crate::leanh::lean_dec(v_dt_3492_);
                    v___x_3497_ = crate::leanh::lean_box(0);
                    v_isShared_3498_ = v_isSharedCheck_3560_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_date_3499_ = lean_thunk_get_own(v_date_3494_);
                crate::leanh::lean_dec_ref(v_date_3494_);
                v_date_3531_ = crate::leanh::lean_ctor_get(v_date_3499_, 0);
                crate::leanh::lean_inc_ref(v_date_3531_);
                v_year_3532_ = crate::leanh::lean_ctor_get(v_date_3531_, 0);
                v_month_3533_ = crate::leanh::lean_ctor_get(v_date_3531_, 1);
                v_isSharedCheck_3558_ = (!crate::leanh::lean_is_exclusive(v_date_3531_)) as u8;
                if v_isSharedCheck_3558_ == 0 {
                    v_unused_3559_ = crate::leanh::lean_ctor_get(v_date_3531_, 2);
                    crate::leanh::lean_dec(v_unused_3559_);
                    v___x_3535_ = v_date_3531_;
                    v_isShared_3536_ = v_isSharedCheck_3558_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_month_3533_);
                    crate::leanh::lean_inc(v_year_3532_);
                    crate::leanh::lean_dec(v_date_3531_);
                    v___x_3535_ = crate::leanh::lean_box(0);
                    v_isShared_3536_ = v_isSharedCheck_3558_;
                    state = 6;
                    continue;
                }
            }
            2 => {
                v_time_3502_ = crate::leanh::lean_ctor_get(v_date_3499_, 1);
                v_isSharedCheck_3529_ = (!crate::leanh::lean_is_exclusive(v_date_3499_)) as u8;
                if v_isSharedCheck_3529_ == 0 {
                    v_unused_3530_ = crate::leanh::lean_ctor_get(v_date_3499_, 0);
                    crate::leanh::lean_dec(v_unused_3530_);
                    v___x_3504_ = v_date_3499_;
                    v_isShared_3505_ = v_isSharedCheck_3529_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_time_3502_);
                    crate::leanh::lean_dec(v_date_3499_);
                    v___x_3504_ = crate::leanh::lean_box(0);
                    v_isShared_3505_ = v_isSharedCheck_3529_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3505_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3504_, 0, v___y_3501_);
                    v___x_3507_ = v___x_3504_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3528_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3528_, 0, v___y_3501_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3528_, 1, v_time_3502_);
                    v___x_3507_ = v_reuseFailAlloc_3528_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                crate::leanh::lean_inc_ref(v___x_3507_);
                v_wt_3508_ = l_Std_Time_PlainDateTime_toWallTime(v___x_3507_);
                crate::leanh::lean_inc_ref(v_rules_3495_);
                v_ltt_3509_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(
                    v_rules_3495_,
                    v_wt_3508_,
                );
                v_tz_3510_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_3509_);
                crate::leanh::lean_dec_ref(v_ltt_3509_);
                v_offset_3511_ = crate::leanh::lean_ctor_get(v_tz_3510_, 0);
                crate::leanh::lean_inc(v_offset_3511_);
                v_second_3512_ = crate::leanh::lean_ctor_get(v_wt_3508_, 0);
                crate::leanh::lean_inc(v_second_3512_);
                v_nano_3513_ = crate::leanh::lean_ctor_get(v_wt_3508_, 1);
                crate::leanh::lean_inc(v_nano_3513_);
                crate::leanh::lean_dec_ref(v_wt_3508_);
                v___f_3514_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3514_, 0, v___x_3507_);
                v___x_3515_ = lean_mk_thunk(v___f_3514_);
                v___x_3516_ = lean_int_neg(v_offset_3511_);
                crate::leanh::lean_dec(v_offset_3511_);
                v___x_3517_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
                );
                v___x_3518_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3519_ = lean_int_mul(v_second_3512_, v___x_3518_);
                crate::leanh::lean_dec(v_second_3512_);
                v___x_3520_ = lean_int_add(v___x_3519_, v_nano_3513_);
                crate::leanh::lean_dec(v_nano_3513_);
                crate::leanh::lean_dec(v___x_3519_);
                v___x_3521_ = lean_int_mul(v___x_3516_, v___x_3518_);
                crate::leanh::lean_dec(v___x_3516_);
                v___x_3522_ = lean_int_add(v___x_3521_, v___x_3517_);
                crate::leanh::lean_dec(v___x_3521_);
                v___x_3523_ = lean_int_add(v___x_3520_, v___x_3522_);
                crate::leanh::lean_dec(v___x_3522_);
                crate::leanh::lean_dec(v___x_3520_);
                v___x_3524_ = l_Std_Time_Duration_ofNanoseconds(v___x_3523_);
                crate::leanh::lean_dec(v___x_3523_);
                if v_isShared_3498_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3497_, 3, v_tz_3510_);
                    crate::leanh::lean_ctor_set(v___x_3497_, 1, v___x_3524_);
                    crate::leanh::lean_ctor_set(v___x_3497_, 0, v___x_3515_);
                    v___x_3526_ = v___x_3497_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3527_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3527_, 0, v___x_3515_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3527_, 1, v___x_3524_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3527_, 2, v_rules_3495_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3527_, 3, v_tz_3510_);
                    v___x_3526_ = v_reuseFailAlloc_3527_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3526_;
            }
            6 => {
                v___x_3547_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_dayOfYear___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_dayOfYear___closed__0_once),
                    _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__0,
                );
                v___x_3548_ = lean_int_mod(v_year_3532_, v___x_3547_);
                v___x_3549_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0,
                );
                v___x_3554_ = lean_int_dec_eq(v___x_3548_, v___x_3549_);
                crate::leanh::lean_dec(v___x_3548_);
                if v___x_3554_ == 0 {
                    v___y_3538_ = v___x_3554_;
                    state = 7;
                    continue;
                } else {
                    v___x_3555_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_dayOfYear___closed__2),
                        core::ptr::addr_of_mut!(
                            l_Std_Time_ZonedDateTime_dayOfYear___closed__2_once
                        ),
                        _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__2,
                    );
                    v___x_3556_ = lean_int_mod(v_year_3532_, v___x_3555_);
                    v___x_3557_ = lean_int_dec_eq(v___x_3556_, v___x_3549_);
                    crate::leanh::lean_dec(v___x_3556_);
                    if v___x_3557_ == 0 {
                        if v___x_3554_ == 0 {
                            state = 10;
                            continue;
                        } else {
                            v___y_3538_ = v___x_3554_;
                            state = 7;
                            continue;
                        }
                    } else {
                        state = 10;
                        continue;
                    }
                }
            }
            7 => {
                v_max_3539_ = l_Std_Time_Month_Ordinal_days(v___y_3538_, v_month_3533_);
                v___x_3540_ = lean_int_dec_lt(v_max_3539_, v_days_3493_);
                if v___x_3540_ == 0 {
                    crate::leanh::lean_dec(v_max_3539_);
                    if v_isShared_3536_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3535_, 2, v_days_3493_);
                        v___x_3542_ = v___x_3535_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_3543_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3543_, 0, v_year_3532_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3543_, 1, v_month_3533_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3543_, 2, v_days_3493_);
                        v___x_3542_ = v_reuseFailAlloc_3543_;
                        state = 8;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_days_3493_);
                    if v_isShared_3536_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3535_, 2, v_max_3539_);
                        v___x_3545_ = v___x_3535_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_3546_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3546_, 0, v_year_3532_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3546_, 1, v_month_3533_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3546_, 2, v_max_3539_);
                        v___x_3545_ = v_reuseFailAlloc_3546_;
                        state = 9;
                        continue;
                    }
                }
            }
            8 => {
                v___y_3501_ = v___x_3542_;
                state = 2;
                continue;
            }
            9 => {
                v___y_3501_ = v___x_3545_;
                state = 2;
                continue;
            }
            10 => {
                v___x_3551_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_dayOfYear___closed__1),
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_dayOfYear___closed__1_once),
                    _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__1,
                );
                v___x_3552_ = lean_int_mod(v_year_3532_, v___x_3551_);
                v___x_3553_ = lean_int_dec_eq(v___x_3552_, v___x_3549_);
                crate::leanh::lean_dec(v___x_3552_);
                v___y_3538_ = v___x_3553_;
                state = 7;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_ZonedDateTime_withDaysRollOver(
    mut v_dt_3563_: *mut crate::leanh::LeanObject,
    mut v_days_3564_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_3565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rules_3566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3569_: u8 = 0;
    let mut v_date_3570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_3571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_3572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3575_: u8 = 0;
    let mut v_year_3576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_month_3577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_wt_3581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ltt_3582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tz_3583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_3584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_3586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3602_: u8 = 0;
    let mut v_isSharedCheck_3603_: u8 = 0;
    let mut v_unused_3604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_3565_ = crate::leanh::lean_ctor_get(v_dt_3563_, 0);
                v_rules_3566_ = crate::leanh::lean_ctor_get(v_dt_3563_, 2);
                v_isSharedCheck_3603_ = (!crate::leanh::lean_is_exclusive(v_dt_3563_)) as u8;
                if v_isSharedCheck_3603_ == 0 {
                    v_unused_3604_ = crate::leanh::lean_ctor_get(v_dt_3563_, 3);
                    crate::leanh::lean_dec(v_unused_3604_);
                    v_unused_3605_ = crate::leanh::lean_ctor_get(v_dt_3563_, 1);
                    crate::leanh::lean_dec(v_unused_3605_);
                    v___x_3568_ = v_dt_3563_;
                    v_isShared_3569_ = v_isSharedCheck_3603_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_rules_3566_);
                    crate::leanh::lean_inc(v_date_3565_);
                    crate::leanh::lean_dec(v_dt_3563_);
                    v___x_3568_ = crate::leanh::lean_box(0);
                    v_isShared_3569_ = v_isSharedCheck_3603_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_date_3570_ = lean_thunk_get_own(v_date_3565_);
                crate::leanh::lean_dec_ref(v_date_3565_);
                v_date_3571_ = crate::leanh::lean_ctor_get(v_date_3570_, 0);
                v_time_3572_ = crate::leanh::lean_ctor_get(v_date_3570_, 1);
                v_isSharedCheck_3602_ = (!crate::leanh::lean_is_exclusive(v_date_3570_)) as u8;
                if v_isSharedCheck_3602_ == 0 {
                    v___x_3574_ = v_date_3570_;
                    v_isShared_3575_ = v_isSharedCheck_3602_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_time_3572_);
                    crate::leanh::lean_inc(v_date_3571_);
                    crate::leanh::lean_dec(v_date_3570_);
                    v___x_3574_ = crate::leanh::lean_box(0);
                    v_isShared_3575_ = v_isSharedCheck_3602_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_year_3576_ = crate::leanh::lean_ctor_get(v_date_3571_, 0);
                crate::leanh::lean_inc(v_year_3576_);
                v_month_3577_ = crate::leanh::lean_ctor_get(v_date_3571_, 1);
                crate::leanh::lean_inc(v_month_3577_);
                crate::leanh::lean_dec_ref(v_date_3571_);
                v___x_3578_ =
                    l_Std_Time_PlainDate_rollOver(v_year_3576_, v_month_3577_, v_days_3564_);
                if v_isShared_3575_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3574_, 0, v___x_3578_);
                    v___x_3580_ = v___x_3574_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3601_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3601_, 0, v___x_3578_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3601_, 1, v_time_3572_);
                    v___x_3580_ = v_reuseFailAlloc_3601_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_inc_ref(v___x_3580_);
                v_wt_3581_ = l_Std_Time_PlainDateTime_toWallTime(v___x_3580_);
                crate::leanh::lean_inc_ref(v_rules_3566_);
                v_ltt_3582_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(
                    v_rules_3566_,
                    v_wt_3581_,
                );
                v_tz_3583_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_3582_);
                crate::leanh::lean_dec_ref(v_ltt_3582_);
                v_offset_3584_ = crate::leanh::lean_ctor_get(v_tz_3583_, 0);
                crate::leanh::lean_inc(v_offset_3584_);
                v_second_3585_ = crate::leanh::lean_ctor_get(v_wt_3581_, 0);
                crate::leanh::lean_inc(v_second_3585_);
                v_nano_3586_ = crate::leanh::lean_ctor_get(v_wt_3581_, 1);
                crate::leanh::lean_inc(v_nano_3586_);
                crate::leanh::lean_dec_ref(v_wt_3581_);
                v___f_3587_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3587_, 0, v___x_3580_);
                v___x_3588_ = lean_mk_thunk(v___f_3587_);
                v___x_3589_ = lean_int_neg(v_offset_3584_);
                crate::leanh::lean_dec(v_offset_3584_);
                v___x_3590_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
                );
                v___x_3591_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3592_ = lean_int_mul(v_second_3585_, v___x_3591_);
                crate::leanh::lean_dec(v_second_3585_);
                v___x_3593_ = lean_int_add(v___x_3592_, v_nano_3586_);
                crate::leanh::lean_dec(v_nano_3586_);
                crate::leanh::lean_dec(v___x_3592_);
                v___x_3594_ = lean_int_mul(v___x_3589_, v___x_3591_);
                crate::leanh::lean_dec(v___x_3589_);
                v___x_3595_ = lean_int_add(v___x_3594_, v___x_3590_);
                crate::leanh::lean_dec(v___x_3594_);
                v___x_3596_ = lean_int_add(v___x_3593_, v___x_3595_);
                crate::leanh::lean_dec(v___x_3595_);
                crate::leanh::lean_dec(v___x_3593_);
                v___x_3597_ = l_Std_Time_Duration_ofNanoseconds(v___x_3596_);
                crate::leanh::lean_dec(v___x_3596_);
                if v_isShared_3569_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3568_, 3, v_tz_3583_);
                    crate::leanh::lean_ctor_set(v___x_3568_, 1, v___x_3597_);
                    crate::leanh::lean_ctor_set(v___x_3568_, 0, v___x_3588_);
                    v___x_3599_ = v___x_3568_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3600_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3600_, 0, v___x_3588_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3600_, 1, v___x_3597_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3600_, 2, v_rules_3566_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3600_, 3, v_tz_3583_);
                    v___x_3599_ = v_reuseFailAlloc_3600_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3599_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_ZonedDateTime_withDaysRollOver___boxed(
    mut v_dt_3606_: *mut crate::leanh::LeanObject,
    mut v_days_3607_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3608_ = l_Std_Time_ZonedDateTime_withDaysRollOver(v_dt_3606_, v_days_3607_);
    crate::leanh::lean_dec(v_days_3607_);
    return v_res_3608_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_withMonthClip(
    mut v_dt_3609_: *mut crate::leanh::LeanObject,
    mut v_month_3610_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_3611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rules_3612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3615_: u8 = 0;
    let mut v_date_3616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_3619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3622_: u8 = 0;
    let mut v___x_3624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_wt_3625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ltt_3626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tz_3627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_3628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_3630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3646_: u8 = 0;
    let mut v_unused_3647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_3648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_year_3649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_day_3650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3653_: u8 = 0;
    let mut v___y_3655_: u8 = 0;
    let mut v_max_3656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3657_: u8 = 0;
    let mut v___x_3659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3670_: u8 = 0;
    let mut v___x_3671_: u8 = 0;
    let mut v___x_3672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3674_: u8 = 0;
    let mut v_isSharedCheck_3675_: u8 = 0;
    let mut v_unused_3676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3677_: u8 = 0;
    let mut v_unused_3678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_3611_ = crate::leanh::lean_ctor_get(v_dt_3609_, 0);
                v_rules_3612_ = crate::leanh::lean_ctor_get(v_dt_3609_, 2);
                v_isSharedCheck_3677_ = (!crate::leanh::lean_is_exclusive(v_dt_3609_)) as u8;
                if v_isSharedCheck_3677_ == 0 {
                    v_unused_3678_ = crate::leanh::lean_ctor_get(v_dt_3609_, 3);
                    crate::leanh::lean_dec(v_unused_3678_);
                    v_unused_3679_ = crate::leanh::lean_ctor_get(v_dt_3609_, 1);
                    crate::leanh::lean_dec(v_unused_3679_);
                    v___x_3614_ = v_dt_3609_;
                    v_isShared_3615_ = v_isSharedCheck_3677_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_rules_3612_);
                    crate::leanh::lean_inc(v_date_3611_);
                    crate::leanh::lean_dec(v_dt_3609_);
                    v___x_3614_ = crate::leanh::lean_box(0);
                    v_isShared_3615_ = v_isSharedCheck_3677_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_date_3616_ = lean_thunk_get_own(v_date_3611_);
                crate::leanh::lean_dec_ref(v_date_3611_);
                v_date_3648_ = crate::leanh::lean_ctor_get(v_date_3616_, 0);
                crate::leanh::lean_inc_ref(v_date_3648_);
                v_year_3649_ = crate::leanh::lean_ctor_get(v_date_3648_, 0);
                v_day_3650_ = crate::leanh::lean_ctor_get(v_date_3648_, 2);
                v_isSharedCheck_3675_ = (!crate::leanh::lean_is_exclusive(v_date_3648_)) as u8;
                if v_isSharedCheck_3675_ == 0 {
                    v_unused_3676_ = crate::leanh::lean_ctor_get(v_date_3648_, 1);
                    crate::leanh::lean_dec(v_unused_3676_);
                    v___x_3652_ = v_date_3648_;
                    v_isShared_3653_ = v_isSharedCheck_3675_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_day_3650_);
                    crate::leanh::lean_inc(v_year_3649_);
                    crate::leanh::lean_dec(v_date_3648_);
                    v___x_3652_ = crate::leanh::lean_box(0);
                    v_isShared_3653_ = v_isSharedCheck_3675_;
                    state = 6;
                    continue;
                }
            }
            2 => {
                v_time_3619_ = crate::leanh::lean_ctor_get(v_date_3616_, 1);
                v_isSharedCheck_3646_ = (!crate::leanh::lean_is_exclusive(v_date_3616_)) as u8;
                if v_isSharedCheck_3646_ == 0 {
                    v_unused_3647_ = crate::leanh::lean_ctor_get(v_date_3616_, 0);
                    crate::leanh::lean_dec(v_unused_3647_);
                    v___x_3621_ = v_date_3616_;
                    v_isShared_3622_ = v_isSharedCheck_3646_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_time_3619_);
                    crate::leanh::lean_dec(v_date_3616_);
                    v___x_3621_ = crate::leanh::lean_box(0);
                    v_isShared_3622_ = v_isSharedCheck_3646_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3622_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3621_, 0, v___y_3618_);
                    v___x_3624_ = v___x_3621_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3645_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3645_, 0, v___y_3618_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3645_, 1, v_time_3619_);
                    v___x_3624_ = v_reuseFailAlloc_3645_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                crate::leanh::lean_inc_ref(v___x_3624_);
                v_wt_3625_ = l_Std_Time_PlainDateTime_toWallTime(v___x_3624_);
                crate::leanh::lean_inc_ref(v_rules_3612_);
                v_ltt_3626_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(
                    v_rules_3612_,
                    v_wt_3625_,
                );
                v_tz_3627_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_3626_);
                crate::leanh::lean_dec_ref(v_ltt_3626_);
                v_offset_3628_ = crate::leanh::lean_ctor_get(v_tz_3627_, 0);
                crate::leanh::lean_inc(v_offset_3628_);
                v_second_3629_ = crate::leanh::lean_ctor_get(v_wt_3625_, 0);
                crate::leanh::lean_inc(v_second_3629_);
                v_nano_3630_ = crate::leanh::lean_ctor_get(v_wt_3625_, 1);
                crate::leanh::lean_inc(v_nano_3630_);
                crate::leanh::lean_dec_ref(v_wt_3625_);
                v___f_3631_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3631_, 0, v___x_3624_);
                v___x_3632_ = lean_mk_thunk(v___f_3631_);
                v___x_3633_ = lean_int_neg(v_offset_3628_);
                crate::leanh::lean_dec(v_offset_3628_);
                v___x_3634_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
                );
                v___x_3635_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3636_ = lean_int_mul(v_second_3629_, v___x_3635_);
                crate::leanh::lean_dec(v_second_3629_);
                v___x_3637_ = lean_int_add(v___x_3636_, v_nano_3630_);
                crate::leanh::lean_dec(v_nano_3630_);
                crate::leanh::lean_dec(v___x_3636_);
                v___x_3638_ = lean_int_mul(v___x_3633_, v___x_3635_);
                crate::leanh::lean_dec(v___x_3633_);
                v___x_3639_ = lean_int_add(v___x_3638_, v___x_3634_);
                crate::leanh::lean_dec(v___x_3638_);
                v___x_3640_ = lean_int_add(v___x_3637_, v___x_3639_);
                crate::leanh::lean_dec(v___x_3639_);
                crate::leanh::lean_dec(v___x_3637_);
                v___x_3641_ = l_Std_Time_Duration_ofNanoseconds(v___x_3640_);
                crate::leanh::lean_dec(v___x_3640_);
                if v_isShared_3615_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3614_, 3, v_tz_3627_);
                    crate::leanh::lean_ctor_set(v___x_3614_, 1, v___x_3641_);
                    crate::leanh::lean_ctor_set(v___x_3614_, 0, v___x_3632_);
                    v___x_3643_ = v___x_3614_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3644_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3644_, 0, v___x_3632_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3644_, 1, v___x_3641_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3644_, 2, v_rules_3612_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3644_, 3, v_tz_3627_);
                    v___x_3643_ = v_reuseFailAlloc_3644_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3643_;
            }
            6 => {
                v___x_3664_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_dayOfYear___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_dayOfYear___closed__0_once),
                    _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__0,
                );
                v___x_3665_ = lean_int_mod(v_year_3649_, v___x_3664_);
                v___x_3666_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0,
                );
                v___x_3671_ = lean_int_dec_eq(v___x_3665_, v___x_3666_);
                crate::leanh::lean_dec(v___x_3665_);
                if v___x_3671_ == 0 {
                    v___y_3655_ = v___x_3671_;
                    state = 7;
                    continue;
                } else {
                    v___x_3672_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_dayOfYear___closed__2),
                        core::ptr::addr_of_mut!(
                            l_Std_Time_ZonedDateTime_dayOfYear___closed__2_once
                        ),
                        _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__2,
                    );
                    v___x_3673_ = lean_int_mod(v_year_3649_, v___x_3672_);
                    v___x_3674_ = lean_int_dec_eq(v___x_3673_, v___x_3666_);
                    crate::leanh::lean_dec(v___x_3673_);
                    if v___x_3674_ == 0 {
                        if v___x_3671_ == 0 {
                            state = 10;
                            continue;
                        } else {
                            v___y_3655_ = v___x_3671_;
                            state = 7;
                            continue;
                        }
                    } else {
                        state = 10;
                        continue;
                    }
                }
            }
            7 => {
                v_max_3656_ = l_Std_Time_Month_Ordinal_days(v___y_3655_, v_month_3610_);
                v___x_3657_ = lean_int_dec_lt(v_max_3656_, v_day_3650_);
                if v___x_3657_ == 0 {
                    crate::leanh::lean_dec(v_max_3656_);
                    if v_isShared_3653_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3652_, 1, v_month_3610_);
                        v___x_3659_ = v___x_3652_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_3660_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3660_, 0, v_year_3649_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3660_, 1, v_month_3610_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3660_, 2, v_day_3650_);
                        v___x_3659_ = v_reuseFailAlloc_3660_;
                        state = 8;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_day_3650_);
                    if v_isShared_3653_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3652_, 2, v_max_3656_);
                        crate::leanh::lean_ctor_set(v___x_3652_, 1, v_month_3610_);
                        v___x_3662_ = v___x_3652_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_3663_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3663_, 0, v_year_3649_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3663_, 1, v_month_3610_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3663_, 2, v_max_3656_);
                        v___x_3662_ = v_reuseFailAlloc_3663_;
                        state = 9;
                        continue;
                    }
                }
            }
            8 => {
                v___y_3618_ = v___x_3659_;
                state = 2;
                continue;
            }
            9 => {
                v___y_3618_ = v___x_3662_;
                state = 2;
                continue;
            }
            10 => {
                v___x_3668_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_dayOfYear___closed__1),
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_dayOfYear___closed__1_once),
                    _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__1,
                );
                v___x_3669_ = lean_int_mod(v_year_3649_, v___x_3668_);
                v___x_3670_ = lean_int_dec_eq(v___x_3669_, v___x_3666_);
                crate::leanh::lean_dec(v___x_3669_);
                v___y_3655_ = v___x_3670_;
                state = 7;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_ZonedDateTime_withMonthRollOver(
    mut v_dt_3680_: *mut crate::leanh::LeanObject,
    mut v_month_3681_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_3682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rules_3683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3686_: u8 = 0;
    let mut v_date_3687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_3688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_3689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3692_: u8 = 0;
    let mut v_year_3693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_day_3694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_wt_3698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ltt_3699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tz_3700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_3701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_3703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3719_: u8 = 0;
    let mut v_isSharedCheck_3720_: u8 = 0;
    let mut v_unused_3721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_3682_ = crate::leanh::lean_ctor_get(v_dt_3680_, 0);
                v_rules_3683_ = crate::leanh::lean_ctor_get(v_dt_3680_, 2);
                v_isSharedCheck_3720_ = (!crate::leanh::lean_is_exclusive(v_dt_3680_)) as u8;
                if v_isSharedCheck_3720_ == 0 {
                    v_unused_3721_ = crate::leanh::lean_ctor_get(v_dt_3680_, 3);
                    crate::leanh::lean_dec(v_unused_3721_);
                    v_unused_3722_ = crate::leanh::lean_ctor_get(v_dt_3680_, 1);
                    crate::leanh::lean_dec(v_unused_3722_);
                    v___x_3685_ = v_dt_3680_;
                    v_isShared_3686_ = v_isSharedCheck_3720_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_rules_3683_);
                    crate::leanh::lean_inc(v_date_3682_);
                    crate::leanh::lean_dec(v_dt_3680_);
                    v___x_3685_ = crate::leanh::lean_box(0);
                    v_isShared_3686_ = v_isSharedCheck_3720_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_date_3687_ = lean_thunk_get_own(v_date_3682_);
                crate::leanh::lean_dec_ref(v_date_3682_);
                v_date_3688_ = crate::leanh::lean_ctor_get(v_date_3687_, 0);
                v_time_3689_ = crate::leanh::lean_ctor_get(v_date_3687_, 1);
                v_isSharedCheck_3719_ = (!crate::leanh::lean_is_exclusive(v_date_3687_)) as u8;
                if v_isSharedCheck_3719_ == 0 {
                    v___x_3691_ = v_date_3687_;
                    v_isShared_3692_ = v_isSharedCheck_3719_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_time_3689_);
                    crate::leanh::lean_inc(v_date_3688_);
                    crate::leanh::lean_dec(v_date_3687_);
                    v___x_3691_ = crate::leanh::lean_box(0);
                    v_isShared_3692_ = v_isSharedCheck_3719_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_year_3693_ = crate::leanh::lean_ctor_get(v_date_3688_, 0);
                crate::leanh::lean_inc(v_year_3693_);
                v_day_3694_ = crate::leanh::lean_ctor_get(v_date_3688_, 2);
                crate::leanh::lean_inc(v_day_3694_);
                crate::leanh::lean_dec_ref(v_date_3688_);
                v___x_3695_ =
                    l_Std_Time_PlainDate_rollOver(v_year_3693_, v_month_3681_, v_day_3694_);
                crate::leanh::lean_dec(v_day_3694_);
                if v_isShared_3692_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3691_, 0, v___x_3695_);
                    v___x_3697_ = v___x_3691_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3718_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3718_, 0, v___x_3695_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3718_, 1, v_time_3689_);
                    v___x_3697_ = v_reuseFailAlloc_3718_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_inc_ref(v___x_3697_);
                v_wt_3698_ = l_Std_Time_PlainDateTime_toWallTime(v___x_3697_);
                crate::leanh::lean_inc_ref(v_rules_3683_);
                v_ltt_3699_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(
                    v_rules_3683_,
                    v_wt_3698_,
                );
                v_tz_3700_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_3699_);
                crate::leanh::lean_dec_ref(v_ltt_3699_);
                v_offset_3701_ = crate::leanh::lean_ctor_get(v_tz_3700_, 0);
                crate::leanh::lean_inc(v_offset_3701_);
                v_second_3702_ = crate::leanh::lean_ctor_get(v_wt_3698_, 0);
                crate::leanh::lean_inc(v_second_3702_);
                v_nano_3703_ = crate::leanh::lean_ctor_get(v_wt_3698_, 1);
                crate::leanh::lean_inc(v_nano_3703_);
                crate::leanh::lean_dec_ref(v_wt_3698_);
                v___f_3704_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3704_, 0, v___x_3697_);
                v___x_3705_ = lean_mk_thunk(v___f_3704_);
                v___x_3706_ = lean_int_neg(v_offset_3701_);
                crate::leanh::lean_dec(v_offset_3701_);
                v___x_3707_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
                );
                v___x_3708_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3709_ = lean_int_mul(v_second_3702_, v___x_3708_);
                crate::leanh::lean_dec(v_second_3702_);
                v___x_3710_ = lean_int_add(v___x_3709_, v_nano_3703_);
                crate::leanh::lean_dec(v_nano_3703_);
                crate::leanh::lean_dec(v___x_3709_);
                v___x_3711_ = lean_int_mul(v___x_3706_, v___x_3708_);
                crate::leanh::lean_dec(v___x_3706_);
                v___x_3712_ = lean_int_add(v___x_3711_, v___x_3707_);
                crate::leanh::lean_dec(v___x_3711_);
                v___x_3713_ = lean_int_add(v___x_3710_, v___x_3712_);
                crate::leanh::lean_dec(v___x_3712_);
                crate::leanh::lean_dec(v___x_3710_);
                v___x_3714_ = l_Std_Time_Duration_ofNanoseconds(v___x_3713_);
                crate::leanh::lean_dec(v___x_3713_);
                if v_isShared_3686_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3685_, 3, v_tz_3700_);
                    crate::leanh::lean_ctor_set(v___x_3685_, 1, v___x_3714_);
                    crate::leanh::lean_ctor_set(v___x_3685_, 0, v___x_3705_);
                    v___x_3716_ = v___x_3685_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3717_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3717_, 0, v___x_3705_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3717_, 1, v___x_3714_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3717_, 2, v_rules_3683_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3717_, 3, v_tz_3700_);
                    v___x_3716_ = v_reuseFailAlloc_3717_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3716_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_ZonedDateTime_withYearClip(
    mut v_dt_3723_: *mut crate::leanh::LeanObject,
    mut v_year_3724_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_3725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rules_3726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3729_: u8 = 0;
    let mut v_date_3730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_3733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3736_: u8 = 0;
    let mut v___x_3738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_wt_3739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ltt_3740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tz_3741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_3742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_3744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3760_: u8 = 0;
    let mut v_unused_3761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_3762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_month_3763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_day_3764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3767_: u8 = 0;
    let mut v___y_3769_: u8 = 0;
    let mut v_max_3770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3771_: u8 = 0;
    let mut v___x_3773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3784_: u8 = 0;
    let mut v___x_3785_: u8 = 0;
    let mut v___x_3786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3788_: u8 = 0;
    let mut v_isSharedCheck_3789_: u8 = 0;
    let mut v_unused_3790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3791_: u8 = 0;
    let mut v_unused_3792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_3725_ = crate::leanh::lean_ctor_get(v_dt_3723_, 0);
                v_rules_3726_ = crate::leanh::lean_ctor_get(v_dt_3723_, 2);
                v_isSharedCheck_3791_ = (!crate::leanh::lean_is_exclusive(v_dt_3723_)) as u8;
                if v_isSharedCheck_3791_ == 0 {
                    v_unused_3792_ = crate::leanh::lean_ctor_get(v_dt_3723_, 3);
                    crate::leanh::lean_dec(v_unused_3792_);
                    v_unused_3793_ = crate::leanh::lean_ctor_get(v_dt_3723_, 1);
                    crate::leanh::lean_dec(v_unused_3793_);
                    v___x_3728_ = v_dt_3723_;
                    v_isShared_3729_ = v_isSharedCheck_3791_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_rules_3726_);
                    crate::leanh::lean_inc(v_date_3725_);
                    crate::leanh::lean_dec(v_dt_3723_);
                    v___x_3728_ = crate::leanh::lean_box(0);
                    v_isShared_3729_ = v_isSharedCheck_3791_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_date_3730_ = lean_thunk_get_own(v_date_3725_);
                crate::leanh::lean_dec_ref(v_date_3725_);
                v_date_3762_ = crate::leanh::lean_ctor_get(v_date_3730_, 0);
                crate::leanh::lean_inc_ref(v_date_3762_);
                v_month_3763_ = crate::leanh::lean_ctor_get(v_date_3762_, 1);
                v_day_3764_ = crate::leanh::lean_ctor_get(v_date_3762_, 2);
                v_isSharedCheck_3789_ = (!crate::leanh::lean_is_exclusive(v_date_3762_)) as u8;
                if v_isSharedCheck_3789_ == 0 {
                    v_unused_3790_ = crate::leanh::lean_ctor_get(v_date_3762_, 0);
                    crate::leanh::lean_dec(v_unused_3790_);
                    v___x_3766_ = v_date_3762_;
                    v_isShared_3767_ = v_isSharedCheck_3789_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_day_3764_);
                    crate::leanh::lean_inc(v_month_3763_);
                    crate::leanh::lean_dec(v_date_3762_);
                    v___x_3766_ = crate::leanh::lean_box(0);
                    v_isShared_3767_ = v_isSharedCheck_3789_;
                    state = 6;
                    continue;
                }
            }
            2 => {
                v_time_3733_ = crate::leanh::lean_ctor_get(v_date_3730_, 1);
                v_isSharedCheck_3760_ = (!crate::leanh::lean_is_exclusive(v_date_3730_)) as u8;
                if v_isSharedCheck_3760_ == 0 {
                    v_unused_3761_ = crate::leanh::lean_ctor_get(v_date_3730_, 0);
                    crate::leanh::lean_dec(v_unused_3761_);
                    v___x_3735_ = v_date_3730_;
                    v_isShared_3736_ = v_isSharedCheck_3760_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_time_3733_);
                    crate::leanh::lean_dec(v_date_3730_);
                    v___x_3735_ = crate::leanh::lean_box(0);
                    v_isShared_3736_ = v_isSharedCheck_3760_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3736_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3735_, 0, v___y_3732_);
                    v___x_3738_ = v___x_3735_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3759_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3759_, 0, v___y_3732_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3759_, 1, v_time_3733_);
                    v___x_3738_ = v_reuseFailAlloc_3759_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                crate::leanh::lean_inc_ref(v___x_3738_);
                v_wt_3739_ = l_Std_Time_PlainDateTime_toWallTime(v___x_3738_);
                crate::leanh::lean_inc_ref(v_rules_3726_);
                v_ltt_3740_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(
                    v_rules_3726_,
                    v_wt_3739_,
                );
                v_tz_3741_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_3740_);
                crate::leanh::lean_dec_ref(v_ltt_3740_);
                v_offset_3742_ = crate::leanh::lean_ctor_get(v_tz_3741_, 0);
                crate::leanh::lean_inc(v_offset_3742_);
                v_second_3743_ = crate::leanh::lean_ctor_get(v_wt_3739_, 0);
                crate::leanh::lean_inc(v_second_3743_);
                v_nano_3744_ = crate::leanh::lean_ctor_get(v_wt_3739_, 1);
                crate::leanh::lean_inc(v_nano_3744_);
                crate::leanh::lean_dec_ref(v_wt_3739_);
                v___f_3745_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3745_, 0, v___x_3738_);
                v___x_3746_ = lean_mk_thunk(v___f_3745_);
                v___x_3747_ = lean_int_neg(v_offset_3742_);
                crate::leanh::lean_dec(v_offset_3742_);
                v___x_3748_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
                );
                v___x_3749_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3750_ = lean_int_mul(v_second_3743_, v___x_3749_);
                crate::leanh::lean_dec(v_second_3743_);
                v___x_3751_ = lean_int_add(v___x_3750_, v_nano_3744_);
                crate::leanh::lean_dec(v_nano_3744_);
                crate::leanh::lean_dec(v___x_3750_);
                v___x_3752_ = lean_int_mul(v___x_3747_, v___x_3749_);
                crate::leanh::lean_dec(v___x_3747_);
                v___x_3753_ = lean_int_add(v___x_3752_, v___x_3748_);
                crate::leanh::lean_dec(v___x_3752_);
                v___x_3754_ = lean_int_add(v___x_3751_, v___x_3753_);
                crate::leanh::lean_dec(v___x_3753_);
                crate::leanh::lean_dec(v___x_3751_);
                v___x_3755_ = l_Std_Time_Duration_ofNanoseconds(v___x_3754_);
                crate::leanh::lean_dec(v___x_3754_);
                if v_isShared_3729_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3728_, 3, v_tz_3741_);
                    crate::leanh::lean_ctor_set(v___x_3728_, 1, v___x_3755_);
                    crate::leanh::lean_ctor_set(v___x_3728_, 0, v___x_3746_);
                    v___x_3757_ = v___x_3728_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3758_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3758_, 0, v___x_3746_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3758_, 1, v___x_3755_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3758_, 2, v_rules_3726_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3758_, 3, v_tz_3741_);
                    v___x_3757_ = v_reuseFailAlloc_3758_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3757_;
            }
            6 => {
                v___x_3778_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_dayOfYear___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_dayOfYear___closed__0_once),
                    _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__0,
                );
                v___x_3779_ = lean_int_mod(v_year_3724_, v___x_3778_);
                v___x_3780_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0,
                );
                v___x_3785_ = lean_int_dec_eq(v___x_3779_, v___x_3780_);
                crate::leanh::lean_dec(v___x_3779_);
                if v___x_3785_ == 0 {
                    v___y_3769_ = v___x_3785_;
                    state = 7;
                    continue;
                } else {
                    v___x_3786_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_dayOfYear___closed__2),
                        core::ptr::addr_of_mut!(
                            l_Std_Time_ZonedDateTime_dayOfYear___closed__2_once
                        ),
                        _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__2,
                    );
                    v___x_3787_ = lean_int_mod(v_year_3724_, v___x_3786_);
                    v___x_3788_ = lean_int_dec_eq(v___x_3787_, v___x_3780_);
                    crate::leanh::lean_dec(v___x_3787_);
                    if v___x_3788_ == 0 {
                        if v___x_3785_ == 0 {
                            state = 10;
                            continue;
                        } else {
                            v___y_3769_ = v___x_3785_;
                            state = 7;
                            continue;
                        }
                    } else {
                        state = 10;
                        continue;
                    }
                }
            }
            7 => {
                v_max_3770_ = l_Std_Time_Month_Ordinal_days(v___y_3769_, v_month_3763_);
                v___x_3771_ = lean_int_dec_lt(v_max_3770_, v_day_3764_);
                if v___x_3771_ == 0 {
                    crate::leanh::lean_dec(v_max_3770_);
                    if v_isShared_3767_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3766_, 0, v_year_3724_);
                        v___x_3773_ = v___x_3766_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_3774_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3774_, 0, v_year_3724_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3774_, 1, v_month_3763_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3774_, 2, v_day_3764_);
                        v___x_3773_ = v_reuseFailAlloc_3774_;
                        state = 8;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_day_3764_);
                    if v_isShared_3767_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3766_, 2, v_max_3770_);
                        crate::leanh::lean_ctor_set(v___x_3766_, 0, v_year_3724_);
                        v___x_3776_ = v___x_3766_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_3777_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3777_, 0, v_year_3724_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3777_, 1, v_month_3763_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3777_, 2, v_max_3770_);
                        v___x_3776_ = v_reuseFailAlloc_3777_;
                        state = 9;
                        continue;
                    }
                }
            }
            8 => {
                v___y_3732_ = v___x_3773_;
                state = 2;
                continue;
            }
            9 => {
                v___y_3732_ = v___x_3776_;
                state = 2;
                continue;
            }
            10 => {
                v___x_3782_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_dayOfYear___closed__1),
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_dayOfYear___closed__1_once),
                    _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__1,
                );
                v___x_3783_ = lean_int_mod(v_year_3724_, v___x_3782_);
                v___x_3784_ = lean_int_dec_eq(v___x_3783_, v___x_3780_);
                crate::leanh::lean_dec(v___x_3783_);
                v___y_3769_ = v___x_3784_;
                state = 7;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_ZonedDateTime_withYearRollOver(
    mut v_dt_3794_: *mut crate::leanh::LeanObject,
    mut v_year_3795_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_3796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rules_3797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3800_: u8 = 0;
    let mut v_date_3801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_3802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_3803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3806_: u8 = 0;
    let mut v_month_3807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_day_3808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_wt_3812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ltt_3813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tz_3814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_3815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_3817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3833_: u8 = 0;
    let mut v_isSharedCheck_3834_: u8 = 0;
    let mut v_unused_3835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_3796_ = crate::leanh::lean_ctor_get(v_dt_3794_, 0);
                v_rules_3797_ = crate::leanh::lean_ctor_get(v_dt_3794_, 2);
                v_isSharedCheck_3834_ = (!crate::leanh::lean_is_exclusive(v_dt_3794_)) as u8;
                if v_isSharedCheck_3834_ == 0 {
                    v_unused_3835_ = crate::leanh::lean_ctor_get(v_dt_3794_, 3);
                    crate::leanh::lean_dec(v_unused_3835_);
                    v_unused_3836_ = crate::leanh::lean_ctor_get(v_dt_3794_, 1);
                    crate::leanh::lean_dec(v_unused_3836_);
                    v___x_3799_ = v_dt_3794_;
                    v_isShared_3800_ = v_isSharedCheck_3834_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_rules_3797_);
                    crate::leanh::lean_inc(v_date_3796_);
                    crate::leanh::lean_dec(v_dt_3794_);
                    v___x_3799_ = crate::leanh::lean_box(0);
                    v_isShared_3800_ = v_isSharedCheck_3834_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_date_3801_ = lean_thunk_get_own(v_date_3796_);
                crate::leanh::lean_dec_ref(v_date_3796_);
                v_date_3802_ = crate::leanh::lean_ctor_get(v_date_3801_, 0);
                v_time_3803_ = crate::leanh::lean_ctor_get(v_date_3801_, 1);
                v_isSharedCheck_3833_ = (!crate::leanh::lean_is_exclusive(v_date_3801_)) as u8;
                if v_isSharedCheck_3833_ == 0 {
                    v___x_3805_ = v_date_3801_;
                    v_isShared_3806_ = v_isSharedCheck_3833_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_time_3803_);
                    crate::leanh::lean_inc(v_date_3802_);
                    crate::leanh::lean_dec(v_date_3801_);
                    v___x_3805_ = crate::leanh::lean_box(0);
                    v_isShared_3806_ = v_isSharedCheck_3833_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_month_3807_ = crate::leanh::lean_ctor_get(v_date_3802_, 1);
                crate::leanh::lean_inc(v_month_3807_);
                v_day_3808_ = crate::leanh::lean_ctor_get(v_date_3802_, 2);
                crate::leanh::lean_inc(v_day_3808_);
                crate::leanh::lean_dec_ref(v_date_3802_);
                v___x_3809_ =
                    l_Std_Time_PlainDate_rollOver(v_year_3795_, v_month_3807_, v_day_3808_);
                crate::leanh::lean_dec(v_day_3808_);
                if v_isShared_3806_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3805_, 0, v___x_3809_);
                    v___x_3811_ = v___x_3805_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3832_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3832_, 0, v___x_3809_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3832_, 1, v_time_3803_);
                    v___x_3811_ = v_reuseFailAlloc_3832_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_inc_ref(v___x_3811_);
                v_wt_3812_ = l_Std_Time_PlainDateTime_toWallTime(v___x_3811_);
                crate::leanh::lean_inc_ref(v_rules_3797_);
                v_ltt_3813_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(
                    v_rules_3797_,
                    v_wt_3812_,
                );
                v_tz_3814_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_3813_);
                crate::leanh::lean_dec_ref(v_ltt_3813_);
                v_offset_3815_ = crate::leanh::lean_ctor_get(v_tz_3814_, 0);
                crate::leanh::lean_inc(v_offset_3815_);
                v_second_3816_ = crate::leanh::lean_ctor_get(v_wt_3812_, 0);
                crate::leanh::lean_inc(v_second_3816_);
                v_nano_3817_ = crate::leanh::lean_ctor_get(v_wt_3812_, 1);
                crate::leanh::lean_inc(v_nano_3817_);
                crate::leanh::lean_dec_ref(v_wt_3812_);
                v___f_3818_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3818_, 0, v___x_3811_);
                v___x_3819_ = lean_mk_thunk(v___f_3818_);
                v___x_3820_ = lean_int_neg(v_offset_3815_);
                crate::leanh::lean_dec(v_offset_3815_);
                v___x_3821_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
                );
                v___x_3822_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3823_ = lean_int_mul(v_second_3816_, v___x_3822_);
                crate::leanh::lean_dec(v_second_3816_);
                v___x_3824_ = lean_int_add(v___x_3823_, v_nano_3817_);
                crate::leanh::lean_dec(v_nano_3817_);
                crate::leanh::lean_dec(v___x_3823_);
                v___x_3825_ = lean_int_mul(v___x_3820_, v___x_3822_);
                crate::leanh::lean_dec(v___x_3820_);
                v___x_3826_ = lean_int_add(v___x_3825_, v___x_3821_);
                crate::leanh::lean_dec(v___x_3825_);
                v___x_3827_ = lean_int_add(v___x_3824_, v___x_3826_);
                crate::leanh::lean_dec(v___x_3826_);
                crate::leanh::lean_dec(v___x_3824_);
                v___x_3828_ = l_Std_Time_Duration_ofNanoseconds(v___x_3827_);
                crate::leanh::lean_dec(v___x_3827_);
                if v_isShared_3800_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3799_, 3, v_tz_3814_);
                    crate::leanh::lean_ctor_set(v___x_3799_, 1, v___x_3828_);
                    crate::leanh::lean_ctor_set(v___x_3799_, 0, v___x_3819_);
                    v___x_3830_ = v___x_3799_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3831_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3831_, 0, v___x_3819_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3831_, 1, v___x_3828_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3831_, 2, v_rules_3797_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3831_, 3, v_tz_3814_);
                    v___x_3830_ = v_reuseFailAlloc_3831_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3830_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_ZonedDateTime_withHours(
    mut v_dt_3837_: *mut crate::leanh::LeanObject,
    mut v_hour_3838_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_3839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rules_3840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3843_: u8 = 0;
    let mut v_date_3844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_3845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_3846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3849_: u8 = 0;
    let mut v_minute_3850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_3852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3855_: u8 = 0;
    let mut v___x_3857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_wt_3860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ltt_3861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tz_3862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_3863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_3865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3882_: u8 = 0;
    let mut v_unused_3883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3884_: u8 = 0;
    let mut v_isSharedCheck_3885_: u8 = 0;
    let mut v_unused_3886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_3839_ = crate::leanh::lean_ctor_get(v_dt_3837_, 0);
                v_rules_3840_ = crate::leanh::lean_ctor_get(v_dt_3837_, 2);
                v_isSharedCheck_3885_ = (!crate::leanh::lean_is_exclusive(v_dt_3837_)) as u8;
                if v_isSharedCheck_3885_ == 0 {
                    v_unused_3886_ = crate::leanh::lean_ctor_get(v_dt_3837_, 3);
                    crate::leanh::lean_dec(v_unused_3886_);
                    v_unused_3887_ = crate::leanh::lean_ctor_get(v_dt_3837_, 1);
                    crate::leanh::lean_dec(v_unused_3887_);
                    v___x_3842_ = v_dt_3837_;
                    v_isShared_3843_ = v_isSharedCheck_3885_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_rules_3840_);
                    crate::leanh::lean_inc(v_date_3839_);
                    crate::leanh::lean_dec(v_dt_3837_);
                    v___x_3842_ = crate::leanh::lean_box(0);
                    v_isShared_3843_ = v_isSharedCheck_3885_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_date_3844_ = lean_thunk_get_own(v_date_3839_);
                crate::leanh::lean_dec_ref(v_date_3839_);
                v_time_3845_ = crate::leanh::lean_ctor_get(v_date_3844_, 1);
                v_date_3846_ = crate::leanh::lean_ctor_get(v_date_3844_, 0);
                v_isSharedCheck_3884_ = (!crate::leanh::lean_is_exclusive(v_date_3844_)) as u8;
                if v_isSharedCheck_3884_ == 0 {
                    v___x_3848_ = v_date_3844_;
                    v_isShared_3849_ = v_isSharedCheck_3884_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_time_3845_);
                    crate::leanh::lean_inc(v_date_3846_);
                    crate::leanh::lean_dec(v_date_3844_);
                    v___x_3848_ = crate::leanh::lean_box(0);
                    v_isShared_3849_ = v_isSharedCheck_3884_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_minute_3850_ = crate::leanh::lean_ctor_get(v_time_3845_, 1);
                v_second_3851_ = crate::leanh::lean_ctor_get(v_time_3845_, 2);
                v_nanosecond_3852_ = crate::leanh::lean_ctor_get(v_time_3845_, 3);
                v_isSharedCheck_3882_ = (!crate::leanh::lean_is_exclusive(v_time_3845_)) as u8;
                if v_isSharedCheck_3882_ == 0 {
                    v_unused_3883_ = crate::leanh::lean_ctor_get(v_time_3845_, 0);
                    crate::leanh::lean_dec(v_unused_3883_);
                    v___x_3854_ = v_time_3845_;
                    v_isShared_3855_ = v_isSharedCheck_3882_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nanosecond_3852_);
                    crate::leanh::lean_inc(v_second_3851_);
                    crate::leanh::lean_inc(v_minute_3850_);
                    crate::leanh::lean_dec(v_time_3845_);
                    v___x_3854_ = crate::leanh::lean_box(0);
                    v_isShared_3855_ = v_isSharedCheck_3882_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3855_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3854_, 0, v_hour_3838_);
                    v___x_3857_ = v___x_3854_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3881_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3881_, 0, v_hour_3838_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3881_, 1, v_minute_3850_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3881_, 2, v_second_3851_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3881_, 3, v_nanosecond_3852_);
                    v___x_3857_ = v_reuseFailAlloc_3881_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3849_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3848_, 1, v___x_3857_);
                    v___x_3859_ = v___x_3848_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3880_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3880_, 0, v_date_3846_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3880_, 1, v___x_3857_);
                    v___x_3859_ = v_reuseFailAlloc_3880_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                crate::leanh::lean_inc_ref(v___x_3859_);
                v_wt_3860_ = l_Std_Time_PlainDateTime_toWallTime(v___x_3859_);
                crate::leanh::lean_inc_ref(v_rules_3840_);
                v_ltt_3861_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(
                    v_rules_3840_,
                    v_wt_3860_,
                );
                v_tz_3862_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_3861_);
                crate::leanh::lean_dec_ref(v_ltt_3861_);
                v_offset_3863_ = crate::leanh::lean_ctor_get(v_tz_3862_, 0);
                crate::leanh::lean_inc(v_offset_3863_);
                v_second_3864_ = crate::leanh::lean_ctor_get(v_wt_3860_, 0);
                crate::leanh::lean_inc(v_second_3864_);
                v_nano_3865_ = crate::leanh::lean_ctor_get(v_wt_3860_, 1);
                crate::leanh::lean_inc(v_nano_3865_);
                crate::leanh::lean_dec_ref(v_wt_3860_);
                v___f_3866_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3866_, 0, v___x_3859_);
                v___x_3867_ = lean_mk_thunk(v___f_3866_);
                v___x_3868_ = lean_int_neg(v_offset_3863_);
                crate::leanh::lean_dec(v_offset_3863_);
                v___x_3869_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
                );
                v___x_3870_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3871_ = lean_int_mul(v_second_3864_, v___x_3870_);
                crate::leanh::lean_dec(v_second_3864_);
                v___x_3872_ = lean_int_add(v___x_3871_, v_nano_3865_);
                crate::leanh::lean_dec(v_nano_3865_);
                crate::leanh::lean_dec(v___x_3871_);
                v___x_3873_ = lean_int_mul(v___x_3868_, v___x_3870_);
                crate::leanh::lean_dec(v___x_3868_);
                v___x_3874_ = lean_int_add(v___x_3873_, v___x_3869_);
                crate::leanh::lean_dec(v___x_3873_);
                v___x_3875_ = lean_int_add(v___x_3872_, v___x_3874_);
                crate::leanh::lean_dec(v___x_3874_);
                crate::leanh::lean_dec(v___x_3872_);
                v___x_3876_ = l_Std_Time_Duration_ofNanoseconds(v___x_3875_);
                crate::leanh::lean_dec(v___x_3875_);
                if v_isShared_3843_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3842_, 3, v_tz_3862_);
                    crate::leanh::lean_ctor_set(v___x_3842_, 1, v___x_3876_);
                    crate::leanh::lean_ctor_set(v___x_3842_, 0, v___x_3867_);
                    v___x_3878_ = v___x_3842_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3879_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3879_, 0, v___x_3867_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3879_, 1, v___x_3876_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3879_, 2, v_rules_3840_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3879_, 3, v_tz_3862_);
                    v___x_3878_ = v_reuseFailAlloc_3879_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3878_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_ZonedDateTime_withMinutes(
    mut v_dt_3888_: *mut crate::leanh::LeanObject,
    mut v_minute_3889_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_3890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rules_3891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3894_: u8 = 0;
    let mut v_date_3895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_3896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_3897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3900_: u8 = 0;
    let mut v_hour_3901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_3903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3906_: u8 = 0;
    let mut v___x_3908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_wt_3911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ltt_3912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tz_3913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_3914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_3916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3933_: u8 = 0;
    let mut v_unused_3934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3935_: u8 = 0;
    let mut v_isSharedCheck_3936_: u8 = 0;
    let mut v_unused_3937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_3890_ = crate::leanh::lean_ctor_get(v_dt_3888_, 0);
                v_rules_3891_ = crate::leanh::lean_ctor_get(v_dt_3888_, 2);
                v_isSharedCheck_3936_ = (!crate::leanh::lean_is_exclusive(v_dt_3888_)) as u8;
                if v_isSharedCheck_3936_ == 0 {
                    v_unused_3937_ = crate::leanh::lean_ctor_get(v_dt_3888_, 3);
                    crate::leanh::lean_dec(v_unused_3937_);
                    v_unused_3938_ = crate::leanh::lean_ctor_get(v_dt_3888_, 1);
                    crate::leanh::lean_dec(v_unused_3938_);
                    v___x_3893_ = v_dt_3888_;
                    v_isShared_3894_ = v_isSharedCheck_3936_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_rules_3891_);
                    crate::leanh::lean_inc(v_date_3890_);
                    crate::leanh::lean_dec(v_dt_3888_);
                    v___x_3893_ = crate::leanh::lean_box(0);
                    v_isShared_3894_ = v_isSharedCheck_3936_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_date_3895_ = lean_thunk_get_own(v_date_3890_);
                crate::leanh::lean_dec_ref(v_date_3890_);
                v_time_3896_ = crate::leanh::lean_ctor_get(v_date_3895_, 1);
                v_date_3897_ = crate::leanh::lean_ctor_get(v_date_3895_, 0);
                v_isSharedCheck_3935_ = (!crate::leanh::lean_is_exclusive(v_date_3895_)) as u8;
                if v_isSharedCheck_3935_ == 0 {
                    v___x_3899_ = v_date_3895_;
                    v_isShared_3900_ = v_isSharedCheck_3935_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_time_3896_);
                    crate::leanh::lean_inc(v_date_3897_);
                    crate::leanh::lean_dec(v_date_3895_);
                    v___x_3899_ = crate::leanh::lean_box(0);
                    v_isShared_3900_ = v_isSharedCheck_3935_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_hour_3901_ = crate::leanh::lean_ctor_get(v_time_3896_, 0);
                v_second_3902_ = crate::leanh::lean_ctor_get(v_time_3896_, 2);
                v_nanosecond_3903_ = crate::leanh::lean_ctor_get(v_time_3896_, 3);
                v_isSharedCheck_3933_ = (!crate::leanh::lean_is_exclusive(v_time_3896_)) as u8;
                if v_isSharedCheck_3933_ == 0 {
                    v_unused_3934_ = crate::leanh::lean_ctor_get(v_time_3896_, 1);
                    crate::leanh::lean_dec(v_unused_3934_);
                    v___x_3905_ = v_time_3896_;
                    v_isShared_3906_ = v_isSharedCheck_3933_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nanosecond_3903_);
                    crate::leanh::lean_inc(v_second_3902_);
                    crate::leanh::lean_inc(v_hour_3901_);
                    crate::leanh::lean_dec(v_time_3896_);
                    v___x_3905_ = crate::leanh::lean_box(0);
                    v_isShared_3906_ = v_isSharedCheck_3933_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3906_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3905_, 1, v_minute_3889_);
                    v___x_3908_ = v___x_3905_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3932_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3932_, 0, v_hour_3901_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3932_, 1, v_minute_3889_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3932_, 2, v_second_3902_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3932_, 3, v_nanosecond_3903_);
                    v___x_3908_ = v_reuseFailAlloc_3932_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3900_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3899_, 1, v___x_3908_);
                    v___x_3910_ = v___x_3899_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3931_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3931_, 0, v_date_3897_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3931_, 1, v___x_3908_);
                    v___x_3910_ = v_reuseFailAlloc_3931_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                crate::leanh::lean_inc_ref(v___x_3910_);
                v_wt_3911_ = l_Std_Time_PlainDateTime_toWallTime(v___x_3910_);
                crate::leanh::lean_inc_ref(v_rules_3891_);
                v_ltt_3912_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(
                    v_rules_3891_,
                    v_wt_3911_,
                );
                v_tz_3913_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_3912_);
                crate::leanh::lean_dec_ref(v_ltt_3912_);
                v_offset_3914_ = crate::leanh::lean_ctor_get(v_tz_3913_, 0);
                crate::leanh::lean_inc(v_offset_3914_);
                v_second_3915_ = crate::leanh::lean_ctor_get(v_wt_3911_, 0);
                crate::leanh::lean_inc(v_second_3915_);
                v_nano_3916_ = crate::leanh::lean_ctor_get(v_wt_3911_, 1);
                crate::leanh::lean_inc(v_nano_3916_);
                crate::leanh::lean_dec_ref(v_wt_3911_);
                v___f_3917_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3917_, 0, v___x_3910_);
                v___x_3918_ = lean_mk_thunk(v___f_3917_);
                v___x_3919_ = lean_int_neg(v_offset_3914_);
                crate::leanh::lean_dec(v_offset_3914_);
                v___x_3920_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
                );
                v___x_3921_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3922_ = lean_int_mul(v_second_3915_, v___x_3921_);
                crate::leanh::lean_dec(v_second_3915_);
                v___x_3923_ = lean_int_add(v___x_3922_, v_nano_3916_);
                crate::leanh::lean_dec(v_nano_3916_);
                crate::leanh::lean_dec(v___x_3922_);
                v___x_3924_ = lean_int_mul(v___x_3919_, v___x_3921_);
                crate::leanh::lean_dec(v___x_3919_);
                v___x_3925_ = lean_int_add(v___x_3924_, v___x_3920_);
                crate::leanh::lean_dec(v___x_3924_);
                v___x_3926_ = lean_int_add(v___x_3923_, v___x_3925_);
                crate::leanh::lean_dec(v___x_3925_);
                crate::leanh::lean_dec(v___x_3923_);
                v___x_3927_ = l_Std_Time_Duration_ofNanoseconds(v___x_3926_);
                crate::leanh::lean_dec(v___x_3926_);
                if v_isShared_3894_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3893_, 3, v_tz_3913_);
                    crate::leanh::lean_ctor_set(v___x_3893_, 1, v___x_3927_);
                    crate::leanh::lean_ctor_set(v___x_3893_, 0, v___x_3918_);
                    v___x_3929_ = v___x_3893_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3930_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3930_, 0, v___x_3918_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3930_, 1, v___x_3927_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3930_, 2, v_rules_3891_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3930_, 3, v_tz_3913_);
                    v___x_3929_ = v_reuseFailAlloc_3930_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3929_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_ZonedDateTime_withSeconds(
    mut v_dt_3939_: *mut crate::leanh::LeanObject,
    mut v_second_3940_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_3941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rules_3942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3945_: u8 = 0;
    let mut v_date_3946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_3947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_3948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3951_: u8 = 0;
    let mut v_hour_3952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_minute_3953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_3954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3957_: u8 = 0;
    let mut v___x_3959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_wt_3962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ltt_3963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tz_3964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_3965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_3967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3984_: u8 = 0;
    let mut v_unused_3985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3986_: u8 = 0;
    let mut v_isSharedCheck_3987_: u8 = 0;
    let mut v_unused_3988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_3941_ = crate::leanh::lean_ctor_get(v_dt_3939_, 0);
                v_rules_3942_ = crate::leanh::lean_ctor_get(v_dt_3939_, 2);
                v_isSharedCheck_3987_ = (!crate::leanh::lean_is_exclusive(v_dt_3939_)) as u8;
                if v_isSharedCheck_3987_ == 0 {
                    v_unused_3988_ = crate::leanh::lean_ctor_get(v_dt_3939_, 3);
                    crate::leanh::lean_dec(v_unused_3988_);
                    v_unused_3989_ = crate::leanh::lean_ctor_get(v_dt_3939_, 1);
                    crate::leanh::lean_dec(v_unused_3989_);
                    v___x_3944_ = v_dt_3939_;
                    v_isShared_3945_ = v_isSharedCheck_3987_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_rules_3942_);
                    crate::leanh::lean_inc(v_date_3941_);
                    crate::leanh::lean_dec(v_dt_3939_);
                    v___x_3944_ = crate::leanh::lean_box(0);
                    v_isShared_3945_ = v_isSharedCheck_3987_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_date_3946_ = lean_thunk_get_own(v_date_3941_);
                crate::leanh::lean_dec_ref(v_date_3941_);
                v_time_3947_ = crate::leanh::lean_ctor_get(v_date_3946_, 1);
                v_date_3948_ = crate::leanh::lean_ctor_get(v_date_3946_, 0);
                v_isSharedCheck_3986_ = (!crate::leanh::lean_is_exclusive(v_date_3946_)) as u8;
                if v_isSharedCheck_3986_ == 0 {
                    v___x_3950_ = v_date_3946_;
                    v_isShared_3951_ = v_isSharedCheck_3986_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_time_3947_);
                    crate::leanh::lean_inc(v_date_3948_);
                    crate::leanh::lean_dec(v_date_3946_);
                    v___x_3950_ = crate::leanh::lean_box(0);
                    v_isShared_3951_ = v_isSharedCheck_3986_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_hour_3952_ = crate::leanh::lean_ctor_get(v_time_3947_, 0);
                v_minute_3953_ = crate::leanh::lean_ctor_get(v_time_3947_, 1);
                v_nanosecond_3954_ = crate::leanh::lean_ctor_get(v_time_3947_, 3);
                v_isSharedCheck_3984_ = (!crate::leanh::lean_is_exclusive(v_time_3947_)) as u8;
                if v_isSharedCheck_3984_ == 0 {
                    v_unused_3985_ = crate::leanh::lean_ctor_get(v_time_3947_, 2);
                    crate::leanh::lean_dec(v_unused_3985_);
                    v___x_3956_ = v_time_3947_;
                    v_isShared_3957_ = v_isSharedCheck_3984_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nanosecond_3954_);
                    crate::leanh::lean_inc(v_minute_3953_);
                    crate::leanh::lean_inc(v_hour_3952_);
                    crate::leanh::lean_dec(v_time_3947_);
                    v___x_3956_ = crate::leanh::lean_box(0);
                    v_isShared_3957_ = v_isSharedCheck_3984_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3957_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3956_, 2, v_second_3940_);
                    v___x_3959_ = v___x_3956_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3983_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3983_, 0, v_hour_3952_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3983_, 1, v_minute_3953_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3983_, 2, v_second_3940_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3983_, 3, v_nanosecond_3954_);
                    v___x_3959_ = v_reuseFailAlloc_3983_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3951_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3950_, 1, v___x_3959_);
                    v___x_3961_ = v___x_3950_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3982_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3982_, 0, v_date_3948_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3982_, 1, v___x_3959_);
                    v___x_3961_ = v_reuseFailAlloc_3982_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                crate::leanh::lean_inc_ref(v___x_3961_);
                v_wt_3962_ = l_Std_Time_PlainDateTime_toWallTime(v___x_3961_);
                crate::leanh::lean_inc_ref(v_rules_3942_);
                v_ltt_3963_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(
                    v_rules_3942_,
                    v_wt_3962_,
                );
                v_tz_3964_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_3963_);
                crate::leanh::lean_dec_ref(v_ltt_3963_);
                v_offset_3965_ = crate::leanh::lean_ctor_get(v_tz_3964_, 0);
                crate::leanh::lean_inc(v_offset_3965_);
                v_second_3966_ = crate::leanh::lean_ctor_get(v_wt_3962_, 0);
                crate::leanh::lean_inc(v_second_3966_);
                v_nano_3967_ = crate::leanh::lean_ctor_get(v_wt_3962_, 1);
                crate::leanh::lean_inc(v_nano_3967_);
                crate::leanh::lean_dec_ref(v_wt_3962_);
                v___f_3968_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3968_, 0, v___x_3961_);
                v___x_3969_ = lean_mk_thunk(v___f_3968_);
                v___x_3970_ = lean_int_neg(v_offset_3965_);
                crate::leanh::lean_dec(v_offset_3965_);
                v___x_3971_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
                );
                v___x_3972_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3973_ = lean_int_mul(v_second_3966_, v___x_3972_);
                crate::leanh::lean_dec(v_second_3966_);
                v___x_3974_ = lean_int_add(v___x_3973_, v_nano_3967_);
                crate::leanh::lean_dec(v_nano_3967_);
                crate::leanh::lean_dec(v___x_3973_);
                v___x_3975_ = lean_int_mul(v___x_3970_, v___x_3972_);
                crate::leanh::lean_dec(v___x_3970_);
                v___x_3976_ = lean_int_add(v___x_3975_, v___x_3971_);
                crate::leanh::lean_dec(v___x_3975_);
                v___x_3977_ = lean_int_add(v___x_3974_, v___x_3976_);
                crate::leanh::lean_dec(v___x_3976_);
                crate::leanh::lean_dec(v___x_3974_);
                v___x_3978_ = l_Std_Time_Duration_ofNanoseconds(v___x_3977_);
                crate::leanh::lean_dec(v___x_3977_);
                if v_isShared_3945_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3944_, 3, v_tz_3964_);
                    crate::leanh::lean_ctor_set(v___x_3944_, 1, v___x_3978_);
                    crate::leanh::lean_ctor_set(v___x_3944_, 0, v___x_3969_);
                    v___x_3980_ = v___x_3944_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3981_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3981_, 0, v___x_3969_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3981_, 1, v___x_3978_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3981_, 2, v_rules_3942_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3981_, 3, v_tz_3964_);
                    v___x_3980_ = v_reuseFailAlloc_3981_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3980_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Std_Time_ZonedDateTime_withMilliseconds___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3990_ = crate::leanh::lean_unsigned_to_nat(1000);
    v___x_3991_ = lean_nat_to_int(v___x_3990_);
    return v___x_3991_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_withMilliseconds(
    mut v_dt_3992_: *mut crate::leanh::LeanObject,
    mut v_millis_3993_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_3994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rules_3995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3998_: u8 = 0;
    let mut v_date_3999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_4000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_4001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4004_: u8 = 0;
    let mut v_hour_4005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_minute_4006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_4007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_4008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4011_: u8 = 0;
    let mut v___x_4012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_wt_4021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ltt_4022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tz_4023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_4024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_4025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_4026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4043_: u8 = 0;
    let mut v_isSharedCheck_4044_: u8 = 0;
    let mut v_isSharedCheck_4045_: u8 = 0;
    let mut v_unused_4046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_3994_ = crate::leanh::lean_ctor_get(v_dt_3992_, 0);
                v_rules_3995_ = crate::leanh::lean_ctor_get(v_dt_3992_, 2);
                v_isSharedCheck_4045_ = (!crate::leanh::lean_is_exclusive(v_dt_3992_)) as u8;
                if v_isSharedCheck_4045_ == 0 {
                    v_unused_4046_ = crate::leanh::lean_ctor_get(v_dt_3992_, 3);
                    crate::leanh::lean_dec(v_unused_4046_);
                    v_unused_4047_ = crate::leanh::lean_ctor_get(v_dt_3992_, 1);
                    crate::leanh::lean_dec(v_unused_4047_);
                    v___x_3997_ = v_dt_3992_;
                    v_isShared_3998_ = v_isSharedCheck_4045_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_rules_3995_);
                    crate::leanh::lean_inc(v_date_3994_);
                    crate::leanh::lean_dec(v_dt_3992_);
                    v___x_3997_ = crate::leanh::lean_box(0);
                    v_isShared_3998_ = v_isSharedCheck_4045_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_date_3999_ = lean_thunk_get_own(v_date_3994_);
                crate::leanh::lean_dec_ref(v_date_3994_);
                v_time_4000_ = crate::leanh::lean_ctor_get(v_date_3999_, 1);
                v_date_4001_ = crate::leanh::lean_ctor_get(v_date_3999_, 0);
                v_isSharedCheck_4044_ = (!crate::leanh::lean_is_exclusive(v_date_3999_)) as u8;
                if v_isSharedCheck_4044_ == 0 {
                    v___x_4003_ = v_date_3999_;
                    v_isShared_4004_ = v_isSharedCheck_4044_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_time_4000_);
                    crate::leanh::lean_inc(v_date_4001_);
                    crate::leanh::lean_dec(v_date_3999_);
                    v___x_4003_ = crate::leanh::lean_box(0);
                    v_isShared_4004_ = v_isSharedCheck_4044_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_hour_4005_ = crate::leanh::lean_ctor_get(v_time_4000_, 0);
                v_minute_4006_ = crate::leanh::lean_ctor_get(v_time_4000_, 1);
                v_second_4007_ = crate::leanh::lean_ctor_get(v_time_4000_, 2);
                v_nanosecond_4008_ = crate::leanh::lean_ctor_get(v_time_4000_, 3);
                v_isSharedCheck_4043_ = (!crate::leanh::lean_is_exclusive(v_time_4000_)) as u8;
                if v_isSharedCheck_4043_ == 0 {
                    v___x_4010_ = v_time_4000_;
                    v_isShared_4011_ = v_isSharedCheck_4043_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nanosecond_4008_);
                    crate::leanh::lean_inc(v_second_4007_);
                    crate::leanh::lean_inc(v_minute_4006_);
                    crate::leanh::lean_inc(v_hour_4005_);
                    crate::leanh::lean_dec(v_time_4000_);
                    v___x_4010_ = crate::leanh::lean_box(0);
                    v_isShared_4011_ = v_isSharedCheck_4043_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4012_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_withMilliseconds___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_withMilliseconds___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_withMilliseconds___closed__0,
                );
                v___x_4013_ = lean_int_emod(v_nanosecond_4008_, v___x_4012_);
                crate::leanh::lean_dec(v_nanosecond_4008_);
                v___x_4014_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_millisecond___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_millisecond___closed__0_once),
                    _init_l_Std_Time_ZonedDateTime_millisecond___closed__0,
                );
                v___x_4015_ = lean_int_mul(v_millis_3993_, v___x_4014_);
                v___x_4016_ = lean_int_add(v___x_4015_, v___x_4013_);
                crate::leanh::lean_dec(v___x_4013_);
                crate::leanh::lean_dec(v___x_4015_);
                if v_isShared_4011_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4010_, 3, v___x_4016_);
                    v___x_4018_ = v___x_4010_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4042_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4042_, 0, v_hour_4005_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4042_, 1, v_minute_4006_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4042_, 2, v_second_4007_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4042_, 3, v___x_4016_);
                    v___x_4018_ = v_reuseFailAlloc_4042_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4004_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4003_, 1, v___x_4018_);
                    v___x_4020_ = v___x_4003_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4041_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4041_, 0, v_date_4001_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4041_, 1, v___x_4018_);
                    v___x_4020_ = v_reuseFailAlloc_4041_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                crate::leanh::lean_inc_ref(v___x_4020_);
                v_wt_4021_ = l_Std_Time_PlainDateTime_toWallTime(v___x_4020_);
                crate::leanh::lean_inc_ref(v_rules_3995_);
                v_ltt_4022_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(
                    v_rules_3995_,
                    v_wt_4021_,
                );
                v_tz_4023_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_4022_);
                crate::leanh::lean_dec_ref(v_ltt_4022_);
                v_offset_4024_ = crate::leanh::lean_ctor_get(v_tz_4023_, 0);
                crate::leanh::lean_inc(v_offset_4024_);
                v_second_4025_ = crate::leanh::lean_ctor_get(v_wt_4021_, 0);
                crate::leanh::lean_inc(v_second_4025_);
                v_nano_4026_ = crate::leanh::lean_ctor_get(v_wt_4021_, 1);
                crate::leanh::lean_inc(v_nano_4026_);
                crate::leanh::lean_dec_ref(v_wt_4021_);
                v___f_4027_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4027_, 0, v___x_4020_);
                v___x_4028_ = lean_mk_thunk(v___f_4027_);
                v___x_4029_ = lean_int_neg(v_offset_4024_);
                crate::leanh::lean_dec(v_offset_4024_);
                v___x_4030_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
                );
                v___x_4031_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_4032_ = lean_int_mul(v_second_4025_, v___x_4031_);
                crate::leanh::lean_dec(v_second_4025_);
                v___x_4033_ = lean_int_add(v___x_4032_, v_nano_4026_);
                crate::leanh::lean_dec(v_nano_4026_);
                crate::leanh::lean_dec(v___x_4032_);
                v___x_4034_ = lean_int_mul(v___x_4029_, v___x_4031_);
                crate::leanh::lean_dec(v___x_4029_);
                v___x_4035_ = lean_int_add(v___x_4034_, v___x_4030_);
                crate::leanh::lean_dec(v___x_4034_);
                v___x_4036_ = lean_int_add(v___x_4033_, v___x_4035_);
                crate::leanh::lean_dec(v___x_4035_);
                crate::leanh::lean_dec(v___x_4033_);
                v___x_4037_ = l_Std_Time_Duration_ofNanoseconds(v___x_4036_);
                crate::leanh::lean_dec(v___x_4036_);
                if v_isShared_3998_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3997_, 3, v_tz_4023_);
                    crate::leanh::lean_ctor_set(v___x_3997_, 1, v___x_4037_);
                    crate::leanh::lean_ctor_set(v___x_3997_, 0, v___x_4028_);
                    v___x_4039_ = v___x_3997_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4040_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4040_, 0, v___x_4028_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4040_, 1, v___x_4037_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4040_, 2, v_rules_3995_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4040_, 3, v_tz_4023_);
                    v___x_4039_ = v_reuseFailAlloc_4040_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4039_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_ZonedDateTime_withMilliseconds___boxed(
    mut v_dt_4048_: *mut crate::leanh::LeanObject,
    mut v_millis_4049_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4050_ = l_Std_Time_ZonedDateTime_withMilliseconds(v_dt_4048_, v_millis_4049_);
    crate::leanh::lean_dec(v_millis_4049_);
    return v_res_4050_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_withNanoseconds(
    mut v_dt_4051_: *mut crate::leanh::LeanObject,
    mut v_nano_4052_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_4053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rules_4054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4057_: u8 = 0;
    let mut v_date_4058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_4059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_4060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4063_: u8 = 0;
    let mut v_hour_4064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_minute_4065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_4066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4069_: u8 = 0;
    let mut v___x_4071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_wt_4074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ltt_4075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tz_4076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_4077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_4078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_4079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4096_: u8 = 0;
    let mut v_unused_4097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4098_: u8 = 0;
    let mut v_isSharedCheck_4099_: u8 = 0;
    let mut v_unused_4100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_4053_ = crate::leanh::lean_ctor_get(v_dt_4051_, 0);
                v_rules_4054_ = crate::leanh::lean_ctor_get(v_dt_4051_, 2);
                v_isSharedCheck_4099_ = (!crate::leanh::lean_is_exclusive(v_dt_4051_)) as u8;
                if v_isSharedCheck_4099_ == 0 {
                    v_unused_4100_ = crate::leanh::lean_ctor_get(v_dt_4051_, 3);
                    crate::leanh::lean_dec(v_unused_4100_);
                    v_unused_4101_ = crate::leanh::lean_ctor_get(v_dt_4051_, 1);
                    crate::leanh::lean_dec(v_unused_4101_);
                    v___x_4056_ = v_dt_4051_;
                    v_isShared_4057_ = v_isSharedCheck_4099_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_rules_4054_);
                    crate::leanh::lean_inc(v_date_4053_);
                    crate::leanh::lean_dec(v_dt_4051_);
                    v___x_4056_ = crate::leanh::lean_box(0);
                    v_isShared_4057_ = v_isSharedCheck_4099_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_date_4058_ = lean_thunk_get_own(v_date_4053_);
                crate::leanh::lean_dec_ref(v_date_4053_);
                v_time_4059_ = crate::leanh::lean_ctor_get(v_date_4058_, 1);
                v_date_4060_ = crate::leanh::lean_ctor_get(v_date_4058_, 0);
                v_isSharedCheck_4098_ = (!crate::leanh::lean_is_exclusive(v_date_4058_)) as u8;
                if v_isSharedCheck_4098_ == 0 {
                    v___x_4062_ = v_date_4058_;
                    v_isShared_4063_ = v_isSharedCheck_4098_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_time_4059_);
                    crate::leanh::lean_inc(v_date_4060_);
                    crate::leanh::lean_dec(v_date_4058_);
                    v___x_4062_ = crate::leanh::lean_box(0);
                    v_isShared_4063_ = v_isSharedCheck_4098_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_hour_4064_ = crate::leanh::lean_ctor_get(v_time_4059_, 0);
                v_minute_4065_ = crate::leanh::lean_ctor_get(v_time_4059_, 1);
                v_second_4066_ = crate::leanh::lean_ctor_get(v_time_4059_, 2);
                v_isSharedCheck_4096_ = (!crate::leanh::lean_is_exclusive(v_time_4059_)) as u8;
                if v_isSharedCheck_4096_ == 0 {
                    v_unused_4097_ = crate::leanh::lean_ctor_get(v_time_4059_, 3);
                    crate::leanh::lean_dec(v_unused_4097_);
                    v___x_4068_ = v_time_4059_;
                    v_isShared_4069_ = v_isSharedCheck_4096_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_second_4066_);
                    crate::leanh::lean_inc(v_minute_4065_);
                    crate::leanh::lean_inc(v_hour_4064_);
                    crate::leanh::lean_dec(v_time_4059_);
                    v___x_4068_ = crate::leanh::lean_box(0);
                    v_isShared_4069_ = v_isSharedCheck_4096_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4069_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4068_, 3, v_nano_4052_);
                    v___x_4071_ = v___x_4068_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4095_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4095_, 0, v_hour_4064_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4095_, 1, v_minute_4065_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4095_, 2, v_second_4066_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4095_, 3, v_nano_4052_);
                    v___x_4071_ = v_reuseFailAlloc_4095_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4063_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4062_, 1, v___x_4071_);
                    v___x_4073_ = v___x_4062_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4094_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4094_, 0, v_date_4060_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4094_, 1, v___x_4071_);
                    v___x_4073_ = v_reuseFailAlloc_4094_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                crate::leanh::lean_inc_ref(v___x_4073_);
                v_wt_4074_ = l_Std_Time_PlainDateTime_toWallTime(v___x_4073_);
                crate::leanh::lean_inc_ref(v_rules_4054_);
                v_ltt_4075_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(
                    v_rules_4054_,
                    v_wt_4074_,
                );
                v_tz_4076_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_4075_);
                crate::leanh::lean_dec_ref(v_ltt_4075_);
                v_offset_4077_ = crate::leanh::lean_ctor_get(v_tz_4076_, 0);
                crate::leanh::lean_inc(v_offset_4077_);
                v_second_4078_ = crate::leanh::lean_ctor_get(v_wt_4074_, 0);
                crate::leanh::lean_inc(v_second_4078_);
                v_nano_4079_ = crate::leanh::lean_ctor_get(v_wt_4074_, 1);
                crate::leanh::lean_inc(v_nano_4079_);
                crate::leanh::lean_dec_ref(v_wt_4074_);
                v___f_4080_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4080_, 0, v___x_4073_);
                v___x_4081_ = lean_mk_thunk(v___f_4080_);
                v___x_4082_ = lean_int_neg(v_offset_4077_);
                crate::leanh::lean_dec(v_offset_4077_);
                v___x_4083_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
                );
                v___x_4084_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_4085_ = lean_int_mul(v_second_4078_, v___x_4084_);
                crate::leanh::lean_dec(v_second_4078_);
                v___x_4086_ = lean_int_add(v___x_4085_, v_nano_4079_);
                crate::leanh::lean_dec(v_nano_4079_);
                crate::leanh::lean_dec(v___x_4085_);
                v___x_4087_ = lean_int_mul(v___x_4082_, v___x_4084_);
                crate::leanh::lean_dec(v___x_4082_);
                v___x_4088_ = lean_int_add(v___x_4087_, v___x_4083_);
                crate::leanh::lean_dec(v___x_4087_);
                v___x_4089_ = lean_int_add(v___x_4086_, v___x_4088_);
                crate::leanh::lean_dec(v___x_4088_);
                crate::leanh::lean_dec(v___x_4086_);
                v___x_4090_ = l_Std_Time_Duration_ofNanoseconds(v___x_4089_);
                crate::leanh::lean_dec(v___x_4089_);
                if v_isShared_4057_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4056_, 3, v_tz_4076_);
                    crate::leanh::lean_ctor_set(v___x_4056_, 1, v___x_4090_);
                    crate::leanh::lean_ctor_set(v___x_4056_, 0, v___x_4081_);
                    v___x_4092_ = v___x_4056_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4093_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4093_, 0, v___x_4081_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4093_, 1, v___x_4090_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4093_, 2, v_rules_4054_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4093_, 3, v_tz_4076_);
                    v___x_4092_ = v_reuseFailAlloc_4093_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4092_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_ZonedDateTime_inLeapYear(
    mut v_date_4102_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_date_4103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_4105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_year_4106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4113_: u8 = 0;
    let mut v___x_4114_: u8 = 0;
    let mut v___x_4115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4117_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_4103_ = crate::leanh::lean_ctor_get(v_date_4102_, 0);
                v___x_4104_ = lean_thunk_get_own(v_date_4103_);
                v_date_4105_ = crate::leanh::lean_ctor_get(v___x_4104_, 0);
                crate::leanh::lean_inc_ref(v_date_4105_);
                crate::leanh::lean_dec(v___x_4104_);
                v_year_4106_ = crate::leanh::lean_ctor_get(v_date_4105_, 0);
                crate::leanh::lean_inc(v_year_4106_);
                crate::leanh::lean_dec_ref(v_date_4105_);
                v___x_4107_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_dayOfYear___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_dayOfYear___closed__0_once),
                    _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__0,
                );
                v___x_4108_ = lean_int_mod(v_year_4106_, v___x_4107_);
                v___x_4109_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0,
                );
                v___x_4114_ = lean_int_dec_eq(v___x_4108_, v___x_4109_);
                crate::leanh::lean_dec(v___x_4108_);
                if v___x_4114_ == 0 {
                    crate::leanh::lean_dec(v_year_4106_);
                    return v___x_4114_;
                } else {
                    v___x_4115_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_dayOfYear___closed__2),
                        core::ptr::addr_of_mut!(
                            l_Std_Time_ZonedDateTime_dayOfYear___closed__2_once
                        ),
                        _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__2,
                    );
                    v___x_4116_ = lean_int_mod(v_year_4106_, v___x_4115_);
                    v___x_4117_ = lean_int_dec_eq(v___x_4116_, v___x_4109_);
                    crate::leanh::lean_dec(v___x_4116_);
                    if v___x_4117_ == 0 {
                        if v___x_4114_ == 0 {
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_year_4106_);
                            return v___x_4114_;
                        }
                    } else {
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4111_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_dayOfYear___closed__1),
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_dayOfYear___closed__1_once),
                    _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__1,
                );
                v___x_4112_ = lean_int_mod(v_year_4106_, v___x_4111_);
                crate::leanh::lean_dec(v_year_4106_);
                v___x_4113_ = lean_int_dec_eq(v___x_4112_, v___x_4109_);
                crate::leanh::lean_dec(v___x_4112_);
                return v___x_4113_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_ZonedDateTime_inLeapYear___boxed(
    mut v_date_4118_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4119_: u8 = 0;
    let mut v_r_4120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4119_ = l_Std_Time_ZonedDateTime_inLeapYear(v_date_4118_);
    crate::leanh::lean_dec_ref(v_date_4118_);
    v_r_4120_ = crate::leanh::lean_box((v_res_4119_) as usize);
    return v_r_4120_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_toEpochDay(
    mut v_date_4121_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_4122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_4124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_date_4122_ = crate::leanh::lean_ctor_get(v_date_4121_, 0);
    v___x_4123_ = lean_thunk_get_own(v_date_4122_);
    v_date_4124_ = crate::leanh::lean_ctor_get(v___x_4123_, 0);
    crate::leanh::lean_inc_ref(v_date_4124_);
    crate::leanh::lean_dec(v___x_4123_);
    v___x_4125_ = l_Std_Time_PlainDate_toEpochDay(v_date_4124_);
    return v___x_4125_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_toEpochDay___boxed(
    mut v_date_4126_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4127_ = l_Std_Time_ZonedDateTime_toEpochDay(v_date_4126_);
    crate::leanh::lean_dec_ref(v_date_4126_);
    return v_res_4127_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_ofEpochDay(
    mut v_days_4128_: *mut crate::leanh::LeanObject,
    mut v_time_4129_: *mut crate::leanh::LeanObject,
    mut v_zt_4130_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_wt_4133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ltt_4134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tz_4135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_4136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_4137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_4138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4131_ = l_Std_Time_PlainDate_ofEpochDay(v_days_4128_);
    v___x_4132_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4132_, 0, v___x_4131_);
    crate::leanh::lean_ctor_set(v___x_4132_, 1, v_time_4129_);
    crate::leanh::lean_inc_ref(v___x_4132_);
    v_wt_4133_ = l_Std_Time_PlainDateTime_toWallTime(v___x_4132_);
    crate::leanh::lean_inc_ref(v_zt_4130_);
    v_ltt_4134_ =
        l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_zt_4130_, v_wt_4133_);
    v_tz_4135_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_4134_);
    crate::leanh::lean_dec_ref(v_ltt_4134_);
    v_offset_4136_ = crate::leanh::lean_ctor_get(v_tz_4135_, 0);
    crate::leanh::lean_inc(v_offset_4136_);
    v_second_4137_ = crate::leanh::lean_ctor_get(v_wt_4133_, 0);
    crate::leanh::lean_inc(v_second_4137_);
    v_nano_4138_ = crate::leanh::lean_ctor_get(v_wt_4133_, 1);
    crate::leanh::lean_inc(v_nano_4138_);
    crate::leanh::lean_dec_ref(v_wt_4133_);
    v___f_4139_ = crate::leanh::lean_alloc_closure(
        l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4139_, 0, v___x_4132_);
    v___x_4140_ = lean_mk_thunk(v___f_4139_);
    v___x_4141_ = lean_int_neg(v_offset_4136_);
    crate::leanh::lean_dec(v_offset_4136_);
    v___x_4142_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once),
        _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
    );
    v___x_4143_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once),
        _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
    );
    v___x_4144_ = lean_int_mul(v_second_4137_, v___x_4143_);
    crate::leanh::lean_dec(v_second_4137_);
    v___x_4145_ = lean_int_add(v___x_4144_, v_nano_4138_);
    crate::leanh::lean_dec(v_nano_4138_);
    crate::leanh::lean_dec(v___x_4144_);
    v___x_4146_ = lean_int_mul(v___x_4141_, v___x_4143_);
    crate::leanh::lean_dec(v___x_4141_);
    v___x_4147_ = lean_int_add(v___x_4146_, v___x_4142_);
    crate::leanh::lean_dec(v___x_4146_);
    v___x_4148_ = lean_int_add(v___x_4145_, v___x_4147_);
    crate::leanh::lean_dec(v___x_4147_);
    crate::leanh::lean_dec(v___x_4145_);
    v___x_4149_ = l_Std_Time_Duration_ofNanoseconds(v___x_4148_);
    crate::leanh::lean_dec(v___x_4148_);
    v___x_4150_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4150_, 0, v___x_4140_);
    crate::leanh::lean_ctor_set(v___x_4150_, 1, v___x_4149_);
    crate::leanh::lean_ctor_set(v___x_4150_, 2, v_zt_4130_);
    crate::leanh::lean_ctor_set(v___x_4150_, 3, v_tz_4135_);
    return v___x_4150_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_ofEpochDay___boxed(
    mut v_days_4151_: *mut crate::leanh::LeanObject,
    mut v_time_4152_: *mut crate::leanh::LeanObject,
    mut v_zt_4153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4154_ = l_Std_Time_ZonedDateTime_ofEpochDay(v_days_4151_, v_time_4152_, v_zt_4153_);
    crate::leanh::lean_dec(v_days_4151_);
    return v_res_4154_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_instHSubDuration___lam__0(
    mut v_x_4183_: *mut crate::leanh::LeanObject,
    mut v_y_4184_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_timestamp_4185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_timestamp_4186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_4187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_4188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_4189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_4190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_timestamp_4185_ = crate::leanh::lean_ctor_get(v_y_4184_, 1);
    v_timestamp_4186_ = crate::leanh::lean_ctor_get(v_x_4183_, 1);
    v_second_4187_ = crate::leanh::lean_ctor_get(v_timestamp_4185_, 0);
    v_nano_4188_ = crate::leanh::lean_ctor_get(v_timestamp_4185_, 1);
    v_second_4189_ = crate::leanh::lean_ctor_get(v_timestamp_4186_, 0);
    v_nano_4190_ = crate::leanh::lean_ctor_get(v_timestamp_4186_, 1);
    v___x_4191_ = lean_int_neg(v_second_4187_);
    v___x_4192_ = lean_int_neg(v_nano_4188_);
    v___x_4193_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once),
        _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
    );
    v___x_4194_ = lean_int_mul(v_second_4189_, v___x_4193_);
    v___x_4195_ = lean_int_add(v___x_4194_, v_nano_4190_);
    crate::leanh::lean_dec(v___x_4194_);
    v___x_4196_ = lean_int_mul(v___x_4191_, v___x_4193_);
    crate::leanh::lean_dec(v___x_4191_);
    v___x_4197_ = lean_int_add(v___x_4196_, v___x_4192_);
    crate::leanh::lean_dec(v___x_4192_);
    crate::leanh::lean_dec(v___x_4196_);
    v___x_4198_ = lean_int_add(v___x_4195_, v___x_4197_);
    crate::leanh::lean_dec(v___x_4197_);
    crate::leanh::lean_dec(v___x_4195_);
    v___x_4199_ = l_Std_Time_Duration_ofNanoseconds(v___x_4198_);
    crate::leanh::lean_dec(v___x_4198_);
    return v___x_4199_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_instHSubDuration___lam__0___boxed(
    mut v_x_4200_: *mut crate::leanh::LeanObject,
    mut v_y_4201_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4202_ = l_Std_Time_ZonedDateTime_instHSubDuration___lam__0(v_x_4200_, v_y_4201_);
    crate::leanh::lean_dec_ref(v_y_4201_);
    crate::leanh::lean_dec_ref(v_x_4200_);
    return v_res_4202_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_instHAddDuration___lam__0(
    mut v_x_4205_: *mut crate::leanh::LeanObject,
    mut v_y_4206_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_second_4207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_4208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nanos_4211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_second_4207_ = crate::leanh::lean_ctor_get(v_y_4206_, 0);
    v_nano_4208_ = crate::leanh::lean_ctor_get(v_y_4206_, 1);
    v___x_4209_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once),
        _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
    );
    v___x_4210_ = lean_int_mul(v_second_4207_, v___x_4209_);
    v_nanos_4211_ = lean_int_add(v___x_4210_, v_nano_4208_);
    crate::leanh::lean_dec(v___x_4210_);
    v___x_4212_ = l_Std_Time_ZonedDateTime_addNanoseconds(v_x_4205_, v_nanos_4211_);
    crate::leanh::lean_dec(v_nanos_4211_);
    return v___x_4212_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_instHAddDuration___lam__0___boxed(
    mut v_x_4213_: *mut crate::leanh::LeanObject,
    mut v_y_4214_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4215_ = l_Std_Time_ZonedDateTime_instHAddDuration___lam__0(v_x_4213_, v_y_4214_);
    crate::leanh::lean_dec_ref(v_y_4214_);
    return v_res_4215_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_instHSubDuration__1___lam__0(
    mut v_x_4218_: *mut crate::leanh::LeanObject,
    mut v_y_4219_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_second_4220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_4221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nanos_4224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_second_4220_ = crate::leanh::lean_ctor_get(v_y_4219_, 0);
    v_nano_4221_ = crate::leanh::lean_ctor_get(v_y_4219_, 1);
    v___x_4222_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once),
        _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
    );
    v___x_4223_ = lean_int_mul(v_second_4220_, v___x_4222_);
    v_nanos_4224_ = lean_int_add(v___x_4223_, v_nano_4221_);
    crate::leanh::lean_dec(v___x_4223_);
    v___x_4225_ = l_Std_Time_ZonedDateTime_subNanoseconds(v_x_4218_, v_nanos_4224_);
    crate::leanh::lean_dec(v_nanos_4224_);
    return v___x_4225_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_instHSubDuration__1___lam__0___boxed(
    mut v_x_4226_: *mut crate::leanh::LeanObject,
    mut v_y_4227_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4228_ = l_Std_Time_ZonedDateTime_instHSubDuration__1___lam__0(v_x_4226_, v_y_4227_);
    crate::leanh::lean_dec_ref(v_y_4227_);
    return v_res_4228_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Time_Zoned_ZonedDateTime(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Time_Zoned_DateTime(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Zoned_ZoneRules(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Time_DateTime_PlainDateTime(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Std_Time_instInhabitedZonedDateTime___private__1 =
        _init_l_Std_Time_instInhabitedZonedDateTime___private__1();
    crate::leanh::lean_mark_persistent(l_Std_Time_instInhabitedZonedDateTime___private__1);
    l_Std_Time_instInhabitedZonedDateTime = _init_l_Std_Time_instInhabitedZonedDateTime();
    crate::leanh::lean_mark_persistent(l_Std_Time_instInhabitedZonedDateTime);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Time_Zoned_ZonedDateTime(
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
pub unsafe fn initialize_Std_Time_Zoned_ZonedDateTime(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Time_Zoned_DateTime(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Time_Zoned_ZoneRules(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Time_DateTime_PlainDateTime(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Zoned_ZonedDateTime(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Time_Zoned_ZonedDateTime(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Time_Zoned_ZonedDateTime(builtin);
}
