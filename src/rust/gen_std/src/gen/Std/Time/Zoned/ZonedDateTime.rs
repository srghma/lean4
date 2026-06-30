// Lean compiler output
// Module: Std.Time.Zoned.ZonedDateTime
// Imports: Std.Time.Zoned.DateTime Std.Time.Zoned.ZoneRules Std.Time.DateTime.PlainDateTime
use crate::ffi::{
    lean_int_add, lean_int_dec_eq, lean_int_dec_lt, lean_int_ediv, lean_int_emod, lean_int_mod,
    lean_int_mul, lean_int_neg, lean_mk_thunk, lean_nat_to_int, lean_thunk_get_own,
};
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
pub static l_Std_Time_instInhabitedZonedDateTime___private__1___closed__0_value:
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
    m_fun: l_Std_Time_instInhabitedZonedDateTime___private__1___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instInhabitedZonedDateTime___private__1___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instInhabitedZonedDateTime___private__1___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_instInhabitedZonedDateTime___private__1___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedZonedDateTime___private__1___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instInhabitedZonedDateTime___private__1___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedZonedDateTime___private__1___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Std_Time_instInhabitedZonedDateTime___private__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_instInhabitedZonedDateTime: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_ZonedDateTime_ofTimestampWithZone___closed__0_value:
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
static mut l_Std_Time_ZonedDateTime_ofTimestampWithZone___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_ofTimestampWithZone___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_ZonedDateTime_millisecond___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_ZonedDateTime_millisecond___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_ZonedDateTime_dayOfYear___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_ZonedDateTime_dayOfYear___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_ZonedDateTime_dayOfYear___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_ZonedDateTime_dayOfYear___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_ZonedDateTime_dayOfYear___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_ZonedDateTime_dayOfYear___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_ZonedDateTime_addDays___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_ZonedDateTime_addDays___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_ZonedDateTime_addWeeks___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_ZonedDateTime_addWeeks___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_ZonedDateTime_addHours___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_ZonedDateTime_addHours___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_ZonedDateTime_addMinutes___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_ZonedDateTime_addMinutes___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_ZonedDateTime_withMilliseconds___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_ZonedDateTime_withMilliseconds___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_ZonedDateTime_instHAddOffset___closed__0_value:
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
    m_fun: l_Std_Time_ZonedDateTime_addDays___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_ZonedDateTime_instHAddOffset___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHAddOffset___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_ZonedDateTime_instHAddOffset: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHAddOffset___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_ZonedDateTime_instHSubOffset___closed__0_value:
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
    m_fun: l_Std_Time_ZonedDateTime_subDays___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_ZonedDateTime_instHSubOffset___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHSubOffset___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_ZonedDateTime_instHSubOffset: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHSubOffset___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_ZonedDateTime_instHAddOffset__1___closed__0_value:
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
    m_fun: l_Std_Time_ZonedDateTime_addWeeks___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_ZonedDateTime_instHAddOffset__1___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHAddOffset__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_ZonedDateTime_instHAddOffset__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHAddOffset__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_ZonedDateTime_instHSubOffset__1___closed__0_value:
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
    m_fun: l_Std_Time_ZonedDateTime_subWeeks___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_ZonedDateTime_instHSubOffset__1___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHSubOffset__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_ZonedDateTime_instHSubOffset__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHSubOffset__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_ZonedDateTime_instHAddOffset__2___closed__0_value:
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
    m_fun: l_Std_Time_ZonedDateTime_addHours___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_ZonedDateTime_instHAddOffset__2___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHAddOffset__2___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_ZonedDateTime_instHAddOffset__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHAddOffset__2___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_ZonedDateTime_instHSubOffset__2___closed__0_value:
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
    m_fun: l_Std_Time_ZonedDateTime_subHours___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_ZonedDateTime_instHSubOffset__2___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHSubOffset__2___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_ZonedDateTime_instHSubOffset__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHSubOffset__2___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_ZonedDateTime_instHAddOffset__3___closed__0_value:
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
    m_fun: l_Std_Time_ZonedDateTime_addMinutes___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_ZonedDateTime_instHAddOffset__3___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHAddOffset__3___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_ZonedDateTime_instHAddOffset__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHAddOffset__3___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_ZonedDateTime_instHSubOffset__3___closed__0_value:
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
    m_fun: l_Std_Time_ZonedDateTime_subMinutes___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_ZonedDateTime_instHSubOffset__3___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHSubOffset__3___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_ZonedDateTime_instHSubOffset__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHSubOffset__3___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_ZonedDateTime_instHAddOffset__4___closed__0_value:
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
    m_fun: l_Std_Time_ZonedDateTime_addSeconds___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_ZonedDateTime_instHAddOffset__4___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHAddOffset__4___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_ZonedDateTime_instHAddOffset__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHAddOffset__4___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_ZonedDateTime_instHSubOffset__4___closed__0_value:
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
    m_fun: l_Std_Time_ZonedDateTime_subSeconds___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_ZonedDateTime_instHSubOffset__4___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHSubOffset__4___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_ZonedDateTime_instHSubOffset__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHSubOffset__4___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_ZonedDateTime_instHAddOffset__5___closed__0_value:
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
    m_fun: l_Std_Time_ZonedDateTime_addMilliseconds___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_ZonedDateTime_instHAddOffset__5___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHAddOffset__5___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_ZonedDateTime_instHAddOffset__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHAddOffset__5___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_ZonedDateTime_instHSubOffset__5___closed__0_value:
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
    m_fun: l_Std_Time_ZonedDateTime_subMilliseconds___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_ZonedDateTime_instHSubOffset__5___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHSubOffset__5___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_ZonedDateTime_instHSubOffset__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHSubOffset__5___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_ZonedDateTime_instHAddOffset__6___closed__0_value:
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
    m_fun: l_Std_Time_ZonedDateTime_addNanoseconds___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_ZonedDateTime_instHAddOffset__6___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHAddOffset__6___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_ZonedDateTime_instHAddOffset__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHAddOffset__6___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_ZonedDateTime_instHSubOffset__6___closed__0_value:
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
    m_fun: l_Std_Time_ZonedDateTime_subNanoseconds___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_ZonedDateTime_instHSubOffset__6___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHSubOffset__6___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_ZonedDateTime_instHSubOffset__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHSubOffset__6___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_ZonedDateTime_instHSubDuration___closed__0_value:
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
    m_fun: l_Std_Time_ZonedDateTime_instHSubDuration___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_ZonedDateTime_instHSubDuration___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHSubDuration___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_ZonedDateTime_instHSubDuration: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHSubDuration___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_ZonedDateTime_instHAddDuration___closed__0_value:
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
    m_fun: l_Std_Time_ZonedDateTime_instHAddDuration___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_ZonedDateTime_instHAddDuration___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHAddDuration___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_ZonedDateTime_instHAddDuration: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHAddDuration___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_ZonedDateTime_instHSubDuration__1___closed__0_value:
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
    m_fun: l_Std_Time_ZonedDateTime_instHSubDuration__1___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_ZonedDateTime_instHSubDuration__1___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHSubDuration__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_ZonedDateTime_instHSubDuration__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHSubDuration__1___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Std_Time_instInhabitedZonedDateTime___private__1___lam__0(
    mut v_x_2116_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2117_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2117_ = l_Std_Time_instInhabitedPlainDateTime_default;
    return v___x_2117_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedZonedDateTime___private__1___closed__1()
-> *mut leanh::LeanObject {
    let mut v___f_2119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2119_ = l_Std_Time_instInhabitedZonedDateTime___private__1___closed__0;
    v___x_2120_ = lean_mk_thunk(v___f_2119_);
    return v___x_2120_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedZonedDateTime___private__1___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2121_ = l_Std_Time_instInhabitedTimeZone_default;
    v___x_2122_ = l_Std_Time_TimeZone_instInhabitedZoneRules_default;
    v___x_2123_ = l_Std_Time_instInhabitedTimestamp_default;
    v___x_2124_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedZonedDateTime___private__1___closed__1),
        core::ptr::addr_of_mut!(
            l_Std_Time_instInhabitedZonedDateTime___private__1___closed__1_once
        ),
        _init_l_Std_Time_instInhabitedZonedDateTime___private__1___closed__1,
    );
    v___x_2125_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_2125_, 0, v___x_2124_);
    leanh::lean_ctor_set(v___x_2125_, 1, v___x_2123_);
    leanh::lean_ctor_set(v___x_2125_, 2, v___x_2122_);
    leanh::lean_ctor_set(v___x_2125_, 3, v___x_2121_);
    return v___x_2125_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedZonedDateTime___private__1()
-> *mut leanh::LeanObject {
    let mut v___x_2126_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2126_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedZonedDateTime___private__1___closed__2),
        core::ptr::addr_of_mut!(
            l_Std_Time_instInhabitedZonedDateTime___private__1___closed__2_once
        ),
        _init_l_Std_Time_instInhabitedZonedDateTime___private__1___closed__2,
    );
    return v___x_2126_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedZonedDateTime() -> *mut leanh::LeanObject {
    let mut v___x_2127_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2127_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedZonedDateTime___private__1___closed__2),
        core::ptr::addr_of_mut!(
            l_Std_Time_instInhabitedZonedDateTime___private__1___closed__2_once
        ),
        _init_l_Std_Time_instInhabitedZonedDateTime___private__1___closed__2,
    );
    return v___x_2127_;
}
pub unsafe fn _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2128_ = leanh::lean_unsigned_to_nat(0);
    v___x_2129_ = lean_nat_to_int(v___x_2128_);
    return v___x_2129_;
}
pub unsafe fn _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2130_ = leanh::lean_unsigned_to_nat(1000000000);
    v___x_2131_ = lean_nat_to_int(v___x_2130_);
    return v___x_2131_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_ofTimestamp___lam__0(
    mut v___y_2132_: *mut leanh::LeanObject,
    mut v_tm_2133_: *mut leanh::LeanObject,
    mut v_x_2134_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_offset_2135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_2136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_offset_2135_ = leanh::lean_ctor_get(v___y_2132_, 0);
    v_second_2136_ = leanh::lean_ctor_get(v_tm_2133_, 0);
    v_nano_2137_ = leanh::lean_ctor_get(v_tm_2133_, 1);
    v___x_2138_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once),
        _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0,
    );
    v___x_2139_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once),
        _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
    );
    v___x_2140_ = lean_int_mul(v_second_2136_, v___x_2139_);
    v___x_2141_ = lean_int_add(v___x_2140_, v_nano_2137_);
    leanh::lean_dec(v___x_2140_);
    v___x_2142_ = lean_int_mul(v_offset_2135_, v___x_2139_);
    v___x_2143_ = lean_int_add(v___x_2142_, v___x_2138_);
    leanh::lean_dec(v___x_2142_);
    v___x_2144_ = lean_int_add(v___x_2141_, v___x_2143_);
    leanh::lean_dec(v___x_2143_);
    leanh::lean_dec(v___x_2141_);
    v___x_2145_ = l_Std_Time_Duration_ofNanoseconds(v___x_2144_);
    leanh::lean_dec(v___x_2144_);
    v___x_2146_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_2145_);
    return v___x_2146_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___boxed(
    mut v___y_2147_: *mut leanh::LeanObject,
    mut v_tm_2148_: *mut leanh::LeanObject,
    mut v_x_2149_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2150_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2150_ = l_Std_Time_ZonedDateTime_ofTimestamp___lam__0(v___y_2147_, v_tm_2148_, v_x_2149_);
    leanh::lean_dec_ref(v_tm_2148_);
    leanh::lean_dec_ref(v___y_2147_);
    return v_res_2150_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_ofTimestamp(
    mut v_tm_2151_: *mut leanh::LeanObject,
    mut v_rules_2152_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initialLocalTimeType_2158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_transitions_2159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_initialLocalTimeType_2158_ = leanh::lean_ctor_get(v_rules_2152_, 0);
                v_transitions_2159_ = leanh::lean_ctor_get(v_rules_2152_, 1);
                v___x_2160_ =
                    l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_2159_, v_tm_2151_);
                if leanh::lean_obj_tag(v___x_2160_) == 0 {
                    leanh::lean_dec_ref_known(v___x_2160_, 1);
                    v___x_2161_ =
                        l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_2158_);
                    v___y_2154_ = v___x_2161_;
                    state = 1;
                    continue;
                } else {
                    v_a_2162_ = leanh::lean_ctor_get(v___x_2160_, 0);
                    leanh::lean_inc(v_a_2162_);
                    leanh::lean_dec_ref_known(v___x_2160_, 1);
                    v___y_2154_ = v_a_2162_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc_ref(v_tm_2151_);
                leanh::lean_inc_ref(v___y_2154_);
                v___f_2155_ = leanh::lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___boxed as *mut core::ffi::c_void,
                    3,
                    2,
                );
                leanh::lean_closure_set(v___f_2155_, 0, v___y_2154_);
                leanh::lean_closure_set(v___f_2155_, 1, v_tm_2151_);
                v___x_2156_ = lean_mk_thunk(v___f_2155_);
                v___x_2157_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_2157_, 0, v___x_2156_);
                leanh::lean_ctor_set(v___x_2157_, 1, v_tm_2151_);
                leanh::lean_ctor_set(v___x_2157_, 2, v_rules_2152_);
                leanh::lean_ctor_set(v___x_2157_, 3, v___y_2154_);
                return v___x_2157_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__0(
    mut v_pdt_2163_: *mut leanh::LeanObject,
    mut v_x_2164_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v_pdt_2163_);
    return v_pdt_2163_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__0___boxed(
    mut v_pdt_2165_: *mut leanh::LeanObject,
    mut v_x_2166_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2167_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2167_ = l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__0(v_pdt_2165_, v_x_2166_);
    leanh::lean_dec_ref(v_pdt_2165_);
    return v_res_2167_;
}
pub unsafe fn _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2168_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once),
        _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0,
    );
    v___x_2169_ = lean_int_neg(v___x_2168_);
    return v___x_2169_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_ofPlainDateTime(
    mut v_pdt_2170_: *mut leanh::LeanObject,
    mut v_zr_2171_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_wt_2172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ltt_2173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tz_2174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_2175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_2176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_pdt_2170_);
    v_wt_2172_ = l_Std_Time_PlainDateTime_toWallTime(v_pdt_2170_);
    leanh::lean_inc_ref(v_zr_2171_);
    v_ltt_2173_ =
        l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_zr_2171_, v_wt_2172_);
    v_tz_2174_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_2173_);
    leanh::lean_dec_ref(v_ltt_2173_);
    v_offset_2175_ = leanh::lean_ctor_get(v_tz_2174_, 0);
    leanh::lean_inc(v_offset_2175_);
    v_second_2176_ = leanh::lean_ctor_get(v_wt_2172_, 0);
    leanh::lean_inc(v_second_2176_);
    v_nano_2177_ = leanh::lean_ctor_get(v_wt_2172_, 1);
    leanh::lean_inc(v_nano_2177_);
    leanh::lean_dec_ref(v_wt_2172_);
    v___f_2178_ = leanh::lean_alloc_closure(
        l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2178_, 0, v_pdt_2170_);
    v___x_2179_ = lean_mk_thunk(v___f_2178_);
    v___x_2180_ = lean_int_neg(v_offset_2175_);
    leanh::lean_dec(v_offset_2175_);
    v___x_2181_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once),
        _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
    );
    v___x_2182_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once),
        _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
    );
    v___x_2183_ = lean_int_mul(v_second_2176_, v___x_2182_);
    leanh::lean_dec(v_second_2176_);
    v___x_2184_ = lean_int_add(v___x_2183_, v_nano_2177_);
    leanh::lean_dec(v_nano_2177_);
    leanh::lean_dec(v___x_2183_);
    v___x_2185_ = lean_int_mul(v___x_2180_, v___x_2182_);
    leanh::lean_dec(v___x_2180_);
    v___x_2186_ = lean_int_add(v___x_2185_, v___x_2181_);
    leanh::lean_dec(v___x_2185_);
    v___x_2187_ = lean_int_add(v___x_2184_, v___x_2186_);
    leanh::lean_dec(v___x_2186_);
    leanh::lean_dec(v___x_2184_);
    v___x_2188_ = l_Std_Time_Duration_ofNanoseconds(v___x_2187_);
    leanh::lean_dec(v___x_2187_);
    v___x_2189_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_2189_, 0, v___x_2179_);
    leanh::lean_ctor_set(v___x_2189_, 1, v___x_2188_);
    leanh::lean_ctor_set(v___x_2189_, 2, v_zr_2171_);
    leanh::lean_ctor_set(v___x_2189_, 3, v_tz_2174_);
    return v___x_2189_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_ofTimestampWithZone___lam__0(
    mut v___y_2190_: *mut leanh::LeanObject,
    mut v_tm_2191_: *mut leanh::LeanObject,
    mut v___x_2192_: *mut leanh::LeanObject,
    mut v_x_2193_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_offset_2194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_2195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_offset_2194_ = leanh::lean_ctor_get(v___y_2190_, 0);
    v_second_2195_ = leanh::lean_ctor_get(v_tm_2191_, 0);
    v_nano_2196_ = leanh::lean_ctor_get(v_tm_2191_, 1);
    v___x_2197_ = lean_nat_to_int(v___x_2192_);
    v___x_2198_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once),
        _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
    );
    v___x_2199_ = lean_int_mul(v_second_2195_, v___x_2198_);
    v___x_2200_ = lean_int_add(v___x_2199_, v_nano_2196_);
    leanh::lean_dec(v___x_2199_);
    v___x_2201_ = lean_int_mul(v_offset_2194_, v___x_2198_);
    v___x_2202_ = lean_int_add(v___x_2201_, v___x_2197_);
    leanh::lean_dec(v___x_2197_);
    leanh::lean_dec(v___x_2201_);
    v___x_2203_ = lean_int_add(v___x_2200_, v___x_2202_);
    leanh::lean_dec(v___x_2202_);
    leanh::lean_dec(v___x_2200_);
    v___x_2204_ = l_Std_Time_Duration_ofNanoseconds(v___x_2203_);
    leanh::lean_dec(v___x_2203_);
    v___x_2205_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_2204_);
    return v___x_2205_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_ofTimestampWithZone___lam__0___boxed(
    mut v___y_2206_: *mut leanh::LeanObject,
    mut v_tm_2207_: *mut leanh::LeanObject,
    mut v___x_2208_: *mut leanh::LeanObject,
    mut v_x_2209_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2210_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2210_ = l_Std_Time_ZonedDateTime_ofTimestampWithZone___lam__0(
        v___y_2206_,
        v_tm_2207_,
        v___x_2208_,
        v_x_2209_,
    );
    leanh::lean_dec_ref(v_tm_2207_);
    leanh::lean_dec_ref(v___y_2206_);
    return v_res_2210_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_ofTimestampWithZone(
    mut v_tm_2213_: *mut leanh::LeanObject,
    mut v_tz_2214_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_offset_2215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_abbreviation_2217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isDST_2218_: u8 = 0;
    let mut v___x_2219_: u8 = 0;
    let mut v___x_2220_: u8 = 0;
    let mut v_ltt_2221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_offset_2215_ = leanh::lean_ctor_get(v_tz_2214_, 0);
                v_name_2216_ = leanh::lean_ctor_get(v_tz_2214_, 1);
                v_abbreviation_2217_ = leanh::lean_ctor_get(v_tz_2214_, 2);
                v_isDST_2218_ = leanh::lean_ctor_get_uint8(
                    v_tz_2214_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                );
                v___x_2219_ = 0;
                v___x_2220_ = 1;
                leanh::lean_inc_ref(v_name_2216_);
                leanh::lean_inc_ref(v_abbreviation_2217_);
                leanh::lean_inc(v_offset_2215_);
                v_ltt_2221_ = leanh::lean_alloc_ctor(0, 3, (3) as u32);
                leanh::lean_ctor_set(v_ltt_2221_, 0, v_offset_2215_);
                leanh::lean_ctor_set(v_ltt_2221_, 1, v_abbreviation_2217_);
                leanh::lean_ctor_set(v_ltt_2221_, 2, v_name_2216_);
                leanh::lean_ctor_set_uint8(
                    v_ltt_2221_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v_isDST_2218_,
                );
                leanh::lean_ctor_set_uint8(
                    v_ltt_2221_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 1) as u32,
                    v___x_2219_,
                );
                leanh::lean_ctor_set_uint8(
                    v_ltt_2221_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 2) as u32,
                    v___x_2220_,
                );
                v___x_2222_ = leanh::lean_unsigned_to_nat(0);
                v___x_2223_ = l_Std_Time_ZonedDateTime_ofTimestampWithZone___closed__0;
                leanh::lean_inc_ref(v_ltt_2221_);
                v___x_2224_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2224_, 0, v_ltt_2221_);
                leanh::lean_ctor_set(v___x_2224_, 1, v___x_2223_);
                v___x_2230_ = l_Std_Time_TimeZone_Transition_timezoneAt(v___x_2223_, v_tm_2213_);
                if leanh::lean_obj_tag(v___x_2230_) == 0 {
                    leanh::lean_dec_ref_known(v___x_2230_, 1);
                    v___x_2231_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_2221_);
                    leanh::lean_dec_ref_known(v_ltt_2221_, 3);
                    v___y_2226_ = v___x_2231_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec_ref_known(v_ltt_2221_, 3);
                    v_a_2232_ = leanh::lean_ctor_get(v___x_2230_, 0);
                    leanh::lean_inc(v_a_2232_);
                    leanh::lean_dec_ref_known(v___x_2230_, 1);
                    v___y_2226_ = v_a_2232_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc_ref(v_tm_2213_);
                leanh::lean_inc_ref(v___y_2226_);
                v___f_2227_ = leanh::lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_ofTimestampWithZone___lam__0___boxed
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                leanh::lean_closure_set(v___f_2227_, 0, v___y_2226_);
                leanh::lean_closure_set(v___f_2227_, 1, v_tm_2213_);
                leanh::lean_closure_set(v___f_2227_, 2, v___x_2222_);
                v___x_2228_ = lean_mk_thunk(v___f_2227_);
                v___x_2229_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_2229_, 0, v___x_2228_);
                leanh::lean_ctor_set(v___x_2229_, 1, v_tm_2213_);
                leanh::lean_ctor_set(v___x_2229_, 2, v___x_2224_);
                leanh::lean_ctor_set(v___x_2229_, 3, v___y_2226_);
                return v___x_2229_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_ZonedDateTime_ofTimestampWithZone___boxed(
    mut v_tm_2233_: *mut leanh::LeanObject,
    mut v_tz_2234_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2235_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2235_ = l_Std_Time_ZonedDateTime_ofTimestampWithZone(v_tm_2233_, v_tz_2234_);
    leanh::lean_dec_ref(v_tz_2234_);
    return v_res_2235_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone___lam__0(
    mut v_tm_2236_: *mut leanh::LeanObject,
    mut v_x_2237_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v_tm_2236_);
    return v_tm_2236_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone___lam__0___boxed(
    mut v_tm_2238_: *mut leanh::LeanObject,
    mut v_x_2239_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2240_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2240_ = l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone___lam__0(v_tm_2238_, v_x_2239_);
    leanh::lean_dec_ref(v_tm_2238_);
    return v_res_2240_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone(
    mut v_tm_2241_: *mut leanh::LeanObject,
    mut v_tz_2242_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_offset_2243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_abbreviation_2245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isDST_2246_: u8 = 0;
    let mut v___x_2247_: u8 = 0;
    let mut v___x_2248_: u8 = 0;
    let mut v_ltt_2249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_wt_2252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ltt_2253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tz_2254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_2255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_2256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_offset_2243_ = leanh::lean_ctor_get(v_tz_2242_, 0);
    v_name_2244_ = leanh::lean_ctor_get(v_tz_2242_, 1);
    v_abbreviation_2245_ = leanh::lean_ctor_get(v_tz_2242_, 2);
    v_isDST_2246_ = leanh::lean_ctor_get_uint8(
        v_tz_2242_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
    );
    v___x_2247_ = 0;
    v___x_2248_ = 1;
    leanh::lean_inc_ref(v_name_2244_);
    leanh::lean_inc_ref(v_abbreviation_2245_);
    leanh::lean_inc(v_offset_2243_);
    v_ltt_2249_ = leanh::lean_alloc_ctor(0, 3, (3) as u32);
    leanh::lean_ctor_set(v_ltt_2249_, 0, v_offset_2243_);
    leanh::lean_ctor_set(v_ltt_2249_, 1, v_abbreviation_2245_);
    leanh::lean_ctor_set(v_ltt_2249_, 2, v_name_2244_);
    leanh::lean_ctor_set_uint8(
        v_ltt_2249_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
        v_isDST_2246_,
    );
    leanh::lean_ctor_set_uint8(
        v_ltt_2249_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 1) as u32,
        v___x_2247_,
    );
    leanh::lean_ctor_set_uint8(
        v_ltt_2249_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 2) as u32,
        v___x_2248_,
    );
    v___x_2250_ = l_Std_Time_ZonedDateTime_ofTimestampWithZone___closed__0;
    v___x_2251_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2251_, 0, v_ltt_2249_);
    leanh::lean_ctor_set(v___x_2251_, 1, v___x_2250_);
    leanh::lean_inc_ref(v_tm_2241_);
    v_wt_2252_ = l_Std_Time_PlainDateTime_toWallTime(v_tm_2241_);
    leanh::lean_inc_ref(v___x_2251_);
    v_ltt_2253_ =
        l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v___x_2251_, v_wt_2252_);
    v_tz_2254_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_2253_);
    leanh::lean_dec_ref(v_ltt_2253_);
    v_offset_2255_ = leanh::lean_ctor_get(v_tz_2254_, 0);
    leanh::lean_inc(v_offset_2255_);
    v_second_2256_ = leanh::lean_ctor_get(v_wt_2252_, 0);
    leanh::lean_inc(v_second_2256_);
    v_nano_2257_ = leanh::lean_ctor_get(v_wt_2252_, 1);
    leanh::lean_inc(v_nano_2257_);
    leanh::lean_dec_ref(v_wt_2252_);
    v___f_2258_ = leanh::lean_alloc_closure(
        l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2258_, 0, v_tm_2241_);
    v___x_2259_ = lean_mk_thunk(v___f_2258_);
    v___x_2260_ = lean_int_neg(v_offset_2255_);
    leanh::lean_dec(v_offset_2255_);
    v___x_2261_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once),
        _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
    );
    v___x_2262_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once),
        _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
    );
    v___x_2263_ = lean_int_mul(v_second_2256_, v___x_2262_);
    leanh::lean_dec(v_second_2256_);
    v___x_2264_ = lean_int_add(v___x_2263_, v_nano_2257_);
    leanh::lean_dec(v_nano_2257_);
    leanh::lean_dec(v___x_2263_);
    v___x_2265_ = lean_int_mul(v___x_2260_, v___x_2262_);
    leanh::lean_dec(v___x_2260_);
    v___x_2266_ = lean_int_add(v___x_2265_, v___x_2261_);
    leanh::lean_dec(v___x_2265_);
    v___x_2267_ = lean_int_add(v___x_2264_, v___x_2266_);
    leanh::lean_dec(v___x_2266_);
    leanh::lean_dec(v___x_2264_);
    v___x_2268_ = l_Std_Time_Duration_ofNanoseconds(v___x_2267_);
    leanh::lean_dec(v___x_2267_);
    v___x_2269_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_2269_, 0, v___x_2259_);
    leanh::lean_ctor_set(v___x_2269_, 1, v___x_2268_);
    leanh::lean_ctor_set(v___x_2269_, 2, v___x_2251_);
    leanh::lean_ctor_set(v___x_2269_, 3, v_tz_2254_);
    return v___x_2269_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone___boxed(
    mut v_tm_2270_: *mut leanh::LeanObject,
    mut v_tz_2271_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2272_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2272_ = l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone(v_tm_2270_, v_tz_2271_);
    leanh::lean_dec_ref(v_tz_2271_);
    return v_res_2272_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_toTimestamp(
    mut v_date_2273_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_timestamp_2274_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_timestamp_2274_ = leanh::lean_ctor_get(v_date_2273_, 1);
    leanh::lean_inc_ref(v_timestamp_2274_);
    return v_timestamp_2274_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_toTimestamp___boxed(
    mut v_date_2275_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2276_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2276_ = l_Std_Time_ZonedDateTime_toTimestamp(v_date_2275_);
    leanh::lean_dec_ref(v_date_2275_);
    return v_res_2276_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_convertZoneRules___lam__0(
    mut v___y_2277_: *mut leanh::LeanObject,
    mut v_timestamp_2278_: *mut leanh::LeanObject,
    mut v_x_2279_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_offset_2280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_2281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_offset_2280_ = leanh::lean_ctor_get(v___y_2277_, 0);
    v_second_2281_ = leanh::lean_ctor_get(v_timestamp_2278_, 0);
    v_nano_2282_ = leanh::lean_ctor_get(v_timestamp_2278_, 1);
    v___x_2283_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once),
        _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0,
    );
    v___x_2284_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once),
        _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
    );
    v___x_2285_ = lean_int_mul(v_second_2281_, v___x_2284_);
    v___x_2286_ = lean_int_add(v___x_2285_, v_nano_2282_);
    leanh::lean_dec(v___x_2285_);
    v___x_2287_ = lean_int_mul(v_offset_2280_, v___x_2284_);
    v___x_2288_ = lean_int_add(v___x_2287_, v___x_2283_);
    leanh::lean_dec(v___x_2287_);
    v___x_2289_ = lean_int_add(v___x_2286_, v___x_2288_);
    leanh::lean_dec(v___x_2288_);
    leanh::lean_dec(v___x_2286_);
    v___x_2290_ = l_Std_Time_Duration_ofNanoseconds(v___x_2289_);
    leanh::lean_dec(v___x_2289_);
    v___x_2291_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_2290_);
    return v___x_2291_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_convertZoneRules___lam__0___boxed(
    mut v___y_2292_: *mut leanh::LeanObject,
    mut v_timestamp_2293_: *mut leanh::LeanObject,
    mut v_x_2294_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2295_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2295_ = l_Std_Time_ZonedDateTime_convertZoneRules___lam__0(
        v___y_2292_,
        v_timestamp_2293_,
        v_x_2294_,
    );
    leanh::lean_dec_ref(v_timestamp_2293_);
    leanh::lean_dec_ref(v___y_2292_);
    return v_res_2295_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_convertZoneRules(
    mut v_date_2296_: *mut leanh::LeanObject,
    mut v_tz_u2081_2297_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_timestamp_2298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2301_: u8 = 0;
    let mut v___y_2303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initialLocalTimeType_2309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_transitions_2310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2314_: u8 = 0;
    let mut v_unused_2315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_2298_ = leanh::lean_ctor_get(v_date_2296_, 1);
                v_isSharedCheck_2314_ = (!leanh::lean_is_exclusive(v_date_2296_)) as u8;
                if v_isSharedCheck_2314_ == 0 {
                    v_unused_2315_ = leanh::lean_ctor_get(v_date_2296_, 3);
                    leanh::lean_dec(v_unused_2315_);
                    v_unused_2316_ = leanh::lean_ctor_get(v_date_2296_, 2);
                    leanh::lean_dec(v_unused_2316_);
                    v_unused_2317_ = leanh::lean_ctor_get(v_date_2296_, 0);
                    leanh::lean_dec(v_unused_2317_);
                    v___x_2300_ = v_date_2296_;
                    v_isShared_2301_ = v_isSharedCheck_2314_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_timestamp_2298_);
                    leanh::lean_dec(v_date_2296_);
                    v___x_2300_ = leanh::lean_box(0);
                    v_isShared_2301_ = v_isSharedCheck_2314_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_initialLocalTimeType_2309_ = leanh::lean_ctor_get(v_tz_u2081_2297_, 0);
                v_transitions_2310_ = leanh::lean_ctor_get(v_tz_u2081_2297_, 1);
                v___x_2311_ = l_Std_Time_TimeZone_Transition_timezoneAt(
                    v_transitions_2310_,
                    v_timestamp_2298_,
                );
                if leanh::lean_obj_tag(v___x_2311_) == 0 {
                    leanh::lean_dec_ref_known(v___x_2311_, 1);
                    v___x_2312_ =
                        l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_2309_);
                    v___y_2303_ = v___x_2312_;
                    state = 2;
                    continue;
                } else {
                    v_a_2313_ = leanh::lean_ctor_get(v___x_2311_, 0);
                    leanh::lean_inc(v_a_2313_);
                    leanh::lean_dec_ref_known(v___x_2311_, 1);
                    v___y_2303_ = v_a_2313_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc_ref(v_timestamp_2298_);
                leanh::lean_inc_ref(v___y_2303_);
                v___f_2304_ = leanh::lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_convertZoneRules___lam__0___boxed
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                leanh::lean_closure_set(v___f_2304_, 0, v___y_2303_);
                leanh::lean_closure_set(v___f_2304_, 1, v_timestamp_2298_);
                v___x_2305_ = lean_mk_thunk(v___f_2304_);
                if v_isShared_2301_ == 0 {
                    leanh::lean_ctor_set(v___x_2300_, 3, v___y_2303_);
                    leanh::lean_ctor_set(v___x_2300_, 2, v_tz_u2081_2297_);
                    leanh::lean_ctor_set(v___x_2300_, 0, v___x_2305_);
                    v___x_2307_ = v___x_2300_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2308_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2308_, 0, v___x_2305_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2308_, 1, v_timestamp_2298_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2308_, 2, v_tz_u2081_2297_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2308_, 3, v___y_2303_);
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
    mut v_dt_2318_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_date_2319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_date_2319_ = leanh::lean_ctor_get(v_dt_2318_, 0);
    v___x_2320_ = lean_thunk_get_own(v_date_2319_);
    return v___x_2320_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_toPlainDateTime___boxed(
    mut v_dt_2321_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2322_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2322_ = l_Std_Time_ZonedDateTime_toPlainDateTime(v_dt_2321_);
    leanh::lean_dec_ref(v_dt_2321_);
    return v_res_2322_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_toDateTime___lam__0(
    mut v_timezone_2323_: *mut leanh::LeanObject,
    mut v_timestamp_2324_: *mut leanh::LeanObject,
    mut v_x_2325_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_offset_2326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_2327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_offset_2326_ = leanh::lean_ctor_get(v_timezone_2323_, 0);
    v_second_2327_ = leanh::lean_ctor_get(v_timestamp_2324_, 0);
    v_nano_2328_ = leanh::lean_ctor_get(v_timestamp_2324_, 1);
    v___x_2329_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once),
        _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0,
    );
    v___x_2330_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once),
        _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
    );
    v___x_2331_ = lean_int_mul(v_second_2327_, v___x_2330_);
    v___x_2332_ = lean_int_add(v___x_2331_, v_nano_2328_);
    leanh::lean_dec(v___x_2331_);
    v___x_2333_ = lean_int_mul(v_offset_2326_, v___x_2330_);
    v___x_2334_ = lean_int_add(v___x_2333_, v___x_2329_);
    leanh::lean_dec(v___x_2333_);
    v___x_2335_ = lean_int_add(v___x_2332_, v___x_2334_);
    leanh::lean_dec(v___x_2334_);
    leanh::lean_dec(v___x_2332_);
    v___x_2336_ = l_Std_Time_Duration_ofNanoseconds(v___x_2335_);
    leanh::lean_dec(v___x_2335_);
    v___x_2337_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_2336_);
    return v___x_2337_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_toDateTime___lam__0___boxed(
    mut v_timezone_2338_: *mut leanh::LeanObject,
    mut v_timestamp_2339_: *mut leanh::LeanObject,
    mut v_x_2340_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2341_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2341_ = l_Std_Time_ZonedDateTime_toDateTime___lam__0(
        v_timezone_2338_,
        v_timestamp_2339_,
        v_x_2340_,
    );
    leanh::lean_dec_ref(v_timestamp_2339_);
    leanh::lean_dec_ref(v_timezone_2338_);
    return v_res_2341_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_toDateTime(
    mut v_dt_2342_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_timestamp_2343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_timezone_2344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_timestamp_2343_ = leanh::lean_ctor_get(v_dt_2342_, 1);
    leanh::lean_inc_ref_n(v_timestamp_2343_, 2);
    v_timezone_2344_ = leanh::lean_ctor_get(v_dt_2342_, 3);
    leanh::lean_inc_ref(v_timezone_2344_);
    leanh::lean_dec_ref(v_dt_2342_);
    v___f_2345_ = leanh::lean_alloc_closure(
        l_Std_Time_ZonedDateTime_toDateTime___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_2345_, 0, v_timezone_2344_);
    leanh::lean_closure_set(v___f_2345_, 1, v_timestamp_2343_);
    v___x_2346_ = lean_mk_thunk(v___f_2345_);
    v___x_2347_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2347_, 0, v_timestamp_2343_);
    leanh::lean_ctor_set(v___x_2347_, 1, v___x_2346_);
    return v___x_2347_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_time(
    mut v_zdt_2348_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_date_2349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_2351_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_date_2349_ = leanh::lean_ctor_get(v_zdt_2348_, 0);
    v___x_2350_ = lean_thunk_get_own(v_date_2349_);
    v_time_2351_ = leanh::lean_ctor_get(v___x_2350_, 1);
    leanh::lean_inc_ref(v_time_2351_);
    leanh::lean_dec(v___x_2350_);
    return v_time_2351_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_time___boxed(
    mut v_zdt_2352_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2353_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2353_ = l_Std_Time_ZonedDateTime_time(v_zdt_2352_);
    leanh::lean_dec_ref(v_zdt_2352_);
    return v_res_2353_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_year(
    mut v_zdt_2354_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_date_2355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_2357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_year_2358_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_date_2355_ = leanh::lean_ctor_get(v_zdt_2354_, 0);
    v___x_2356_ = lean_thunk_get_own(v_date_2355_);
    v_date_2357_ = leanh::lean_ctor_get(v___x_2356_, 0);
    leanh::lean_inc_ref(v_date_2357_);
    leanh::lean_dec(v___x_2356_);
    v_year_2358_ = leanh::lean_ctor_get(v_date_2357_, 0);
    leanh::lean_inc(v_year_2358_);
    leanh::lean_dec_ref(v_date_2357_);
    return v_year_2358_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_year___boxed(
    mut v_zdt_2359_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2360_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2360_ = l_Std_Time_ZonedDateTime_year(v_zdt_2359_);
    leanh::lean_dec_ref(v_zdt_2359_);
    return v_res_2360_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_month(
    mut v_zdt_2361_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_date_2362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_2364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_month_2365_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_date_2362_ = leanh::lean_ctor_get(v_zdt_2361_, 0);
    v___x_2363_ = lean_thunk_get_own(v_date_2362_);
    v_date_2364_ = leanh::lean_ctor_get(v___x_2363_, 0);
    leanh::lean_inc_ref(v_date_2364_);
    leanh::lean_dec(v___x_2363_);
    v_month_2365_ = leanh::lean_ctor_get(v_date_2364_, 1);
    leanh::lean_inc(v_month_2365_);
    leanh::lean_dec_ref(v_date_2364_);
    return v_month_2365_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_month___boxed(
    mut v_zdt_2366_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2367_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2367_ = l_Std_Time_ZonedDateTime_month(v_zdt_2366_);
    leanh::lean_dec_ref(v_zdt_2366_);
    return v_res_2367_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_day(
    mut v_zdt_2368_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_date_2369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_2371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_day_2372_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_date_2369_ = leanh::lean_ctor_get(v_zdt_2368_, 0);
    v___x_2370_ = lean_thunk_get_own(v_date_2369_);
    v_date_2371_ = leanh::lean_ctor_get(v___x_2370_, 0);
    leanh::lean_inc_ref(v_date_2371_);
    leanh::lean_dec(v___x_2370_);
    v_day_2372_ = leanh::lean_ctor_get(v_date_2371_, 2);
    leanh::lean_inc(v_day_2372_);
    leanh::lean_dec_ref(v_date_2371_);
    return v_day_2372_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_day___boxed(
    mut v_zdt_2373_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2374_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2374_ = l_Std_Time_ZonedDateTime_day(v_zdt_2373_);
    leanh::lean_dec_ref(v_zdt_2373_);
    return v_res_2374_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_hour(
    mut v_zdt_2375_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_date_2376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_2378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hour_2379_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_date_2376_ = leanh::lean_ctor_get(v_zdt_2375_, 0);
    v___x_2377_ = lean_thunk_get_own(v_date_2376_);
    v_time_2378_ = leanh::lean_ctor_get(v___x_2377_, 1);
    leanh::lean_inc_ref(v_time_2378_);
    leanh::lean_dec(v___x_2377_);
    v_hour_2379_ = leanh::lean_ctor_get(v_time_2378_, 0);
    leanh::lean_inc(v_hour_2379_);
    leanh::lean_dec_ref(v_time_2378_);
    return v_hour_2379_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_hour___boxed(
    mut v_zdt_2380_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2381_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2381_ = l_Std_Time_ZonedDateTime_hour(v_zdt_2380_);
    leanh::lean_dec_ref(v_zdt_2380_);
    return v_res_2381_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_minute(
    mut v_zdt_2382_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_date_2383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_2385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_minute_2386_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_date_2383_ = leanh::lean_ctor_get(v_zdt_2382_, 0);
    v___x_2384_ = lean_thunk_get_own(v_date_2383_);
    v_time_2385_ = leanh::lean_ctor_get(v___x_2384_, 1);
    leanh::lean_inc_ref(v_time_2385_);
    leanh::lean_dec(v___x_2384_);
    v_minute_2386_ = leanh::lean_ctor_get(v_time_2385_, 1);
    leanh::lean_inc(v_minute_2386_);
    leanh::lean_dec_ref(v_time_2385_);
    return v_minute_2386_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_minute___boxed(
    mut v_zdt_2387_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2388_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2388_ = l_Std_Time_ZonedDateTime_minute(v_zdt_2387_);
    leanh::lean_dec_ref(v_zdt_2387_);
    return v_res_2388_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_second(
    mut v_zdt_2389_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_date_2390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_2392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_2393_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_date_2390_ = leanh::lean_ctor_get(v_zdt_2389_, 0);
    v___x_2391_ = lean_thunk_get_own(v_date_2390_);
    v_time_2392_ = leanh::lean_ctor_get(v___x_2391_, 1);
    leanh::lean_inc_ref(v_time_2392_);
    leanh::lean_dec(v___x_2391_);
    v_second_2393_ = leanh::lean_ctor_get(v_time_2392_, 2);
    leanh::lean_inc(v_second_2393_);
    leanh::lean_dec_ref(v_time_2392_);
    return v_second_2393_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_second___boxed(
    mut v_zdt_2394_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2395_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2395_ = l_Std_Time_ZonedDateTime_second(v_zdt_2394_);
    leanh::lean_dec_ref(v_zdt_2394_);
    return v_res_2395_;
}
pub unsafe fn _init_l_Std_Time_ZonedDateTime_millisecond___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2396_ = leanh::lean_unsigned_to_nat(1000000);
    v___x_2397_ = lean_nat_to_int(v___x_2396_);
    return v___x_2397_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_millisecond(
    mut v_dt_2398_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_date_2399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_2401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_2402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2404_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_date_2399_ = leanh::lean_ctor_get(v_dt_2398_, 0);
    v___x_2400_ = lean_thunk_get_own(v_date_2399_);
    v_time_2401_ = leanh::lean_ctor_get(v___x_2400_, 1);
    leanh::lean_inc_ref(v_time_2401_);
    leanh::lean_dec(v___x_2400_);
    v_nanosecond_2402_ = leanh::lean_ctor_get(v_time_2401_, 3);
    leanh::lean_inc(v_nanosecond_2402_);
    leanh::lean_dec_ref(v_time_2401_);
    v___x_2403_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_millisecond___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_millisecond___closed__0_once),
        _init_l_Std_Time_ZonedDateTime_millisecond___closed__0,
    );
    v___x_2404_ = lean_int_ediv(v_nanosecond_2402_, v___x_2403_);
    leanh::lean_dec(v_nanosecond_2402_);
    return v___x_2404_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_millisecond___boxed(
    mut v_dt_2405_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2406_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2406_ = l_Std_Time_ZonedDateTime_millisecond(v_dt_2405_);
    leanh::lean_dec_ref(v_dt_2405_);
    return v_res_2406_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_nanosecond(
    mut v_zdt_2407_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_date_2408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_2410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_2411_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_date_2408_ = leanh::lean_ctor_get(v_zdt_2407_, 0);
    v___x_2409_ = lean_thunk_get_own(v_date_2408_);
    v_time_2410_ = leanh::lean_ctor_get(v___x_2409_, 1);
    leanh::lean_inc_ref(v_time_2410_);
    leanh::lean_dec(v___x_2409_);
    v_nanosecond_2411_ = leanh::lean_ctor_get(v_time_2410_, 3);
    leanh::lean_inc(v_nanosecond_2411_);
    leanh::lean_dec_ref(v_time_2410_);
    return v_nanosecond_2411_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_nanosecond___boxed(
    mut v_zdt_2412_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2413_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2413_ = l_Std_Time_ZonedDateTime_nanosecond(v_zdt_2412_);
    leanh::lean_dec_ref(v_zdt_2412_);
    return v_res_2413_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_offset(
    mut v_zdt_2414_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_timezone_2415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_2416_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_timezone_2415_ = leanh::lean_ctor_get(v_zdt_2414_, 3);
    v_offset_2416_ = leanh::lean_ctor_get(v_timezone_2415_, 0);
    leanh::lean_inc(v_offset_2416_);
    return v_offset_2416_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_offset___boxed(
    mut v_zdt_2417_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2418_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2418_ = l_Std_Time_ZonedDateTime_offset(v_zdt_2417_);
    leanh::lean_dec_ref(v_zdt_2417_);
    return v_res_2418_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_weekday(
    mut v_zdt_2419_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_date_2420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_2422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2423_: u8 = 0;
    v_date_2420_ = leanh::lean_ctor_get(v_zdt_2419_, 0);
    v___x_2421_ = lean_thunk_get_own(v_date_2420_);
    v_date_2422_ = leanh::lean_ctor_get(v___x_2421_, 0);
    leanh::lean_inc_ref(v_date_2422_);
    leanh::lean_dec(v___x_2421_);
    v___x_2423_ = l_Std_Time_PlainDate_weekday(v_date_2422_);
    return v___x_2423_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_weekday___boxed(
    mut v_zdt_2424_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2425_: u8 = 0;
    let mut v_r_2426_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2425_ = l_Std_Time_ZonedDateTime_weekday(v_zdt_2424_);
    leanh::lean_dec_ref(v_zdt_2424_);
    v_r_2426_ = leanh::lean_box((v_res_2425_) as usize);
    return v_r_2426_;
}
pub unsafe fn _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__0() -> *mut leanh::LeanObject
{
    let mut v___x_2427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2428_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2427_ = leanh::lean_unsigned_to_nat(4);
    v___x_2428_ = lean_nat_to_int(v___x_2427_);
    return v___x_2428_;
}
pub unsafe fn _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__1() -> *mut leanh::LeanObject
{
    let mut v___x_2429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2429_ = leanh::lean_unsigned_to_nat(400);
    v___x_2430_ = lean_nat_to_int(v___x_2429_);
    return v___x_2430_;
}
pub unsafe fn _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__2() -> *mut leanh::LeanObject
{
    let mut v___x_2431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2431_ = leanh::lean_unsigned_to_nat(100);
    v___x_2432_ = lean_nat_to_int(v___x_2431_);
    return v___x_2432_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_dayOfYear(
    mut v_date_2433_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_date_2434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2436_: u8 = 0;
    let mut v___x_2437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_2438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2441_: u8 = 0;
    let mut v_month_2442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_day_2443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2448_: u8 = 0;
    let mut v_unused_2449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_2451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_year_2452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: u8 = 0;
    let mut v___x_2460_: u8 = 0;
    let mut v___x_2461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_2434_ = leanh::lean_ctor_get(v_date_2433_, 0);
                v___x_2450_ = lean_thunk_get_own(v_date_2434_);
                v_date_2451_ = leanh::lean_ctor_get(v___x_2450_, 0);
                leanh::lean_inc_ref(v_date_2451_);
                leanh::lean_dec(v___x_2450_);
                v_year_2452_ = leanh::lean_ctor_get(v_date_2451_, 0);
                leanh::lean_inc(v_year_2452_);
                leanh::lean_dec_ref(v_date_2451_);
                v___x_2453_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_dayOfYear___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_dayOfYear___closed__0_once),
                    _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__0,
                );
                v___x_2454_ = lean_int_mod(v_year_2452_, v___x_2453_);
                v___x_2455_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0,
                );
                v___x_2460_ = lean_int_dec_eq(v___x_2454_, v___x_2455_);
                leanh::lean_dec(v___x_2454_);
                if v___x_2460_ == 0 {
                    leanh::lean_dec(v_year_2452_);
                    v___y_2436_ = v___x_2460_;
                    state = 1;
                    continue;
                } else {
                    v___x_2461_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_dayOfYear___closed__2),
                        core::ptr::addr_of_mut!(
                            l_Std_Time_ZonedDateTime_dayOfYear___closed__2_once
                        ),
                        _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__2,
                    );
                    v___x_2462_ = lean_int_mod(v_year_2452_, v___x_2461_);
                    v___x_2463_ = lean_int_dec_eq(v___x_2462_, v___x_2455_);
                    leanh::lean_dec(v___x_2462_);
                    if v___x_2463_ == 0 {
                        if v___x_2460_ == 0 {
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_dec(v_year_2452_);
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
                v_date_2438_ = leanh::lean_ctor_get(v___x_2437_, 0);
                v_isSharedCheck_2448_ = (!leanh::lean_is_exclusive(v___x_2437_)) as u8;
                if v_isSharedCheck_2448_ == 0 {
                    v_unused_2449_ = leanh::lean_ctor_get(v___x_2437_, 1);
                    leanh::lean_dec(v_unused_2449_);
                    v___x_2440_ = v___x_2437_;
                    v_isShared_2441_ = v_isSharedCheck_2448_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_date_2438_);
                    leanh::lean_dec(v___x_2437_);
                    v___x_2440_ = leanh::lean_box(0);
                    v_isShared_2441_ = v_isSharedCheck_2448_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_month_2442_ = leanh::lean_ctor_get(v_date_2438_, 1);
                leanh::lean_inc(v_month_2442_);
                v_day_2443_ = leanh::lean_ctor_get(v_date_2438_, 2);
                leanh::lean_inc(v_day_2443_);
                leanh::lean_dec_ref(v_date_2438_);
                if v_isShared_2441_ == 0 {
                    leanh::lean_ctor_set(v___x_2440_, 1, v_day_2443_);
                    leanh::lean_ctor_set(v___x_2440_, 0, v_month_2442_);
                    v___x_2445_ = v___x_2440_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2447_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2447_, 0, v_month_2442_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2447_, 1, v_day_2443_);
                    v___x_2445_ = v_reuseFailAlloc_2447_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2446_ = l_Std_Time_ValidDate_dayOfYear(v___y_2436_, v___x_2445_);
                leanh::lean_dec_ref(v___x_2445_);
                return v___x_2446_;
            }
            4 => {
                v___x_2457_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_dayOfYear___closed__1),
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_dayOfYear___closed__1_once),
                    _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__1,
                );
                v___x_2458_ = lean_int_mod(v_year_2452_, v___x_2457_);
                leanh::lean_dec(v_year_2452_);
                v___x_2459_ = lean_int_dec_eq(v___x_2458_, v___x_2455_);
                leanh::lean_dec(v___x_2458_);
                v___y_2436_ = v___x_2459_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_ZonedDateTime_dayOfYear___boxed(
    mut v_date_2464_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2465_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2465_ = l_Std_Time_ZonedDateTime_dayOfYear(v_date_2464_);
    leanh::lean_dec_ref(v_date_2464_);
    return v_res_2465_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_weekOfYear(
    mut v_date_2466_: *mut leanh::LeanObject,
    mut v_firstDay_2467_: u8,
) -> *mut leanh::LeanObject {
    let mut v_date_2468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_2470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_date_2468_ = leanh::lean_ctor_get(v_date_2466_, 0);
    v___x_2469_ = lean_thunk_get_own(v_date_2468_);
    v_date_2470_ = leanh::lean_ctor_get(v___x_2469_, 0);
    leanh::lean_inc_ref(v_date_2470_);
    leanh::lean_dec(v___x_2469_);
    v___x_2471_ = l_Std_Time_PlainDate_weekOfYear(v_date_2470_, v_firstDay_2467_);
    return v___x_2471_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_weekOfYear___boxed(
    mut v_date_2472_: *mut leanh::LeanObject,
    mut v_firstDay_2473_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_firstDay_boxed_2474_: u8 = 0;
    let mut v_res_2475_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_firstDay_boxed_2474_ = (leanh::lean_unbox(v_firstDay_2473_) as u8);
    v_res_2475_ = l_Std_Time_ZonedDateTime_weekOfYear(v_date_2472_, v_firstDay_boxed_2474_);
    leanh::lean_dec_ref(v_date_2472_);
    return v_res_2475_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_weekYear(
    mut v_date_2476_: *mut leanh::LeanObject,
    mut v_firstDay_2477_: u8,
) -> *mut leanh::LeanObject {
    let mut v_date_2478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_2480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_date_2478_ = leanh::lean_ctor_get(v_date_2476_, 0);
    v___x_2479_ = lean_thunk_get_own(v_date_2478_);
    v_date_2480_ = leanh::lean_ctor_get(v___x_2479_, 0);
    leanh::lean_inc_ref(v_date_2480_);
    leanh::lean_dec(v___x_2479_);
    v___x_2481_ = l_Std_Time_PlainDate_weekYear(v_date_2480_, v_firstDay_2477_);
    return v___x_2481_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_weekYear___boxed(
    mut v_date_2482_: *mut leanh::LeanObject,
    mut v_firstDay_2483_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_firstDay_boxed_2484_: u8 = 0;
    let mut v_res_2485_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_firstDay_boxed_2484_ = (leanh::lean_unbox(v_firstDay_2483_) as u8);
    v_res_2485_ = l_Std_Time_ZonedDateTime_weekYear(v_date_2482_, v_firstDay_boxed_2484_);
    leanh::lean_dec_ref(v_date_2482_);
    return v_res_2485_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_weekOfMonth(
    mut v_date_2486_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_date_2487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2489_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_date_2487_ = leanh::lean_ctor_get(v_date_2486_, 0);
    v___x_2488_ = lean_thunk_get_own(v_date_2487_);
    v___x_2489_ = l_Std_Time_PlainDateTime_weekOfMonth(v___x_2488_);
    leanh::lean_dec(v___x_2488_);
    return v___x_2489_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_weekOfMonth___boxed(
    mut v_date_2490_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2491_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2491_ = l_Std_Time_ZonedDateTime_weekOfMonth(v_date_2490_);
    leanh::lean_dec_ref(v_date_2490_);
    return v_res_2491_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_alignedWeekOfMonth(
    mut v_date_2492_: *mut leanh::LeanObject,
    mut v_firstDay_2493_: u8,
) -> *mut leanh::LeanObject {
    let mut v_date_2494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_2496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2497_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_date_2494_ = leanh::lean_ctor_get(v_date_2492_, 0);
    v___x_2495_ = lean_thunk_get_own(v_date_2494_);
    v_date_2496_ = leanh::lean_ctor_get(v___x_2495_, 0);
    leanh::lean_inc_ref(v_date_2496_);
    leanh::lean_dec(v___x_2495_);
    v___x_2497_ = l_Std_Time_PlainDate_alignedWeekOfMonth(v_date_2496_, v_firstDay_2493_);
    return v___x_2497_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_alignedWeekOfMonth___boxed(
    mut v_date_2498_: *mut leanh::LeanObject,
    mut v_firstDay_2499_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_firstDay_boxed_2500_: u8 = 0;
    let mut v_res_2501_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_firstDay_boxed_2500_ = (leanh::lean_unbox(v_firstDay_2499_) as u8);
    v_res_2501_ = l_Std_Time_ZonedDateTime_alignedWeekOfMonth(v_date_2498_, v_firstDay_boxed_2500_);
    leanh::lean_dec_ref(v_date_2498_);
    return v_res_2501_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_quarter(
    mut v_date_2502_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_date_2503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_2505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_date_2503_ = leanh::lean_ctor_get(v_date_2502_, 0);
    v___x_2504_ = lean_thunk_get_own(v_date_2503_);
    v_date_2505_ = leanh::lean_ctor_get(v___x_2504_, 0);
    leanh::lean_inc_ref(v_date_2505_);
    leanh::lean_dec(v___x_2504_);
    v___x_2506_ = l_Std_Time_PlainDate_quarter(v_date_2505_);
    leanh::lean_dec_ref(v_date_2505_);
    return v___x_2506_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_quarter___boxed(
    mut v_date_2507_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2508_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2508_ = l_Std_Time_ZonedDateTime_quarter(v_date_2507_);
    leanh::lean_dec_ref(v_date_2507_);
    return v_res_2508_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_addDays___lam__0(
    mut v___y_2509_: *mut leanh::LeanObject,
    mut v___x_2510_: *mut leanh::LeanObject,
    mut v___x_2511_: *mut leanh::LeanObject,
    mut v___x_2512_: *mut leanh::LeanObject,
    mut v_x_2513_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_offset_2514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_2515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2523_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_offset_2514_ = leanh::lean_ctor_get(v___y_2509_, 0);
    v_second_2515_ = leanh::lean_ctor_get(v___x_2510_, 0);
    v_nano_2516_ = leanh::lean_ctor_get(v___x_2510_, 1);
    v___x_2517_ = lean_int_mul(v_second_2515_, v___x_2511_);
    v___x_2518_ = lean_int_add(v___x_2517_, v_nano_2516_);
    leanh::lean_dec(v___x_2517_);
    v___x_2519_ = lean_int_mul(v_offset_2514_, v___x_2511_);
    v___x_2520_ = lean_int_add(v___x_2519_, v___x_2512_);
    leanh::lean_dec(v___x_2519_);
    v___x_2521_ = lean_int_add(v___x_2518_, v___x_2520_);
    leanh::lean_dec(v___x_2520_);
    leanh::lean_dec(v___x_2518_);
    v___x_2522_ = l_Std_Time_Duration_ofNanoseconds(v___x_2521_);
    leanh::lean_dec(v___x_2521_);
    v___x_2523_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_2522_);
    return v___x_2523_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_addDays___lam__0___boxed(
    mut v___y_2524_: *mut leanh::LeanObject,
    mut v___x_2525_: *mut leanh::LeanObject,
    mut v___x_2526_: *mut leanh::LeanObject,
    mut v___x_2527_: *mut leanh::LeanObject,
    mut v_x_2528_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2529_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2529_ = l_Std_Time_ZonedDateTime_addDays___lam__0(
        v___y_2524_,
        v___x_2525_,
        v___x_2526_,
        v___x_2527_,
        v_x_2528_,
    );
    leanh::lean_dec(v___x_2527_);
    leanh::lean_dec(v___x_2526_);
    leanh::lean_dec_ref(v___x_2525_);
    leanh::lean_dec_ref(v___y_2524_);
    return v_res_2529_;
}
pub unsafe fn _init_l_Std_Time_ZonedDateTime_addDays___closed__0() -> *mut leanh::LeanObject
{
    let mut v___x_2530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2530_ = leanh::lean_unsigned_to_nat(86400);
    v___x_2531_ = lean_nat_to_int(v___x_2530_);
    return v___x_2531_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_addDays(
    mut v_dt_2532_: *mut leanh::LeanObject,
    mut v_days_2533_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_timestamp_2534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rules_2535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2538_: u8 = 0;
    let mut v_second_2539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initialLocalTimeType_2541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_transitions_2542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2563_: u8 = 0;
    let mut v_unused_2564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_2534_ = leanh::lean_ctor_get(v_dt_2532_, 1);
                v_rules_2535_ = leanh::lean_ctor_get(v_dt_2532_, 2);
                v_isSharedCheck_2563_ = (!leanh::lean_is_exclusive(v_dt_2532_)) as u8;
                if v_isSharedCheck_2563_ == 0 {
                    v_unused_2564_ = leanh::lean_ctor_get(v_dt_2532_, 3);
                    leanh::lean_dec(v_unused_2564_);
                    v_unused_2565_ = leanh::lean_ctor_get(v_dt_2532_, 0);
                    leanh::lean_dec(v_unused_2565_);
                    v___x_2537_ = v_dt_2532_;
                    v_isShared_2538_ = v_isSharedCheck_2563_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_rules_2535_);
                    leanh::lean_inc(v_timestamp_2534_);
                    leanh::lean_dec(v_dt_2532_);
                    v___x_2537_ = leanh::lean_box(0);
                    v_isShared_2538_ = v_isSharedCheck_2563_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_second_2539_ = leanh::lean_ctor_get(v_timestamp_2534_, 0);
                leanh::lean_inc(v_second_2539_);
                v_nano_2540_ = leanh::lean_ctor_get(v_timestamp_2534_, 1);
                leanh::lean_inc(v_nano_2540_);
                leanh::lean_dec_ref(v_timestamp_2534_);
                v_initialLocalTimeType_2541_ = leanh::lean_ctor_get(v_rules_2535_, 0);
                v_transitions_2542_ = leanh::lean_ctor_get(v_rules_2535_, 1);
                v___x_2543_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_addDays___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_addDays___closed__0_once),
                    _init_l_Std_Time_ZonedDateTime_addDays___closed__0,
                );
                v___x_2544_ = lean_int_mul(v_days_2533_, v___x_2543_);
                v___x_2545_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0,
                );
                v___x_2546_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_2547_ = lean_int_mul(v_second_2539_, v___x_2546_);
                leanh::lean_dec(v_second_2539_);
                v___x_2548_ = lean_int_add(v___x_2547_, v_nano_2540_);
                leanh::lean_dec(v_nano_2540_);
                leanh::lean_dec(v___x_2547_);
                v___x_2549_ = lean_int_mul(v___x_2544_, v___x_2546_);
                leanh::lean_dec(v___x_2544_);
                v___x_2550_ = lean_int_add(v___x_2549_, v___x_2545_);
                leanh::lean_dec(v___x_2549_);
                v___x_2551_ = lean_int_add(v___x_2548_, v___x_2550_);
                leanh::lean_dec(v___x_2550_);
                leanh::lean_dec(v___x_2548_);
                v___x_2552_ = l_Std_Time_Duration_ofNanoseconds(v___x_2551_);
                leanh::lean_dec(v___x_2551_);
                v___x_2560_ =
                    l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_2542_, v___x_2552_);
                if leanh::lean_obj_tag(v___x_2560_) == 0 {
                    leanh::lean_dec_ref_known(v___x_2560_, 1);
                    v___x_2561_ =
                        l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_2541_);
                    v___y_2554_ = v___x_2561_;
                    state = 2;
                    continue;
                } else {
                    v_a_2562_ = leanh::lean_ctor_get(v___x_2560_, 0);
                    leanh::lean_inc(v_a_2562_);
                    leanh::lean_dec_ref_known(v___x_2560_, 1);
                    v___y_2554_ = v_a_2562_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc_ref(v___x_2552_);
                leanh::lean_inc_ref(v___y_2554_);
                v___f_2555_ = leanh::lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addDays___lam__0___boxed as *mut core::ffi::c_void,
                    5,
                    4,
                );
                leanh::lean_closure_set(v___f_2555_, 0, v___y_2554_);
                leanh::lean_closure_set(v___f_2555_, 1, v___x_2552_);
                leanh::lean_closure_set(v___f_2555_, 2, v___x_2546_);
                leanh::lean_closure_set(v___f_2555_, 3, v___x_2545_);
                v___x_2556_ = lean_mk_thunk(v___f_2555_);
                if v_isShared_2538_ == 0 {
                    leanh::lean_ctor_set(v___x_2537_, 3, v___y_2554_);
                    leanh::lean_ctor_set(v___x_2537_, 1, v___x_2552_);
                    leanh::lean_ctor_set(v___x_2537_, 0, v___x_2556_);
                    v___x_2558_ = v___x_2537_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2559_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2559_, 0, v___x_2556_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2559_, 1, v___x_2552_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2559_, 2, v_rules_2535_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2559_, 3, v___y_2554_);
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
    mut v_dt_2566_: *mut leanh::LeanObject,
    mut v_days_2567_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2568_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2568_ = l_Std_Time_ZonedDateTime_addDays(v_dt_2566_, v_days_2567_);
    leanh::lean_dec(v_days_2567_);
    return v_res_2568_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_subDays(
    mut v_dt_2569_: *mut leanh::LeanObject,
    mut v_days_2570_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_timestamp_2571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rules_2572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2575_: u8 = 0;
    let mut v_second_2576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initialLocalTimeType_2578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_transitions_2579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2602_: u8 = 0;
    let mut v_unused_2603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_2571_ = leanh::lean_ctor_get(v_dt_2569_, 1);
                v_rules_2572_ = leanh::lean_ctor_get(v_dt_2569_, 2);
                v_isSharedCheck_2602_ = (!leanh::lean_is_exclusive(v_dt_2569_)) as u8;
                if v_isSharedCheck_2602_ == 0 {
                    v_unused_2603_ = leanh::lean_ctor_get(v_dt_2569_, 3);
                    leanh::lean_dec(v_unused_2603_);
                    v_unused_2604_ = leanh::lean_ctor_get(v_dt_2569_, 0);
                    leanh::lean_dec(v_unused_2604_);
                    v___x_2574_ = v_dt_2569_;
                    v_isShared_2575_ = v_isSharedCheck_2602_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_rules_2572_);
                    leanh::lean_inc(v_timestamp_2571_);
                    leanh::lean_dec(v_dt_2569_);
                    v___x_2574_ = leanh::lean_box(0);
                    v_isShared_2575_ = v_isSharedCheck_2602_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_second_2576_ = leanh::lean_ctor_get(v_timestamp_2571_, 0);
                leanh::lean_inc(v_second_2576_);
                v_nano_2577_ = leanh::lean_ctor_get(v_timestamp_2571_, 1);
                leanh::lean_inc(v_nano_2577_);
                leanh::lean_dec_ref(v_timestamp_2571_);
                v_initialLocalTimeType_2578_ = leanh::lean_ctor_get(v_rules_2572_, 0);
                v_transitions_2579_ = leanh::lean_ctor_get(v_rules_2572_, 1);
                v___x_2580_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_addDays___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_addDays___closed__0_once),
                    _init_l_Std_Time_ZonedDateTime_addDays___closed__0,
                );
                v___x_2581_ = lean_int_mul(v_days_2570_, v___x_2580_);
                v___x_2582_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0,
                );
                v___x_2583_ = lean_int_neg(v___x_2581_);
                leanh::lean_dec(v___x_2581_);
                v___x_2584_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
                );
                v___x_2585_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_2586_ = lean_int_mul(v_second_2576_, v___x_2585_);
                leanh::lean_dec(v_second_2576_);
                v___x_2587_ = lean_int_add(v___x_2586_, v_nano_2577_);
                leanh::lean_dec(v_nano_2577_);
                leanh::lean_dec(v___x_2586_);
                v___x_2588_ = lean_int_mul(v___x_2583_, v___x_2585_);
                leanh::lean_dec(v___x_2583_);
                v___x_2589_ = lean_int_add(v___x_2588_, v___x_2584_);
                leanh::lean_dec(v___x_2588_);
                v___x_2590_ = lean_int_add(v___x_2587_, v___x_2589_);
                leanh::lean_dec(v___x_2589_);
                leanh::lean_dec(v___x_2587_);
                v___x_2591_ = l_Std_Time_Duration_ofNanoseconds(v___x_2590_);
                leanh::lean_dec(v___x_2590_);
                v___x_2599_ =
                    l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_2579_, v___x_2591_);
                if leanh::lean_obj_tag(v___x_2599_) == 0 {
                    leanh::lean_dec_ref_known(v___x_2599_, 1);
                    v___x_2600_ =
                        l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_2578_);
                    v___y_2593_ = v___x_2600_;
                    state = 2;
                    continue;
                } else {
                    v_a_2601_ = leanh::lean_ctor_get(v___x_2599_, 0);
                    leanh::lean_inc(v_a_2601_);
                    leanh::lean_dec_ref_known(v___x_2599_, 1);
                    v___y_2593_ = v_a_2601_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc_ref(v___x_2591_);
                leanh::lean_inc_ref(v___y_2593_);
                v___f_2594_ = leanh::lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addDays___lam__0___boxed as *mut core::ffi::c_void,
                    5,
                    4,
                );
                leanh::lean_closure_set(v___f_2594_, 0, v___y_2593_);
                leanh::lean_closure_set(v___f_2594_, 1, v___x_2591_);
                leanh::lean_closure_set(v___f_2594_, 2, v___x_2585_);
                leanh::lean_closure_set(v___f_2594_, 3, v___x_2582_);
                v___x_2595_ = lean_mk_thunk(v___f_2594_);
                if v_isShared_2575_ == 0 {
                    leanh::lean_ctor_set(v___x_2574_, 3, v___y_2593_);
                    leanh::lean_ctor_set(v___x_2574_, 1, v___x_2591_);
                    leanh::lean_ctor_set(v___x_2574_, 0, v___x_2595_);
                    v___x_2597_ = v___x_2574_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2598_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2598_, 0, v___x_2595_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2598_, 1, v___x_2591_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2598_, 2, v_rules_2572_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2598_, 3, v___y_2593_);
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
    mut v_dt_2605_: *mut leanh::LeanObject,
    mut v_days_2606_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2607_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2607_ = l_Std_Time_ZonedDateTime_subDays(v_dt_2605_, v_days_2606_);
    leanh::lean_dec(v_days_2606_);
    return v_res_2607_;
}
pub unsafe fn _init_l_Std_Time_ZonedDateTime_addWeeks___closed__0() -> *mut leanh::LeanObject
{
    let mut v___x_2608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2608_ = leanh::lean_unsigned_to_nat(7);
    v___x_2609_ = lean_nat_to_int(v___x_2608_);
    return v___x_2609_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_addWeeks(
    mut v_dt_2610_: *mut leanh::LeanObject,
    mut v_weeks_2611_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_timestamp_2612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rules_2613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2616_: u8 = 0;
    let mut v_second_2617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initialLocalTimeType_2619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_transitions_2620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2643_: u8 = 0;
    let mut v_unused_2644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_2612_ = leanh::lean_ctor_get(v_dt_2610_, 1);
                v_rules_2613_ = leanh::lean_ctor_get(v_dt_2610_, 2);
                v_isSharedCheck_2643_ = (!leanh::lean_is_exclusive(v_dt_2610_)) as u8;
                if v_isSharedCheck_2643_ == 0 {
                    v_unused_2644_ = leanh::lean_ctor_get(v_dt_2610_, 3);
                    leanh::lean_dec(v_unused_2644_);
                    v_unused_2645_ = leanh::lean_ctor_get(v_dt_2610_, 0);
                    leanh::lean_dec(v_unused_2645_);
                    v___x_2615_ = v_dt_2610_;
                    v_isShared_2616_ = v_isSharedCheck_2643_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_rules_2613_);
                    leanh::lean_inc(v_timestamp_2612_);
                    leanh::lean_dec(v_dt_2610_);
                    v___x_2615_ = leanh::lean_box(0);
                    v_isShared_2616_ = v_isSharedCheck_2643_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_second_2617_ = leanh::lean_ctor_get(v_timestamp_2612_, 0);
                leanh::lean_inc(v_second_2617_);
                v_nano_2618_ = leanh::lean_ctor_get(v_timestamp_2612_, 1);
                leanh::lean_inc(v_nano_2618_);
                leanh::lean_dec_ref(v_timestamp_2612_);
                v_initialLocalTimeType_2619_ = leanh::lean_ctor_get(v_rules_2613_, 0);
                v_transitions_2620_ = leanh::lean_ctor_get(v_rules_2613_, 1);
                v___x_2621_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_addWeeks___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_addWeeks___closed__0_once),
                    _init_l_Std_Time_ZonedDateTime_addWeeks___closed__0,
                );
                v___x_2622_ = lean_int_mul(v_weeks_2611_, v___x_2621_);
                v___x_2623_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_addDays___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_addDays___closed__0_once),
                    _init_l_Std_Time_ZonedDateTime_addDays___closed__0,
                );
                v___x_2624_ = lean_int_mul(v___x_2622_, v___x_2623_);
                leanh::lean_dec(v___x_2622_);
                v___x_2625_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0,
                );
                v___x_2626_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_2627_ = lean_int_mul(v_second_2617_, v___x_2626_);
                leanh::lean_dec(v_second_2617_);
                v___x_2628_ = lean_int_add(v___x_2627_, v_nano_2618_);
                leanh::lean_dec(v_nano_2618_);
                leanh::lean_dec(v___x_2627_);
                v___x_2629_ = lean_int_mul(v___x_2624_, v___x_2626_);
                leanh::lean_dec(v___x_2624_);
                v___x_2630_ = lean_int_add(v___x_2629_, v___x_2625_);
                leanh::lean_dec(v___x_2629_);
                v___x_2631_ = lean_int_add(v___x_2628_, v___x_2630_);
                leanh::lean_dec(v___x_2630_);
                leanh::lean_dec(v___x_2628_);
                v___x_2632_ = l_Std_Time_Duration_ofNanoseconds(v___x_2631_);
                leanh::lean_dec(v___x_2631_);
                v___x_2640_ =
                    l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_2620_, v___x_2632_);
                if leanh::lean_obj_tag(v___x_2640_) == 0 {
                    leanh::lean_dec_ref_known(v___x_2640_, 1);
                    v___x_2641_ =
                        l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_2619_);
                    v___y_2634_ = v___x_2641_;
                    state = 2;
                    continue;
                } else {
                    v_a_2642_ = leanh::lean_ctor_get(v___x_2640_, 0);
                    leanh::lean_inc(v_a_2642_);
                    leanh::lean_dec_ref_known(v___x_2640_, 1);
                    v___y_2634_ = v_a_2642_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc_ref(v___x_2632_);
                leanh::lean_inc_ref(v___y_2634_);
                v___f_2635_ = leanh::lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addDays___lam__0___boxed as *mut core::ffi::c_void,
                    5,
                    4,
                );
                leanh::lean_closure_set(v___f_2635_, 0, v___y_2634_);
                leanh::lean_closure_set(v___f_2635_, 1, v___x_2632_);
                leanh::lean_closure_set(v___f_2635_, 2, v___x_2626_);
                leanh::lean_closure_set(v___f_2635_, 3, v___x_2625_);
                v___x_2636_ = lean_mk_thunk(v___f_2635_);
                if v_isShared_2616_ == 0 {
                    leanh::lean_ctor_set(v___x_2615_, 3, v___y_2634_);
                    leanh::lean_ctor_set(v___x_2615_, 1, v___x_2632_);
                    leanh::lean_ctor_set(v___x_2615_, 0, v___x_2636_);
                    v___x_2638_ = v___x_2615_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2639_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2639_, 0, v___x_2636_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2639_, 1, v___x_2632_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2639_, 2, v_rules_2613_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2639_, 3, v___y_2634_);
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
    mut v_dt_2646_: *mut leanh::LeanObject,
    mut v_weeks_2647_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2648_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2648_ = l_Std_Time_ZonedDateTime_addWeeks(v_dt_2646_, v_weeks_2647_);
    leanh::lean_dec(v_weeks_2647_);
    return v_res_2648_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_subWeeks(
    mut v_dt_2649_: *mut leanh::LeanObject,
    mut v_weeks_2650_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_timestamp_2651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rules_2652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2655_: u8 = 0;
    let mut v_second_2656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initialLocalTimeType_2658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_transitions_2659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2684_: u8 = 0;
    let mut v_unused_2685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_2651_ = leanh::lean_ctor_get(v_dt_2649_, 1);
                v_rules_2652_ = leanh::lean_ctor_get(v_dt_2649_, 2);
                v_isSharedCheck_2684_ = (!leanh::lean_is_exclusive(v_dt_2649_)) as u8;
                if v_isSharedCheck_2684_ == 0 {
                    v_unused_2685_ = leanh::lean_ctor_get(v_dt_2649_, 3);
                    leanh::lean_dec(v_unused_2685_);
                    v_unused_2686_ = leanh::lean_ctor_get(v_dt_2649_, 0);
                    leanh::lean_dec(v_unused_2686_);
                    v___x_2654_ = v_dt_2649_;
                    v_isShared_2655_ = v_isSharedCheck_2684_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_rules_2652_);
                    leanh::lean_inc(v_timestamp_2651_);
                    leanh::lean_dec(v_dt_2649_);
                    v___x_2654_ = leanh::lean_box(0);
                    v_isShared_2655_ = v_isSharedCheck_2684_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_second_2656_ = leanh::lean_ctor_get(v_timestamp_2651_, 0);
                leanh::lean_inc(v_second_2656_);
                v_nano_2657_ = leanh::lean_ctor_get(v_timestamp_2651_, 1);
                leanh::lean_inc(v_nano_2657_);
                leanh::lean_dec_ref(v_timestamp_2651_);
                v_initialLocalTimeType_2658_ = leanh::lean_ctor_get(v_rules_2652_, 0);
                v_transitions_2659_ = leanh::lean_ctor_get(v_rules_2652_, 1);
                v___x_2660_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_addWeeks___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_addWeeks___closed__0_once),
                    _init_l_Std_Time_ZonedDateTime_addWeeks___closed__0,
                );
                v___x_2661_ = lean_int_mul(v_weeks_2650_, v___x_2660_);
                v___x_2662_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_addDays___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_addDays___closed__0_once),
                    _init_l_Std_Time_ZonedDateTime_addDays___closed__0,
                );
                v___x_2663_ = lean_int_mul(v___x_2661_, v___x_2662_);
                leanh::lean_dec(v___x_2661_);
                v___x_2664_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0,
                );
                v___x_2665_ = lean_int_neg(v___x_2663_);
                leanh::lean_dec(v___x_2663_);
                v___x_2666_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
                );
                v___x_2667_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_2668_ = lean_int_mul(v_second_2656_, v___x_2667_);
                leanh::lean_dec(v_second_2656_);
                v___x_2669_ = lean_int_add(v___x_2668_, v_nano_2657_);
                leanh::lean_dec(v_nano_2657_);
                leanh::lean_dec(v___x_2668_);
                v___x_2670_ = lean_int_mul(v___x_2665_, v___x_2667_);
                leanh::lean_dec(v___x_2665_);
                v___x_2671_ = lean_int_add(v___x_2670_, v___x_2666_);
                leanh::lean_dec(v___x_2670_);
                v___x_2672_ = lean_int_add(v___x_2669_, v___x_2671_);
                leanh::lean_dec(v___x_2671_);
                leanh::lean_dec(v___x_2669_);
                v___x_2673_ = l_Std_Time_Duration_ofNanoseconds(v___x_2672_);
                leanh::lean_dec(v___x_2672_);
                v___x_2681_ =
                    l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_2659_, v___x_2673_);
                if leanh::lean_obj_tag(v___x_2681_) == 0 {
                    leanh::lean_dec_ref_known(v___x_2681_, 1);
                    v___x_2682_ =
                        l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_2658_);
                    v___y_2675_ = v___x_2682_;
                    state = 2;
                    continue;
                } else {
                    v_a_2683_ = leanh::lean_ctor_get(v___x_2681_, 0);
                    leanh::lean_inc(v_a_2683_);
                    leanh::lean_dec_ref_known(v___x_2681_, 1);
                    v___y_2675_ = v_a_2683_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc_ref(v___x_2673_);
                leanh::lean_inc_ref(v___y_2675_);
                v___f_2676_ = leanh::lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addDays___lam__0___boxed as *mut core::ffi::c_void,
                    5,
                    4,
                );
                leanh::lean_closure_set(v___f_2676_, 0, v___y_2675_);
                leanh::lean_closure_set(v___f_2676_, 1, v___x_2673_);
                leanh::lean_closure_set(v___f_2676_, 2, v___x_2667_);
                leanh::lean_closure_set(v___f_2676_, 3, v___x_2664_);
                v___x_2677_ = lean_mk_thunk(v___f_2676_);
                if v_isShared_2655_ == 0 {
                    leanh::lean_ctor_set(v___x_2654_, 3, v___y_2675_);
                    leanh::lean_ctor_set(v___x_2654_, 1, v___x_2673_);
                    leanh::lean_ctor_set(v___x_2654_, 0, v___x_2677_);
                    v___x_2679_ = v___x_2654_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2680_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2680_, 0, v___x_2677_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2680_, 1, v___x_2673_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2680_, 2, v_rules_2652_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2680_, 3, v___y_2675_);
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
    mut v_dt_2687_: *mut leanh::LeanObject,
    mut v_weeks_2688_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2689_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2689_ = l_Std_Time_ZonedDateTime_subWeeks(v_dt_2687_, v_weeks_2688_);
    leanh::lean_dec(v_weeks_2688_);
    return v_res_2689_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_addMonthsClip___lam__0(
    mut v___x_2690_: *mut leanh::LeanObject,
    mut v_x_2691_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v___x_2690_);
    return v___x_2690_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed(
    mut v___x_2692_: *mut leanh::LeanObject,
    mut v_x_2693_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2694_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2694_ = l_Std_Time_ZonedDateTime_addMonthsClip___lam__0(v___x_2692_, v_x_2693_);
    leanh::lean_dec_ref(v___x_2692_);
    return v_res_2694_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_addMonthsClip(
    mut v_dt_2695_: *mut leanh::LeanObject,
    mut v_months_2696_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_date_2697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rules_2698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2701_: u8 = 0;
    let mut v___x_2702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_wt_2704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ltt_2705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tz_2706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_2707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_2708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2724_: u8 = 0;
    let mut v_unused_2725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_2697_ = leanh::lean_ctor_get(v_dt_2695_, 0);
                v_rules_2698_ = leanh::lean_ctor_get(v_dt_2695_, 2);
                v_isSharedCheck_2724_ = (!leanh::lean_is_exclusive(v_dt_2695_)) as u8;
                if v_isSharedCheck_2724_ == 0 {
                    v_unused_2725_ = leanh::lean_ctor_get(v_dt_2695_, 3);
                    leanh::lean_dec(v_unused_2725_);
                    v_unused_2726_ = leanh::lean_ctor_get(v_dt_2695_, 1);
                    leanh::lean_dec(v_unused_2726_);
                    v___x_2700_ = v_dt_2695_;
                    v_isShared_2701_ = v_isSharedCheck_2724_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_rules_2698_);
                    leanh::lean_inc(v_date_2697_);
                    leanh::lean_dec(v_dt_2695_);
                    v___x_2700_ = leanh::lean_box(0);
                    v_isShared_2701_ = v_isSharedCheck_2724_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2702_ = lean_thunk_get_own(v_date_2697_);
                leanh::lean_dec_ref(v_date_2697_);
                v___x_2703_ = l_Std_Time_PlainDateTime_addMonthsClip(v___x_2702_, v_months_2696_);
                leanh::lean_inc_ref(v___x_2703_);
                v_wt_2704_ = l_Std_Time_PlainDateTime_toWallTime(v___x_2703_);
                leanh::lean_inc_ref(v_rules_2698_);
                v_ltt_2705_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(
                    v_rules_2698_,
                    v_wt_2704_,
                );
                v_tz_2706_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_2705_);
                leanh::lean_dec_ref(v_ltt_2705_);
                v_offset_2707_ = leanh::lean_ctor_get(v_tz_2706_, 0);
                leanh::lean_inc(v_offset_2707_);
                v_second_2708_ = leanh::lean_ctor_get(v_wt_2704_, 0);
                leanh::lean_inc(v_second_2708_);
                v_nano_2709_ = leanh::lean_ctor_get(v_wt_2704_, 1);
                leanh::lean_inc(v_nano_2709_);
                leanh::lean_dec_ref(v_wt_2704_);
                v___f_2710_ = leanh::lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v___f_2710_, 0, v___x_2703_);
                v___x_2711_ = lean_mk_thunk(v___f_2710_);
                v___x_2712_ = lean_int_neg(v_offset_2707_);
                leanh::lean_dec(v_offset_2707_);
                v___x_2713_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
                );
                v___x_2714_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_2715_ = lean_int_mul(v_second_2708_, v___x_2714_);
                leanh::lean_dec(v_second_2708_);
                v___x_2716_ = lean_int_add(v___x_2715_, v_nano_2709_);
                leanh::lean_dec(v_nano_2709_);
                leanh::lean_dec(v___x_2715_);
                v___x_2717_ = lean_int_mul(v___x_2712_, v___x_2714_);
                leanh::lean_dec(v___x_2712_);
                v___x_2718_ = lean_int_add(v___x_2717_, v___x_2713_);
                leanh::lean_dec(v___x_2717_);
                v___x_2719_ = lean_int_add(v___x_2716_, v___x_2718_);
                leanh::lean_dec(v___x_2718_);
                leanh::lean_dec(v___x_2716_);
                v___x_2720_ = l_Std_Time_Duration_ofNanoseconds(v___x_2719_);
                leanh::lean_dec(v___x_2719_);
                if v_isShared_2701_ == 0 {
                    leanh::lean_ctor_set(v___x_2700_, 3, v_tz_2706_);
                    leanh::lean_ctor_set(v___x_2700_, 1, v___x_2720_);
                    leanh::lean_ctor_set(v___x_2700_, 0, v___x_2711_);
                    v___x_2722_ = v___x_2700_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2723_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2723_, 0, v___x_2711_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2723_, 1, v___x_2720_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2723_, 2, v_rules_2698_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2723_, 3, v_tz_2706_);
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
    mut v_dt_2727_: *mut leanh::LeanObject,
    mut v_months_2728_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2729_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2729_ = l_Std_Time_ZonedDateTime_addMonthsClip(v_dt_2727_, v_months_2728_);
    leanh::lean_dec(v_months_2728_);
    return v_res_2729_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_subMonthsClip(
    mut v_dt_2730_: *mut leanh::LeanObject,
    mut v_months_2731_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_date_2732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rules_2733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2736_: u8 = 0;
    let mut v___x_2737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_2738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_2739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2742_: u8 = 0;
    let mut v___x_2743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_wt_2747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ltt_2748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tz_2749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_2750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_2751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2768_: u8 = 0;
    let mut v_isSharedCheck_2769_: u8 = 0;
    let mut v_unused_2770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_2732_ = leanh::lean_ctor_get(v_dt_2730_, 0);
                v_rules_2733_ = leanh::lean_ctor_get(v_dt_2730_, 2);
                v_isSharedCheck_2769_ = (!leanh::lean_is_exclusive(v_dt_2730_)) as u8;
                if v_isSharedCheck_2769_ == 0 {
                    v_unused_2770_ = leanh::lean_ctor_get(v_dt_2730_, 3);
                    leanh::lean_dec(v_unused_2770_);
                    v_unused_2771_ = leanh::lean_ctor_get(v_dt_2730_, 1);
                    leanh::lean_dec(v_unused_2771_);
                    v___x_2735_ = v_dt_2730_;
                    v_isShared_2736_ = v_isSharedCheck_2769_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_rules_2733_);
                    leanh::lean_inc(v_date_2732_);
                    leanh::lean_dec(v_dt_2730_);
                    v___x_2735_ = leanh::lean_box(0);
                    v_isShared_2736_ = v_isSharedCheck_2769_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2737_ = lean_thunk_get_own(v_date_2732_);
                leanh::lean_dec_ref(v_date_2732_);
                v_date_2738_ = leanh::lean_ctor_get(v___x_2737_, 0);
                v_time_2739_ = leanh::lean_ctor_get(v___x_2737_, 1);
                v_isSharedCheck_2768_ = (!leanh::lean_is_exclusive(v___x_2737_)) as u8;
                if v_isSharedCheck_2768_ == 0 {
                    v___x_2741_ = v___x_2737_;
                    v_isShared_2742_ = v_isSharedCheck_2768_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_time_2739_);
                    leanh::lean_inc(v_date_2738_);
                    leanh::lean_dec(v___x_2737_);
                    v___x_2741_ = leanh::lean_box(0);
                    v_isShared_2742_ = v_isSharedCheck_2768_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2743_ = lean_int_neg(v_months_2731_);
                v___x_2744_ = l_Std_Time_PlainDate_addMonthsClip(v_date_2738_, v___x_2743_);
                leanh::lean_dec(v___x_2743_);
                if v_isShared_2742_ == 0 {
                    leanh::lean_ctor_set(v___x_2741_, 0, v___x_2744_);
                    v___x_2746_ = v___x_2741_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2767_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2767_, 0, v___x_2744_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2767_, 1, v_time_2739_);
                    v___x_2746_ = v_reuseFailAlloc_2767_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                leanh::lean_inc_ref(v___x_2746_);
                v_wt_2747_ = l_Std_Time_PlainDateTime_toWallTime(v___x_2746_);
                leanh::lean_inc_ref(v_rules_2733_);
                v_ltt_2748_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(
                    v_rules_2733_,
                    v_wt_2747_,
                );
                v_tz_2749_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_2748_);
                leanh::lean_dec_ref(v_ltt_2748_);
                v_offset_2750_ = leanh::lean_ctor_get(v_tz_2749_, 0);
                leanh::lean_inc(v_offset_2750_);
                v_second_2751_ = leanh::lean_ctor_get(v_wt_2747_, 0);
                leanh::lean_inc(v_second_2751_);
                v_nano_2752_ = leanh::lean_ctor_get(v_wt_2747_, 1);
                leanh::lean_inc(v_nano_2752_);
                leanh::lean_dec_ref(v_wt_2747_);
                v___f_2753_ = leanh::lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v___f_2753_, 0, v___x_2746_);
                v___x_2754_ = lean_mk_thunk(v___f_2753_);
                v___x_2755_ = lean_int_neg(v_offset_2750_);
                leanh::lean_dec(v_offset_2750_);
                v___x_2756_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
                );
                v___x_2757_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_2758_ = lean_int_mul(v_second_2751_, v___x_2757_);
                leanh::lean_dec(v_second_2751_);
                v___x_2759_ = lean_int_add(v___x_2758_, v_nano_2752_);
                leanh::lean_dec(v_nano_2752_);
                leanh::lean_dec(v___x_2758_);
                v___x_2760_ = lean_int_mul(v___x_2755_, v___x_2757_);
                leanh::lean_dec(v___x_2755_);
                v___x_2761_ = lean_int_add(v___x_2760_, v___x_2756_);
                leanh::lean_dec(v___x_2760_);
                v___x_2762_ = lean_int_add(v___x_2759_, v___x_2761_);
                leanh::lean_dec(v___x_2761_);
                leanh::lean_dec(v___x_2759_);
                v___x_2763_ = l_Std_Time_Duration_ofNanoseconds(v___x_2762_);
                leanh::lean_dec(v___x_2762_);
                if v_isShared_2736_ == 0 {
                    leanh::lean_ctor_set(v___x_2735_, 3, v_tz_2749_);
                    leanh::lean_ctor_set(v___x_2735_, 1, v___x_2763_);
                    leanh::lean_ctor_set(v___x_2735_, 0, v___x_2754_);
                    v___x_2765_ = v___x_2735_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2766_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2766_, 0, v___x_2754_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2766_, 1, v___x_2763_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2766_, 2, v_rules_2733_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2766_, 3, v_tz_2749_);
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
    mut v_dt_2772_: *mut leanh::LeanObject,
    mut v_months_2773_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2774_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2774_ = l_Std_Time_ZonedDateTime_subMonthsClip(v_dt_2772_, v_months_2773_);
    leanh::lean_dec(v_months_2773_);
    return v_res_2774_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_addMonthsRollOver(
    mut v_dt_2775_: *mut leanh::LeanObject,
    mut v_months_2776_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_date_2777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rules_2778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2781_: u8 = 0;
    let mut v___x_2782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_wt_2784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ltt_2785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tz_2786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_2787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_2788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2804_: u8 = 0;
    let mut v_unused_2805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_2777_ = leanh::lean_ctor_get(v_dt_2775_, 0);
                v_rules_2778_ = leanh::lean_ctor_get(v_dt_2775_, 2);
                v_isSharedCheck_2804_ = (!leanh::lean_is_exclusive(v_dt_2775_)) as u8;
                if v_isSharedCheck_2804_ == 0 {
                    v_unused_2805_ = leanh::lean_ctor_get(v_dt_2775_, 3);
                    leanh::lean_dec(v_unused_2805_);
                    v_unused_2806_ = leanh::lean_ctor_get(v_dt_2775_, 1);
                    leanh::lean_dec(v_unused_2806_);
                    v___x_2780_ = v_dt_2775_;
                    v_isShared_2781_ = v_isSharedCheck_2804_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_rules_2778_);
                    leanh::lean_inc(v_date_2777_);
                    leanh::lean_dec(v_dt_2775_);
                    v___x_2780_ = leanh::lean_box(0);
                    v_isShared_2781_ = v_isSharedCheck_2804_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2782_ = lean_thunk_get_own(v_date_2777_);
                leanh::lean_dec_ref(v_date_2777_);
                v___x_2783_ =
                    l_Std_Time_PlainDateTime_addMonthsRollOver(v___x_2782_, v_months_2776_);
                leanh::lean_inc_ref(v___x_2783_);
                v_wt_2784_ = l_Std_Time_PlainDateTime_toWallTime(v___x_2783_);
                leanh::lean_inc_ref(v_rules_2778_);
                v_ltt_2785_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(
                    v_rules_2778_,
                    v_wt_2784_,
                );
                v_tz_2786_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_2785_);
                leanh::lean_dec_ref(v_ltt_2785_);
                v_offset_2787_ = leanh::lean_ctor_get(v_tz_2786_, 0);
                leanh::lean_inc(v_offset_2787_);
                v_second_2788_ = leanh::lean_ctor_get(v_wt_2784_, 0);
                leanh::lean_inc(v_second_2788_);
                v_nano_2789_ = leanh::lean_ctor_get(v_wt_2784_, 1);
                leanh::lean_inc(v_nano_2789_);
                leanh::lean_dec_ref(v_wt_2784_);
                v___f_2790_ = leanh::lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v___f_2790_, 0, v___x_2783_);
                v___x_2791_ = lean_mk_thunk(v___f_2790_);
                v___x_2792_ = lean_int_neg(v_offset_2787_);
                leanh::lean_dec(v_offset_2787_);
                v___x_2793_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
                );
                v___x_2794_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_2795_ = lean_int_mul(v_second_2788_, v___x_2794_);
                leanh::lean_dec(v_second_2788_);
                v___x_2796_ = lean_int_add(v___x_2795_, v_nano_2789_);
                leanh::lean_dec(v_nano_2789_);
                leanh::lean_dec(v___x_2795_);
                v___x_2797_ = lean_int_mul(v___x_2792_, v___x_2794_);
                leanh::lean_dec(v___x_2792_);
                v___x_2798_ = lean_int_add(v___x_2797_, v___x_2793_);
                leanh::lean_dec(v___x_2797_);
                v___x_2799_ = lean_int_add(v___x_2796_, v___x_2798_);
                leanh::lean_dec(v___x_2798_);
                leanh::lean_dec(v___x_2796_);
                v___x_2800_ = l_Std_Time_Duration_ofNanoseconds(v___x_2799_);
                leanh::lean_dec(v___x_2799_);
                if v_isShared_2781_ == 0 {
                    leanh::lean_ctor_set(v___x_2780_, 3, v_tz_2786_);
                    leanh::lean_ctor_set(v___x_2780_, 1, v___x_2800_);
                    leanh::lean_ctor_set(v___x_2780_, 0, v___x_2791_);
                    v___x_2802_ = v___x_2780_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2803_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2803_, 0, v___x_2791_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2803_, 1, v___x_2800_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2803_, 2, v_rules_2778_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2803_, 3, v_tz_2786_);
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
    mut v_dt_2807_: *mut leanh::LeanObject,
    mut v_months_2808_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2809_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2809_ = l_Std_Time_ZonedDateTime_addMonthsRollOver(v_dt_2807_, v_months_2808_);
    leanh::lean_dec(v_months_2808_);
    return v_res_2809_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_subMonthsRollOver(
    mut v_dt_2810_: *mut leanh::LeanObject,
    mut v_months_2811_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_date_2812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rules_2813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2816_: u8 = 0;
    let mut v___x_2817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_2818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_2819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2822_: u8 = 0;
    let mut v___x_2823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_wt_2827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ltt_2828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tz_2829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_2830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_2831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2848_: u8 = 0;
    let mut v_isSharedCheck_2849_: u8 = 0;
    let mut v_unused_2850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_2812_ = leanh::lean_ctor_get(v_dt_2810_, 0);
                v_rules_2813_ = leanh::lean_ctor_get(v_dt_2810_, 2);
                v_isSharedCheck_2849_ = (!leanh::lean_is_exclusive(v_dt_2810_)) as u8;
                if v_isSharedCheck_2849_ == 0 {
                    v_unused_2850_ = leanh::lean_ctor_get(v_dt_2810_, 3);
                    leanh::lean_dec(v_unused_2850_);
                    v_unused_2851_ = leanh::lean_ctor_get(v_dt_2810_, 1);
                    leanh::lean_dec(v_unused_2851_);
                    v___x_2815_ = v_dt_2810_;
                    v_isShared_2816_ = v_isSharedCheck_2849_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_rules_2813_);
                    leanh::lean_inc(v_date_2812_);
                    leanh::lean_dec(v_dt_2810_);
                    v___x_2815_ = leanh::lean_box(0);
                    v_isShared_2816_ = v_isSharedCheck_2849_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2817_ = lean_thunk_get_own(v_date_2812_);
                leanh::lean_dec_ref(v_date_2812_);
                v_date_2818_ = leanh::lean_ctor_get(v___x_2817_, 0);
                v_time_2819_ = leanh::lean_ctor_get(v___x_2817_, 1);
                v_isSharedCheck_2848_ = (!leanh::lean_is_exclusive(v___x_2817_)) as u8;
                if v_isSharedCheck_2848_ == 0 {
                    v___x_2821_ = v___x_2817_;
                    v_isShared_2822_ = v_isSharedCheck_2848_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_time_2819_);
                    leanh::lean_inc(v_date_2818_);
                    leanh::lean_dec(v___x_2817_);
                    v___x_2821_ = leanh::lean_box(0);
                    v_isShared_2822_ = v_isSharedCheck_2848_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2823_ = lean_int_neg(v_months_2811_);
                v___x_2824_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_2818_, v___x_2823_);
                leanh::lean_dec(v___x_2823_);
                if v_isShared_2822_ == 0 {
                    leanh::lean_ctor_set(v___x_2821_, 0, v___x_2824_);
                    v___x_2826_ = v___x_2821_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2847_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2847_, 0, v___x_2824_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2847_, 1, v_time_2819_);
                    v___x_2826_ = v_reuseFailAlloc_2847_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                leanh::lean_inc_ref(v___x_2826_);
                v_wt_2827_ = l_Std_Time_PlainDateTime_toWallTime(v___x_2826_);
                leanh::lean_inc_ref(v_rules_2813_);
                v_ltt_2828_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(
                    v_rules_2813_,
                    v_wt_2827_,
                );
                v_tz_2829_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_2828_);
                leanh::lean_dec_ref(v_ltt_2828_);
                v_offset_2830_ = leanh::lean_ctor_get(v_tz_2829_, 0);
                leanh::lean_inc(v_offset_2830_);
                v_second_2831_ = leanh::lean_ctor_get(v_wt_2827_, 0);
                leanh::lean_inc(v_second_2831_);
                v_nano_2832_ = leanh::lean_ctor_get(v_wt_2827_, 1);
                leanh::lean_inc(v_nano_2832_);
                leanh::lean_dec_ref(v_wt_2827_);
                v___f_2833_ = leanh::lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v___f_2833_, 0, v___x_2826_);
                v___x_2834_ = lean_mk_thunk(v___f_2833_);
                v___x_2835_ = lean_int_neg(v_offset_2830_);
                leanh::lean_dec(v_offset_2830_);
                v___x_2836_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
                );
                v___x_2837_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_2838_ = lean_int_mul(v_second_2831_, v___x_2837_);
                leanh::lean_dec(v_second_2831_);
                v___x_2839_ = lean_int_add(v___x_2838_, v_nano_2832_);
                leanh::lean_dec(v_nano_2832_);
                leanh::lean_dec(v___x_2838_);
                v___x_2840_ = lean_int_mul(v___x_2835_, v___x_2837_);
                leanh::lean_dec(v___x_2835_);
                v___x_2841_ = lean_int_add(v___x_2840_, v___x_2836_);
                leanh::lean_dec(v___x_2840_);
                v___x_2842_ = lean_int_add(v___x_2839_, v___x_2841_);
                leanh::lean_dec(v___x_2841_);
                leanh::lean_dec(v___x_2839_);
                v___x_2843_ = l_Std_Time_Duration_ofNanoseconds(v___x_2842_);
                leanh::lean_dec(v___x_2842_);
                if v_isShared_2816_ == 0 {
                    leanh::lean_ctor_set(v___x_2815_, 3, v_tz_2829_);
                    leanh::lean_ctor_set(v___x_2815_, 1, v___x_2843_);
                    leanh::lean_ctor_set(v___x_2815_, 0, v___x_2834_);
                    v___x_2845_ = v___x_2815_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2846_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2846_, 0, v___x_2834_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2846_, 1, v___x_2843_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2846_, 2, v_rules_2813_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2846_, 3, v_tz_2829_);
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
    mut v_dt_2852_: *mut leanh::LeanObject,
    mut v_months_2853_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2854_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2854_ = l_Std_Time_ZonedDateTime_subMonthsRollOver(v_dt_2852_, v_months_2853_);
    leanh::lean_dec(v_months_2853_);
    return v_res_2854_;
}
pub unsafe fn _init_l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2856_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2855_ = leanh::lean_unsigned_to_nat(12);
    v___x_2856_ = lean_nat_to_int(v___x_2855_);
    return v___x_2856_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_addYearsRollOver(
    mut v_dt_2857_: *mut leanh::LeanObject,
    mut v_years_2858_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_date_2859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rules_2860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2863_: u8 = 0;
    let mut v___x_2864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_2865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_2866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2869_: u8 = 0;
    let mut v___x_2870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_wt_2875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ltt_2876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tz_2877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_2878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_2879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2896_: u8 = 0;
    let mut v_isSharedCheck_2897_: u8 = 0;
    let mut v_unused_2898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_2859_ = leanh::lean_ctor_get(v_dt_2857_, 0);
                v_rules_2860_ = leanh::lean_ctor_get(v_dt_2857_, 2);
                v_isSharedCheck_2897_ = (!leanh::lean_is_exclusive(v_dt_2857_)) as u8;
                if v_isSharedCheck_2897_ == 0 {
                    v_unused_2898_ = leanh::lean_ctor_get(v_dt_2857_, 3);
                    leanh::lean_dec(v_unused_2898_);
                    v_unused_2899_ = leanh::lean_ctor_get(v_dt_2857_, 1);
                    leanh::lean_dec(v_unused_2899_);
                    v___x_2862_ = v_dt_2857_;
                    v_isShared_2863_ = v_isSharedCheck_2897_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_rules_2860_);
                    leanh::lean_inc(v_date_2859_);
                    leanh::lean_dec(v_dt_2857_);
                    v___x_2862_ = leanh::lean_box(0);
                    v_isShared_2863_ = v_isSharedCheck_2897_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2864_ = lean_thunk_get_own(v_date_2859_);
                leanh::lean_dec_ref(v_date_2859_);
                v_date_2865_ = leanh::lean_ctor_get(v___x_2864_, 0);
                v_time_2866_ = leanh::lean_ctor_get(v___x_2864_, 1);
                v_isSharedCheck_2896_ = (!leanh::lean_is_exclusive(v___x_2864_)) as u8;
                if v_isSharedCheck_2896_ == 0 {
                    v___x_2868_ = v___x_2864_;
                    v_isShared_2869_ = v_isSharedCheck_2896_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_time_2866_);
                    leanh::lean_inc(v_date_2865_);
                    leanh::lean_dec(v___x_2864_);
                    v___x_2868_ = leanh::lean_box(0);
                    v_isShared_2869_ = v_isSharedCheck_2896_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2870_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0,
                );
                v___x_2871_ = lean_int_mul(v_years_2858_, v___x_2870_);
                v___x_2872_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_2865_, v___x_2871_);
                leanh::lean_dec(v___x_2871_);
                if v_isShared_2869_ == 0 {
                    leanh::lean_ctor_set(v___x_2868_, 0, v___x_2872_);
                    v___x_2874_ = v___x_2868_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2895_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2895_, 0, v___x_2872_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2895_, 1, v_time_2866_);
                    v___x_2874_ = v_reuseFailAlloc_2895_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                leanh::lean_inc_ref(v___x_2874_);
                v_wt_2875_ = l_Std_Time_PlainDateTime_toWallTime(v___x_2874_);
                leanh::lean_inc_ref(v_rules_2860_);
                v_ltt_2876_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(
                    v_rules_2860_,
                    v_wt_2875_,
                );
                v_tz_2877_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_2876_);
                leanh::lean_dec_ref(v_ltt_2876_);
                v_offset_2878_ = leanh::lean_ctor_get(v_tz_2877_, 0);
                leanh::lean_inc(v_offset_2878_);
                v_second_2879_ = leanh::lean_ctor_get(v_wt_2875_, 0);
                leanh::lean_inc(v_second_2879_);
                v_nano_2880_ = leanh::lean_ctor_get(v_wt_2875_, 1);
                leanh::lean_inc(v_nano_2880_);
                leanh::lean_dec_ref(v_wt_2875_);
                v___f_2881_ = leanh::lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v___f_2881_, 0, v___x_2874_);
                v___x_2882_ = lean_mk_thunk(v___f_2881_);
                v___x_2883_ = lean_int_neg(v_offset_2878_);
                leanh::lean_dec(v_offset_2878_);
                v___x_2884_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
                );
                v___x_2885_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_2886_ = lean_int_mul(v_second_2879_, v___x_2885_);
                leanh::lean_dec(v_second_2879_);
                v___x_2887_ = lean_int_add(v___x_2886_, v_nano_2880_);
                leanh::lean_dec(v_nano_2880_);
                leanh::lean_dec(v___x_2886_);
                v___x_2888_ = lean_int_mul(v___x_2883_, v___x_2885_);
                leanh::lean_dec(v___x_2883_);
                v___x_2889_ = lean_int_add(v___x_2888_, v___x_2884_);
                leanh::lean_dec(v___x_2888_);
                v___x_2890_ = lean_int_add(v___x_2887_, v___x_2889_);
                leanh::lean_dec(v___x_2889_);
                leanh::lean_dec(v___x_2887_);
                v___x_2891_ = l_Std_Time_Duration_ofNanoseconds(v___x_2890_);
                leanh::lean_dec(v___x_2890_);
                if v_isShared_2863_ == 0 {
                    leanh::lean_ctor_set(v___x_2862_, 3, v_tz_2877_);
                    leanh::lean_ctor_set(v___x_2862_, 1, v___x_2891_);
                    leanh::lean_ctor_set(v___x_2862_, 0, v___x_2882_);
                    v___x_2893_ = v___x_2862_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2894_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2894_, 0, v___x_2882_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2894_, 1, v___x_2891_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2894_, 2, v_rules_2860_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2894_, 3, v_tz_2877_);
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
    mut v_dt_2900_: *mut leanh::LeanObject,
    mut v_years_2901_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2902_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2902_ = l_Std_Time_ZonedDateTime_addYearsRollOver(v_dt_2900_, v_years_2901_);
    leanh::lean_dec(v_years_2901_);
    return v_res_2902_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_addYearsClip(
    mut v_dt_2903_: *mut leanh::LeanObject,
    mut v_years_2904_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_date_2905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rules_2906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2909_: u8 = 0;
    let mut v___x_2910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_2911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_2912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2915_: u8 = 0;
    let mut v___x_2916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_wt_2921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ltt_2922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tz_2923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_2924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_2925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2942_: u8 = 0;
    let mut v_isSharedCheck_2943_: u8 = 0;
    let mut v_unused_2944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_2905_ = leanh::lean_ctor_get(v_dt_2903_, 0);
                v_rules_2906_ = leanh::lean_ctor_get(v_dt_2903_, 2);
                v_isSharedCheck_2943_ = (!leanh::lean_is_exclusive(v_dt_2903_)) as u8;
                if v_isSharedCheck_2943_ == 0 {
                    v_unused_2944_ = leanh::lean_ctor_get(v_dt_2903_, 3);
                    leanh::lean_dec(v_unused_2944_);
                    v_unused_2945_ = leanh::lean_ctor_get(v_dt_2903_, 1);
                    leanh::lean_dec(v_unused_2945_);
                    v___x_2908_ = v_dt_2903_;
                    v_isShared_2909_ = v_isSharedCheck_2943_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_rules_2906_);
                    leanh::lean_inc(v_date_2905_);
                    leanh::lean_dec(v_dt_2903_);
                    v___x_2908_ = leanh::lean_box(0);
                    v_isShared_2909_ = v_isSharedCheck_2943_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2910_ = lean_thunk_get_own(v_date_2905_);
                leanh::lean_dec_ref(v_date_2905_);
                v_date_2911_ = leanh::lean_ctor_get(v___x_2910_, 0);
                v_time_2912_ = leanh::lean_ctor_get(v___x_2910_, 1);
                v_isSharedCheck_2942_ = (!leanh::lean_is_exclusive(v___x_2910_)) as u8;
                if v_isSharedCheck_2942_ == 0 {
                    v___x_2914_ = v___x_2910_;
                    v_isShared_2915_ = v_isSharedCheck_2942_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_time_2912_);
                    leanh::lean_inc(v_date_2911_);
                    leanh::lean_dec(v___x_2910_);
                    v___x_2914_ = leanh::lean_box(0);
                    v_isShared_2915_ = v_isSharedCheck_2942_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2916_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0,
                );
                v___x_2917_ = lean_int_mul(v_years_2904_, v___x_2916_);
                v___x_2918_ = l_Std_Time_PlainDate_addMonthsClip(v_date_2911_, v___x_2917_);
                leanh::lean_dec(v___x_2917_);
                if v_isShared_2915_ == 0 {
                    leanh::lean_ctor_set(v___x_2914_, 0, v___x_2918_);
                    v___x_2920_ = v___x_2914_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2941_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2941_, 0, v___x_2918_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2941_, 1, v_time_2912_);
                    v___x_2920_ = v_reuseFailAlloc_2941_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                leanh::lean_inc_ref(v___x_2920_);
                v_wt_2921_ = l_Std_Time_PlainDateTime_toWallTime(v___x_2920_);
                leanh::lean_inc_ref(v_rules_2906_);
                v_ltt_2922_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(
                    v_rules_2906_,
                    v_wt_2921_,
                );
                v_tz_2923_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_2922_);
                leanh::lean_dec_ref(v_ltt_2922_);
                v_offset_2924_ = leanh::lean_ctor_get(v_tz_2923_, 0);
                leanh::lean_inc(v_offset_2924_);
                v_second_2925_ = leanh::lean_ctor_get(v_wt_2921_, 0);
                leanh::lean_inc(v_second_2925_);
                v_nano_2926_ = leanh::lean_ctor_get(v_wt_2921_, 1);
                leanh::lean_inc(v_nano_2926_);
                leanh::lean_dec_ref(v_wt_2921_);
                v___f_2927_ = leanh::lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v___f_2927_, 0, v___x_2920_);
                v___x_2928_ = lean_mk_thunk(v___f_2927_);
                v___x_2929_ = lean_int_neg(v_offset_2924_);
                leanh::lean_dec(v_offset_2924_);
                v___x_2930_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
                );
                v___x_2931_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_2932_ = lean_int_mul(v_second_2925_, v___x_2931_);
                leanh::lean_dec(v_second_2925_);
                v___x_2933_ = lean_int_add(v___x_2932_, v_nano_2926_);
                leanh::lean_dec(v_nano_2926_);
                leanh::lean_dec(v___x_2932_);
                v___x_2934_ = lean_int_mul(v___x_2929_, v___x_2931_);
                leanh::lean_dec(v___x_2929_);
                v___x_2935_ = lean_int_add(v___x_2934_, v___x_2930_);
                leanh::lean_dec(v___x_2934_);
                v___x_2936_ = lean_int_add(v___x_2933_, v___x_2935_);
                leanh::lean_dec(v___x_2935_);
                leanh::lean_dec(v___x_2933_);
                v___x_2937_ = l_Std_Time_Duration_ofNanoseconds(v___x_2936_);
                leanh::lean_dec(v___x_2936_);
                if v_isShared_2909_ == 0 {
                    leanh::lean_ctor_set(v___x_2908_, 3, v_tz_2923_);
                    leanh::lean_ctor_set(v___x_2908_, 1, v___x_2937_);
                    leanh::lean_ctor_set(v___x_2908_, 0, v___x_2928_);
                    v___x_2939_ = v___x_2908_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2940_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2940_, 0, v___x_2928_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2940_, 1, v___x_2937_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2940_, 2, v_rules_2906_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2940_, 3, v_tz_2923_);
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
    mut v_dt_2946_: *mut leanh::LeanObject,
    mut v_years_2947_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2948_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2948_ = l_Std_Time_ZonedDateTime_addYearsClip(v_dt_2946_, v_years_2947_);
    leanh::lean_dec(v_years_2947_);
    return v_res_2948_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_subYearsClip(
    mut v_dt_2949_: *mut leanh::LeanObject,
    mut v_years_2950_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_date_2951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rules_2952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2955_: u8 = 0;
    let mut v___x_2956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_2957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_2958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2961_: u8 = 0;
    let mut v___x_2962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_wt_2968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ltt_2969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tz_2970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_2971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_2972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2989_: u8 = 0;
    let mut v_isSharedCheck_2990_: u8 = 0;
    let mut v_unused_2991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_2951_ = leanh::lean_ctor_get(v_dt_2949_, 0);
                v_rules_2952_ = leanh::lean_ctor_get(v_dt_2949_, 2);
                v_isSharedCheck_2990_ = (!leanh::lean_is_exclusive(v_dt_2949_)) as u8;
                if v_isSharedCheck_2990_ == 0 {
                    v_unused_2991_ = leanh::lean_ctor_get(v_dt_2949_, 3);
                    leanh::lean_dec(v_unused_2991_);
                    v_unused_2992_ = leanh::lean_ctor_get(v_dt_2949_, 1);
                    leanh::lean_dec(v_unused_2992_);
                    v___x_2954_ = v_dt_2949_;
                    v_isShared_2955_ = v_isSharedCheck_2990_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_rules_2952_);
                    leanh::lean_inc(v_date_2951_);
                    leanh::lean_dec(v_dt_2949_);
                    v___x_2954_ = leanh::lean_box(0);
                    v_isShared_2955_ = v_isSharedCheck_2990_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2956_ = lean_thunk_get_own(v_date_2951_);
                leanh::lean_dec_ref(v_date_2951_);
                v_date_2957_ = leanh::lean_ctor_get(v___x_2956_, 0);
                v_time_2958_ = leanh::lean_ctor_get(v___x_2956_, 1);
                v_isSharedCheck_2989_ = (!leanh::lean_is_exclusive(v___x_2956_)) as u8;
                if v_isSharedCheck_2989_ == 0 {
                    v___x_2960_ = v___x_2956_;
                    v_isShared_2961_ = v_isSharedCheck_2989_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_time_2958_);
                    leanh::lean_inc(v_date_2957_);
                    leanh::lean_dec(v___x_2956_);
                    v___x_2960_ = leanh::lean_box(0);
                    v_isShared_2961_ = v_isSharedCheck_2989_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2962_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0,
                );
                v___x_2963_ = lean_int_mul(v_years_2950_, v___x_2962_);
                v___x_2964_ = lean_int_neg(v___x_2963_);
                leanh::lean_dec(v___x_2963_);
                v___x_2965_ = l_Std_Time_PlainDate_addMonthsClip(v_date_2957_, v___x_2964_);
                leanh::lean_dec(v___x_2964_);
                if v_isShared_2961_ == 0 {
                    leanh::lean_ctor_set(v___x_2960_, 0, v___x_2965_);
                    v___x_2967_ = v___x_2960_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2988_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2988_, 0, v___x_2965_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2988_, 1, v_time_2958_);
                    v___x_2967_ = v_reuseFailAlloc_2988_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                leanh::lean_inc_ref(v___x_2967_);
                v_wt_2968_ = l_Std_Time_PlainDateTime_toWallTime(v___x_2967_);
                leanh::lean_inc_ref(v_rules_2952_);
                v_ltt_2969_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(
                    v_rules_2952_,
                    v_wt_2968_,
                );
                v_tz_2970_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_2969_);
                leanh::lean_dec_ref(v_ltt_2969_);
                v_offset_2971_ = leanh::lean_ctor_get(v_tz_2970_, 0);
                leanh::lean_inc(v_offset_2971_);
                v_second_2972_ = leanh::lean_ctor_get(v_wt_2968_, 0);
                leanh::lean_inc(v_second_2972_);
                v_nano_2973_ = leanh::lean_ctor_get(v_wt_2968_, 1);
                leanh::lean_inc(v_nano_2973_);
                leanh::lean_dec_ref(v_wt_2968_);
                v___f_2974_ = leanh::lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v___f_2974_, 0, v___x_2967_);
                v___x_2975_ = lean_mk_thunk(v___f_2974_);
                v___x_2976_ = lean_int_neg(v_offset_2971_);
                leanh::lean_dec(v_offset_2971_);
                v___x_2977_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
                );
                v___x_2978_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_2979_ = lean_int_mul(v_second_2972_, v___x_2978_);
                leanh::lean_dec(v_second_2972_);
                v___x_2980_ = lean_int_add(v___x_2979_, v_nano_2973_);
                leanh::lean_dec(v_nano_2973_);
                leanh::lean_dec(v___x_2979_);
                v___x_2981_ = lean_int_mul(v___x_2976_, v___x_2978_);
                leanh::lean_dec(v___x_2976_);
                v___x_2982_ = lean_int_add(v___x_2981_, v___x_2977_);
                leanh::lean_dec(v___x_2981_);
                v___x_2983_ = lean_int_add(v___x_2980_, v___x_2982_);
                leanh::lean_dec(v___x_2982_);
                leanh::lean_dec(v___x_2980_);
                v___x_2984_ = l_Std_Time_Duration_ofNanoseconds(v___x_2983_);
                leanh::lean_dec(v___x_2983_);
                if v_isShared_2955_ == 0 {
                    leanh::lean_ctor_set(v___x_2954_, 3, v_tz_2970_);
                    leanh::lean_ctor_set(v___x_2954_, 1, v___x_2984_);
                    leanh::lean_ctor_set(v___x_2954_, 0, v___x_2975_);
                    v___x_2986_ = v___x_2954_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2987_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2987_, 0, v___x_2975_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2987_, 1, v___x_2984_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2987_, 2, v_rules_2952_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2987_, 3, v_tz_2970_);
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
    mut v_dt_2993_: *mut leanh::LeanObject,
    mut v_years_2994_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2995_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2995_ = l_Std_Time_ZonedDateTime_subYearsClip(v_dt_2993_, v_years_2994_);
    leanh::lean_dec(v_years_2994_);
    return v_res_2995_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_subYearsRollOver(
    mut v_dt_2996_: *mut leanh::LeanObject,
    mut v_years_2997_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_date_2998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rules_2999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3002_: u8 = 0;
    let mut v___x_3003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_3004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_3005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3008_: u8 = 0;
    let mut v___x_3009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_wt_3015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ltt_3016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tz_3017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_3018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_3020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3036_: u8 = 0;
    let mut v_isSharedCheck_3037_: u8 = 0;
    let mut v_unused_3038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_2998_ = leanh::lean_ctor_get(v_dt_2996_, 0);
                v_rules_2999_ = leanh::lean_ctor_get(v_dt_2996_, 2);
                v_isSharedCheck_3037_ = (!leanh::lean_is_exclusive(v_dt_2996_)) as u8;
                if v_isSharedCheck_3037_ == 0 {
                    v_unused_3038_ = leanh::lean_ctor_get(v_dt_2996_, 3);
                    leanh::lean_dec(v_unused_3038_);
                    v_unused_3039_ = leanh::lean_ctor_get(v_dt_2996_, 1);
                    leanh::lean_dec(v_unused_3039_);
                    v___x_3001_ = v_dt_2996_;
                    v_isShared_3002_ = v_isSharedCheck_3037_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_rules_2999_);
                    leanh::lean_inc(v_date_2998_);
                    leanh::lean_dec(v_dt_2996_);
                    v___x_3001_ = leanh::lean_box(0);
                    v_isShared_3002_ = v_isSharedCheck_3037_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3003_ = lean_thunk_get_own(v_date_2998_);
                leanh::lean_dec_ref(v_date_2998_);
                v_date_3004_ = leanh::lean_ctor_get(v___x_3003_, 0);
                v_time_3005_ = leanh::lean_ctor_get(v___x_3003_, 1);
                v_isSharedCheck_3036_ = (!leanh::lean_is_exclusive(v___x_3003_)) as u8;
                if v_isSharedCheck_3036_ == 0 {
                    v___x_3007_ = v___x_3003_;
                    v_isShared_3008_ = v_isSharedCheck_3036_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_time_3005_);
                    leanh::lean_inc(v_date_3004_);
                    leanh::lean_dec(v___x_3003_);
                    v___x_3007_ = leanh::lean_box(0);
                    v_isShared_3008_ = v_isSharedCheck_3036_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3009_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0,
                );
                v___x_3010_ = lean_int_mul(v_years_2997_, v___x_3009_);
                v___x_3011_ = lean_int_neg(v___x_3010_);
                leanh::lean_dec(v___x_3010_);
                v___x_3012_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_3004_, v___x_3011_);
                leanh::lean_dec(v___x_3011_);
                if v_isShared_3008_ == 0 {
                    leanh::lean_ctor_set(v___x_3007_, 0, v___x_3012_);
                    v___x_3014_ = v___x_3007_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3035_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3035_, 0, v___x_3012_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3035_, 1, v_time_3005_);
                    v___x_3014_ = v_reuseFailAlloc_3035_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                leanh::lean_inc_ref(v___x_3014_);
                v_wt_3015_ = l_Std_Time_PlainDateTime_toWallTime(v___x_3014_);
                leanh::lean_inc_ref(v_rules_2999_);
                v_ltt_3016_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(
                    v_rules_2999_,
                    v_wt_3015_,
                );
                v_tz_3017_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_3016_);
                leanh::lean_dec_ref(v_ltt_3016_);
                v_offset_3018_ = leanh::lean_ctor_get(v_tz_3017_, 0);
                leanh::lean_inc(v_offset_3018_);
                v_second_3019_ = leanh::lean_ctor_get(v_wt_3015_, 0);
                leanh::lean_inc(v_second_3019_);
                v_nano_3020_ = leanh::lean_ctor_get(v_wt_3015_, 1);
                leanh::lean_inc(v_nano_3020_);
                leanh::lean_dec_ref(v_wt_3015_);
                v___f_3021_ = leanh::lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v___f_3021_, 0, v___x_3014_);
                v___x_3022_ = lean_mk_thunk(v___f_3021_);
                v___x_3023_ = lean_int_neg(v_offset_3018_);
                leanh::lean_dec(v_offset_3018_);
                v___x_3024_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
                );
                v___x_3025_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3026_ = lean_int_mul(v_second_3019_, v___x_3025_);
                leanh::lean_dec(v_second_3019_);
                v___x_3027_ = lean_int_add(v___x_3026_, v_nano_3020_);
                leanh::lean_dec(v_nano_3020_);
                leanh::lean_dec(v___x_3026_);
                v___x_3028_ = lean_int_mul(v___x_3023_, v___x_3025_);
                leanh::lean_dec(v___x_3023_);
                v___x_3029_ = lean_int_add(v___x_3028_, v___x_3024_);
                leanh::lean_dec(v___x_3028_);
                v___x_3030_ = lean_int_add(v___x_3027_, v___x_3029_);
                leanh::lean_dec(v___x_3029_);
                leanh::lean_dec(v___x_3027_);
                v___x_3031_ = l_Std_Time_Duration_ofNanoseconds(v___x_3030_);
                leanh::lean_dec(v___x_3030_);
                if v_isShared_3002_ == 0 {
                    leanh::lean_ctor_set(v___x_3001_, 3, v_tz_3017_);
                    leanh::lean_ctor_set(v___x_3001_, 1, v___x_3031_);
                    leanh::lean_ctor_set(v___x_3001_, 0, v___x_3022_);
                    v___x_3033_ = v___x_3001_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3034_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3034_, 0, v___x_3022_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3034_, 1, v___x_3031_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3034_, 2, v_rules_2999_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3034_, 3, v_tz_3017_);
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
    mut v_dt_3040_: *mut leanh::LeanObject,
    mut v_years_3041_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3042_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3042_ = l_Std_Time_ZonedDateTime_subYearsRollOver(v_dt_3040_, v_years_3041_);
    leanh::lean_dec(v_years_3041_);
    return v_res_3042_;
}
pub unsafe fn _init_l_Std_Time_ZonedDateTime_addHours___closed__0() -> *mut leanh::LeanObject
{
    let mut v___x_3043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3043_ = leanh::lean_unsigned_to_nat(3600);
    v___x_3044_ = lean_nat_to_int(v___x_3043_);
    return v___x_3044_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_addHours(
    mut v_dt_3045_: *mut leanh::LeanObject,
    mut v_hours_3046_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_timestamp_3047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rules_3048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3051_: u8 = 0;
    let mut v_second_3052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_3053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initialLocalTimeType_3054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_transitions_3055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3076_: u8 = 0;
    let mut v_unused_3077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_3047_ = leanh::lean_ctor_get(v_dt_3045_, 1);
                v_rules_3048_ = leanh::lean_ctor_get(v_dt_3045_, 2);
                v_isSharedCheck_3076_ = (!leanh::lean_is_exclusive(v_dt_3045_)) as u8;
                if v_isSharedCheck_3076_ == 0 {
                    v_unused_3077_ = leanh::lean_ctor_get(v_dt_3045_, 3);
                    leanh::lean_dec(v_unused_3077_);
                    v_unused_3078_ = leanh::lean_ctor_get(v_dt_3045_, 0);
                    leanh::lean_dec(v_unused_3078_);
                    v___x_3050_ = v_dt_3045_;
                    v_isShared_3051_ = v_isSharedCheck_3076_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_rules_3048_);
                    leanh::lean_inc(v_timestamp_3047_);
                    leanh::lean_dec(v_dt_3045_);
                    v___x_3050_ = leanh::lean_box(0);
                    v_isShared_3051_ = v_isSharedCheck_3076_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_second_3052_ = leanh::lean_ctor_get(v_timestamp_3047_, 0);
                leanh::lean_inc(v_second_3052_);
                v_nano_3053_ = leanh::lean_ctor_get(v_timestamp_3047_, 1);
                leanh::lean_inc(v_nano_3053_);
                leanh::lean_dec_ref(v_timestamp_3047_);
                v_initialLocalTimeType_3054_ = leanh::lean_ctor_get(v_rules_3048_, 0);
                v_transitions_3055_ = leanh::lean_ctor_get(v_rules_3048_, 1);
                v___x_3056_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_addHours___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_addHours___closed__0_once),
                    _init_l_Std_Time_ZonedDateTime_addHours___closed__0,
                );
                v___x_3057_ = lean_int_mul(v_hours_3046_, v___x_3056_);
                v___x_3058_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0,
                );
                v___x_3059_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3060_ = lean_int_mul(v_second_3052_, v___x_3059_);
                leanh::lean_dec(v_second_3052_);
                v___x_3061_ = lean_int_add(v___x_3060_, v_nano_3053_);
                leanh::lean_dec(v_nano_3053_);
                leanh::lean_dec(v___x_3060_);
                v___x_3062_ = lean_int_mul(v___x_3057_, v___x_3059_);
                leanh::lean_dec(v___x_3057_);
                v___x_3063_ = lean_int_add(v___x_3062_, v___x_3058_);
                leanh::lean_dec(v___x_3062_);
                v___x_3064_ = lean_int_add(v___x_3061_, v___x_3063_);
                leanh::lean_dec(v___x_3063_);
                leanh::lean_dec(v___x_3061_);
                v___x_3065_ = l_Std_Time_Duration_ofNanoseconds(v___x_3064_);
                leanh::lean_dec(v___x_3064_);
                v___x_3073_ =
                    l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_3055_, v___x_3065_);
                if leanh::lean_obj_tag(v___x_3073_) == 0 {
                    leanh::lean_dec_ref_known(v___x_3073_, 1);
                    v___x_3074_ =
                        l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_3054_);
                    v___y_3067_ = v___x_3074_;
                    state = 2;
                    continue;
                } else {
                    v_a_3075_ = leanh::lean_ctor_get(v___x_3073_, 0);
                    leanh::lean_inc(v_a_3075_);
                    leanh::lean_dec_ref_known(v___x_3073_, 1);
                    v___y_3067_ = v_a_3075_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc_ref(v___x_3065_);
                leanh::lean_inc_ref(v___y_3067_);
                v___f_3068_ = leanh::lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addDays___lam__0___boxed as *mut core::ffi::c_void,
                    5,
                    4,
                );
                leanh::lean_closure_set(v___f_3068_, 0, v___y_3067_);
                leanh::lean_closure_set(v___f_3068_, 1, v___x_3065_);
                leanh::lean_closure_set(v___f_3068_, 2, v___x_3059_);
                leanh::lean_closure_set(v___f_3068_, 3, v___x_3058_);
                v___x_3069_ = lean_mk_thunk(v___f_3068_);
                if v_isShared_3051_ == 0 {
                    leanh::lean_ctor_set(v___x_3050_, 3, v___y_3067_);
                    leanh::lean_ctor_set(v___x_3050_, 1, v___x_3065_);
                    leanh::lean_ctor_set(v___x_3050_, 0, v___x_3069_);
                    v___x_3071_ = v___x_3050_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3072_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3072_, 0, v___x_3069_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3072_, 1, v___x_3065_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3072_, 2, v_rules_3048_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3072_, 3, v___y_3067_);
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
    mut v_dt_3079_: *mut leanh::LeanObject,
    mut v_hours_3080_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3081_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3081_ = l_Std_Time_ZonedDateTime_addHours(v_dt_3079_, v_hours_3080_);
    leanh::lean_dec(v_hours_3080_);
    return v_res_3081_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_subHours(
    mut v_dt_3082_: *mut leanh::LeanObject,
    mut v_hours_3083_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_timestamp_3084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rules_3085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3088_: u8 = 0;
    let mut v_second_3089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_3090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initialLocalTimeType_3091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_transitions_3092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3115_: u8 = 0;
    let mut v_unused_3116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_3084_ = leanh::lean_ctor_get(v_dt_3082_, 1);
                v_rules_3085_ = leanh::lean_ctor_get(v_dt_3082_, 2);
                v_isSharedCheck_3115_ = (!leanh::lean_is_exclusive(v_dt_3082_)) as u8;
                if v_isSharedCheck_3115_ == 0 {
                    v_unused_3116_ = leanh::lean_ctor_get(v_dt_3082_, 3);
                    leanh::lean_dec(v_unused_3116_);
                    v_unused_3117_ = leanh::lean_ctor_get(v_dt_3082_, 0);
                    leanh::lean_dec(v_unused_3117_);
                    v___x_3087_ = v_dt_3082_;
                    v_isShared_3088_ = v_isSharedCheck_3115_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_rules_3085_);
                    leanh::lean_inc(v_timestamp_3084_);
                    leanh::lean_dec(v_dt_3082_);
                    v___x_3087_ = leanh::lean_box(0);
                    v_isShared_3088_ = v_isSharedCheck_3115_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_second_3089_ = leanh::lean_ctor_get(v_timestamp_3084_, 0);
                leanh::lean_inc(v_second_3089_);
                v_nano_3090_ = leanh::lean_ctor_get(v_timestamp_3084_, 1);
                leanh::lean_inc(v_nano_3090_);
                leanh::lean_dec_ref(v_timestamp_3084_);
                v_initialLocalTimeType_3091_ = leanh::lean_ctor_get(v_rules_3085_, 0);
                v_transitions_3092_ = leanh::lean_ctor_get(v_rules_3085_, 1);
                v___x_3093_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_addHours___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_addHours___closed__0_once),
                    _init_l_Std_Time_ZonedDateTime_addHours___closed__0,
                );
                v___x_3094_ = lean_int_mul(v_hours_3083_, v___x_3093_);
                v___x_3095_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0,
                );
                v___x_3096_ = lean_int_neg(v___x_3094_);
                leanh::lean_dec(v___x_3094_);
                v___x_3097_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
                );
                v___x_3098_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3099_ = lean_int_mul(v_second_3089_, v___x_3098_);
                leanh::lean_dec(v_second_3089_);
                v___x_3100_ = lean_int_add(v___x_3099_, v_nano_3090_);
                leanh::lean_dec(v_nano_3090_);
                leanh::lean_dec(v___x_3099_);
                v___x_3101_ = lean_int_mul(v___x_3096_, v___x_3098_);
                leanh::lean_dec(v___x_3096_);
                v___x_3102_ = lean_int_add(v___x_3101_, v___x_3097_);
                leanh::lean_dec(v___x_3101_);
                v___x_3103_ = lean_int_add(v___x_3100_, v___x_3102_);
                leanh::lean_dec(v___x_3102_);
                leanh::lean_dec(v___x_3100_);
                v___x_3104_ = l_Std_Time_Duration_ofNanoseconds(v___x_3103_);
                leanh::lean_dec(v___x_3103_);
                v___x_3112_ =
                    l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_3092_, v___x_3104_);
                if leanh::lean_obj_tag(v___x_3112_) == 0 {
                    leanh::lean_dec_ref_known(v___x_3112_, 1);
                    v___x_3113_ =
                        l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_3091_);
                    v___y_3106_ = v___x_3113_;
                    state = 2;
                    continue;
                } else {
                    v_a_3114_ = leanh::lean_ctor_get(v___x_3112_, 0);
                    leanh::lean_inc(v_a_3114_);
                    leanh::lean_dec_ref_known(v___x_3112_, 1);
                    v___y_3106_ = v_a_3114_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc_ref(v___x_3104_);
                leanh::lean_inc_ref(v___y_3106_);
                v___f_3107_ = leanh::lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addDays___lam__0___boxed as *mut core::ffi::c_void,
                    5,
                    4,
                );
                leanh::lean_closure_set(v___f_3107_, 0, v___y_3106_);
                leanh::lean_closure_set(v___f_3107_, 1, v___x_3104_);
                leanh::lean_closure_set(v___f_3107_, 2, v___x_3098_);
                leanh::lean_closure_set(v___f_3107_, 3, v___x_3095_);
                v___x_3108_ = lean_mk_thunk(v___f_3107_);
                if v_isShared_3088_ == 0 {
                    leanh::lean_ctor_set(v___x_3087_, 3, v___y_3106_);
                    leanh::lean_ctor_set(v___x_3087_, 1, v___x_3104_);
                    leanh::lean_ctor_set(v___x_3087_, 0, v___x_3108_);
                    v___x_3110_ = v___x_3087_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3111_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3111_, 0, v___x_3108_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3111_, 1, v___x_3104_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3111_, 2, v_rules_3085_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3111_, 3, v___y_3106_);
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
    mut v_dt_3118_: *mut leanh::LeanObject,
    mut v_hours_3119_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3120_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3120_ = l_Std_Time_ZonedDateTime_subHours(v_dt_3118_, v_hours_3119_);
    leanh::lean_dec(v_hours_3119_);
    return v_res_3120_;
}
pub unsafe fn _init_l_Std_Time_ZonedDateTime_addMinutes___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3122_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3121_ = leanh::lean_unsigned_to_nat(60);
    v___x_3122_ = lean_nat_to_int(v___x_3121_);
    return v___x_3122_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_addMinutes(
    mut v_dt_3123_: *mut leanh::LeanObject,
    mut v_minutes_3124_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_timestamp_3125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rules_3126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3129_: u8 = 0;
    let mut v_second_3130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_3131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initialLocalTimeType_3132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_transitions_3133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3154_: u8 = 0;
    let mut v_unused_3155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_3125_ = leanh::lean_ctor_get(v_dt_3123_, 1);
                v_rules_3126_ = leanh::lean_ctor_get(v_dt_3123_, 2);
                v_isSharedCheck_3154_ = (!leanh::lean_is_exclusive(v_dt_3123_)) as u8;
                if v_isSharedCheck_3154_ == 0 {
                    v_unused_3155_ = leanh::lean_ctor_get(v_dt_3123_, 3);
                    leanh::lean_dec(v_unused_3155_);
                    v_unused_3156_ = leanh::lean_ctor_get(v_dt_3123_, 0);
                    leanh::lean_dec(v_unused_3156_);
                    v___x_3128_ = v_dt_3123_;
                    v_isShared_3129_ = v_isSharedCheck_3154_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_rules_3126_);
                    leanh::lean_inc(v_timestamp_3125_);
                    leanh::lean_dec(v_dt_3123_);
                    v___x_3128_ = leanh::lean_box(0);
                    v_isShared_3129_ = v_isSharedCheck_3154_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_second_3130_ = leanh::lean_ctor_get(v_timestamp_3125_, 0);
                leanh::lean_inc(v_second_3130_);
                v_nano_3131_ = leanh::lean_ctor_get(v_timestamp_3125_, 1);
                leanh::lean_inc(v_nano_3131_);
                leanh::lean_dec_ref(v_timestamp_3125_);
                v_initialLocalTimeType_3132_ = leanh::lean_ctor_get(v_rules_3126_, 0);
                v_transitions_3133_ = leanh::lean_ctor_get(v_rules_3126_, 1);
                v___x_3134_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_addMinutes___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_addMinutes___closed__0_once),
                    _init_l_Std_Time_ZonedDateTime_addMinutes___closed__0,
                );
                v___x_3135_ = lean_int_mul(v_minutes_3124_, v___x_3134_);
                v___x_3136_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0,
                );
                v___x_3137_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3138_ = lean_int_mul(v_second_3130_, v___x_3137_);
                leanh::lean_dec(v_second_3130_);
                v___x_3139_ = lean_int_add(v___x_3138_, v_nano_3131_);
                leanh::lean_dec(v_nano_3131_);
                leanh::lean_dec(v___x_3138_);
                v___x_3140_ = lean_int_mul(v___x_3135_, v___x_3137_);
                leanh::lean_dec(v___x_3135_);
                v___x_3141_ = lean_int_add(v___x_3140_, v___x_3136_);
                leanh::lean_dec(v___x_3140_);
                v___x_3142_ = lean_int_add(v___x_3139_, v___x_3141_);
                leanh::lean_dec(v___x_3141_);
                leanh::lean_dec(v___x_3139_);
                v___x_3143_ = l_Std_Time_Duration_ofNanoseconds(v___x_3142_);
                leanh::lean_dec(v___x_3142_);
                v___x_3151_ =
                    l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_3133_, v___x_3143_);
                if leanh::lean_obj_tag(v___x_3151_) == 0 {
                    leanh::lean_dec_ref_known(v___x_3151_, 1);
                    v___x_3152_ =
                        l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_3132_);
                    v___y_3145_ = v___x_3152_;
                    state = 2;
                    continue;
                } else {
                    v_a_3153_ = leanh::lean_ctor_get(v___x_3151_, 0);
                    leanh::lean_inc(v_a_3153_);
                    leanh::lean_dec_ref_known(v___x_3151_, 1);
                    v___y_3145_ = v_a_3153_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc_ref(v___x_3143_);
                leanh::lean_inc_ref(v___y_3145_);
                v___f_3146_ = leanh::lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addDays___lam__0___boxed as *mut core::ffi::c_void,
                    5,
                    4,
                );
                leanh::lean_closure_set(v___f_3146_, 0, v___y_3145_);
                leanh::lean_closure_set(v___f_3146_, 1, v___x_3143_);
                leanh::lean_closure_set(v___f_3146_, 2, v___x_3137_);
                leanh::lean_closure_set(v___f_3146_, 3, v___x_3136_);
                v___x_3147_ = lean_mk_thunk(v___f_3146_);
                if v_isShared_3129_ == 0 {
                    leanh::lean_ctor_set(v___x_3128_, 3, v___y_3145_);
                    leanh::lean_ctor_set(v___x_3128_, 1, v___x_3143_);
                    leanh::lean_ctor_set(v___x_3128_, 0, v___x_3147_);
                    v___x_3149_ = v___x_3128_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3150_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3150_, 0, v___x_3147_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3150_, 1, v___x_3143_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3150_, 2, v_rules_3126_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3150_, 3, v___y_3145_);
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
    mut v_dt_3157_: *mut leanh::LeanObject,
    mut v_minutes_3158_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3159_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3159_ = l_Std_Time_ZonedDateTime_addMinutes(v_dt_3157_, v_minutes_3158_);
    leanh::lean_dec(v_minutes_3158_);
    return v_res_3159_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_subMinutes(
    mut v_dt_3160_: *mut leanh::LeanObject,
    mut v_minutes_3161_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_timestamp_3162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rules_3163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3166_: u8 = 0;
    let mut v_second_3167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_3168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initialLocalTimeType_3169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_transitions_3170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3193_: u8 = 0;
    let mut v_unused_3194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_3162_ = leanh::lean_ctor_get(v_dt_3160_, 1);
                v_rules_3163_ = leanh::lean_ctor_get(v_dt_3160_, 2);
                v_isSharedCheck_3193_ = (!leanh::lean_is_exclusive(v_dt_3160_)) as u8;
                if v_isSharedCheck_3193_ == 0 {
                    v_unused_3194_ = leanh::lean_ctor_get(v_dt_3160_, 3);
                    leanh::lean_dec(v_unused_3194_);
                    v_unused_3195_ = leanh::lean_ctor_get(v_dt_3160_, 0);
                    leanh::lean_dec(v_unused_3195_);
                    v___x_3165_ = v_dt_3160_;
                    v_isShared_3166_ = v_isSharedCheck_3193_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_rules_3163_);
                    leanh::lean_inc(v_timestamp_3162_);
                    leanh::lean_dec(v_dt_3160_);
                    v___x_3165_ = leanh::lean_box(0);
                    v_isShared_3166_ = v_isSharedCheck_3193_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_second_3167_ = leanh::lean_ctor_get(v_timestamp_3162_, 0);
                leanh::lean_inc(v_second_3167_);
                v_nano_3168_ = leanh::lean_ctor_get(v_timestamp_3162_, 1);
                leanh::lean_inc(v_nano_3168_);
                leanh::lean_dec_ref(v_timestamp_3162_);
                v_initialLocalTimeType_3169_ = leanh::lean_ctor_get(v_rules_3163_, 0);
                v_transitions_3170_ = leanh::lean_ctor_get(v_rules_3163_, 1);
                v___x_3171_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_addMinutes___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_addMinutes___closed__0_once),
                    _init_l_Std_Time_ZonedDateTime_addMinutes___closed__0,
                );
                v___x_3172_ = lean_int_mul(v_minutes_3161_, v___x_3171_);
                v___x_3173_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0,
                );
                v___x_3174_ = lean_int_neg(v___x_3172_);
                leanh::lean_dec(v___x_3172_);
                v___x_3175_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
                );
                v___x_3176_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3177_ = lean_int_mul(v_second_3167_, v___x_3176_);
                leanh::lean_dec(v_second_3167_);
                v___x_3178_ = lean_int_add(v___x_3177_, v_nano_3168_);
                leanh::lean_dec(v_nano_3168_);
                leanh::lean_dec(v___x_3177_);
                v___x_3179_ = lean_int_mul(v___x_3174_, v___x_3176_);
                leanh::lean_dec(v___x_3174_);
                v___x_3180_ = lean_int_add(v___x_3179_, v___x_3175_);
                leanh::lean_dec(v___x_3179_);
                v___x_3181_ = lean_int_add(v___x_3178_, v___x_3180_);
                leanh::lean_dec(v___x_3180_);
                leanh::lean_dec(v___x_3178_);
                v___x_3182_ = l_Std_Time_Duration_ofNanoseconds(v___x_3181_);
                leanh::lean_dec(v___x_3181_);
                v___x_3190_ =
                    l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_3170_, v___x_3182_);
                if leanh::lean_obj_tag(v___x_3190_) == 0 {
                    leanh::lean_dec_ref_known(v___x_3190_, 1);
                    v___x_3191_ =
                        l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_3169_);
                    v___y_3184_ = v___x_3191_;
                    state = 2;
                    continue;
                } else {
                    v_a_3192_ = leanh::lean_ctor_get(v___x_3190_, 0);
                    leanh::lean_inc(v_a_3192_);
                    leanh::lean_dec_ref_known(v___x_3190_, 1);
                    v___y_3184_ = v_a_3192_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc_ref(v___x_3182_);
                leanh::lean_inc_ref(v___y_3184_);
                v___f_3185_ = leanh::lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addDays___lam__0___boxed as *mut core::ffi::c_void,
                    5,
                    4,
                );
                leanh::lean_closure_set(v___f_3185_, 0, v___y_3184_);
                leanh::lean_closure_set(v___f_3185_, 1, v___x_3182_);
                leanh::lean_closure_set(v___f_3185_, 2, v___x_3176_);
                leanh::lean_closure_set(v___f_3185_, 3, v___x_3173_);
                v___x_3186_ = lean_mk_thunk(v___f_3185_);
                if v_isShared_3166_ == 0 {
                    leanh::lean_ctor_set(v___x_3165_, 3, v___y_3184_);
                    leanh::lean_ctor_set(v___x_3165_, 1, v___x_3182_);
                    leanh::lean_ctor_set(v___x_3165_, 0, v___x_3186_);
                    v___x_3188_ = v___x_3165_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3189_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3189_, 0, v___x_3186_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3189_, 1, v___x_3182_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3189_, 2, v_rules_3163_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3189_, 3, v___y_3184_);
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
    mut v_dt_3196_: *mut leanh::LeanObject,
    mut v_minutes_3197_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3198_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3198_ = l_Std_Time_ZonedDateTime_subMinutes(v_dt_3196_, v_minutes_3197_);
    leanh::lean_dec(v_minutes_3197_);
    return v_res_3198_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_addMilliseconds___lam__0(
    mut v___y_3199_: *mut leanh::LeanObject,
    mut v___x_3200_: *mut leanh::LeanObject,
    mut v___x_3201_: *mut leanh::LeanObject,
    mut v_x_3202_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_offset_3203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_3205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_offset_3203_ = leanh::lean_ctor_get(v___y_3199_, 0);
    v_second_3204_ = leanh::lean_ctor_get(v___x_3200_, 0);
    v_nano_3205_ = leanh::lean_ctor_get(v___x_3200_, 1);
    v___x_3206_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once),
        _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0,
    );
    v___x_3207_ = lean_int_mul(v_second_3204_, v___x_3201_);
    v___x_3208_ = lean_int_add(v___x_3207_, v_nano_3205_);
    leanh::lean_dec(v___x_3207_);
    v___x_3209_ = lean_int_mul(v_offset_3203_, v___x_3201_);
    v___x_3210_ = lean_int_add(v___x_3209_, v___x_3206_);
    leanh::lean_dec(v___x_3209_);
    v___x_3211_ = lean_int_add(v___x_3208_, v___x_3210_);
    leanh::lean_dec(v___x_3210_);
    leanh::lean_dec(v___x_3208_);
    v___x_3212_ = l_Std_Time_Duration_ofNanoseconds(v___x_3211_);
    leanh::lean_dec(v___x_3211_);
    v___x_3213_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_3212_);
    return v___x_3213_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_addMilliseconds___lam__0___boxed(
    mut v___y_3214_: *mut leanh::LeanObject,
    mut v___x_3215_: *mut leanh::LeanObject,
    mut v___x_3216_: *mut leanh::LeanObject,
    mut v_x_3217_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3218_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3218_ = l_Std_Time_ZonedDateTime_addMilliseconds___lam__0(
        v___y_3214_,
        v___x_3215_,
        v___x_3216_,
        v_x_3217_,
    );
    leanh::lean_dec(v___x_3216_);
    leanh::lean_dec_ref(v___x_3215_);
    leanh::lean_dec_ref(v___y_3214_);
    return v_res_3218_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_addMilliseconds(
    mut v_dt_3219_: *mut leanh::LeanObject,
    mut v_milliseconds_3220_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_timestamp_3221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rules_3222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3225_: u8 = 0;
    let mut v_second_3226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_3227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_3232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initialLocalTimeType_3233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_transitions_3234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3252_: u8 = 0;
    let mut v_unused_3253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_3221_ = leanh::lean_ctor_get(v_dt_3219_, 1);
                v_rules_3222_ = leanh::lean_ctor_get(v_dt_3219_, 2);
                v_isSharedCheck_3252_ = (!leanh::lean_is_exclusive(v_dt_3219_)) as u8;
                if v_isSharedCheck_3252_ == 0 {
                    v_unused_3253_ = leanh::lean_ctor_get(v_dt_3219_, 3);
                    leanh::lean_dec(v_unused_3253_);
                    v_unused_3254_ = leanh::lean_ctor_get(v_dt_3219_, 0);
                    leanh::lean_dec(v_unused_3254_);
                    v___x_3224_ = v_dt_3219_;
                    v_isShared_3225_ = v_isSharedCheck_3252_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_rules_3222_);
                    leanh::lean_inc(v_timestamp_3221_);
                    leanh::lean_dec(v_dt_3219_);
                    v___x_3224_ = leanh::lean_box(0);
                    v_isShared_3225_ = v_isSharedCheck_3252_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_second_3226_ = leanh::lean_ctor_get(v_timestamp_3221_, 0);
                leanh::lean_inc(v_second_3226_);
                v_nano_3227_ = leanh::lean_ctor_get(v_timestamp_3221_, 1);
                leanh::lean_inc(v_nano_3227_);
                leanh::lean_dec_ref(v_timestamp_3221_);
                v___x_3228_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_millisecond___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_millisecond___closed__0_once),
                    _init_l_Std_Time_ZonedDateTime_millisecond___closed__0,
                );
                v___x_3229_ = lean_int_mul(v_milliseconds_3220_, v___x_3228_);
                v___x_3230_ = l_Std_Time_Duration_ofNanoseconds(v___x_3229_);
                leanh::lean_dec(v___x_3229_);
                v_second_3231_ = leanh::lean_ctor_get(v___x_3230_, 0);
                leanh::lean_inc(v_second_3231_);
                v_nano_3232_ = leanh::lean_ctor_get(v___x_3230_, 1);
                leanh::lean_inc(v_nano_3232_);
                leanh::lean_dec_ref(v___x_3230_);
                v_initialLocalTimeType_3233_ = leanh::lean_ctor_get(v_rules_3222_, 0);
                v_transitions_3234_ = leanh::lean_ctor_get(v_rules_3222_, 1);
                v___x_3235_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3236_ = lean_int_mul(v_second_3226_, v___x_3235_);
                leanh::lean_dec(v_second_3226_);
                v___x_3237_ = lean_int_add(v___x_3236_, v_nano_3227_);
                leanh::lean_dec(v_nano_3227_);
                leanh::lean_dec(v___x_3236_);
                v___x_3238_ = lean_int_mul(v_second_3231_, v___x_3235_);
                leanh::lean_dec(v_second_3231_);
                v___x_3239_ = lean_int_add(v___x_3238_, v_nano_3232_);
                leanh::lean_dec(v_nano_3232_);
                leanh::lean_dec(v___x_3238_);
                v___x_3240_ = lean_int_add(v___x_3237_, v___x_3239_);
                leanh::lean_dec(v___x_3239_);
                leanh::lean_dec(v___x_3237_);
                v___x_3241_ = l_Std_Time_Duration_ofNanoseconds(v___x_3240_);
                leanh::lean_dec(v___x_3240_);
                v___x_3249_ =
                    l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_3234_, v___x_3241_);
                if leanh::lean_obj_tag(v___x_3249_) == 0 {
                    leanh::lean_dec_ref_known(v___x_3249_, 1);
                    v___x_3250_ =
                        l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_3233_);
                    v___y_3243_ = v___x_3250_;
                    state = 2;
                    continue;
                } else {
                    v_a_3251_ = leanh::lean_ctor_get(v___x_3249_, 0);
                    leanh::lean_inc(v_a_3251_);
                    leanh::lean_dec_ref_known(v___x_3249_, 1);
                    v___y_3243_ = v_a_3251_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc_ref(v___x_3241_);
                leanh::lean_inc_ref(v___y_3243_);
                v___f_3244_ = leanh::lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addMilliseconds___lam__0___boxed
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                leanh::lean_closure_set(v___f_3244_, 0, v___y_3243_);
                leanh::lean_closure_set(v___f_3244_, 1, v___x_3241_);
                leanh::lean_closure_set(v___f_3244_, 2, v___x_3235_);
                v___x_3245_ = lean_mk_thunk(v___f_3244_);
                if v_isShared_3225_ == 0 {
                    leanh::lean_ctor_set(v___x_3224_, 3, v___y_3243_);
                    leanh::lean_ctor_set(v___x_3224_, 1, v___x_3241_);
                    leanh::lean_ctor_set(v___x_3224_, 0, v___x_3245_);
                    v___x_3247_ = v___x_3224_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3248_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3248_, 0, v___x_3245_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3248_, 1, v___x_3241_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3248_, 2, v_rules_3222_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3248_, 3, v___y_3243_);
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
    mut v_dt_3255_: *mut leanh::LeanObject,
    mut v_milliseconds_3256_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3257_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3257_ = l_Std_Time_ZonedDateTime_addMilliseconds(v_dt_3255_, v_milliseconds_3256_);
    leanh::lean_dec(v_milliseconds_3256_);
    return v_res_3257_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_subMilliseconds(
    mut v_dt_3258_: *mut leanh::LeanObject,
    mut v_milliseconds_3259_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_timestamp_3260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rules_3261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3264_: u8 = 0;
    let mut v___x_3265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_3269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_3271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initialLocalTimeType_3272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_transitions_3273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3293_: u8 = 0;
    let mut v_unused_3294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_3260_ = leanh::lean_ctor_get(v_dt_3258_, 1);
                v_rules_3261_ = leanh::lean_ctor_get(v_dt_3258_, 2);
                v_isSharedCheck_3293_ = (!leanh::lean_is_exclusive(v_dt_3258_)) as u8;
                if v_isSharedCheck_3293_ == 0 {
                    v_unused_3294_ = leanh::lean_ctor_get(v_dt_3258_, 3);
                    leanh::lean_dec(v_unused_3294_);
                    v_unused_3295_ = leanh::lean_ctor_get(v_dt_3258_, 0);
                    leanh::lean_dec(v_unused_3295_);
                    v___x_3263_ = v_dt_3258_;
                    v_isShared_3264_ = v_isSharedCheck_3293_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_rules_3261_);
                    leanh::lean_inc(v_timestamp_3260_);
                    leanh::lean_dec(v_dt_3258_);
                    v___x_3263_ = leanh::lean_box(0);
                    v_isShared_3264_ = v_isSharedCheck_3293_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3265_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_millisecond___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_millisecond___closed__0_once),
                    _init_l_Std_Time_ZonedDateTime_millisecond___closed__0,
                );
                v___x_3266_ = lean_int_mul(v_milliseconds_3259_, v___x_3265_);
                v___x_3267_ = l_Std_Time_Duration_ofNanoseconds(v___x_3266_);
                leanh::lean_dec(v___x_3266_);
                v_second_3268_ = leanh::lean_ctor_get(v___x_3267_, 0);
                leanh::lean_inc(v_second_3268_);
                v_nano_3269_ = leanh::lean_ctor_get(v___x_3267_, 1);
                leanh::lean_inc(v_nano_3269_);
                leanh::lean_dec_ref(v___x_3267_);
                v_second_3270_ = leanh::lean_ctor_get(v_timestamp_3260_, 0);
                leanh::lean_inc(v_second_3270_);
                v_nano_3271_ = leanh::lean_ctor_get(v_timestamp_3260_, 1);
                leanh::lean_inc(v_nano_3271_);
                leanh::lean_dec_ref(v_timestamp_3260_);
                v_initialLocalTimeType_3272_ = leanh::lean_ctor_get(v_rules_3261_, 0);
                v_transitions_3273_ = leanh::lean_ctor_get(v_rules_3261_, 1);
                v___x_3274_ = lean_int_neg(v_second_3268_);
                leanh::lean_dec(v_second_3268_);
                v___x_3275_ = lean_int_neg(v_nano_3269_);
                leanh::lean_dec(v_nano_3269_);
                v___x_3276_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3277_ = lean_int_mul(v_second_3270_, v___x_3276_);
                leanh::lean_dec(v_second_3270_);
                v___x_3278_ = lean_int_add(v___x_3277_, v_nano_3271_);
                leanh::lean_dec(v_nano_3271_);
                leanh::lean_dec(v___x_3277_);
                v___x_3279_ = lean_int_mul(v___x_3274_, v___x_3276_);
                leanh::lean_dec(v___x_3274_);
                v___x_3280_ = lean_int_add(v___x_3279_, v___x_3275_);
                leanh::lean_dec(v___x_3275_);
                leanh::lean_dec(v___x_3279_);
                v___x_3281_ = lean_int_add(v___x_3278_, v___x_3280_);
                leanh::lean_dec(v___x_3280_);
                leanh::lean_dec(v___x_3278_);
                v___x_3282_ = l_Std_Time_Duration_ofNanoseconds(v___x_3281_);
                leanh::lean_dec(v___x_3281_);
                v___x_3290_ =
                    l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_3273_, v___x_3282_);
                if leanh::lean_obj_tag(v___x_3290_) == 0 {
                    leanh::lean_dec_ref_known(v___x_3290_, 1);
                    v___x_3291_ =
                        l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_3272_);
                    v___y_3284_ = v___x_3291_;
                    state = 2;
                    continue;
                } else {
                    v_a_3292_ = leanh::lean_ctor_get(v___x_3290_, 0);
                    leanh::lean_inc(v_a_3292_);
                    leanh::lean_dec_ref_known(v___x_3290_, 1);
                    v___y_3284_ = v_a_3292_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc_ref(v___x_3282_);
                leanh::lean_inc_ref(v___y_3284_);
                v___f_3285_ = leanh::lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addMilliseconds___lam__0___boxed
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                leanh::lean_closure_set(v___f_3285_, 0, v___y_3284_);
                leanh::lean_closure_set(v___f_3285_, 1, v___x_3282_);
                leanh::lean_closure_set(v___f_3285_, 2, v___x_3276_);
                v___x_3286_ = lean_mk_thunk(v___f_3285_);
                if v_isShared_3264_ == 0 {
                    leanh::lean_ctor_set(v___x_3263_, 3, v___y_3284_);
                    leanh::lean_ctor_set(v___x_3263_, 1, v___x_3282_);
                    leanh::lean_ctor_set(v___x_3263_, 0, v___x_3286_);
                    v___x_3288_ = v___x_3263_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3289_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3289_, 0, v___x_3286_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3289_, 1, v___x_3282_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3289_, 2, v_rules_3261_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3289_, 3, v___y_3284_);
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
    mut v_dt_3296_: *mut leanh::LeanObject,
    mut v_milliseconds_3297_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3298_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3298_ = l_Std_Time_ZonedDateTime_subMilliseconds(v_dt_3296_, v_milliseconds_3297_);
    leanh::lean_dec(v_milliseconds_3297_);
    return v_res_3298_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_addSeconds(
    mut v_dt_3299_: *mut leanh::LeanObject,
    mut v_seconds_3300_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_timestamp_3301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rules_3302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3305_: u8 = 0;
    let mut v_second_3306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_3307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initialLocalTimeType_3308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_transitions_3309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3328_: u8 = 0;
    let mut v_unused_3329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_3301_ = leanh::lean_ctor_get(v_dt_3299_, 1);
                v_rules_3302_ = leanh::lean_ctor_get(v_dt_3299_, 2);
                v_isSharedCheck_3328_ = (!leanh::lean_is_exclusive(v_dt_3299_)) as u8;
                if v_isSharedCheck_3328_ == 0 {
                    v_unused_3329_ = leanh::lean_ctor_get(v_dt_3299_, 3);
                    leanh::lean_dec(v_unused_3329_);
                    v_unused_3330_ = leanh::lean_ctor_get(v_dt_3299_, 0);
                    leanh::lean_dec(v_unused_3330_);
                    v___x_3304_ = v_dt_3299_;
                    v_isShared_3305_ = v_isSharedCheck_3328_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_rules_3302_);
                    leanh::lean_inc(v_timestamp_3301_);
                    leanh::lean_dec(v_dt_3299_);
                    v___x_3304_ = leanh::lean_box(0);
                    v_isShared_3305_ = v_isSharedCheck_3328_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_second_3306_ = leanh::lean_ctor_get(v_timestamp_3301_, 0);
                leanh::lean_inc(v_second_3306_);
                v_nano_3307_ = leanh::lean_ctor_get(v_timestamp_3301_, 1);
                leanh::lean_inc(v_nano_3307_);
                leanh::lean_dec_ref(v_timestamp_3301_);
                v_initialLocalTimeType_3308_ = leanh::lean_ctor_get(v_rules_3302_, 0);
                v_transitions_3309_ = leanh::lean_ctor_get(v_rules_3302_, 1);
                v___x_3310_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0,
                );
                v___x_3311_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3312_ = lean_int_mul(v_second_3306_, v___x_3311_);
                leanh::lean_dec(v_second_3306_);
                v___x_3313_ = lean_int_add(v___x_3312_, v_nano_3307_);
                leanh::lean_dec(v_nano_3307_);
                leanh::lean_dec(v___x_3312_);
                v___x_3314_ = lean_int_mul(v_seconds_3300_, v___x_3311_);
                v___x_3315_ = lean_int_add(v___x_3314_, v___x_3310_);
                leanh::lean_dec(v___x_3314_);
                v___x_3316_ = lean_int_add(v___x_3313_, v___x_3315_);
                leanh::lean_dec(v___x_3315_);
                leanh::lean_dec(v___x_3313_);
                v___x_3317_ = l_Std_Time_Duration_ofNanoseconds(v___x_3316_);
                leanh::lean_dec(v___x_3316_);
                v___x_3325_ =
                    l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_3309_, v___x_3317_);
                if leanh::lean_obj_tag(v___x_3325_) == 0 {
                    leanh::lean_dec_ref_known(v___x_3325_, 1);
                    v___x_3326_ =
                        l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_3308_);
                    v___y_3319_ = v___x_3326_;
                    state = 2;
                    continue;
                } else {
                    v_a_3327_ = leanh::lean_ctor_get(v___x_3325_, 0);
                    leanh::lean_inc(v_a_3327_);
                    leanh::lean_dec_ref_known(v___x_3325_, 1);
                    v___y_3319_ = v_a_3327_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc_ref(v___x_3317_);
                leanh::lean_inc_ref(v___y_3319_);
                v___f_3320_ = leanh::lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addDays___lam__0___boxed as *mut core::ffi::c_void,
                    5,
                    4,
                );
                leanh::lean_closure_set(v___f_3320_, 0, v___y_3319_);
                leanh::lean_closure_set(v___f_3320_, 1, v___x_3317_);
                leanh::lean_closure_set(v___f_3320_, 2, v___x_3311_);
                leanh::lean_closure_set(v___f_3320_, 3, v___x_3310_);
                v___x_3321_ = lean_mk_thunk(v___f_3320_);
                if v_isShared_3305_ == 0 {
                    leanh::lean_ctor_set(v___x_3304_, 3, v___y_3319_);
                    leanh::lean_ctor_set(v___x_3304_, 1, v___x_3317_);
                    leanh::lean_ctor_set(v___x_3304_, 0, v___x_3321_);
                    v___x_3323_ = v___x_3304_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3324_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3324_, 0, v___x_3321_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3324_, 1, v___x_3317_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3324_, 2, v_rules_3302_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3324_, 3, v___y_3319_);
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
    mut v_dt_3331_: *mut leanh::LeanObject,
    mut v_seconds_3332_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3333_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3333_ = l_Std_Time_ZonedDateTime_addSeconds(v_dt_3331_, v_seconds_3332_);
    leanh::lean_dec(v_seconds_3332_);
    return v_res_3333_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_subSeconds(
    mut v_dt_3334_: *mut leanh::LeanObject,
    mut v_seconds_3335_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_timestamp_3336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rules_3337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3340_: u8 = 0;
    let mut v_second_3341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_3342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initialLocalTimeType_3343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_transitions_3344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3365_: u8 = 0;
    let mut v_unused_3366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_3336_ = leanh::lean_ctor_get(v_dt_3334_, 1);
                v_rules_3337_ = leanh::lean_ctor_get(v_dt_3334_, 2);
                v_isSharedCheck_3365_ = (!leanh::lean_is_exclusive(v_dt_3334_)) as u8;
                if v_isSharedCheck_3365_ == 0 {
                    v_unused_3366_ = leanh::lean_ctor_get(v_dt_3334_, 3);
                    leanh::lean_dec(v_unused_3366_);
                    v_unused_3367_ = leanh::lean_ctor_get(v_dt_3334_, 0);
                    leanh::lean_dec(v_unused_3367_);
                    v___x_3339_ = v_dt_3334_;
                    v_isShared_3340_ = v_isSharedCheck_3365_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_rules_3337_);
                    leanh::lean_inc(v_timestamp_3336_);
                    leanh::lean_dec(v_dt_3334_);
                    v___x_3339_ = leanh::lean_box(0);
                    v_isShared_3340_ = v_isSharedCheck_3365_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_second_3341_ = leanh::lean_ctor_get(v_timestamp_3336_, 0);
                leanh::lean_inc(v_second_3341_);
                v_nano_3342_ = leanh::lean_ctor_get(v_timestamp_3336_, 1);
                leanh::lean_inc(v_nano_3342_);
                leanh::lean_dec_ref(v_timestamp_3336_);
                v_initialLocalTimeType_3343_ = leanh::lean_ctor_get(v_rules_3337_, 0);
                v_transitions_3344_ = leanh::lean_ctor_get(v_rules_3337_, 1);
                v___x_3345_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0,
                );
                v___x_3346_ = lean_int_neg(v_seconds_3335_);
                v___x_3347_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
                );
                v___x_3348_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3349_ = lean_int_mul(v_second_3341_, v___x_3348_);
                leanh::lean_dec(v_second_3341_);
                v___x_3350_ = lean_int_add(v___x_3349_, v_nano_3342_);
                leanh::lean_dec(v_nano_3342_);
                leanh::lean_dec(v___x_3349_);
                v___x_3351_ = lean_int_mul(v___x_3346_, v___x_3348_);
                leanh::lean_dec(v___x_3346_);
                v___x_3352_ = lean_int_add(v___x_3351_, v___x_3347_);
                leanh::lean_dec(v___x_3351_);
                v___x_3353_ = lean_int_add(v___x_3350_, v___x_3352_);
                leanh::lean_dec(v___x_3352_);
                leanh::lean_dec(v___x_3350_);
                v___x_3354_ = l_Std_Time_Duration_ofNanoseconds(v___x_3353_);
                leanh::lean_dec(v___x_3353_);
                v___x_3362_ =
                    l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_3344_, v___x_3354_);
                if leanh::lean_obj_tag(v___x_3362_) == 0 {
                    leanh::lean_dec_ref_known(v___x_3362_, 1);
                    v___x_3363_ =
                        l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_3343_);
                    v___y_3356_ = v___x_3363_;
                    state = 2;
                    continue;
                } else {
                    v_a_3364_ = leanh::lean_ctor_get(v___x_3362_, 0);
                    leanh::lean_inc(v_a_3364_);
                    leanh::lean_dec_ref_known(v___x_3362_, 1);
                    v___y_3356_ = v_a_3364_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc_ref(v___x_3354_);
                leanh::lean_inc_ref(v___y_3356_);
                v___f_3357_ = leanh::lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addDays___lam__0___boxed as *mut core::ffi::c_void,
                    5,
                    4,
                );
                leanh::lean_closure_set(v___f_3357_, 0, v___y_3356_);
                leanh::lean_closure_set(v___f_3357_, 1, v___x_3354_);
                leanh::lean_closure_set(v___f_3357_, 2, v___x_3348_);
                leanh::lean_closure_set(v___f_3357_, 3, v___x_3345_);
                v___x_3358_ = lean_mk_thunk(v___f_3357_);
                if v_isShared_3340_ == 0 {
                    leanh::lean_ctor_set(v___x_3339_, 3, v___y_3356_);
                    leanh::lean_ctor_set(v___x_3339_, 1, v___x_3354_);
                    leanh::lean_ctor_set(v___x_3339_, 0, v___x_3358_);
                    v___x_3360_ = v___x_3339_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3361_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3361_, 0, v___x_3358_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3361_, 1, v___x_3354_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3361_, 2, v_rules_3337_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3361_, 3, v___y_3356_);
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
    mut v_dt_3368_: *mut leanh::LeanObject,
    mut v_seconds_3369_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3370_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3370_ = l_Std_Time_ZonedDateTime_subSeconds(v_dt_3368_, v_seconds_3369_);
    leanh::lean_dec(v_seconds_3369_);
    return v_res_3370_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_addNanoseconds(
    mut v_dt_3371_: *mut leanh::LeanObject,
    mut v_nanoseconds_3372_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_timestamp_3373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rules_3374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3377_: u8 = 0;
    let mut v_second_3378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_3379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_3382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initialLocalTimeType_3383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_transitions_3384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3402_: u8 = 0;
    let mut v_unused_3403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_3373_ = leanh::lean_ctor_get(v_dt_3371_, 1);
                v_rules_3374_ = leanh::lean_ctor_get(v_dt_3371_, 2);
                v_isSharedCheck_3402_ = (!leanh::lean_is_exclusive(v_dt_3371_)) as u8;
                if v_isSharedCheck_3402_ == 0 {
                    v_unused_3403_ = leanh::lean_ctor_get(v_dt_3371_, 3);
                    leanh::lean_dec(v_unused_3403_);
                    v_unused_3404_ = leanh::lean_ctor_get(v_dt_3371_, 0);
                    leanh::lean_dec(v_unused_3404_);
                    v___x_3376_ = v_dt_3371_;
                    v_isShared_3377_ = v_isSharedCheck_3402_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_rules_3374_);
                    leanh::lean_inc(v_timestamp_3373_);
                    leanh::lean_dec(v_dt_3371_);
                    v___x_3376_ = leanh::lean_box(0);
                    v_isShared_3377_ = v_isSharedCheck_3402_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_second_3378_ = leanh::lean_ctor_get(v_timestamp_3373_, 0);
                leanh::lean_inc(v_second_3378_);
                v_nano_3379_ = leanh::lean_ctor_get(v_timestamp_3373_, 1);
                leanh::lean_inc(v_nano_3379_);
                leanh::lean_dec_ref(v_timestamp_3373_);
                v___x_3380_ = l_Std_Time_Duration_ofNanoseconds(v_nanoseconds_3372_);
                v_second_3381_ = leanh::lean_ctor_get(v___x_3380_, 0);
                leanh::lean_inc(v_second_3381_);
                v_nano_3382_ = leanh::lean_ctor_get(v___x_3380_, 1);
                leanh::lean_inc(v_nano_3382_);
                leanh::lean_dec_ref(v___x_3380_);
                v_initialLocalTimeType_3383_ = leanh::lean_ctor_get(v_rules_3374_, 0);
                v_transitions_3384_ = leanh::lean_ctor_get(v_rules_3374_, 1);
                v___x_3385_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3386_ = lean_int_mul(v_second_3378_, v___x_3385_);
                leanh::lean_dec(v_second_3378_);
                v___x_3387_ = lean_int_add(v___x_3386_, v_nano_3379_);
                leanh::lean_dec(v_nano_3379_);
                leanh::lean_dec(v___x_3386_);
                v___x_3388_ = lean_int_mul(v_second_3381_, v___x_3385_);
                leanh::lean_dec(v_second_3381_);
                v___x_3389_ = lean_int_add(v___x_3388_, v_nano_3382_);
                leanh::lean_dec(v_nano_3382_);
                leanh::lean_dec(v___x_3388_);
                v___x_3390_ = lean_int_add(v___x_3387_, v___x_3389_);
                leanh::lean_dec(v___x_3389_);
                leanh::lean_dec(v___x_3387_);
                v___x_3391_ = l_Std_Time_Duration_ofNanoseconds(v___x_3390_);
                leanh::lean_dec(v___x_3390_);
                v___x_3399_ =
                    l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_3384_, v___x_3391_);
                if leanh::lean_obj_tag(v___x_3399_) == 0 {
                    leanh::lean_dec_ref_known(v___x_3399_, 1);
                    v___x_3400_ =
                        l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_3383_);
                    v___y_3393_ = v___x_3400_;
                    state = 2;
                    continue;
                } else {
                    v_a_3401_ = leanh::lean_ctor_get(v___x_3399_, 0);
                    leanh::lean_inc(v_a_3401_);
                    leanh::lean_dec_ref_known(v___x_3399_, 1);
                    v___y_3393_ = v_a_3401_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc_ref(v___x_3391_);
                leanh::lean_inc_ref(v___y_3393_);
                v___f_3394_ = leanh::lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addMilliseconds___lam__0___boxed
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                leanh::lean_closure_set(v___f_3394_, 0, v___y_3393_);
                leanh::lean_closure_set(v___f_3394_, 1, v___x_3391_);
                leanh::lean_closure_set(v___f_3394_, 2, v___x_3385_);
                v___x_3395_ = lean_mk_thunk(v___f_3394_);
                if v_isShared_3377_ == 0 {
                    leanh::lean_ctor_set(v___x_3376_, 3, v___y_3393_);
                    leanh::lean_ctor_set(v___x_3376_, 1, v___x_3391_);
                    leanh::lean_ctor_set(v___x_3376_, 0, v___x_3395_);
                    v___x_3397_ = v___x_3376_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3398_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3398_, 0, v___x_3395_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3398_, 1, v___x_3391_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3398_, 2, v_rules_3374_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3398_, 3, v___y_3393_);
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
    mut v_dt_3405_: *mut leanh::LeanObject,
    mut v_nanoseconds_3406_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3407_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3407_ = l_Std_Time_ZonedDateTime_addNanoseconds(v_dt_3405_, v_nanoseconds_3406_);
    leanh::lean_dec(v_nanoseconds_3406_);
    return v_res_3407_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_subNanoseconds(
    mut v_dt_3408_: *mut leanh::LeanObject,
    mut v_nanoseconds_3409_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_timestamp_3410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rules_3411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3414_: u8 = 0;
    let mut v___x_3415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_3417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_3419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initialLocalTimeType_3420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_transitions_3421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3441_: u8 = 0;
    let mut v_unused_3442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_3410_ = leanh::lean_ctor_get(v_dt_3408_, 1);
                v_rules_3411_ = leanh::lean_ctor_get(v_dt_3408_, 2);
                v_isSharedCheck_3441_ = (!leanh::lean_is_exclusive(v_dt_3408_)) as u8;
                if v_isSharedCheck_3441_ == 0 {
                    v_unused_3442_ = leanh::lean_ctor_get(v_dt_3408_, 3);
                    leanh::lean_dec(v_unused_3442_);
                    v_unused_3443_ = leanh::lean_ctor_get(v_dt_3408_, 0);
                    leanh::lean_dec(v_unused_3443_);
                    v___x_3413_ = v_dt_3408_;
                    v_isShared_3414_ = v_isSharedCheck_3441_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_rules_3411_);
                    leanh::lean_inc(v_timestamp_3410_);
                    leanh::lean_dec(v_dt_3408_);
                    v___x_3413_ = leanh::lean_box(0);
                    v_isShared_3414_ = v_isSharedCheck_3441_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3415_ = l_Std_Time_Duration_ofNanoseconds(v_nanoseconds_3409_);
                v_second_3416_ = leanh::lean_ctor_get(v___x_3415_, 0);
                leanh::lean_inc(v_second_3416_);
                v_nano_3417_ = leanh::lean_ctor_get(v___x_3415_, 1);
                leanh::lean_inc(v_nano_3417_);
                leanh::lean_dec_ref(v___x_3415_);
                v_second_3418_ = leanh::lean_ctor_get(v_timestamp_3410_, 0);
                leanh::lean_inc(v_second_3418_);
                v_nano_3419_ = leanh::lean_ctor_get(v_timestamp_3410_, 1);
                leanh::lean_inc(v_nano_3419_);
                leanh::lean_dec_ref(v_timestamp_3410_);
                v_initialLocalTimeType_3420_ = leanh::lean_ctor_get(v_rules_3411_, 0);
                v_transitions_3421_ = leanh::lean_ctor_get(v_rules_3411_, 1);
                v___x_3422_ = lean_int_neg(v_second_3416_);
                leanh::lean_dec(v_second_3416_);
                v___x_3423_ = lean_int_neg(v_nano_3417_);
                leanh::lean_dec(v_nano_3417_);
                v___x_3424_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3425_ = lean_int_mul(v_second_3418_, v___x_3424_);
                leanh::lean_dec(v_second_3418_);
                v___x_3426_ = lean_int_add(v___x_3425_, v_nano_3419_);
                leanh::lean_dec(v_nano_3419_);
                leanh::lean_dec(v___x_3425_);
                v___x_3427_ = lean_int_mul(v___x_3422_, v___x_3424_);
                leanh::lean_dec(v___x_3422_);
                v___x_3428_ = lean_int_add(v___x_3427_, v___x_3423_);
                leanh::lean_dec(v___x_3423_);
                leanh::lean_dec(v___x_3427_);
                v___x_3429_ = lean_int_add(v___x_3426_, v___x_3428_);
                leanh::lean_dec(v___x_3428_);
                leanh::lean_dec(v___x_3426_);
                v___x_3430_ = l_Std_Time_Duration_ofNanoseconds(v___x_3429_);
                leanh::lean_dec(v___x_3429_);
                v___x_3438_ =
                    l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_3421_, v___x_3430_);
                if leanh::lean_obj_tag(v___x_3438_) == 0 {
                    leanh::lean_dec_ref_known(v___x_3438_, 1);
                    v___x_3439_ =
                        l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_3420_);
                    v___y_3432_ = v___x_3439_;
                    state = 2;
                    continue;
                } else {
                    v_a_3440_ = leanh::lean_ctor_get(v___x_3438_, 0);
                    leanh::lean_inc(v_a_3440_);
                    leanh::lean_dec_ref_known(v___x_3438_, 1);
                    v___y_3432_ = v_a_3440_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc_ref(v___x_3430_);
                leanh::lean_inc_ref(v___y_3432_);
                v___f_3433_ = leanh::lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addMilliseconds___lam__0___boxed
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                leanh::lean_closure_set(v___f_3433_, 0, v___y_3432_);
                leanh::lean_closure_set(v___f_3433_, 1, v___x_3430_);
                leanh::lean_closure_set(v___f_3433_, 2, v___x_3424_);
                v___x_3434_ = lean_mk_thunk(v___f_3433_);
                if v_isShared_3414_ == 0 {
                    leanh::lean_ctor_set(v___x_3413_, 3, v___y_3432_);
                    leanh::lean_ctor_set(v___x_3413_, 1, v___x_3430_);
                    leanh::lean_ctor_set(v___x_3413_, 0, v___x_3434_);
                    v___x_3436_ = v___x_3413_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3437_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3437_, 0, v___x_3434_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3437_, 1, v___x_3430_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3437_, 2, v_rules_3411_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3437_, 3, v___y_3432_);
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
    mut v_dt_3444_: *mut leanh::LeanObject,
    mut v_nanoseconds_3445_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3446_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3446_ = l_Std_Time_ZonedDateTime_subNanoseconds(v_dt_3444_, v_nanoseconds_3445_);
    leanh::lean_dec(v_nanoseconds_3445_);
    return v_res_3446_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_era(mut v_date_3447_: *mut leanh::LeanObject) -> u8 {
    let mut v_date_3448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_3450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_year_3451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: u8 = 0;
    v_date_3448_ = leanh::lean_ctor_get(v_date_3447_, 0);
    v___x_3449_ = lean_thunk_get_own(v_date_3448_);
    v_date_3450_ = leanh::lean_ctor_get(v___x_3449_, 0);
    leanh::lean_inc_ref(v_date_3450_);
    leanh::lean_dec(v___x_3449_);
    v_year_3451_ = leanh::lean_ctor_get(v_date_3450_, 0);
    leanh::lean_inc(v_year_3451_);
    leanh::lean_dec_ref(v_date_3450_);
    v___x_3452_ = l_Std_Time_Year_Offset_era(v_year_3451_);
    leanh::lean_dec(v_year_3451_);
    return v___x_3452_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_era___boxed(
    mut v_date_3453_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3454_: u8 = 0;
    let mut v_r_3455_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3454_ = l_Std_Time_ZonedDateTime_era(v_date_3453_);
    leanh::lean_dec_ref(v_date_3453_);
    v_r_3455_ = leanh::lean_box((v_res_3454_) as usize);
    return v_r_3455_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_withWeekday(
    mut v_dt_3456_: *mut leanh::LeanObject,
    mut v_desiredWeekday_3457_: u8,
) -> *mut leanh::LeanObject {
    let mut v_date_3458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rules_3459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3462_: u8 = 0;
    let mut v_date_3463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_wt_3465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ltt_3466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tz_3467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_3468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_3470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3485_: u8 = 0;
    let mut v_unused_3486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_3458_ = leanh::lean_ctor_get(v_dt_3456_, 0);
                v_rules_3459_ = leanh::lean_ctor_get(v_dt_3456_, 2);
                v_isSharedCheck_3485_ = (!leanh::lean_is_exclusive(v_dt_3456_)) as u8;
                if v_isSharedCheck_3485_ == 0 {
                    v_unused_3486_ = leanh::lean_ctor_get(v_dt_3456_, 3);
                    leanh::lean_dec(v_unused_3486_);
                    v_unused_3487_ = leanh::lean_ctor_get(v_dt_3456_, 1);
                    leanh::lean_dec(v_unused_3487_);
                    v___x_3461_ = v_dt_3456_;
                    v_isShared_3462_ = v_isSharedCheck_3485_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_rules_3459_);
                    leanh::lean_inc(v_date_3458_);
                    leanh::lean_dec(v_dt_3456_);
                    v___x_3461_ = leanh::lean_box(0);
                    v_isShared_3462_ = v_isSharedCheck_3485_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_date_3463_ = lean_thunk_get_own(v_date_3458_);
                leanh::lean_dec_ref(v_date_3458_);
                v___x_3464_ =
                    l_Std_Time_PlainDateTime_withWeekday(v_date_3463_, v_desiredWeekday_3457_);
                leanh::lean_inc_ref(v___x_3464_);
                v_wt_3465_ = l_Std_Time_PlainDateTime_toWallTime(v___x_3464_);
                leanh::lean_inc_ref(v_rules_3459_);
                v_ltt_3466_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(
                    v_rules_3459_,
                    v_wt_3465_,
                );
                v_tz_3467_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_3466_);
                leanh::lean_dec_ref(v_ltt_3466_);
                v_offset_3468_ = leanh::lean_ctor_get(v_tz_3467_, 0);
                leanh::lean_inc(v_offset_3468_);
                v_second_3469_ = leanh::lean_ctor_get(v_wt_3465_, 0);
                leanh::lean_inc(v_second_3469_);
                v_nano_3470_ = leanh::lean_ctor_get(v_wt_3465_, 1);
                leanh::lean_inc(v_nano_3470_);
                leanh::lean_dec_ref(v_wt_3465_);
                v___f_3471_ = leanh::lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v___f_3471_, 0, v___x_3464_);
                v___x_3472_ = lean_mk_thunk(v___f_3471_);
                v___x_3473_ = lean_int_neg(v_offset_3468_);
                leanh::lean_dec(v_offset_3468_);
                v___x_3474_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
                );
                v___x_3475_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3476_ = lean_int_mul(v_second_3469_, v___x_3475_);
                leanh::lean_dec(v_second_3469_);
                v___x_3477_ = lean_int_add(v___x_3476_, v_nano_3470_);
                leanh::lean_dec(v_nano_3470_);
                leanh::lean_dec(v___x_3476_);
                v___x_3478_ = lean_int_mul(v___x_3473_, v___x_3475_);
                leanh::lean_dec(v___x_3473_);
                v___x_3479_ = lean_int_add(v___x_3478_, v___x_3474_);
                leanh::lean_dec(v___x_3478_);
                v___x_3480_ = lean_int_add(v___x_3477_, v___x_3479_);
                leanh::lean_dec(v___x_3479_);
                leanh::lean_dec(v___x_3477_);
                v___x_3481_ = l_Std_Time_Duration_ofNanoseconds(v___x_3480_);
                leanh::lean_dec(v___x_3480_);
                if v_isShared_3462_ == 0 {
                    leanh::lean_ctor_set(v___x_3461_, 3, v_tz_3467_);
                    leanh::lean_ctor_set(v___x_3461_, 1, v___x_3481_);
                    leanh::lean_ctor_set(v___x_3461_, 0, v___x_3472_);
                    v___x_3483_ = v___x_3461_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3484_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3484_, 0, v___x_3472_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3484_, 1, v___x_3481_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3484_, 2, v_rules_3459_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3484_, 3, v_tz_3467_);
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
    mut v_dt_3488_: *mut leanh::LeanObject,
    mut v_desiredWeekday_3489_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_desiredWeekday_boxed_3490_: u8 = 0;
    let mut v_res_3491_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_desiredWeekday_boxed_3490_ = (leanh::lean_unbox(v_desiredWeekday_3489_) as u8);
    v_res_3491_ = l_Std_Time_ZonedDateTime_withWeekday(v_dt_3488_, v_desiredWeekday_boxed_3490_);
    return v_res_3491_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_withDaysClip(
    mut v_dt_3492_: *mut leanh::LeanObject,
    mut v_days_3493_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_date_3494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rules_3495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3498_: u8 = 0;
    let mut v_date_3499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_3502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3505_: u8 = 0;
    let mut v___x_3507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_wt_3508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ltt_3509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tz_3510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_3511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_3513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3529_: u8 = 0;
    let mut v_unused_3530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_3531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_year_3532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_month_3533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3536_: u8 = 0;
    let mut v___y_3538_: u8 = 0;
    let mut v_max_3539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3540_: u8 = 0;
    let mut v___x_3542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3553_: u8 = 0;
    let mut v___x_3554_: u8 = 0;
    let mut v___x_3555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3557_: u8 = 0;
    let mut v_isSharedCheck_3558_: u8 = 0;
    let mut v_unused_3559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3560_: u8 = 0;
    let mut v_unused_3561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_3494_ = leanh::lean_ctor_get(v_dt_3492_, 0);
                v_rules_3495_ = leanh::lean_ctor_get(v_dt_3492_, 2);
                v_isSharedCheck_3560_ = (!leanh::lean_is_exclusive(v_dt_3492_)) as u8;
                if v_isSharedCheck_3560_ == 0 {
                    v_unused_3561_ = leanh::lean_ctor_get(v_dt_3492_, 3);
                    leanh::lean_dec(v_unused_3561_);
                    v_unused_3562_ = leanh::lean_ctor_get(v_dt_3492_, 1);
                    leanh::lean_dec(v_unused_3562_);
                    v___x_3497_ = v_dt_3492_;
                    v_isShared_3498_ = v_isSharedCheck_3560_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_rules_3495_);
                    leanh::lean_inc(v_date_3494_);
                    leanh::lean_dec(v_dt_3492_);
                    v___x_3497_ = leanh::lean_box(0);
                    v_isShared_3498_ = v_isSharedCheck_3560_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_date_3499_ = lean_thunk_get_own(v_date_3494_);
                leanh::lean_dec_ref(v_date_3494_);
                v_date_3531_ = leanh::lean_ctor_get(v_date_3499_, 0);
                leanh::lean_inc_ref(v_date_3531_);
                v_year_3532_ = leanh::lean_ctor_get(v_date_3531_, 0);
                v_month_3533_ = leanh::lean_ctor_get(v_date_3531_, 1);
                v_isSharedCheck_3558_ = (!leanh::lean_is_exclusive(v_date_3531_)) as u8;
                if v_isSharedCheck_3558_ == 0 {
                    v_unused_3559_ = leanh::lean_ctor_get(v_date_3531_, 2);
                    leanh::lean_dec(v_unused_3559_);
                    v___x_3535_ = v_date_3531_;
                    v_isShared_3536_ = v_isSharedCheck_3558_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_inc(v_month_3533_);
                    leanh::lean_inc(v_year_3532_);
                    leanh::lean_dec(v_date_3531_);
                    v___x_3535_ = leanh::lean_box(0);
                    v_isShared_3536_ = v_isSharedCheck_3558_;
                    state = 6;
                    continue;
                }
            }
            2 => {
                v_time_3502_ = leanh::lean_ctor_get(v_date_3499_, 1);
                v_isSharedCheck_3529_ = (!leanh::lean_is_exclusive(v_date_3499_)) as u8;
                if v_isSharedCheck_3529_ == 0 {
                    v_unused_3530_ = leanh::lean_ctor_get(v_date_3499_, 0);
                    leanh::lean_dec(v_unused_3530_);
                    v___x_3504_ = v_date_3499_;
                    v_isShared_3505_ = v_isSharedCheck_3529_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_time_3502_);
                    leanh::lean_dec(v_date_3499_);
                    v___x_3504_ = leanh::lean_box(0);
                    v_isShared_3505_ = v_isSharedCheck_3529_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3505_ == 0 {
                    leanh::lean_ctor_set(v___x_3504_, 0, v___y_3501_);
                    v___x_3507_ = v___x_3504_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3528_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3528_, 0, v___y_3501_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3528_, 1, v_time_3502_);
                    v___x_3507_ = v_reuseFailAlloc_3528_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                leanh::lean_inc_ref(v___x_3507_);
                v_wt_3508_ = l_Std_Time_PlainDateTime_toWallTime(v___x_3507_);
                leanh::lean_inc_ref(v_rules_3495_);
                v_ltt_3509_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(
                    v_rules_3495_,
                    v_wt_3508_,
                );
                v_tz_3510_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_3509_);
                leanh::lean_dec_ref(v_ltt_3509_);
                v_offset_3511_ = leanh::lean_ctor_get(v_tz_3510_, 0);
                leanh::lean_inc(v_offset_3511_);
                v_second_3512_ = leanh::lean_ctor_get(v_wt_3508_, 0);
                leanh::lean_inc(v_second_3512_);
                v_nano_3513_ = leanh::lean_ctor_get(v_wt_3508_, 1);
                leanh::lean_inc(v_nano_3513_);
                leanh::lean_dec_ref(v_wt_3508_);
                v___f_3514_ = leanh::lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v___f_3514_, 0, v___x_3507_);
                v___x_3515_ = lean_mk_thunk(v___f_3514_);
                v___x_3516_ = lean_int_neg(v_offset_3511_);
                leanh::lean_dec(v_offset_3511_);
                v___x_3517_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
                );
                v___x_3518_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3519_ = lean_int_mul(v_second_3512_, v___x_3518_);
                leanh::lean_dec(v_second_3512_);
                v___x_3520_ = lean_int_add(v___x_3519_, v_nano_3513_);
                leanh::lean_dec(v_nano_3513_);
                leanh::lean_dec(v___x_3519_);
                v___x_3521_ = lean_int_mul(v___x_3516_, v___x_3518_);
                leanh::lean_dec(v___x_3516_);
                v___x_3522_ = lean_int_add(v___x_3521_, v___x_3517_);
                leanh::lean_dec(v___x_3521_);
                v___x_3523_ = lean_int_add(v___x_3520_, v___x_3522_);
                leanh::lean_dec(v___x_3522_);
                leanh::lean_dec(v___x_3520_);
                v___x_3524_ = l_Std_Time_Duration_ofNanoseconds(v___x_3523_);
                leanh::lean_dec(v___x_3523_);
                if v_isShared_3498_ == 0 {
                    leanh::lean_ctor_set(v___x_3497_, 3, v_tz_3510_);
                    leanh::lean_ctor_set(v___x_3497_, 1, v___x_3524_);
                    leanh::lean_ctor_set(v___x_3497_, 0, v___x_3515_);
                    v___x_3526_ = v___x_3497_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3527_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3527_, 0, v___x_3515_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3527_, 1, v___x_3524_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3527_, 2, v_rules_3495_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3527_, 3, v_tz_3510_);
                    v___x_3526_ = v_reuseFailAlloc_3527_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3526_;
            }
            6 => {
                v___x_3547_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_dayOfYear___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_dayOfYear___closed__0_once),
                    _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__0,
                );
                v___x_3548_ = lean_int_mod(v_year_3532_, v___x_3547_);
                v___x_3549_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0,
                );
                v___x_3554_ = lean_int_dec_eq(v___x_3548_, v___x_3549_);
                leanh::lean_dec(v___x_3548_);
                if v___x_3554_ == 0 {
                    v___y_3538_ = v___x_3554_;
                    state = 7;
                    continue;
                } else {
                    v___x_3555_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_dayOfYear___closed__2),
                        core::ptr::addr_of_mut!(
                            l_Std_Time_ZonedDateTime_dayOfYear___closed__2_once
                        ),
                        _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__2,
                    );
                    v___x_3556_ = lean_int_mod(v_year_3532_, v___x_3555_);
                    v___x_3557_ = lean_int_dec_eq(v___x_3556_, v___x_3549_);
                    leanh::lean_dec(v___x_3556_);
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
                    leanh::lean_dec(v_max_3539_);
                    if v_isShared_3536_ == 0 {
                        leanh::lean_ctor_set(v___x_3535_, 2, v_days_3493_);
                        v___x_3542_ = v___x_3535_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_3543_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3543_, 0, v_year_3532_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3543_, 1, v_month_3533_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3543_, 2, v_days_3493_);
                        v___x_3542_ = v_reuseFailAlloc_3543_;
                        state = 8;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_days_3493_);
                    if v_isShared_3536_ == 0 {
                        leanh::lean_ctor_set(v___x_3535_, 2, v_max_3539_);
                        v___x_3545_ = v___x_3535_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_3546_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3546_, 0, v_year_3532_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3546_, 1, v_month_3533_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3546_, 2, v_max_3539_);
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
                v___x_3551_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_dayOfYear___closed__1),
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_dayOfYear___closed__1_once),
                    _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__1,
                );
                v___x_3552_ = lean_int_mod(v_year_3532_, v___x_3551_);
                v___x_3553_ = lean_int_dec_eq(v___x_3552_, v___x_3549_);
                leanh::lean_dec(v___x_3552_);
                v___y_3538_ = v___x_3553_;
                state = 7;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_ZonedDateTime_withDaysRollOver(
    mut v_dt_3563_: *mut leanh::LeanObject,
    mut v_days_3564_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_date_3565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rules_3566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3569_: u8 = 0;
    let mut v_date_3570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_3571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_3572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3575_: u8 = 0;
    let mut v_year_3576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_month_3577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_wt_3581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ltt_3582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tz_3583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_3584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_3586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3602_: u8 = 0;
    let mut v_isSharedCheck_3603_: u8 = 0;
    let mut v_unused_3604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_3565_ = leanh::lean_ctor_get(v_dt_3563_, 0);
                v_rules_3566_ = leanh::lean_ctor_get(v_dt_3563_, 2);
                v_isSharedCheck_3603_ = (!leanh::lean_is_exclusive(v_dt_3563_)) as u8;
                if v_isSharedCheck_3603_ == 0 {
                    v_unused_3604_ = leanh::lean_ctor_get(v_dt_3563_, 3);
                    leanh::lean_dec(v_unused_3604_);
                    v_unused_3605_ = leanh::lean_ctor_get(v_dt_3563_, 1);
                    leanh::lean_dec(v_unused_3605_);
                    v___x_3568_ = v_dt_3563_;
                    v_isShared_3569_ = v_isSharedCheck_3603_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_rules_3566_);
                    leanh::lean_inc(v_date_3565_);
                    leanh::lean_dec(v_dt_3563_);
                    v___x_3568_ = leanh::lean_box(0);
                    v_isShared_3569_ = v_isSharedCheck_3603_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_date_3570_ = lean_thunk_get_own(v_date_3565_);
                leanh::lean_dec_ref(v_date_3565_);
                v_date_3571_ = leanh::lean_ctor_get(v_date_3570_, 0);
                v_time_3572_ = leanh::lean_ctor_get(v_date_3570_, 1);
                v_isSharedCheck_3602_ = (!leanh::lean_is_exclusive(v_date_3570_)) as u8;
                if v_isSharedCheck_3602_ == 0 {
                    v___x_3574_ = v_date_3570_;
                    v_isShared_3575_ = v_isSharedCheck_3602_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_time_3572_);
                    leanh::lean_inc(v_date_3571_);
                    leanh::lean_dec(v_date_3570_);
                    v___x_3574_ = leanh::lean_box(0);
                    v_isShared_3575_ = v_isSharedCheck_3602_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_year_3576_ = leanh::lean_ctor_get(v_date_3571_, 0);
                leanh::lean_inc(v_year_3576_);
                v_month_3577_ = leanh::lean_ctor_get(v_date_3571_, 1);
                leanh::lean_inc(v_month_3577_);
                leanh::lean_dec_ref(v_date_3571_);
                v___x_3578_ =
                    l_Std_Time_PlainDate_rollOver(v_year_3576_, v_month_3577_, v_days_3564_);
                if v_isShared_3575_ == 0 {
                    leanh::lean_ctor_set(v___x_3574_, 0, v___x_3578_);
                    v___x_3580_ = v___x_3574_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3601_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3601_, 0, v___x_3578_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3601_, 1, v_time_3572_);
                    v___x_3580_ = v_reuseFailAlloc_3601_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                leanh::lean_inc_ref(v___x_3580_);
                v_wt_3581_ = l_Std_Time_PlainDateTime_toWallTime(v___x_3580_);
                leanh::lean_inc_ref(v_rules_3566_);
                v_ltt_3582_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(
                    v_rules_3566_,
                    v_wt_3581_,
                );
                v_tz_3583_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_3582_);
                leanh::lean_dec_ref(v_ltt_3582_);
                v_offset_3584_ = leanh::lean_ctor_get(v_tz_3583_, 0);
                leanh::lean_inc(v_offset_3584_);
                v_second_3585_ = leanh::lean_ctor_get(v_wt_3581_, 0);
                leanh::lean_inc(v_second_3585_);
                v_nano_3586_ = leanh::lean_ctor_get(v_wt_3581_, 1);
                leanh::lean_inc(v_nano_3586_);
                leanh::lean_dec_ref(v_wt_3581_);
                v___f_3587_ = leanh::lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v___f_3587_, 0, v___x_3580_);
                v___x_3588_ = lean_mk_thunk(v___f_3587_);
                v___x_3589_ = lean_int_neg(v_offset_3584_);
                leanh::lean_dec(v_offset_3584_);
                v___x_3590_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
                );
                v___x_3591_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3592_ = lean_int_mul(v_second_3585_, v___x_3591_);
                leanh::lean_dec(v_second_3585_);
                v___x_3593_ = lean_int_add(v___x_3592_, v_nano_3586_);
                leanh::lean_dec(v_nano_3586_);
                leanh::lean_dec(v___x_3592_);
                v___x_3594_ = lean_int_mul(v___x_3589_, v___x_3591_);
                leanh::lean_dec(v___x_3589_);
                v___x_3595_ = lean_int_add(v___x_3594_, v___x_3590_);
                leanh::lean_dec(v___x_3594_);
                v___x_3596_ = lean_int_add(v___x_3593_, v___x_3595_);
                leanh::lean_dec(v___x_3595_);
                leanh::lean_dec(v___x_3593_);
                v___x_3597_ = l_Std_Time_Duration_ofNanoseconds(v___x_3596_);
                leanh::lean_dec(v___x_3596_);
                if v_isShared_3569_ == 0 {
                    leanh::lean_ctor_set(v___x_3568_, 3, v_tz_3583_);
                    leanh::lean_ctor_set(v___x_3568_, 1, v___x_3597_);
                    leanh::lean_ctor_set(v___x_3568_, 0, v___x_3588_);
                    v___x_3599_ = v___x_3568_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3600_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3600_, 0, v___x_3588_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3600_, 1, v___x_3597_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3600_, 2, v_rules_3566_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3600_, 3, v_tz_3583_);
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
    mut v_dt_3606_: *mut leanh::LeanObject,
    mut v_days_3607_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3608_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3608_ = l_Std_Time_ZonedDateTime_withDaysRollOver(v_dt_3606_, v_days_3607_);
    leanh::lean_dec(v_days_3607_);
    return v_res_3608_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_withMonthClip(
    mut v_dt_3609_: *mut leanh::LeanObject,
    mut v_month_3610_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_date_3611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rules_3612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3615_: u8 = 0;
    let mut v_date_3616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_3619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3622_: u8 = 0;
    let mut v___x_3624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_wt_3625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ltt_3626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tz_3627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_3628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_3630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3646_: u8 = 0;
    let mut v_unused_3647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_3648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_year_3649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_day_3650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3653_: u8 = 0;
    let mut v___y_3655_: u8 = 0;
    let mut v_max_3656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3657_: u8 = 0;
    let mut v___x_3659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3670_: u8 = 0;
    let mut v___x_3671_: u8 = 0;
    let mut v___x_3672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3674_: u8 = 0;
    let mut v_isSharedCheck_3675_: u8 = 0;
    let mut v_unused_3676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3677_: u8 = 0;
    let mut v_unused_3678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_3611_ = leanh::lean_ctor_get(v_dt_3609_, 0);
                v_rules_3612_ = leanh::lean_ctor_get(v_dt_3609_, 2);
                v_isSharedCheck_3677_ = (!leanh::lean_is_exclusive(v_dt_3609_)) as u8;
                if v_isSharedCheck_3677_ == 0 {
                    v_unused_3678_ = leanh::lean_ctor_get(v_dt_3609_, 3);
                    leanh::lean_dec(v_unused_3678_);
                    v_unused_3679_ = leanh::lean_ctor_get(v_dt_3609_, 1);
                    leanh::lean_dec(v_unused_3679_);
                    v___x_3614_ = v_dt_3609_;
                    v_isShared_3615_ = v_isSharedCheck_3677_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_rules_3612_);
                    leanh::lean_inc(v_date_3611_);
                    leanh::lean_dec(v_dt_3609_);
                    v___x_3614_ = leanh::lean_box(0);
                    v_isShared_3615_ = v_isSharedCheck_3677_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_date_3616_ = lean_thunk_get_own(v_date_3611_);
                leanh::lean_dec_ref(v_date_3611_);
                v_date_3648_ = leanh::lean_ctor_get(v_date_3616_, 0);
                leanh::lean_inc_ref(v_date_3648_);
                v_year_3649_ = leanh::lean_ctor_get(v_date_3648_, 0);
                v_day_3650_ = leanh::lean_ctor_get(v_date_3648_, 2);
                v_isSharedCheck_3675_ = (!leanh::lean_is_exclusive(v_date_3648_)) as u8;
                if v_isSharedCheck_3675_ == 0 {
                    v_unused_3676_ = leanh::lean_ctor_get(v_date_3648_, 1);
                    leanh::lean_dec(v_unused_3676_);
                    v___x_3652_ = v_date_3648_;
                    v_isShared_3653_ = v_isSharedCheck_3675_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_inc(v_day_3650_);
                    leanh::lean_inc(v_year_3649_);
                    leanh::lean_dec(v_date_3648_);
                    v___x_3652_ = leanh::lean_box(0);
                    v_isShared_3653_ = v_isSharedCheck_3675_;
                    state = 6;
                    continue;
                }
            }
            2 => {
                v_time_3619_ = leanh::lean_ctor_get(v_date_3616_, 1);
                v_isSharedCheck_3646_ = (!leanh::lean_is_exclusive(v_date_3616_)) as u8;
                if v_isSharedCheck_3646_ == 0 {
                    v_unused_3647_ = leanh::lean_ctor_get(v_date_3616_, 0);
                    leanh::lean_dec(v_unused_3647_);
                    v___x_3621_ = v_date_3616_;
                    v_isShared_3622_ = v_isSharedCheck_3646_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_time_3619_);
                    leanh::lean_dec(v_date_3616_);
                    v___x_3621_ = leanh::lean_box(0);
                    v_isShared_3622_ = v_isSharedCheck_3646_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3622_ == 0 {
                    leanh::lean_ctor_set(v___x_3621_, 0, v___y_3618_);
                    v___x_3624_ = v___x_3621_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3645_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3645_, 0, v___y_3618_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3645_, 1, v_time_3619_);
                    v___x_3624_ = v_reuseFailAlloc_3645_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                leanh::lean_inc_ref(v___x_3624_);
                v_wt_3625_ = l_Std_Time_PlainDateTime_toWallTime(v___x_3624_);
                leanh::lean_inc_ref(v_rules_3612_);
                v_ltt_3626_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(
                    v_rules_3612_,
                    v_wt_3625_,
                );
                v_tz_3627_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_3626_);
                leanh::lean_dec_ref(v_ltt_3626_);
                v_offset_3628_ = leanh::lean_ctor_get(v_tz_3627_, 0);
                leanh::lean_inc(v_offset_3628_);
                v_second_3629_ = leanh::lean_ctor_get(v_wt_3625_, 0);
                leanh::lean_inc(v_second_3629_);
                v_nano_3630_ = leanh::lean_ctor_get(v_wt_3625_, 1);
                leanh::lean_inc(v_nano_3630_);
                leanh::lean_dec_ref(v_wt_3625_);
                v___f_3631_ = leanh::lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v___f_3631_, 0, v___x_3624_);
                v___x_3632_ = lean_mk_thunk(v___f_3631_);
                v___x_3633_ = lean_int_neg(v_offset_3628_);
                leanh::lean_dec(v_offset_3628_);
                v___x_3634_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
                );
                v___x_3635_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3636_ = lean_int_mul(v_second_3629_, v___x_3635_);
                leanh::lean_dec(v_second_3629_);
                v___x_3637_ = lean_int_add(v___x_3636_, v_nano_3630_);
                leanh::lean_dec(v_nano_3630_);
                leanh::lean_dec(v___x_3636_);
                v___x_3638_ = lean_int_mul(v___x_3633_, v___x_3635_);
                leanh::lean_dec(v___x_3633_);
                v___x_3639_ = lean_int_add(v___x_3638_, v___x_3634_);
                leanh::lean_dec(v___x_3638_);
                v___x_3640_ = lean_int_add(v___x_3637_, v___x_3639_);
                leanh::lean_dec(v___x_3639_);
                leanh::lean_dec(v___x_3637_);
                v___x_3641_ = l_Std_Time_Duration_ofNanoseconds(v___x_3640_);
                leanh::lean_dec(v___x_3640_);
                if v_isShared_3615_ == 0 {
                    leanh::lean_ctor_set(v___x_3614_, 3, v_tz_3627_);
                    leanh::lean_ctor_set(v___x_3614_, 1, v___x_3641_);
                    leanh::lean_ctor_set(v___x_3614_, 0, v___x_3632_);
                    v___x_3643_ = v___x_3614_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3644_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3644_, 0, v___x_3632_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3644_, 1, v___x_3641_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3644_, 2, v_rules_3612_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3644_, 3, v_tz_3627_);
                    v___x_3643_ = v_reuseFailAlloc_3644_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3643_;
            }
            6 => {
                v___x_3664_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_dayOfYear___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_dayOfYear___closed__0_once),
                    _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__0,
                );
                v___x_3665_ = lean_int_mod(v_year_3649_, v___x_3664_);
                v___x_3666_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0,
                );
                v___x_3671_ = lean_int_dec_eq(v___x_3665_, v___x_3666_);
                leanh::lean_dec(v___x_3665_);
                if v___x_3671_ == 0 {
                    v___y_3655_ = v___x_3671_;
                    state = 7;
                    continue;
                } else {
                    v___x_3672_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_dayOfYear___closed__2),
                        core::ptr::addr_of_mut!(
                            l_Std_Time_ZonedDateTime_dayOfYear___closed__2_once
                        ),
                        _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__2,
                    );
                    v___x_3673_ = lean_int_mod(v_year_3649_, v___x_3672_);
                    v___x_3674_ = lean_int_dec_eq(v___x_3673_, v___x_3666_);
                    leanh::lean_dec(v___x_3673_);
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
                    leanh::lean_dec(v_max_3656_);
                    if v_isShared_3653_ == 0 {
                        leanh::lean_ctor_set(v___x_3652_, 1, v_month_3610_);
                        v___x_3659_ = v___x_3652_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_3660_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3660_, 0, v_year_3649_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3660_, 1, v_month_3610_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3660_, 2, v_day_3650_);
                        v___x_3659_ = v_reuseFailAlloc_3660_;
                        state = 8;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_day_3650_);
                    if v_isShared_3653_ == 0 {
                        leanh::lean_ctor_set(v___x_3652_, 2, v_max_3656_);
                        leanh::lean_ctor_set(v___x_3652_, 1, v_month_3610_);
                        v___x_3662_ = v___x_3652_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_3663_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3663_, 0, v_year_3649_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3663_, 1, v_month_3610_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3663_, 2, v_max_3656_);
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
                v___x_3668_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_dayOfYear___closed__1),
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_dayOfYear___closed__1_once),
                    _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__1,
                );
                v___x_3669_ = lean_int_mod(v_year_3649_, v___x_3668_);
                v___x_3670_ = lean_int_dec_eq(v___x_3669_, v___x_3666_);
                leanh::lean_dec(v___x_3669_);
                v___y_3655_ = v___x_3670_;
                state = 7;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_ZonedDateTime_withMonthRollOver(
    mut v_dt_3680_: *mut leanh::LeanObject,
    mut v_month_3681_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_date_3682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rules_3683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3686_: u8 = 0;
    let mut v_date_3687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_3688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_3689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3692_: u8 = 0;
    let mut v_year_3693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_day_3694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_wt_3698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ltt_3699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tz_3700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_3701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_3703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3719_: u8 = 0;
    let mut v_isSharedCheck_3720_: u8 = 0;
    let mut v_unused_3721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_3682_ = leanh::lean_ctor_get(v_dt_3680_, 0);
                v_rules_3683_ = leanh::lean_ctor_get(v_dt_3680_, 2);
                v_isSharedCheck_3720_ = (!leanh::lean_is_exclusive(v_dt_3680_)) as u8;
                if v_isSharedCheck_3720_ == 0 {
                    v_unused_3721_ = leanh::lean_ctor_get(v_dt_3680_, 3);
                    leanh::lean_dec(v_unused_3721_);
                    v_unused_3722_ = leanh::lean_ctor_get(v_dt_3680_, 1);
                    leanh::lean_dec(v_unused_3722_);
                    v___x_3685_ = v_dt_3680_;
                    v_isShared_3686_ = v_isSharedCheck_3720_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_rules_3683_);
                    leanh::lean_inc(v_date_3682_);
                    leanh::lean_dec(v_dt_3680_);
                    v___x_3685_ = leanh::lean_box(0);
                    v_isShared_3686_ = v_isSharedCheck_3720_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_date_3687_ = lean_thunk_get_own(v_date_3682_);
                leanh::lean_dec_ref(v_date_3682_);
                v_date_3688_ = leanh::lean_ctor_get(v_date_3687_, 0);
                v_time_3689_ = leanh::lean_ctor_get(v_date_3687_, 1);
                v_isSharedCheck_3719_ = (!leanh::lean_is_exclusive(v_date_3687_)) as u8;
                if v_isSharedCheck_3719_ == 0 {
                    v___x_3691_ = v_date_3687_;
                    v_isShared_3692_ = v_isSharedCheck_3719_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_time_3689_);
                    leanh::lean_inc(v_date_3688_);
                    leanh::lean_dec(v_date_3687_);
                    v___x_3691_ = leanh::lean_box(0);
                    v_isShared_3692_ = v_isSharedCheck_3719_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_year_3693_ = leanh::lean_ctor_get(v_date_3688_, 0);
                leanh::lean_inc(v_year_3693_);
                v_day_3694_ = leanh::lean_ctor_get(v_date_3688_, 2);
                leanh::lean_inc(v_day_3694_);
                leanh::lean_dec_ref(v_date_3688_);
                v___x_3695_ =
                    l_Std_Time_PlainDate_rollOver(v_year_3693_, v_month_3681_, v_day_3694_);
                leanh::lean_dec(v_day_3694_);
                if v_isShared_3692_ == 0 {
                    leanh::lean_ctor_set(v___x_3691_, 0, v___x_3695_);
                    v___x_3697_ = v___x_3691_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3718_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3718_, 0, v___x_3695_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3718_, 1, v_time_3689_);
                    v___x_3697_ = v_reuseFailAlloc_3718_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                leanh::lean_inc_ref(v___x_3697_);
                v_wt_3698_ = l_Std_Time_PlainDateTime_toWallTime(v___x_3697_);
                leanh::lean_inc_ref(v_rules_3683_);
                v_ltt_3699_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(
                    v_rules_3683_,
                    v_wt_3698_,
                );
                v_tz_3700_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_3699_);
                leanh::lean_dec_ref(v_ltt_3699_);
                v_offset_3701_ = leanh::lean_ctor_get(v_tz_3700_, 0);
                leanh::lean_inc(v_offset_3701_);
                v_second_3702_ = leanh::lean_ctor_get(v_wt_3698_, 0);
                leanh::lean_inc(v_second_3702_);
                v_nano_3703_ = leanh::lean_ctor_get(v_wt_3698_, 1);
                leanh::lean_inc(v_nano_3703_);
                leanh::lean_dec_ref(v_wt_3698_);
                v___f_3704_ = leanh::lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v___f_3704_, 0, v___x_3697_);
                v___x_3705_ = lean_mk_thunk(v___f_3704_);
                v___x_3706_ = lean_int_neg(v_offset_3701_);
                leanh::lean_dec(v_offset_3701_);
                v___x_3707_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
                );
                v___x_3708_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3709_ = lean_int_mul(v_second_3702_, v___x_3708_);
                leanh::lean_dec(v_second_3702_);
                v___x_3710_ = lean_int_add(v___x_3709_, v_nano_3703_);
                leanh::lean_dec(v_nano_3703_);
                leanh::lean_dec(v___x_3709_);
                v___x_3711_ = lean_int_mul(v___x_3706_, v___x_3708_);
                leanh::lean_dec(v___x_3706_);
                v___x_3712_ = lean_int_add(v___x_3711_, v___x_3707_);
                leanh::lean_dec(v___x_3711_);
                v___x_3713_ = lean_int_add(v___x_3710_, v___x_3712_);
                leanh::lean_dec(v___x_3712_);
                leanh::lean_dec(v___x_3710_);
                v___x_3714_ = l_Std_Time_Duration_ofNanoseconds(v___x_3713_);
                leanh::lean_dec(v___x_3713_);
                if v_isShared_3686_ == 0 {
                    leanh::lean_ctor_set(v___x_3685_, 3, v_tz_3700_);
                    leanh::lean_ctor_set(v___x_3685_, 1, v___x_3714_);
                    leanh::lean_ctor_set(v___x_3685_, 0, v___x_3705_);
                    v___x_3716_ = v___x_3685_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3717_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3717_, 0, v___x_3705_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3717_, 1, v___x_3714_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3717_, 2, v_rules_3683_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3717_, 3, v_tz_3700_);
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
    mut v_dt_3723_: *mut leanh::LeanObject,
    mut v_year_3724_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_date_3725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rules_3726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3729_: u8 = 0;
    let mut v_date_3730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_3733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3736_: u8 = 0;
    let mut v___x_3738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_wt_3739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ltt_3740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tz_3741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_3742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_3744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3760_: u8 = 0;
    let mut v_unused_3761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_3762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_month_3763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_day_3764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3767_: u8 = 0;
    let mut v___y_3769_: u8 = 0;
    let mut v_max_3770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3771_: u8 = 0;
    let mut v___x_3773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3784_: u8 = 0;
    let mut v___x_3785_: u8 = 0;
    let mut v___x_3786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3788_: u8 = 0;
    let mut v_isSharedCheck_3789_: u8 = 0;
    let mut v_unused_3790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3791_: u8 = 0;
    let mut v_unused_3792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_3725_ = leanh::lean_ctor_get(v_dt_3723_, 0);
                v_rules_3726_ = leanh::lean_ctor_get(v_dt_3723_, 2);
                v_isSharedCheck_3791_ = (!leanh::lean_is_exclusive(v_dt_3723_)) as u8;
                if v_isSharedCheck_3791_ == 0 {
                    v_unused_3792_ = leanh::lean_ctor_get(v_dt_3723_, 3);
                    leanh::lean_dec(v_unused_3792_);
                    v_unused_3793_ = leanh::lean_ctor_get(v_dt_3723_, 1);
                    leanh::lean_dec(v_unused_3793_);
                    v___x_3728_ = v_dt_3723_;
                    v_isShared_3729_ = v_isSharedCheck_3791_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_rules_3726_);
                    leanh::lean_inc(v_date_3725_);
                    leanh::lean_dec(v_dt_3723_);
                    v___x_3728_ = leanh::lean_box(0);
                    v_isShared_3729_ = v_isSharedCheck_3791_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_date_3730_ = lean_thunk_get_own(v_date_3725_);
                leanh::lean_dec_ref(v_date_3725_);
                v_date_3762_ = leanh::lean_ctor_get(v_date_3730_, 0);
                leanh::lean_inc_ref(v_date_3762_);
                v_month_3763_ = leanh::lean_ctor_get(v_date_3762_, 1);
                v_day_3764_ = leanh::lean_ctor_get(v_date_3762_, 2);
                v_isSharedCheck_3789_ = (!leanh::lean_is_exclusive(v_date_3762_)) as u8;
                if v_isSharedCheck_3789_ == 0 {
                    v_unused_3790_ = leanh::lean_ctor_get(v_date_3762_, 0);
                    leanh::lean_dec(v_unused_3790_);
                    v___x_3766_ = v_date_3762_;
                    v_isShared_3767_ = v_isSharedCheck_3789_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_inc(v_day_3764_);
                    leanh::lean_inc(v_month_3763_);
                    leanh::lean_dec(v_date_3762_);
                    v___x_3766_ = leanh::lean_box(0);
                    v_isShared_3767_ = v_isSharedCheck_3789_;
                    state = 6;
                    continue;
                }
            }
            2 => {
                v_time_3733_ = leanh::lean_ctor_get(v_date_3730_, 1);
                v_isSharedCheck_3760_ = (!leanh::lean_is_exclusive(v_date_3730_)) as u8;
                if v_isSharedCheck_3760_ == 0 {
                    v_unused_3761_ = leanh::lean_ctor_get(v_date_3730_, 0);
                    leanh::lean_dec(v_unused_3761_);
                    v___x_3735_ = v_date_3730_;
                    v_isShared_3736_ = v_isSharedCheck_3760_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_time_3733_);
                    leanh::lean_dec(v_date_3730_);
                    v___x_3735_ = leanh::lean_box(0);
                    v_isShared_3736_ = v_isSharedCheck_3760_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3736_ == 0 {
                    leanh::lean_ctor_set(v___x_3735_, 0, v___y_3732_);
                    v___x_3738_ = v___x_3735_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3759_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3759_, 0, v___y_3732_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3759_, 1, v_time_3733_);
                    v___x_3738_ = v_reuseFailAlloc_3759_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                leanh::lean_inc_ref(v___x_3738_);
                v_wt_3739_ = l_Std_Time_PlainDateTime_toWallTime(v___x_3738_);
                leanh::lean_inc_ref(v_rules_3726_);
                v_ltt_3740_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(
                    v_rules_3726_,
                    v_wt_3739_,
                );
                v_tz_3741_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_3740_);
                leanh::lean_dec_ref(v_ltt_3740_);
                v_offset_3742_ = leanh::lean_ctor_get(v_tz_3741_, 0);
                leanh::lean_inc(v_offset_3742_);
                v_second_3743_ = leanh::lean_ctor_get(v_wt_3739_, 0);
                leanh::lean_inc(v_second_3743_);
                v_nano_3744_ = leanh::lean_ctor_get(v_wt_3739_, 1);
                leanh::lean_inc(v_nano_3744_);
                leanh::lean_dec_ref(v_wt_3739_);
                v___f_3745_ = leanh::lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v___f_3745_, 0, v___x_3738_);
                v___x_3746_ = lean_mk_thunk(v___f_3745_);
                v___x_3747_ = lean_int_neg(v_offset_3742_);
                leanh::lean_dec(v_offset_3742_);
                v___x_3748_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
                );
                v___x_3749_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3750_ = lean_int_mul(v_second_3743_, v___x_3749_);
                leanh::lean_dec(v_second_3743_);
                v___x_3751_ = lean_int_add(v___x_3750_, v_nano_3744_);
                leanh::lean_dec(v_nano_3744_);
                leanh::lean_dec(v___x_3750_);
                v___x_3752_ = lean_int_mul(v___x_3747_, v___x_3749_);
                leanh::lean_dec(v___x_3747_);
                v___x_3753_ = lean_int_add(v___x_3752_, v___x_3748_);
                leanh::lean_dec(v___x_3752_);
                v___x_3754_ = lean_int_add(v___x_3751_, v___x_3753_);
                leanh::lean_dec(v___x_3753_);
                leanh::lean_dec(v___x_3751_);
                v___x_3755_ = l_Std_Time_Duration_ofNanoseconds(v___x_3754_);
                leanh::lean_dec(v___x_3754_);
                if v_isShared_3729_ == 0 {
                    leanh::lean_ctor_set(v___x_3728_, 3, v_tz_3741_);
                    leanh::lean_ctor_set(v___x_3728_, 1, v___x_3755_);
                    leanh::lean_ctor_set(v___x_3728_, 0, v___x_3746_);
                    v___x_3757_ = v___x_3728_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3758_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3758_, 0, v___x_3746_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3758_, 1, v___x_3755_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3758_, 2, v_rules_3726_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3758_, 3, v_tz_3741_);
                    v___x_3757_ = v_reuseFailAlloc_3758_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3757_;
            }
            6 => {
                v___x_3778_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_dayOfYear___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_dayOfYear___closed__0_once),
                    _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__0,
                );
                v___x_3779_ = lean_int_mod(v_year_3724_, v___x_3778_);
                v___x_3780_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0,
                );
                v___x_3785_ = lean_int_dec_eq(v___x_3779_, v___x_3780_);
                leanh::lean_dec(v___x_3779_);
                if v___x_3785_ == 0 {
                    v___y_3769_ = v___x_3785_;
                    state = 7;
                    continue;
                } else {
                    v___x_3786_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_dayOfYear___closed__2),
                        core::ptr::addr_of_mut!(
                            l_Std_Time_ZonedDateTime_dayOfYear___closed__2_once
                        ),
                        _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__2,
                    );
                    v___x_3787_ = lean_int_mod(v_year_3724_, v___x_3786_);
                    v___x_3788_ = lean_int_dec_eq(v___x_3787_, v___x_3780_);
                    leanh::lean_dec(v___x_3787_);
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
                    leanh::lean_dec(v_max_3770_);
                    if v_isShared_3767_ == 0 {
                        leanh::lean_ctor_set(v___x_3766_, 0, v_year_3724_);
                        v___x_3773_ = v___x_3766_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_3774_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3774_, 0, v_year_3724_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3774_, 1, v_month_3763_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3774_, 2, v_day_3764_);
                        v___x_3773_ = v_reuseFailAlloc_3774_;
                        state = 8;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_day_3764_);
                    if v_isShared_3767_ == 0 {
                        leanh::lean_ctor_set(v___x_3766_, 2, v_max_3770_);
                        leanh::lean_ctor_set(v___x_3766_, 0, v_year_3724_);
                        v___x_3776_ = v___x_3766_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_3777_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3777_, 0, v_year_3724_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3777_, 1, v_month_3763_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3777_, 2, v_max_3770_);
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
                v___x_3782_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_dayOfYear___closed__1),
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_dayOfYear___closed__1_once),
                    _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__1,
                );
                v___x_3783_ = lean_int_mod(v_year_3724_, v___x_3782_);
                v___x_3784_ = lean_int_dec_eq(v___x_3783_, v___x_3780_);
                leanh::lean_dec(v___x_3783_);
                v___y_3769_ = v___x_3784_;
                state = 7;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_ZonedDateTime_withYearRollOver(
    mut v_dt_3794_: *mut leanh::LeanObject,
    mut v_year_3795_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_date_3796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rules_3797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3800_: u8 = 0;
    let mut v_date_3801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_3802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_3803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3806_: u8 = 0;
    let mut v_month_3807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_day_3808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_wt_3812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ltt_3813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tz_3814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_3815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_3817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3833_: u8 = 0;
    let mut v_isSharedCheck_3834_: u8 = 0;
    let mut v_unused_3835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_3796_ = leanh::lean_ctor_get(v_dt_3794_, 0);
                v_rules_3797_ = leanh::lean_ctor_get(v_dt_3794_, 2);
                v_isSharedCheck_3834_ = (!leanh::lean_is_exclusive(v_dt_3794_)) as u8;
                if v_isSharedCheck_3834_ == 0 {
                    v_unused_3835_ = leanh::lean_ctor_get(v_dt_3794_, 3);
                    leanh::lean_dec(v_unused_3835_);
                    v_unused_3836_ = leanh::lean_ctor_get(v_dt_3794_, 1);
                    leanh::lean_dec(v_unused_3836_);
                    v___x_3799_ = v_dt_3794_;
                    v_isShared_3800_ = v_isSharedCheck_3834_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_rules_3797_);
                    leanh::lean_inc(v_date_3796_);
                    leanh::lean_dec(v_dt_3794_);
                    v___x_3799_ = leanh::lean_box(0);
                    v_isShared_3800_ = v_isSharedCheck_3834_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_date_3801_ = lean_thunk_get_own(v_date_3796_);
                leanh::lean_dec_ref(v_date_3796_);
                v_date_3802_ = leanh::lean_ctor_get(v_date_3801_, 0);
                v_time_3803_ = leanh::lean_ctor_get(v_date_3801_, 1);
                v_isSharedCheck_3833_ = (!leanh::lean_is_exclusive(v_date_3801_)) as u8;
                if v_isSharedCheck_3833_ == 0 {
                    v___x_3805_ = v_date_3801_;
                    v_isShared_3806_ = v_isSharedCheck_3833_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_time_3803_);
                    leanh::lean_inc(v_date_3802_);
                    leanh::lean_dec(v_date_3801_);
                    v___x_3805_ = leanh::lean_box(0);
                    v_isShared_3806_ = v_isSharedCheck_3833_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_month_3807_ = leanh::lean_ctor_get(v_date_3802_, 1);
                leanh::lean_inc(v_month_3807_);
                v_day_3808_ = leanh::lean_ctor_get(v_date_3802_, 2);
                leanh::lean_inc(v_day_3808_);
                leanh::lean_dec_ref(v_date_3802_);
                v___x_3809_ =
                    l_Std_Time_PlainDate_rollOver(v_year_3795_, v_month_3807_, v_day_3808_);
                leanh::lean_dec(v_day_3808_);
                if v_isShared_3806_ == 0 {
                    leanh::lean_ctor_set(v___x_3805_, 0, v___x_3809_);
                    v___x_3811_ = v___x_3805_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3832_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3832_, 0, v___x_3809_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3832_, 1, v_time_3803_);
                    v___x_3811_ = v_reuseFailAlloc_3832_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                leanh::lean_inc_ref(v___x_3811_);
                v_wt_3812_ = l_Std_Time_PlainDateTime_toWallTime(v___x_3811_);
                leanh::lean_inc_ref(v_rules_3797_);
                v_ltt_3813_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(
                    v_rules_3797_,
                    v_wt_3812_,
                );
                v_tz_3814_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_3813_);
                leanh::lean_dec_ref(v_ltt_3813_);
                v_offset_3815_ = leanh::lean_ctor_get(v_tz_3814_, 0);
                leanh::lean_inc(v_offset_3815_);
                v_second_3816_ = leanh::lean_ctor_get(v_wt_3812_, 0);
                leanh::lean_inc(v_second_3816_);
                v_nano_3817_ = leanh::lean_ctor_get(v_wt_3812_, 1);
                leanh::lean_inc(v_nano_3817_);
                leanh::lean_dec_ref(v_wt_3812_);
                v___f_3818_ = leanh::lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v___f_3818_, 0, v___x_3811_);
                v___x_3819_ = lean_mk_thunk(v___f_3818_);
                v___x_3820_ = lean_int_neg(v_offset_3815_);
                leanh::lean_dec(v_offset_3815_);
                v___x_3821_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
                );
                v___x_3822_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3823_ = lean_int_mul(v_second_3816_, v___x_3822_);
                leanh::lean_dec(v_second_3816_);
                v___x_3824_ = lean_int_add(v___x_3823_, v_nano_3817_);
                leanh::lean_dec(v_nano_3817_);
                leanh::lean_dec(v___x_3823_);
                v___x_3825_ = lean_int_mul(v___x_3820_, v___x_3822_);
                leanh::lean_dec(v___x_3820_);
                v___x_3826_ = lean_int_add(v___x_3825_, v___x_3821_);
                leanh::lean_dec(v___x_3825_);
                v___x_3827_ = lean_int_add(v___x_3824_, v___x_3826_);
                leanh::lean_dec(v___x_3826_);
                leanh::lean_dec(v___x_3824_);
                v___x_3828_ = l_Std_Time_Duration_ofNanoseconds(v___x_3827_);
                leanh::lean_dec(v___x_3827_);
                if v_isShared_3800_ == 0 {
                    leanh::lean_ctor_set(v___x_3799_, 3, v_tz_3814_);
                    leanh::lean_ctor_set(v___x_3799_, 1, v___x_3828_);
                    leanh::lean_ctor_set(v___x_3799_, 0, v___x_3819_);
                    v___x_3830_ = v___x_3799_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3831_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3831_, 0, v___x_3819_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3831_, 1, v___x_3828_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3831_, 2, v_rules_3797_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3831_, 3, v_tz_3814_);
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
    mut v_dt_3837_: *mut leanh::LeanObject,
    mut v_hour_3838_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_date_3839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rules_3840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3843_: u8 = 0;
    let mut v_date_3844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_3845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_3846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3849_: u8 = 0;
    let mut v_minute_3850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_3852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3855_: u8 = 0;
    let mut v___x_3857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_wt_3860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ltt_3861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tz_3862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_3863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_3865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3882_: u8 = 0;
    let mut v_unused_3883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3884_: u8 = 0;
    let mut v_isSharedCheck_3885_: u8 = 0;
    let mut v_unused_3886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_3839_ = leanh::lean_ctor_get(v_dt_3837_, 0);
                v_rules_3840_ = leanh::lean_ctor_get(v_dt_3837_, 2);
                v_isSharedCheck_3885_ = (!leanh::lean_is_exclusive(v_dt_3837_)) as u8;
                if v_isSharedCheck_3885_ == 0 {
                    v_unused_3886_ = leanh::lean_ctor_get(v_dt_3837_, 3);
                    leanh::lean_dec(v_unused_3886_);
                    v_unused_3887_ = leanh::lean_ctor_get(v_dt_3837_, 1);
                    leanh::lean_dec(v_unused_3887_);
                    v___x_3842_ = v_dt_3837_;
                    v_isShared_3843_ = v_isSharedCheck_3885_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_rules_3840_);
                    leanh::lean_inc(v_date_3839_);
                    leanh::lean_dec(v_dt_3837_);
                    v___x_3842_ = leanh::lean_box(0);
                    v_isShared_3843_ = v_isSharedCheck_3885_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_date_3844_ = lean_thunk_get_own(v_date_3839_);
                leanh::lean_dec_ref(v_date_3839_);
                v_time_3845_ = leanh::lean_ctor_get(v_date_3844_, 1);
                v_date_3846_ = leanh::lean_ctor_get(v_date_3844_, 0);
                v_isSharedCheck_3884_ = (!leanh::lean_is_exclusive(v_date_3844_)) as u8;
                if v_isSharedCheck_3884_ == 0 {
                    v___x_3848_ = v_date_3844_;
                    v_isShared_3849_ = v_isSharedCheck_3884_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_time_3845_);
                    leanh::lean_inc(v_date_3846_);
                    leanh::lean_dec(v_date_3844_);
                    v___x_3848_ = leanh::lean_box(0);
                    v_isShared_3849_ = v_isSharedCheck_3884_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_minute_3850_ = leanh::lean_ctor_get(v_time_3845_, 1);
                v_second_3851_ = leanh::lean_ctor_get(v_time_3845_, 2);
                v_nanosecond_3852_ = leanh::lean_ctor_get(v_time_3845_, 3);
                v_isSharedCheck_3882_ = (!leanh::lean_is_exclusive(v_time_3845_)) as u8;
                if v_isSharedCheck_3882_ == 0 {
                    v_unused_3883_ = leanh::lean_ctor_get(v_time_3845_, 0);
                    leanh::lean_dec(v_unused_3883_);
                    v___x_3854_ = v_time_3845_;
                    v_isShared_3855_ = v_isSharedCheck_3882_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_nanosecond_3852_);
                    leanh::lean_inc(v_second_3851_);
                    leanh::lean_inc(v_minute_3850_);
                    leanh::lean_dec(v_time_3845_);
                    v___x_3854_ = leanh::lean_box(0);
                    v_isShared_3855_ = v_isSharedCheck_3882_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3855_ == 0 {
                    leanh::lean_ctor_set(v___x_3854_, 0, v_hour_3838_);
                    v___x_3857_ = v___x_3854_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3881_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3881_, 0, v_hour_3838_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3881_, 1, v_minute_3850_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3881_, 2, v_second_3851_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3881_, 3, v_nanosecond_3852_);
                    v___x_3857_ = v_reuseFailAlloc_3881_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3849_ == 0 {
                    leanh::lean_ctor_set(v___x_3848_, 1, v___x_3857_);
                    v___x_3859_ = v___x_3848_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3880_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3880_, 0, v_date_3846_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3880_, 1, v___x_3857_);
                    v___x_3859_ = v_reuseFailAlloc_3880_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                leanh::lean_inc_ref(v___x_3859_);
                v_wt_3860_ = l_Std_Time_PlainDateTime_toWallTime(v___x_3859_);
                leanh::lean_inc_ref(v_rules_3840_);
                v_ltt_3861_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(
                    v_rules_3840_,
                    v_wt_3860_,
                );
                v_tz_3862_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_3861_);
                leanh::lean_dec_ref(v_ltt_3861_);
                v_offset_3863_ = leanh::lean_ctor_get(v_tz_3862_, 0);
                leanh::lean_inc(v_offset_3863_);
                v_second_3864_ = leanh::lean_ctor_get(v_wt_3860_, 0);
                leanh::lean_inc(v_second_3864_);
                v_nano_3865_ = leanh::lean_ctor_get(v_wt_3860_, 1);
                leanh::lean_inc(v_nano_3865_);
                leanh::lean_dec_ref(v_wt_3860_);
                v___f_3866_ = leanh::lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v___f_3866_, 0, v___x_3859_);
                v___x_3867_ = lean_mk_thunk(v___f_3866_);
                v___x_3868_ = lean_int_neg(v_offset_3863_);
                leanh::lean_dec(v_offset_3863_);
                v___x_3869_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
                );
                v___x_3870_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3871_ = lean_int_mul(v_second_3864_, v___x_3870_);
                leanh::lean_dec(v_second_3864_);
                v___x_3872_ = lean_int_add(v___x_3871_, v_nano_3865_);
                leanh::lean_dec(v_nano_3865_);
                leanh::lean_dec(v___x_3871_);
                v___x_3873_ = lean_int_mul(v___x_3868_, v___x_3870_);
                leanh::lean_dec(v___x_3868_);
                v___x_3874_ = lean_int_add(v___x_3873_, v___x_3869_);
                leanh::lean_dec(v___x_3873_);
                v___x_3875_ = lean_int_add(v___x_3872_, v___x_3874_);
                leanh::lean_dec(v___x_3874_);
                leanh::lean_dec(v___x_3872_);
                v___x_3876_ = l_Std_Time_Duration_ofNanoseconds(v___x_3875_);
                leanh::lean_dec(v___x_3875_);
                if v_isShared_3843_ == 0 {
                    leanh::lean_ctor_set(v___x_3842_, 3, v_tz_3862_);
                    leanh::lean_ctor_set(v___x_3842_, 1, v___x_3876_);
                    leanh::lean_ctor_set(v___x_3842_, 0, v___x_3867_);
                    v___x_3878_ = v___x_3842_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3879_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3879_, 0, v___x_3867_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3879_, 1, v___x_3876_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3879_, 2, v_rules_3840_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3879_, 3, v_tz_3862_);
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
    mut v_dt_3888_: *mut leanh::LeanObject,
    mut v_minute_3889_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_date_3890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rules_3891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3894_: u8 = 0;
    let mut v_date_3895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_3896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_3897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3900_: u8 = 0;
    let mut v_hour_3901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_3903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3906_: u8 = 0;
    let mut v___x_3908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_wt_3911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ltt_3912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tz_3913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_3914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_3916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3933_: u8 = 0;
    let mut v_unused_3934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3935_: u8 = 0;
    let mut v_isSharedCheck_3936_: u8 = 0;
    let mut v_unused_3937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_3890_ = leanh::lean_ctor_get(v_dt_3888_, 0);
                v_rules_3891_ = leanh::lean_ctor_get(v_dt_3888_, 2);
                v_isSharedCheck_3936_ = (!leanh::lean_is_exclusive(v_dt_3888_)) as u8;
                if v_isSharedCheck_3936_ == 0 {
                    v_unused_3937_ = leanh::lean_ctor_get(v_dt_3888_, 3);
                    leanh::lean_dec(v_unused_3937_);
                    v_unused_3938_ = leanh::lean_ctor_get(v_dt_3888_, 1);
                    leanh::lean_dec(v_unused_3938_);
                    v___x_3893_ = v_dt_3888_;
                    v_isShared_3894_ = v_isSharedCheck_3936_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_rules_3891_);
                    leanh::lean_inc(v_date_3890_);
                    leanh::lean_dec(v_dt_3888_);
                    v___x_3893_ = leanh::lean_box(0);
                    v_isShared_3894_ = v_isSharedCheck_3936_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_date_3895_ = lean_thunk_get_own(v_date_3890_);
                leanh::lean_dec_ref(v_date_3890_);
                v_time_3896_ = leanh::lean_ctor_get(v_date_3895_, 1);
                v_date_3897_ = leanh::lean_ctor_get(v_date_3895_, 0);
                v_isSharedCheck_3935_ = (!leanh::lean_is_exclusive(v_date_3895_)) as u8;
                if v_isSharedCheck_3935_ == 0 {
                    v___x_3899_ = v_date_3895_;
                    v_isShared_3900_ = v_isSharedCheck_3935_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_time_3896_);
                    leanh::lean_inc(v_date_3897_);
                    leanh::lean_dec(v_date_3895_);
                    v___x_3899_ = leanh::lean_box(0);
                    v_isShared_3900_ = v_isSharedCheck_3935_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_hour_3901_ = leanh::lean_ctor_get(v_time_3896_, 0);
                v_second_3902_ = leanh::lean_ctor_get(v_time_3896_, 2);
                v_nanosecond_3903_ = leanh::lean_ctor_get(v_time_3896_, 3);
                v_isSharedCheck_3933_ = (!leanh::lean_is_exclusive(v_time_3896_)) as u8;
                if v_isSharedCheck_3933_ == 0 {
                    v_unused_3934_ = leanh::lean_ctor_get(v_time_3896_, 1);
                    leanh::lean_dec(v_unused_3934_);
                    v___x_3905_ = v_time_3896_;
                    v_isShared_3906_ = v_isSharedCheck_3933_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_nanosecond_3903_);
                    leanh::lean_inc(v_second_3902_);
                    leanh::lean_inc(v_hour_3901_);
                    leanh::lean_dec(v_time_3896_);
                    v___x_3905_ = leanh::lean_box(0);
                    v_isShared_3906_ = v_isSharedCheck_3933_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3906_ == 0 {
                    leanh::lean_ctor_set(v___x_3905_, 1, v_minute_3889_);
                    v___x_3908_ = v___x_3905_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3932_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3932_, 0, v_hour_3901_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3932_, 1, v_minute_3889_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3932_, 2, v_second_3902_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3932_, 3, v_nanosecond_3903_);
                    v___x_3908_ = v_reuseFailAlloc_3932_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3900_ == 0 {
                    leanh::lean_ctor_set(v___x_3899_, 1, v___x_3908_);
                    v___x_3910_ = v___x_3899_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3931_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3931_, 0, v_date_3897_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3931_, 1, v___x_3908_);
                    v___x_3910_ = v_reuseFailAlloc_3931_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                leanh::lean_inc_ref(v___x_3910_);
                v_wt_3911_ = l_Std_Time_PlainDateTime_toWallTime(v___x_3910_);
                leanh::lean_inc_ref(v_rules_3891_);
                v_ltt_3912_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(
                    v_rules_3891_,
                    v_wt_3911_,
                );
                v_tz_3913_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_3912_);
                leanh::lean_dec_ref(v_ltt_3912_);
                v_offset_3914_ = leanh::lean_ctor_get(v_tz_3913_, 0);
                leanh::lean_inc(v_offset_3914_);
                v_second_3915_ = leanh::lean_ctor_get(v_wt_3911_, 0);
                leanh::lean_inc(v_second_3915_);
                v_nano_3916_ = leanh::lean_ctor_get(v_wt_3911_, 1);
                leanh::lean_inc(v_nano_3916_);
                leanh::lean_dec_ref(v_wt_3911_);
                v___f_3917_ = leanh::lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v___f_3917_, 0, v___x_3910_);
                v___x_3918_ = lean_mk_thunk(v___f_3917_);
                v___x_3919_ = lean_int_neg(v_offset_3914_);
                leanh::lean_dec(v_offset_3914_);
                v___x_3920_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
                );
                v___x_3921_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3922_ = lean_int_mul(v_second_3915_, v___x_3921_);
                leanh::lean_dec(v_second_3915_);
                v___x_3923_ = lean_int_add(v___x_3922_, v_nano_3916_);
                leanh::lean_dec(v_nano_3916_);
                leanh::lean_dec(v___x_3922_);
                v___x_3924_ = lean_int_mul(v___x_3919_, v___x_3921_);
                leanh::lean_dec(v___x_3919_);
                v___x_3925_ = lean_int_add(v___x_3924_, v___x_3920_);
                leanh::lean_dec(v___x_3924_);
                v___x_3926_ = lean_int_add(v___x_3923_, v___x_3925_);
                leanh::lean_dec(v___x_3925_);
                leanh::lean_dec(v___x_3923_);
                v___x_3927_ = l_Std_Time_Duration_ofNanoseconds(v___x_3926_);
                leanh::lean_dec(v___x_3926_);
                if v_isShared_3894_ == 0 {
                    leanh::lean_ctor_set(v___x_3893_, 3, v_tz_3913_);
                    leanh::lean_ctor_set(v___x_3893_, 1, v___x_3927_);
                    leanh::lean_ctor_set(v___x_3893_, 0, v___x_3918_);
                    v___x_3929_ = v___x_3893_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3930_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3930_, 0, v___x_3918_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3930_, 1, v___x_3927_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3930_, 2, v_rules_3891_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3930_, 3, v_tz_3913_);
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
    mut v_dt_3939_: *mut leanh::LeanObject,
    mut v_second_3940_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_date_3941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rules_3942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3945_: u8 = 0;
    let mut v_date_3946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_3947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_3948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3951_: u8 = 0;
    let mut v_hour_3952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_minute_3953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_3954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3957_: u8 = 0;
    let mut v___x_3959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_wt_3962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ltt_3963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tz_3964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_3965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_3967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3984_: u8 = 0;
    let mut v_unused_3985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3986_: u8 = 0;
    let mut v_isSharedCheck_3987_: u8 = 0;
    let mut v_unused_3988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_3941_ = leanh::lean_ctor_get(v_dt_3939_, 0);
                v_rules_3942_ = leanh::lean_ctor_get(v_dt_3939_, 2);
                v_isSharedCheck_3987_ = (!leanh::lean_is_exclusive(v_dt_3939_)) as u8;
                if v_isSharedCheck_3987_ == 0 {
                    v_unused_3988_ = leanh::lean_ctor_get(v_dt_3939_, 3);
                    leanh::lean_dec(v_unused_3988_);
                    v_unused_3989_ = leanh::lean_ctor_get(v_dt_3939_, 1);
                    leanh::lean_dec(v_unused_3989_);
                    v___x_3944_ = v_dt_3939_;
                    v_isShared_3945_ = v_isSharedCheck_3987_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_rules_3942_);
                    leanh::lean_inc(v_date_3941_);
                    leanh::lean_dec(v_dt_3939_);
                    v___x_3944_ = leanh::lean_box(0);
                    v_isShared_3945_ = v_isSharedCheck_3987_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_date_3946_ = lean_thunk_get_own(v_date_3941_);
                leanh::lean_dec_ref(v_date_3941_);
                v_time_3947_ = leanh::lean_ctor_get(v_date_3946_, 1);
                v_date_3948_ = leanh::lean_ctor_get(v_date_3946_, 0);
                v_isSharedCheck_3986_ = (!leanh::lean_is_exclusive(v_date_3946_)) as u8;
                if v_isSharedCheck_3986_ == 0 {
                    v___x_3950_ = v_date_3946_;
                    v_isShared_3951_ = v_isSharedCheck_3986_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_time_3947_);
                    leanh::lean_inc(v_date_3948_);
                    leanh::lean_dec(v_date_3946_);
                    v___x_3950_ = leanh::lean_box(0);
                    v_isShared_3951_ = v_isSharedCheck_3986_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_hour_3952_ = leanh::lean_ctor_get(v_time_3947_, 0);
                v_minute_3953_ = leanh::lean_ctor_get(v_time_3947_, 1);
                v_nanosecond_3954_ = leanh::lean_ctor_get(v_time_3947_, 3);
                v_isSharedCheck_3984_ = (!leanh::lean_is_exclusive(v_time_3947_)) as u8;
                if v_isSharedCheck_3984_ == 0 {
                    v_unused_3985_ = leanh::lean_ctor_get(v_time_3947_, 2);
                    leanh::lean_dec(v_unused_3985_);
                    v___x_3956_ = v_time_3947_;
                    v_isShared_3957_ = v_isSharedCheck_3984_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_nanosecond_3954_);
                    leanh::lean_inc(v_minute_3953_);
                    leanh::lean_inc(v_hour_3952_);
                    leanh::lean_dec(v_time_3947_);
                    v___x_3956_ = leanh::lean_box(0);
                    v_isShared_3957_ = v_isSharedCheck_3984_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3957_ == 0 {
                    leanh::lean_ctor_set(v___x_3956_, 2, v_second_3940_);
                    v___x_3959_ = v___x_3956_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3983_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3983_, 0, v_hour_3952_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3983_, 1, v_minute_3953_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3983_, 2, v_second_3940_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3983_, 3, v_nanosecond_3954_);
                    v___x_3959_ = v_reuseFailAlloc_3983_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3951_ == 0 {
                    leanh::lean_ctor_set(v___x_3950_, 1, v___x_3959_);
                    v___x_3961_ = v___x_3950_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3982_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3982_, 0, v_date_3948_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3982_, 1, v___x_3959_);
                    v___x_3961_ = v_reuseFailAlloc_3982_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                leanh::lean_inc_ref(v___x_3961_);
                v_wt_3962_ = l_Std_Time_PlainDateTime_toWallTime(v___x_3961_);
                leanh::lean_inc_ref(v_rules_3942_);
                v_ltt_3963_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(
                    v_rules_3942_,
                    v_wt_3962_,
                );
                v_tz_3964_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_3963_);
                leanh::lean_dec_ref(v_ltt_3963_);
                v_offset_3965_ = leanh::lean_ctor_get(v_tz_3964_, 0);
                leanh::lean_inc(v_offset_3965_);
                v_second_3966_ = leanh::lean_ctor_get(v_wt_3962_, 0);
                leanh::lean_inc(v_second_3966_);
                v_nano_3967_ = leanh::lean_ctor_get(v_wt_3962_, 1);
                leanh::lean_inc(v_nano_3967_);
                leanh::lean_dec_ref(v_wt_3962_);
                v___f_3968_ = leanh::lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v___f_3968_, 0, v___x_3961_);
                v___x_3969_ = lean_mk_thunk(v___f_3968_);
                v___x_3970_ = lean_int_neg(v_offset_3965_);
                leanh::lean_dec(v_offset_3965_);
                v___x_3971_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
                );
                v___x_3972_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3973_ = lean_int_mul(v_second_3966_, v___x_3972_);
                leanh::lean_dec(v_second_3966_);
                v___x_3974_ = lean_int_add(v___x_3973_, v_nano_3967_);
                leanh::lean_dec(v_nano_3967_);
                leanh::lean_dec(v___x_3973_);
                v___x_3975_ = lean_int_mul(v___x_3970_, v___x_3972_);
                leanh::lean_dec(v___x_3970_);
                v___x_3976_ = lean_int_add(v___x_3975_, v___x_3971_);
                leanh::lean_dec(v___x_3975_);
                v___x_3977_ = lean_int_add(v___x_3974_, v___x_3976_);
                leanh::lean_dec(v___x_3976_);
                leanh::lean_dec(v___x_3974_);
                v___x_3978_ = l_Std_Time_Duration_ofNanoseconds(v___x_3977_);
                leanh::lean_dec(v___x_3977_);
                if v_isShared_3945_ == 0 {
                    leanh::lean_ctor_set(v___x_3944_, 3, v_tz_3964_);
                    leanh::lean_ctor_set(v___x_3944_, 1, v___x_3978_);
                    leanh::lean_ctor_set(v___x_3944_, 0, v___x_3969_);
                    v___x_3980_ = v___x_3944_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3981_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3981_, 0, v___x_3969_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3981_, 1, v___x_3978_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3981_, 2, v_rules_3942_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3981_, 3, v_tz_3964_);
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
-> *mut leanh::LeanObject {
    let mut v___x_3990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3990_ = leanh::lean_unsigned_to_nat(1000);
    v___x_3991_ = lean_nat_to_int(v___x_3990_);
    return v___x_3991_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_withMilliseconds(
    mut v_dt_3992_: *mut leanh::LeanObject,
    mut v_millis_3993_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_date_3994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rules_3995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3998_: u8 = 0;
    let mut v_date_3999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_4000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_4001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4004_: u8 = 0;
    let mut v_hour_4005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_minute_4006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_4007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_4008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4011_: u8 = 0;
    let mut v___x_4012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_wt_4021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ltt_4022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tz_4023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_4024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_4025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_4026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4043_: u8 = 0;
    let mut v_isSharedCheck_4044_: u8 = 0;
    let mut v_isSharedCheck_4045_: u8 = 0;
    let mut v_unused_4046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_3994_ = leanh::lean_ctor_get(v_dt_3992_, 0);
                v_rules_3995_ = leanh::lean_ctor_get(v_dt_3992_, 2);
                v_isSharedCheck_4045_ = (!leanh::lean_is_exclusive(v_dt_3992_)) as u8;
                if v_isSharedCheck_4045_ == 0 {
                    v_unused_4046_ = leanh::lean_ctor_get(v_dt_3992_, 3);
                    leanh::lean_dec(v_unused_4046_);
                    v_unused_4047_ = leanh::lean_ctor_get(v_dt_3992_, 1);
                    leanh::lean_dec(v_unused_4047_);
                    v___x_3997_ = v_dt_3992_;
                    v_isShared_3998_ = v_isSharedCheck_4045_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_rules_3995_);
                    leanh::lean_inc(v_date_3994_);
                    leanh::lean_dec(v_dt_3992_);
                    v___x_3997_ = leanh::lean_box(0);
                    v_isShared_3998_ = v_isSharedCheck_4045_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_date_3999_ = lean_thunk_get_own(v_date_3994_);
                leanh::lean_dec_ref(v_date_3994_);
                v_time_4000_ = leanh::lean_ctor_get(v_date_3999_, 1);
                v_date_4001_ = leanh::lean_ctor_get(v_date_3999_, 0);
                v_isSharedCheck_4044_ = (!leanh::lean_is_exclusive(v_date_3999_)) as u8;
                if v_isSharedCheck_4044_ == 0 {
                    v___x_4003_ = v_date_3999_;
                    v_isShared_4004_ = v_isSharedCheck_4044_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_time_4000_);
                    leanh::lean_inc(v_date_4001_);
                    leanh::lean_dec(v_date_3999_);
                    v___x_4003_ = leanh::lean_box(0);
                    v_isShared_4004_ = v_isSharedCheck_4044_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_hour_4005_ = leanh::lean_ctor_get(v_time_4000_, 0);
                v_minute_4006_ = leanh::lean_ctor_get(v_time_4000_, 1);
                v_second_4007_ = leanh::lean_ctor_get(v_time_4000_, 2);
                v_nanosecond_4008_ = leanh::lean_ctor_get(v_time_4000_, 3);
                v_isSharedCheck_4043_ = (!leanh::lean_is_exclusive(v_time_4000_)) as u8;
                if v_isSharedCheck_4043_ == 0 {
                    v___x_4010_ = v_time_4000_;
                    v_isShared_4011_ = v_isSharedCheck_4043_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_nanosecond_4008_);
                    leanh::lean_inc(v_second_4007_);
                    leanh::lean_inc(v_minute_4006_);
                    leanh::lean_inc(v_hour_4005_);
                    leanh::lean_dec(v_time_4000_);
                    v___x_4010_ = leanh::lean_box(0);
                    v_isShared_4011_ = v_isSharedCheck_4043_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4012_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_withMilliseconds___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_withMilliseconds___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_withMilliseconds___closed__0,
                );
                v___x_4013_ = lean_int_emod(v_nanosecond_4008_, v___x_4012_);
                leanh::lean_dec(v_nanosecond_4008_);
                v___x_4014_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_millisecond___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_millisecond___closed__0_once),
                    _init_l_Std_Time_ZonedDateTime_millisecond___closed__0,
                );
                v___x_4015_ = lean_int_mul(v_millis_3993_, v___x_4014_);
                v___x_4016_ = lean_int_add(v___x_4015_, v___x_4013_);
                leanh::lean_dec(v___x_4013_);
                leanh::lean_dec(v___x_4015_);
                if v_isShared_4011_ == 0 {
                    leanh::lean_ctor_set(v___x_4010_, 3, v___x_4016_);
                    v___x_4018_ = v___x_4010_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4042_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4042_, 0, v_hour_4005_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4042_, 1, v_minute_4006_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4042_, 2, v_second_4007_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4042_, 3, v___x_4016_);
                    v___x_4018_ = v_reuseFailAlloc_4042_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4004_ == 0 {
                    leanh::lean_ctor_set(v___x_4003_, 1, v___x_4018_);
                    v___x_4020_ = v___x_4003_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4041_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4041_, 0, v_date_4001_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4041_, 1, v___x_4018_);
                    v___x_4020_ = v_reuseFailAlloc_4041_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                leanh::lean_inc_ref(v___x_4020_);
                v_wt_4021_ = l_Std_Time_PlainDateTime_toWallTime(v___x_4020_);
                leanh::lean_inc_ref(v_rules_3995_);
                v_ltt_4022_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(
                    v_rules_3995_,
                    v_wt_4021_,
                );
                v_tz_4023_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_4022_);
                leanh::lean_dec_ref(v_ltt_4022_);
                v_offset_4024_ = leanh::lean_ctor_get(v_tz_4023_, 0);
                leanh::lean_inc(v_offset_4024_);
                v_second_4025_ = leanh::lean_ctor_get(v_wt_4021_, 0);
                leanh::lean_inc(v_second_4025_);
                v_nano_4026_ = leanh::lean_ctor_get(v_wt_4021_, 1);
                leanh::lean_inc(v_nano_4026_);
                leanh::lean_dec_ref(v_wt_4021_);
                v___f_4027_ = leanh::lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v___f_4027_, 0, v___x_4020_);
                v___x_4028_ = lean_mk_thunk(v___f_4027_);
                v___x_4029_ = lean_int_neg(v_offset_4024_);
                leanh::lean_dec(v_offset_4024_);
                v___x_4030_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
                );
                v___x_4031_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_4032_ = lean_int_mul(v_second_4025_, v___x_4031_);
                leanh::lean_dec(v_second_4025_);
                v___x_4033_ = lean_int_add(v___x_4032_, v_nano_4026_);
                leanh::lean_dec(v_nano_4026_);
                leanh::lean_dec(v___x_4032_);
                v___x_4034_ = lean_int_mul(v___x_4029_, v___x_4031_);
                leanh::lean_dec(v___x_4029_);
                v___x_4035_ = lean_int_add(v___x_4034_, v___x_4030_);
                leanh::lean_dec(v___x_4034_);
                v___x_4036_ = lean_int_add(v___x_4033_, v___x_4035_);
                leanh::lean_dec(v___x_4035_);
                leanh::lean_dec(v___x_4033_);
                v___x_4037_ = l_Std_Time_Duration_ofNanoseconds(v___x_4036_);
                leanh::lean_dec(v___x_4036_);
                if v_isShared_3998_ == 0 {
                    leanh::lean_ctor_set(v___x_3997_, 3, v_tz_4023_);
                    leanh::lean_ctor_set(v___x_3997_, 1, v___x_4037_);
                    leanh::lean_ctor_set(v___x_3997_, 0, v___x_4028_);
                    v___x_4039_ = v___x_3997_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4040_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4040_, 0, v___x_4028_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4040_, 1, v___x_4037_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4040_, 2, v_rules_3995_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4040_, 3, v_tz_4023_);
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
    mut v_dt_4048_: *mut leanh::LeanObject,
    mut v_millis_4049_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4050_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4050_ = l_Std_Time_ZonedDateTime_withMilliseconds(v_dt_4048_, v_millis_4049_);
    leanh::lean_dec(v_millis_4049_);
    return v_res_4050_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_withNanoseconds(
    mut v_dt_4051_: *mut leanh::LeanObject,
    mut v_nano_4052_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_date_4053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rules_4054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4057_: u8 = 0;
    let mut v_date_4058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_4059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_4060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4063_: u8 = 0;
    let mut v_hour_4064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_minute_4065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_4066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4069_: u8 = 0;
    let mut v___x_4071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_wt_4074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ltt_4075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tz_4076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_4077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_4078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_4079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4096_: u8 = 0;
    let mut v_unused_4097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4098_: u8 = 0;
    let mut v_isSharedCheck_4099_: u8 = 0;
    let mut v_unused_4100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_4053_ = leanh::lean_ctor_get(v_dt_4051_, 0);
                v_rules_4054_ = leanh::lean_ctor_get(v_dt_4051_, 2);
                v_isSharedCheck_4099_ = (!leanh::lean_is_exclusive(v_dt_4051_)) as u8;
                if v_isSharedCheck_4099_ == 0 {
                    v_unused_4100_ = leanh::lean_ctor_get(v_dt_4051_, 3);
                    leanh::lean_dec(v_unused_4100_);
                    v_unused_4101_ = leanh::lean_ctor_get(v_dt_4051_, 1);
                    leanh::lean_dec(v_unused_4101_);
                    v___x_4056_ = v_dt_4051_;
                    v_isShared_4057_ = v_isSharedCheck_4099_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_rules_4054_);
                    leanh::lean_inc(v_date_4053_);
                    leanh::lean_dec(v_dt_4051_);
                    v___x_4056_ = leanh::lean_box(0);
                    v_isShared_4057_ = v_isSharedCheck_4099_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_date_4058_ = lean_thunk_get_own(v_date_4053_);
                leanh::lean_dec_ref(v_date_4053_);
                v_time_4059_ = leanh::lean_ctor_get(v_date_4058_, 1);
                v_date_4060_ = leanh::lean_ctor_get(v_date_4058_, 0);
                v_isSharedCheck_4098_ = (!leanh::lean_is_exclusive(v_date_4058_)) as u8;
                if v_isSharedCheck_4098_ == 0 {
                    v___x_4062_ = v_date_4058_;
                    v_isShared_4063_ = v_isSharedCheck_4098_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_time_4059_);
                    leanh::lean_inc(v_date_4060_);
                    leanh::lean_dec(v_date_4058_);
                    v___x_4062_ = leanh::lean_box(0);
                    v_isShared_4063_ = v_isSharedCheck_4098_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_hour_4064_ = leanh::lean_ctor_get(v_time_4059_, 0);
                v_minute_4065_ = leanh::lean_ctor_get(v_time_4059_, 1);
                v_second_4066_ = leanh::lean_ctor_get(v_time_4059_, 2);
                v_isSharedCheck_4096_ = (!leanh::lean_is_exclusive(v_time_4059_)) as u8;
                if v_isSharedCheck_4096_ == 0 {
                    v_unused_4097_ = leanh::lean_ctor_get(v_time_4059_, 3);
                    leanh::lean_dec(v_unused_4097_);
                    v___x_4068_ = v_time_4059_;
                    v_isShared_4069_ = v_isSharedCheck_4096_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_second_4066_);
                    leanh::lean_inc(v_minute_4065_);
                    leanh::lean_inc(v_hour_4064_);
                    leanh::lean_dec(v_time_4059_);
                    v___x_4068_ = leanh::lean_box(0);
                    v_isShared_4069_ = v_isSharedCheck_4096_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4069_ == 0 {
                    leanh::lean_ctor_set(v___x_4068_, 3, v_nano_4052_);
                    v___x_4071_ = v___x_4068_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4095_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4095_, 0, v_hour_4064_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4095_, 1, v_minute_4065_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4095_, 2, v_second_4066_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4095_, 3, v_nano_4052_);
                    v___x_4071_ = v_reuseFailAlloc_4095_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4063_ == 0 {
                    leanh::lean_ctor_set(v___x_4062_, 1, v___x_4071_);
                    v___x_4073_ = v___x_4062_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4094_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4094_, 0, v_date_4060_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4094_, 1, v___x_4071_);
                    v___x_4073_ = v_reuseFailAlloc_4094_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                leanh::lean_inc_ref(v___x_4073_);
                v_wt_4074_ = l_Std_Time_PlainDateTime_toWallTime(v___x_4073_);
                leanh::lean_inc_ref(v_rules_4054_);
                v_ltt_4075_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(
                    v_rules_4054_,
                    v_wt_4074_,
                );
                v_tz_4076_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_4075_);
                leanh::lean_dec_ref(v_ltt_4075_);
                v_offset_4077_ = leanh::lean_ctor_get(v_tz_4076_, 0);
                leanh::lean_inc(v_offset_4077_);
                v_second_4078_ = leanh::lean_ctor_get(v_wt_4074_, 0);
                leanh::lean_inc(v_second_4078_);
                v_nano_4079_ = leanh::lean_ctor_get(v_wt_4074_, 1);
                leanh::lean_inc(v_nano_4079_);
                leanh::lean_dec_ref(v_wt_4074_);
                v___f_4080_ = leanh::lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v___f_4080_, 0, v___x_4073_);
                v___x_4081_ = lean_mk_thunk(v___f_4080_);
                v___x_4082_ = lean_int_neg(v_offset_4077_);
                leanh::lean_dec(v_offset_4077_);
                v___x_4083_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
                );
                v___x_4084_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_4085_ = lean_int_mul(v_second_4078_, v___x_4084_);
                leanh::lean_dec(v_second_4078_);
                v___x_4086_ = lean_int_add(v___x_4085_, v_nano_4079_);
                leanh::lean_dec(v_nano_4079_);
                leanh::lean_dec(v___x_4085_);
                v___x_4087_ = lean_int_mul(v___x_4082_, v___x_4084_);
                leanh::lean_dec(v___x_4082_);
                v___x_4088_ = lean_int_add(v___x_4087_, v___x_4083_);
                leanh::lean_dec(v___x_4087_);
                v___x_4089_ = lean_int_add(v___x_4086_, v___x_4088_);
                leanh::lean_dec(v___x_4088_);
                leanh::lean_dec(v___x_4086_);
                v___x_4090_ = l_Std_Time_Duration_ofNanoseconds(v___x_4089_);
                leanh::lean_dec(v___x_4089_);
                if v_isShared_4057_ == 0 {
                    leanh::lean_ctor_set(v___x_4056_, 3, v_tz_4076_);
                    leanh::lean_ctor_set(v___x_4056_, 1, v___x_4090_);
                    leanh::lean_ctor_set(v___x_4056_, 0, v___x_4081_);
                    v___x_4092_ = v___x_4056_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4093_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4093_, 0, v___x_4081_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4093_, 1, v___x_4090_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4093_, 2, v_rules_4054_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4093_, 3, v_tz_4076_);
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
    mut v_date_4102_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_date_4103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_4105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_year_4106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4113_: u8 = 0;
    let mut v___x_4114_: u8 = 0;
    let mut v___x_4115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4117_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_4103_ = leanh::lean_ctor_get(v_date_4102_, 0);
                v___x_4104_ = lean_thunk_get_own(v_date_4103_);
                v_date_4105_ = leanh::lean_ctor_get(v___x_4104_, 0);
                leanh::lean_inc_ref(v_date_4105_);
                leanh::lean_dec(v___x_4104_);
                v_year_4106_ = leanh::lean_ctor_get(v_date_4105_, 0);
                leanh::lean_inc(v_year_4106_);
                leanh::lean_dec_ref(v_date_4105_);
                v___x_4107_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_dayOfYear___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_dayOfYear___closed__0_once),
                    _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__0,
                );
                v___x_4108_ = lean_int_mod(v_year_4106_, v___x_4107_);
                v___x_4109_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0,
                );
                v___x_4114_ = lean_int_dec_eq(v___x_4108_, v___x_4109_);
                leanh::lean_dec(v___x_4108_);
                if v___x_4114_ == 0 {
                    leanh::lean_dec(v_year_4106_);
                    return v___x_4114_;
                } else {
                    v___x_4115_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_dayOfYear___closed__2),
                        core::ptr::addr_of_mut!(
                            l_Std_Time_ZonedDateTime_dayOfYear___closed__2_once
                        ),
                        _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__2,
                    );
                    v___x_4116_ = lean_int_mod(v_year_4106_, v___x_4115_);
                    v___x_4117_ = lean_int_dec_eq(v___x_4116_, v___x_4109_);
                    leanh::lean_dec(v___x_4116_);
                    if v___x_4117_ == 0 {
                        if v___x_4114_ == 0 {
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_year_4106_);
                            return v___x_4114_;
                        }
                    } else {
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4111_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_dayOfYear___closed__1),
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_dayOfYear___closed__1_once),
                    _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__1,
                );
                v___x_4112_ = lean_int_mod(v_year_4106_, v___x_4111_);
                leanh::lean_dec(v_year_4106_);
                v___x_4113_ = lean_int_dec_eq(v___x_4112_, v___x_4109_);
                leanh::lean_dec(v___x_4112_);
                return v___x_4113_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_ZonedDateTime_inLeapYear___boxed(
    mut v_date_4118_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4119_: u8 = 0;
    let mut v_r_4120_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4119_ = l_Std_Time_ZonedDateTime_inLeapYear(v_date_4118_);
    leanh::lean_dec_ref(v_date_4118_);
    v_r_4120_ = leanh::lean_box((v_res_4119_) as usize);
    return v_r_4120_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_toEpochDay(
    mut v_date_4121_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_date_4122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_4124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4125_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_date_4122_ = leanh::lean_ctor_get(v_date_4121_, 0);
    v___x_4123_ = lean_thunk_get_own(v_date_4122_);
    v_date_4124_ = leanh::lean_ctor_get(v___x_4123_, 0);
    leanh::lean_inc_ref(v_date_4124_);
    leanh::lean_dec(v___x_4123_);
    v___x_4125_ = l_Std_Time_PlainDate_toEpochDay(v_date_4124_);
    return v___x_4125_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_toEpochDay___boxed(
    mut v_date_4126_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4127_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4127_ = l_Std_Time_ZonedDateTime_toEpochDay(v_date_4126_);
    leanh::lean_dec_ref(v_date_4126_);
    return v_res_4127_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_ofEpochDay(
    mut v_days_4128_: *mut leanh::LeanObject,
    mut v_time_4129_: *mut leanh::LeanObject,
    mut v_zt_4130_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_wt_4133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ltt_4134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tz_4135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_4136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_4137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_4138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4150_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4131_ = l_Std_Time_PlainDate_ofEpochDay(v_days_4128_);
    v___x_4132_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4132_, 0, v___x_4131_);
    leanh::lean_ctor_set(v___x_4132_, 1, v_time_4129_);
    leanh::lean_inc_ref(v___x_4132_);
    v_wt_4133_ = l_Std_Time_PlainDateTime_toWallTime(v___x_4132_);
    leanh::lean_inc_ref(v_zt_4130_);
    v_ltt_4134_ =
        l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_zt_4130_, v_wt_4133_);
    v_tz_4135_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_4134_);
    leanh::lean_dec_ref(v_ltt_4134_);
    v_offset_4136_ = leanh::lean_ctor_get(v_tz_4135_, 0);
    leanh::lean_inc(v_offset_4136_);
    v_second_4137_ = leanh::lean_ctor_get(v_wt_4133_, 0);
    leanh::lean_inc(v_second_4137_);
    v_nano_4138_ = leanh::lean_ctor_get(v_wt_4133_, 1);
    leanh::lean_inc(v_nano_4138_);
    leanh::lean_dec_ref(v_wt_4133_);
    v___f_4139_ = leanh::lean_alloc_closure(
        l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_4139_, 0, v___x_4132_);
    v___x_4140_ = lean_mk_thunk(v___f_4139_);
    v___x_4141_ = lean_int_neg(v_offset_4136_);
    leanh::lean_dec(v_offset_4136_);
    v___x_4142_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once),
        _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
    );
    v___x_4143_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once),
        _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
    );
    v___x_4144_ = lean_int_mul(v_second_4137_, v___x_4143_);
    leanh::lean_dec(v_second_4137_);
    v___x_4145_ = lean_int_add(v___x_4144_, v_nano_4138_);
    leanh::lean_dec(v_nano_4138_);
    leanh::lean_dec(v___x_4144_);
    v___x_4146_ = lean_int_mul(v___x_4141_, v___x_4143_);
    leanh::lean_dec(v___x_4141_);
    v___x_4147_ = lean_int_add(v___x_4146_, v___x_4142_);
    leanh::lean_dec(v___x_4146_);
    v___x_4148_ = lean_int_add(v___x_4145_, v___x_4147_);
    leanh::lean_dec(v___x_4147_);
    leanh::lean_dec(v___x_4145_);
    v___x_4149_ = l_Std_Time_Duration_ofNanoseconds(v___x_4148_);
    leanh::lean_dec(v___x_4148_);
    v___x_4150_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_4150_, 0, v___x_4140_);
    leanh::lean_ctor_set(v___x_4150_, 1, v___x_4149_);
    leanh::lean_ctor_set(v___x_4150_, 2, v_zt_4130_);
    leanh::lean_ctor_set(v___x_4150_, 3, v_tz_4135_);
    return v___x_4150_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_ofEpochDay___boxed(
    mut v_days_4151_: *mut leanh::LeanObject,
    mut v_time_4152_: *mut leanh::LeanObject,
    mut v_zt_4153_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4154_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4154_ = l_Std_Time_ZonedDateTime_ofEpochDay(v_days_4151_, v_time_4152_, v_zt_4153_);
    leanh::lean_dec(v_days_4151_);
    return v_res_4154_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_instHSubDuration___lam__0(
    mut v_x_4183_: *mut leanh::LeanObject,
    mut v_y_4184_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_timestamp_4185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_timestamp_4186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_4187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_4188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_4189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_4190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4199_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_timestamp_4185_ = leanh::lean_ctor_get(v_y_4184_, 1);
    v_timestamp_4186_ = leanh::lean_ctor_get(v_x_4183_, 1);
    v_second_4187_ = leanh::lean_ctor_get(v_timestamp_4185_, 0);
    v_nano_4188_ = leanh::lean_ctor_get(v_timestamp_4185_, 1);
    v_second_4189_ = leanh::lean_ctor_get(v_timestamp_4186_, 0);
    v_nano_4190_ = leanh::lean_ctor_get(v_timestamp_4186_, 1);
    v___x_4191_ = lean_int_neg(v_second_4187_);
    v___x_4192_ = lean_int_neg(v_nano_4188_);
    v___x_4193_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once),
        _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
    );
    v___x_4194_ = lean_int_mul(v_second_4189_, v___x_4193_);
    v___x_4195_ = lean_int_add(v___x_4194_, v_nano_4190_);
    leanh::lean_dec(v___x_4194_);
    v___x_4196_ = lean_int_mul(v___x_4191_, v___x_4193_);
    leanh::lean_dec(v___x_4191_);
    v___x_4197_ = lean_int_add(v___x_4196_, v___x_4192_);
    leanh::lean_dec(v___x_4192_);
    leanh::lean_dec(v___x_4196_);
    v___x_4198_ = lean_int_add(v___x_4195_, v___x_4197_);
    leanh::lean_dec(v___x_4197_);
    leanh::lean_dec(v___x_4195_);
    v___x_4199_ = l_Std_Time_Duration_ofNanoseconds(v___x_4198_);
    leanh::lean_dec(v___x_4198_);
    return v___x_4199_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_instHSubDuration___lam__0___boxed(
    mut v_x_4200_: *mut leanh::LeanObject,
    mut v_y_4201_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4202_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4202_ = l_Std_Time_ZonedDateTime_instHSubDuration___lam__0(v_x_4200_, v_y_4201_);
    leanh::lean_dec_ref(v_y_4201_);
    leanh::lean_dec_ref(v_x_4200_);
    return v_res_4202_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_instHAddDuration___lam__0(
    mut v_x_4205_: *mut leanh::LeanObject,
    mut v_y_4206_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_second_4207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_4208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nanos_4211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_second_4207_ = leanh::lean_ctor_get(v_y_4206_, 0);
    v_nano_4208_ = leanh::lean_ctor_get(v_y_4206_, 1);
    v___x_4209_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once),
        _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
    );
    v___x_4210_ = lean_int_mul(v_second_4207_, v___x_4209_);
    v_nanos_4211_ = lean_int_add(v___x_4210_, v_nano_4208_);
    leanh::lean_dec(v___x_4210_);
    v___x_4212_ = l_Std_Time_ZonedDateTime_addNanoseconds(v_x_4205_, v_nanos_4211_);
    leanh::lean_dec(v_nanos_4211_);
    return v___x_4212_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_instHAddDuration___lam__0___boxed(
    mut v_x_4213_: *mut leanh::LeanObject,
    mut v_y_4214_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4215_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4215_ = l_Std_Time_ZonedDateTime_instHAddDuration___lam__0(v_x_4213_, v_y_4214_);
    leanh::lean_dec_ref(v_y_4214_);
    return v_res_4215_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_instHSubDuration__1___lam__0(
    mut v_x_4218_: *mut leanh::LeanObject,
    mut v_y_4219_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_second_4220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_4221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nanos_4224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4225_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_second_4220_ = leanh::lean_ctor_get(v_y_4219_, 0);
    v_nano_4221_ = leanh::lean_ctor_get(v_y_4219_, 1);
    v___x_4222_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once),
        _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
    );
    v___x_4223_ = lean_int_mul(v_second_4220_, v___x_4222_);
    v_nanos_4224_ = lean_int_add(v___x_4223_, v_nano_4221_);
    leanh::lean_dec(v___x_4223_);
    v___x_4225_ = l_Std_Time_ZonedDateTime_subNanoseconds(v_x_4218_, v_nanos_4224_);
    leanh::lean_dec(v_nanos_4224_);
    return v___x_4225_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_instHSubDuration__1___lam__0___boxed(
    mut v_x_4226_: *mut leanh::LeanObject,
    mut v_y_4227_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4228_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4228_ = l_Std_Time_ZonedDateTime_instHSubDuration__1___lam__0(v_x_4226_, v_y_4227_);
    leanh::lean_dec_ref(v_y_4227_);
    return v_res_4228_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Time_Zoned_ZonedDateTime(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Time_Zoned_DateTime(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Zoned_ZoneRules(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Time_DateTime_PlainDateTime(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Std_Time_instInhabitedZonedDateTime___private__1 =
        _init_l_Std_Time_instInhabitedZonedDateTime___private__1();
    leanh::lean_mark_persistent(l_Std_Time_instInhabitedZonedDateTime___private__1);
    l_Std_Time_instInhabitedZonedDateTime = _init_l_Std_Time_instInhabitedZonedDateTime();
    leanh::lean_mark_persistent(l_Std_Time_instInhabitedZonedDateTime);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Time_Zoned_ZonedDateTime(
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
pub unsafe fn initialize_Std_Time_Zoned_ZonedDateTime(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Time_Zoned_DateTime(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Time_Zoned_ZoneRules(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Time_DateTime_PlainDateTime(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Zoned_ZonedDateTime(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Time_Zoned_ZonedDateTime(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Time_Zoned_ZonedDateTime(builtin);
}