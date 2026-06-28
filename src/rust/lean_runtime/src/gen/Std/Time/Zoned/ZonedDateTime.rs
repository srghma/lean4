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
use crate::lean_imports_rs::Init::Core::{lean_mk_thunk, lean_thunk_get_own};
use crate::lean_imports_rs::Init::Data::Int::Basic::{
    lean_int_add, lean_int_dec_eq, lean_int_dec_lt, lean_int_mul, lean_int_neg, lean_nat_to_int,
};
use crate::lean_imports_rs::Init::Data::Int::DivMod::Basic::{
    lean_int_ediv, lean_int_emod, lean_int_mod,
};
use crate::lean_imports_rs::Init::Prelude::lean_mk_empty_array_with_capacity;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_uint8,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_ref, lean_inc_ref_n,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent,
    lean_obj_once, lean_obj_tag, lean_unbox, lean_unsigned_to_nat,
};
pub static l_Std_Time_instInhabitedZonedDateTime___private__1___closed__0_value: LeanClosureObject<
    0,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Time_instInhabitedZonedDateTime___private__1___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instInhabitedZonedDateTime___private__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instInhabitedZonedDateTime___private__1___closed__0_value)
        as *mut LeanObject;
static mut l_Std_Time_instInhabitedZonedDateTime___private__1___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedZonedDateTime___private__1___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedZonedDateTime___private__1___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedZonedDateTime___private__1___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_instInhabitedZonedDateTime___private__1: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_instInhabitedZonedDateTime: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_ZonedDateTime_ofTimestampWithZone___closed__0_value: LeanArrayObject<0> =
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
static mut l_Std_Time_ZonedDateTime_ofTimestampWithZone___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_ofTimestampWithZone___closed__0_value)
        as *mut LeanObject;
static mut l_Std_Time_ZonedDateTime_millisecond___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_ZonedDateTime_millisecond___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_ZonedDateTime_dayOfYear___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_ZonedDateTime_dayOfYear___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_ZonedDateTime_dayOfYear___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_ZonedDateTime_dayOfYear___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_ZonedDateTime_dayOfYear___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_ZonedDateTime_dayOfYear___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_ZonedDateTime_addDays___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_ZonedDateTime_addDays___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_ZonedDateTime_addWeeks___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_ZonedDateTime_addWeeks___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_ZonedDateTime_addHours___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_ZonedDateTime_addHours___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_ZonedDateTime_addMinutes___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_ZonedDateTime_addMinutes___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_ZonedDateTime_withMilliseconds___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_ZonedDateTime_withMilliseconds___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_ZonedDateTime_instHAddOffset___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Time_ZonedDateTime_addDays___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_ZonedDateTime_instHAddOffset___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHAddOffset___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Time_ZonedDateTime_instHAddOffset: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHAddOffset___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Time_ZonedDateTime_instHSubOffset___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Time_ZonedDateTime_subDays___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_ZonedDateTime_instHSubOffset___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHSubOffset___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Time_ZonedDateTime_instHSubOffset: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHSubOffset___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Time_ZonedDateTime_instHAddOffset__1___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Time_ZonedDateTime_addWeeks___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_ZonedDateTime_instHAddOffset__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHAddOffset__1___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Time_ZonedDateTime_instHAddOffset__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHAddOffset__1___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Time_ZonedDateTime_instHSubOffset__1___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Time_ZonedDateTime_subWeeks___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_ZonedDateTime_instHSubOffset__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHSubOffset__1___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Time_ZonedDateTime_instHSubOffset__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHSubOffset__1___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Time_ZonedDateTime_instHAddOffset__2___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Time_ZonedDateTime_addHours___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_ZonedDateTime_instHAddOffset__2___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHAddOffset__2___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Time_ZonedDateTime_instHAddOffset__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHAddOffset__2___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Time_ZonedDateTime_instHSubOffset__2___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Time_ZonedDateTime_subHours___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_ZonedDateTime_instHSubOffset__2___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHSubOffset__2___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Time_ZonedDateTime_instHSubOffset__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHSubOffset__2___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Time_ZonedDateTime_instHAddOffset__3___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Time_ZonedDateTime_addMinutes___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_ZonedDateTime_instHAddOffset__3___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHAddOffset__3___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Time_ZonedDateTime_instHAddOffset__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHAddOffset__3___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Time_ZonedDateTime_instHSubOffset__3___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Time_ZonedDateTime_subMinutes___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_ZonedDateTime_instHSubOffset__3___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHSubOffset__3___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Time_ZonedDateTime_instHSubOffset__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHSubOffset__3___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Time_ZonedDateTime_instHAddOffset__4___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Time_ZonedDateTime_addSeconds___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_ZonedDateTime_instHAddOffset__4___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHAddOffset__4___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Time_ZonedDateTime_instHAddOffset__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHAddOffset__4___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Time_ZonedDateTime_instHSubOffset__4___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Time_ZonedDateTime_subSeconds___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_ZonedDateTime_instHSubOffset__4___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHSubOffset__4___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Time_ZonedDateTime_instHSubOffset__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHSubOffset__4___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Time_ZonedDateTime_instHAddOffset__5___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Time_ZonedDateTime_addMilliseconds___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_ZonedDateTime_instHAddOffset__5___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHAddOffset__5___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Time_ZonedDateTime_instHAddOffset__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHAddOffset__5___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Time_ZonedDateTime_instHSubOffset__5___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Time_ZonedDateTime_subMilliseconds___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_ZonedDateTime_instHSubOffset__5___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHSubOffset__5___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Time_ZonedDateTime_instHSubOffset__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHSubOffset__5___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Time_ZonedDateTime_instHAddOffset__6___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Time_ZonedDateTime_addNanoseconds___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_ZonedDateTime_instHAddOffset__6___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHAddOffset__6___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Time_ZonedDateTime_instHAddOffset__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHAddOffset__6___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Time_ZonedDateTime_instHSubOffset__6___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Time_ZonedDateTime_subNanoseconds___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_ZonedDateTime_instHSubOffset__6___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHSubOffset__6___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Time_ZonedDateTime_instHSubOffset__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHSubOffset__6___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Time_ZonedDateTime_instHSubDuration___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Time_ZonedDateTime_instHSubDuration___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_ZonedDateTime_instHSubDuration___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHSubDuration___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Time_ZonedDateTime_instHSubDuration: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHSubDuration___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Time_ZonedDateTime_instHAddDuration___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Time_ZonedDateTime_instHAddDuration___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_ZonedDateTime_instHAddDuration___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHAddDuration___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Time_ZonedDateTime_instHAddDuration: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHAddDuration___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Time_ZonedDateTime_instHSubDuration__1___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Time_ZonedDateTime_instHSubDuration__1___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_ZonedDateTime_instHSubDuration__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHSubDuration__1___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Time_ZonedDateTime_instHSubDuration__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instHSubDuration__1___closed__0_value)
        as *mut LeanObject;
pub unsafe fn l_Std_Time_instInhabitedZonedDateTime___private__1___lam__0(
    mut v_x_2116_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2117_: *mut LeanObject = core::ptr::null_mut();
    v___x_2117_ = l_Std_Time_instInhabitedPlainDateTime_default;
    return v___x_2117_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedZonedDateTime___private__1___closed__1()
-> *mut LeanObject {
    let mut v___f_2119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut LeanObject = core::ptr::null_mut();
    v___f_2119_ = l_Std_Time_instInhabitedZonedDateTime___private__1___closed__0;
    v___x_2120_ = lean_mk_thunk(v___f_2119_);
    return v___x_2120_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedZonedDateTime___private__1___closed__2()
-> *mut LeanObject {
    let mut v___x_2121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: *mut LeanObject = core::ptr::null_mut();
    v___x_2121_ = l_Std_Time_instInhabitedTimeZone_default;
    v___x_2122_ = l_Std_Time_TimeZone_instInhabitedZoneRules_default;
    v___x_2123_ = l_Std_Time_instInhabitedTimestamp_default;
    v___x_2124_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedZonedDateTime___private__1___closed__1),
        core::ptr::addr_of_mut!(
            l_Std_Time_instInhabitedZonedDateTime___private__1___closed__1_once
        ),
        _init_l_Std_Time_instInhabitedZonedDateTime___private__1___closed__1,
    );
    v___x_2125_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_2125_, 0, v___x_2124_);
    lean_ctor_set(v___x_2125_, 1, v___x_2123_);
    lean_ctor_set(v___x_2125_, 2, v___x_2122_);
    lean_ctor_set(v___x_2125_, 3, v___x_2121_);
    return v___x_2125_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedZonedDateTime___private__1() -> *mut LeanObject {
    let mut v___x_2126_: *mut LeanObject = core::ptr::null_mut();
    v___x_2126_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedZonedDateTime___private__1___closed__2),
        core::ptr::addr_of_mut!(
            l_Std_Time_instInhabitedZonedDateTime___private__1___closed__2_once
        ),
        _init_l_Std_Time_instInhabitedZonedDateTime___private__1___closed__2,
    );
    return v___x_2126_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedZonedDateTime() -> *mut LeanObject {
    let mut v___x_2127_: *mut LeanObject = core::ptr::null_mut();
    v___x_2127_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedZonedDateTime___private__1___closed__2),
        core::ptr::addr_of_mut!(
            l_Std_Time_instInhabitedZonedDateTime___private__1___closed__2_once
        ),
        _init_l_Std_Time_instInhabitedZonedDateTime___private__1___closed__2,
    );
    return v___x_2127_;
}
pub unsafe fn _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0() -> *mut LeanObject {
    let mut v___x_2128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut LeanObject = core::ptr::null_mut();
    v___x_2128_ = lean_unsigned_to_nat(0);
    v___x_2129_ = lean_nat_to_int(v___x_2128_);
    return v___x_2129_;
}
pub unsafe fn _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1() -> *mut LeanObject {
    let mut v___x_2130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut LeanObject = core::ptr::null_mut();
    v___x_2130_ = lean_unsigned_to_nat(1000000000);
    v___x_2131_ = lean_nat_to_int(v___x_2130_);
    return v___x_2131_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_ofTimestamp___lam__0(
    mut v___y_2132_: *mut LeanObject,
    mut v_tm_2133_: *mut LeanObject,
    mut v_x_2134_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_offset_2135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_2136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_2137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut LeanObject = core::ptr::null_mut();
    v_offset_2135_ = lean_ctor_get(v___y_2132_, 0);
    v_second_2136_ = lean_ctor_get(v_tm_2133_, 0);
    v_nano_2137_ = lean_ctor_get(v_tm_2133_, 1);
    v___x_2138_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once),
        _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0,
    );
    v___x_2139_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once),
        _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
    );
    v___x_2140_ = lean_int_mul(v_second_2136_, v___x_2139_);
    v___x_2141_ = lean_int_add(v___x_2140_, v_nano_2137_);
    lean_dec(v___x_2140_);
    v___x_2142_ = lean_int_mul(v_offset_2135_, v___x_2139_);
    v___x_2143_ = lean_int_add(v___x_2142_, v___x_2138_);
    lean_dec(v___x_2142_);
    v___x_2144_ = lean_int_add(v___x_2141_, v___x_2143_);
    lean_dec(v___x_2143_);
    lean_dec(v___x_2141_);
    v___x_2145_ = l_Std_Time_Duration_ofNanoseconds(v___x_2144_);
    lean_dec(v___x_2144_);
    v___x_2146_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_2145_);
    return v___x_2146_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___boxed(
    mut v___y_2147_: *mut LeanObject,
    mut v_tm_2148_: *mut LeanObject,
    mut v_x_2149_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2150_: *mut LeanObject = core::ptr::null_mut();
    v_res_2150_ = l_Std_Time_ZonedDateTime_ofTimestamp___lam__0(v___y_2147_, v_tm_2148_, v_x_2149_);
    lean_dec_ref(v_tm_2148_);
    lean_dec_ref(v___y_2147_);
    return v_res_2150_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_ofTimestamp(
    mut v_tm_2151_: *mut LeanObject,
    mut v_rules_2152_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initialLocalTimeType_2158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_transitions_2159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2162_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_initialLocalTimeType_2158_ = lean_ctor_get(v_rules_2152_, 0);
                v_transitions_2159_ = lean_ctor_get(v_rules_2152_, 1);
                v___x_2160_ =
                    l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_2159_, v_tm_2151_);
                if lean_obj_tag(v___x_2160_) == 0 {
                    lean_dec_ref_known(v___x_2160_, 1);
                    v___x_2161_ =
                        l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_2158_);
                    v___y_2154_ = v___x_2161_;
                    state = 1;
                    continue;
                } else {
                    v_a_2162_ = lean_ctor_get(v___x_2160_, 0);
                    lean_inc(v_a_2162_);
                    lean_dec_ref_known(v___x_2160_, 1);
                    v___y_2154_ = v_a_2162_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc_ref(v_tm_2151_);
                lean_inc_ref(v___y_2154_);
                v___f_2155_ = lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___boxed as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___f_2155_, 0, v___y_2154_);
                lean_closure_set(v___f_2155_, 1, v_tm_2151_);
                v___x_2156_ = lean_mk_thunk(v___f_2155_);
                v___x_2157_ = lean_alloc_ctor(0, 4, (0) as u32);
                lean_ctor_set(v___x_2157_, 0, v___x_2156_);
                lean_ctor_set(v___x_2157_, 1, v_tm_2151_);
                lean_ctor_set(v___x_2157_, 2, v_rules_2152_);
                lean_ctor_set(v___x_2157_, 3, v___y_2154_);
                return v___x_2157_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__0(
    mut v_pdt_2163_: *mut LeanObject,
    mut v_x_2164_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc_ref(v_pdt_2163_);
    return v_pdt_2163_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__0___boxed(
    mut v_pdt_2165_: *mut LeanObject,
    mut v_x_2166_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2167_: *mut LeanObject = core::ptr::null_mut();
    v_res_2167_ = l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__0(v_pdt_2165_, v_x_2166_);
    lean_dec_ref(v_pdt_2165_);
    return v_res_2167_;
}
pub unsafe fn _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0() -> *mut LeanObject {
    let mut v___x_2168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: *mut LeanObject = core::ptr::null_mut();
    v___x_2168_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once),
        _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0,
    );
    v___x_2169_ = lean_int_neg(v___x_2168_);
    return v___x_2169_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_ofPlainDateTime(
    mut v_pdt_2170_: *mut LeanObject,
    mut v_zr_2171_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_wt_2172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ltt_2173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tz_2174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_offset_2175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_2176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_2177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_pdt_2170_);
    v_wt_2172_ = l_Std_Time_PlainDateTime_toWallTime(v_pdt_2170_);
    lean_inc_ref(v_zr_2171_);
    v_ltt_2173_ =
        l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_zr_2171_, v_wt_2172_);
    v_tz_2174_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_2173_);
    lean_dec_ref(v_ltt_2173_);
    v_offset_2175_ = lean_ctor_get(v_tz_2174_, 0);
    lean_inc(v_offset_2175_);
    v_second_2176_ = lean_ctor_get(v_wt_2172_, 0);
    lean_inc(v_second_2176_);
    v_nano_2177_ = lean_ctor_get(v_wt_2172_, 1);
    lean_inc(v_nano_2177_);
    lean_dec_ref(v_wt_2172_);
    v___f_2178_ = lean_alloc_closure(
        l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2178_, 0, v_pdt_2170_);
    v___x_2179_ = lean_mk_thunk(v___f_2178_);
    v___x_2180_ = lean_int_neg(v_offset_2175_);
    lean_dec(v_offset_2175_);
    v___x_2181_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once),
        _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
    );
    v___x_2182_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once),
        _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
    );
    v___x_2183_ = lean_int_mul(v_second_2176_, v___x_2182_);
    lean_dec(v_second_2176_);
    v___x_2184_ = lean_int_add(v___x_2183_, v_nano_2177_);
    lean_dec(v_nano_2177_);
    lean_dec(v___x_2183_);
    v___x_2185_ = lean_int_mul(v___x_2180_, v___x_2182_);
    lean_dec(v___x_2180_);
    v___x_2186_ = lean_int_add(v___x_2185_, v___x_2181_);
    lean_dec(v___x_2185_);
    v___x_2187_ = lean_int_add(v___x_2184_, v___x_2186_);
    lean_dec(v___x_2186_);
    lean_dec(v___x_2184_);
    v___x_2188_ = l_Std_Time_Duration_ofNanoseconds(v___x_2187_);
    lean_dec(v___x_2187_);
    v___x_2189_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_2189_, 0, v___x_2179_);
    lean_ctor_set(v___x_2189_, 1, v___x_2188_);
    lean_ctor_set(v___x_2189_, 2, v_zr_2171_);
    lean_ctor_set(v___x_2189_, 3, v_tz_2174_);
    return v___x_2189_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_ofTimestampWithZone___lam__0(
    mut v___y_2190_: *mut LeanObject,
    mut v_tm_2191_: *mut LeanObject,
    mut v___x_2192_: *mut LeanObject,
    mut v_x_2193_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_offset_2194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_2195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_2196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut LeanObject = core::ptr::null_mut();
    v_offset_2194_ = lean_ctor_get(v___y_2190_, 0);
    v_second_2195_ = lean_ctor_get(v_tm_2191_, 0);
    v_nano_2196_ = lean_ctor_get(v_tm_2191_, 1);
    v___x_2197_ = lean_nat_to_int(v___x_2192_);
    v___x_2198_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once),
        _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
    );
    v___x_2199_ = lean_int_mul(v_second_2195_, v___x_2198_);
    v___x_2200_ = lean_int_add(v___x_2199_, v_nano_2196_);
    lean_dec(v___x_2199_);
    v___x_2201_ = lean_int_mul(v_offset_2194_, v___x_2198_);
    v___x_2202_ = lean_int_add(v___x_2201_, v___x_2197_);
    lean_dec(v___x_2197_);
    lean_dec(v___x_2201_);
    v___x_2203_ = lean_int_add(v___x_2200_, v___x_2202_);
    lean_dec(v___x_2202_);
    lean_dec(v___x_2200_);
    v___x_2204_ = l_Std_Time_Duration_ofNanoseconds(v___x_2203_);
    lean_dec(v___x_2203_);
    v___x_2205_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_2204_);
    return v___x_2205_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_ofTimestampWithZone___lam__0___boxed(
    mut v___y_2206_: *mut LeanObject,
    mut v_tm_2207_: *mut LeanObject,
    mut v___x_2208_: *mut LeanObject,
    mut v_x_2209_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2210_: *mut LeanObject = core::ptr::null_mut();
    v_res_2210_ = l_Std_Time_ZonedDateTime_ofTimestampWithZone___lam__0(
        v___y_2206_,
        v_tm_2207_,
        v___x_2208_,
        v_x_2209_,
    );
    lean_dec_ref(v_tm_2207_);
    lean_dec_ref(v___y_2206_);
    return v_res_2210_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_ofTimestampWithZone(
    mut v_tm_2213_: *mut LeanObject,
    mut v_tz_2214_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_offset_2215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_2216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_abbreviation_2217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isDST_2218_: u8 = 0;
    let mut v___x_2219_: u8 = 0;
    let mut v___x_2220_: u8 = 0;
    let mut v_ltt_2221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2232_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_offset_2215_ = lean_ctor_get(v_tz_2214_, 0);
                v_name_2216_ = lean_ctor_get(v_tz_2214_, 1);
                v_abbreviation_2217_ = lean_ctor_get(v_tz_2214_, 2);
                v_isDST_2218_ = lean_ctor_get_uint8(
                    v_tz_2214_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v___x_2219_ = 0;
                v___x_2220_ = 1;
                lean_inc_ref(v_name_2216_);
                lean_inc_ref(v_abbreviation_2217_);
                lean_inc(v_offset_2215_);
                v_ltt_2221_ = lean_alloc_ctor(0, 3, (3) as u32);
                lean_ctor_set(v_ltt_2221_, 0, v_offset_2215_);
                lean_ctor_set(v_ltt_2221_, 1, v_abbreviation_2217_);
                lean_ctor_set(v_ltt_2221_, 2, v_name_2216_);
                lean_ctor_set_uint8(
                    v_ltt_2221_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v_isDST_2218_,
                );
                lean_ctor_set_uint8(
                    v_ltt_2221_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                    v___x_2219_,
                );
                lean_ctor_set_uint8(
                    v_ltt_2221_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                    v___x_2220_,
                );
                v___x_2222_ = lean_unsigned_to_nat(0);
                v___x_2223_ = l_Std_Time_ZonedDateTime_ofTimestampWithZone___closed__0;
                lean_inc_ref(v_ltt_2221_);
                v___x_2224_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2224_, 0, v_ltt_2221_);
                lean_ctor_set(v___x_2224_, 1, v___x_2223_);
                v___x_2230_ = l_Std_Time_TimeZone_Transition_timezoneAt(v___x_2223_, v_tm_2213_);
                if lean_obj_tag(v___x_2230_) == 0 {
                    lean_dec_ref_known(v___x_2230_, 1);
                    v___x_2231_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_2221_);
                    lean_dec_ref_known(v_ltt_2221_, 3);
                    v___y_2226_ = v___x_2231_;
                    state = 1;
                    continue;
                } else {
                    lean_dec_ref_known(v_ltt_2221_, 3);
                    v_a_2232_ = lean_ctor_get(v___x_2230_, 0);
                    lean_inc(v_a_2232_);
                    lean_dec_ref_known(v___x_2230_, 1);
                    v___y_2226_ = v_a_2232_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc_ref(v_tm_2213_);
                lean_inc_ref(v___y_2226_);
                v___f_2227_ = lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_ofTimestampWithZone___lam__0___boxed
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                lean_closure_set(v___f_2227_, 0, v___y_2226_);
                lean_closure_set(v___f_2227_, 1, v_tm_2213_);
                lean_closure_set(v___f_2227_, 2, v___x_2222_);
                v___x_2228_ = lean_mk_thunk(v___f_2227_);
                v___x_2229_ = lean_alloc_ctor(0, 4, (0) as u32);
                lean_ctor_set(v___x_2229_, 0, v___x_2228_);
                lean_ctor_set(v___x_2229_, 1, v_tm_2213_);
                lean_ctor_set(v___x_2229_, 2, v___x_2224_);
                lean_ctor_set(v___x_2229_, 3, v___y_2226_);
                return v___x_2229_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_ZonedDateTime_ofTimestampWithZone___boxed(
    mut v_tm_2233_: *mut LeanObject,
    mut v_tz_2234_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2235_: *mut LeanObject = core::ptr::null_mut();
    v_res_2235_ = l_Std_Time_ZonedDateTime_ofTimestampWithZone(v_tm_2233_, v_tz_2234_);
    lean_dec_ref(v_tz_2234_);
    return v_res_2235_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone___lam__0(
    mut v_tm_2236_: *mut LeanObject,
    mut v_x_2237_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc_ref(v_tm_2236_);
    return v_tm_2236_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone___lam__0___boxed(
    mut v_tm_2238_: *mut LeanObject,
    mut v_x_2239_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2240_: *mut LeanObject = core::ptr::null_mut();
    v_res_2240_ = l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone___lam__0(v_tm_2238_, v_x_2239_);
    lean_dec_ref(v_tm_2238_);
    return v_res_2240_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone(
    mut v_tm_2241_: *mut LeanObject,
    mut v_tz_2242_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_offset_2243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_2244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_abbreviation_2245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isDST_2246_: u8 = 0;
    let mut v___x_2247_: u8 = 0;
    let mut v___x_2248_: u8 = 0;
    let mut v_ltt_2249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_wt_2252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ltt_2253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tz_2254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_offset_2255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_2256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_2257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut LeanObject = core::ptr::null_mut();
    v_offset_2243_ = lean_ctor_get(v_tz_2242_, 0);
    v_name_2244_ = lean_ctor_get(v_tz_2242_, 1);
    v_abbreviation_2245_ = lean_ctor_get(v_tz_2242_, 2);
    v_isDST_2246_ = lean_ctor_get_uint8(
        v_tz_2242_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
    );
    v___x_2247_ = 0;
    v___x_2248_ = 1;
    lean_inc_ref(v_name_2244_);
    lean_inc_ref(v_abbreviation_2245_);
    lean_inc(v_offset_2243_);
    v_ltt_2249_ = lean_alloc_ctor(0, 3, (3) as u32);
    lean_ctor_set(v_ltt_2249_, 0, v_offset_2243_);
    lean_ctor_set(v_ltt_2249_, 1, v_abbreviation_2245_);
    lean_ctor_set(v_ltt_2249_, 2, v_name_2244_);
    lean_ctor_set_uint8(
        v_ltt_2249_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
        v_isDST_2246_,
    );
    lean_ctor_set_uint8(
        v_ltt_2249_,
        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
        v___x_2247_,
    );
    lean_ctor_set_uint8(
        v_ltt_2249_,
        (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
        v___x_2248_,
    );
    v___x_2250_ = l_Std_Time_ZonedDateTime_ofTimestampWithZone___closed__0;
    v___x_2251_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2251_, 0, v_ltt_2249_);
    lean_ctor_set(v___x_2251_, 1, v___x_2250_);
    lean_inc_ref(v_tm_2241_);
    v_wt_2252_ = l_Std_Time_PlainDateTime_toWallTime(v_tm_2241_);
    lean_inc_ref(v___x_2251_);
    v_ltt_2253_ =
        l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v___x_2251_, v_wt_2252_);
    v_tz_2254_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_2253_);
    lean_dec_ref(v_ltt_2253_);
    v_offset_2255_ = lean_ctor_get(v_tz_2254_, 0);
    lean_inc(v_offset_2255_);
    v_second_2256_ = lean_ctor_get(v_wt_2252_, 0);
    lean_inc(v_second_2256_);
    v_nano_2257_ = lean_ctor_get(v_wt_2252_, 1);
    lean_inc(v_nano_2257_);
    lean_dec_ref(v_wt_2252_);
    v___f_2258_ = lean_alloc_closure(
        l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2258_, 0, v_tm_2241_);
    v___x_2259_ = lean_mk_thunk(v___f_2258_);
    v___x_2260_ = lean_int_neg(v_offset_2255_);
    lean_dec(v_offset_2255_);
    v___x_2261_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once),
        _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
    );
    v___x_2262_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once),
        _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
    );
    v___x_2263_ = lean_int_mul(v_second_2256_, v___x_2262_);
    lean_dec(v_second_2256_);
    v___x_2264_ = lean_int_add(v___x_2263_, v_nano_2257_);
    lean_dec(v_nano_2257_);
    lean_dec(v___x_2263_);
    v___x_2265_ = lean_int_mul(v___x_2260_, v___x_2262_);
    lean_dec(v___x_2260_);
    v___x_2266_ = lean_int_add(v___x_2265_, v___x_2261_);
    lean_dec(v___x_2265_);
    v___x_2267_ = lean_int_add(v___x_2264_, v___x_2266_);
    lean_dec(v___x_2266_);
    lean_dec(v___x_2264_);
    v___x_2268_ = l_Std_Time_Duration_ofNanoseconds(v___x_2267_);
    lean_dec(v___x_2267_);
    v___x_2269_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_2269_, 0, v___x_2259_);
    lean_ctor_set(v___x_2269_, 1, v___x_2268_);
    lean_ctor_set(v___x_2269_, 2, v___x_2251_);
    lean_ctor_set(v___x_2269_, 3, v_tz_2254_);
    return v___x_2269_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone___boxed(
    mut v_tm_2270_: *mut LeanObject,
    mut v_tz_2271_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2272_: *mut LeanObject = core::ptr::null_mut();
    v_res_2272_ = l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone(v_tm_2270_, v_tz_2271_);
    lean_dec_ref(v_tz_2271_);
    return v_res_2272_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_toTimestamp(
    mut v_date_2273_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_timestamp_2274_: *mut LeanObject = core::ptr::null_mut();
    v_timestamp_2274_ = lean_ctor_get(v_date_2273_, 1);
    lean_inc_ref(v_timestamp_2274_);
    return v_timestamp_2274_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_toTimestamp___boxed(
    mut v_date_2275_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2276_: *mut LeanObject = core::ptr::null_mut();
    v_res_2276_ = l_Std_Time_ZonedDateTime_toTimestamp(v_date_2275_);
    lean_dec_ref(v_date_2275_);
    return v_res_2276_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_convertZoneRules___lam__0(
    mut v___y_2277_: *mut LeanObject,
    mut v_timestamp_2278_: *mut LeanObject,
    mut v_x_2279_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_offset_2280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_2281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_2282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut LeanObject = core::ptr::null_mut();
    v_offset_2280_ = lean_ctor_get(v___y_2277_, 0);
    v_second_2281_ = lean_ctor_get(v_timestamp_2278_, 0);
    v_nano_2282_ = lean_ctor_get(v_timestamp_2278_, 1);
    v___x_2283_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once),
        _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0,
    );
    v___x_2284_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once),
        _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
    );
    v___x_2285_ = lean_int_mul(v_second_2281_, v___x_2284_);
    v___x_2286_ = lean_int_add(v___x_2285_, v_nano_2282_);
    lean_dec(v___x_2285_);
    v___x_2287_ = lean_int_mul(v_offset_2280_, v___x_2284_);
    v___x_2288_ = lean_int_add(v___x_2287_, v___x_2283_);
    lean_dec(v___x_2287_);
    v___x_2289_ = lean_int_add(v___x_2286_, v___x_2288_);
    lean_dec(v___x_2288_);
    lean_dec(v___x_2286_);
    v___x_2290_ = l_Std_Time_Duration_ofNanoseconds(v___x_2289_);
    lean_dec(v___x_2289_);
    v___x_2291_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_2290_);
    return v___x_2291_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_convertZoneRules___lam__0___boxed(
    mut v___y_2292_: *mut LeanObject,
    mut v_timestamp_2293_: *mut LeanObject,
    mut v_x_2294_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2295_: *mut LeanObject = core::ptr::null_mut();
    v_res_2295_ = l_Std_Time_ZonedDateTime_convertZoneRules___lam__0(
        v___y_2292_,
        v_timestamp_2293_,
        v_x_2294_,
    );
    lean_dec_ref(v_timestamp_2293_);
    lean_dec_ref(v___y_2292_);
    return v_res_2295_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_convertZoneRules(
    mut v_date_2296_: *mut LeanObject,
    mut v_tz_u2081_2297_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_timestamp_2298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2301_: u8 = 0;
    let mut v___y_2303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initialLocalTimeType_2309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_transitions_2310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2314_: u8 = 0;
    let mut v_unused_2315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2317_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_2298_ = lean_ctor_get(v_date_2296_, 1);
                v_isSharedCheck_2314_ = (!lean_is_exclusive(v_date_2296_)) as u8;
                if v_isSharedCheck_2314_ == 0 {
                    v_unused_2315_ = lean_ctor_get(v_date_2296_, 3);
                    lean_dec(v_unused_2315_);
                    v_unused_2316_ = lean_ctor_get(v_date_2296_, 2);
                    lean_dec(v_unused_2316_);
                    v_unused_2317_ = lean_ctor_get(v_date_2296_, 0);
                    lean_dec(v_unused_2317_);
                    v___x_2300_ = v_date_2296_;
                    v_isShared_2301_ = v_isSharedCheck_2314_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_timestamp_2298_);
                    lean_dec(v_date_2296_);
                    v___x_2300_ = lean_box(0);
                    v_isShared_2301_ = v_isSharedCheck_2314_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_initialLocalTimeType_2309_ = lean_ctor_get(v_tz_u2081_2297_, 0);
                v_transitions_2310_ = lean_ctor_get(v_tz_u2081_2297_, 1);
                v___x_2311_ = l_Std_Time_TimeZone_Transition_timezoneAt(
                    v_transitions_2310_,
                    v_timestamp_2298_,
                );
                if lean_obj_tag(v___x_2311_) == 0 {
                    lean_dec_ref_known(v___x_2311_, 1);
                    v___x_2312_ =
                        l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_2309_);
                    v___y_2303_ = v___x_2312_;
                    state = 2;
                    continue;
                } else {
                    v_a_2313_ = lean_ctor_get(v___x_2311_, 0);
                    lean_inc(v_a_2313_);
                    lean_dec_ref_known(v___x_2311_, 1);
                    v___y_2303_ = v_a_2313_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc_ref(v_timestamp_2298_);
                lean_inc_ref(v___y_2303_);
                v___f_2304_ = lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_convertZoneRules___lam__0___boxed
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___f_2304_, 0, v___y_2303_);
                lean_closure_set(v___f_2304_, 1, v_timestamp_2298_);
                v___x_2305_ = lean_mk_thunk(v___f_2304_);
                if v_isShared_2301_ == 0 {
                    lean_ctor_set(v___x_2300_, 3, v___y_2303_);
                    lean_ctor_set(v___x_2300_, 2, v_tz_u2081_2297_);
                    lean_ctor_set(v___x_2300_, 0, v___x_2305_);
                    v___x_2307_ = v___x_2300_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2308_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2308_, 0, v___x_2305_);
                    lean_ctor_set(v_reuseFailAlloc_2308_, 1, v_timestamp_2298_);
                    lean_ctor_set(v_reuseFailAlloc_2308_, 2, v_tz_u2081_2297_);
                    lean_ctor_set(v_reuseFailAlloc_2308_, 3, v___y_2303_);
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
    mut v_dt_2318_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_2319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: *mut LeanObject = core::ptr::null_mut();
    v_date_2319_ = lean_ctor_get(v_dt_2318_, 0);
    v___x_2320_ = lean_thunk_get_own(v_date_2319_);
    return v___x_2320_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_toPlainDateTime___boxed(
    mut v_dt_2321_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2322_: *mut LeanObject = core::ptr::null_mut();
    v_res_2322_ = l_Std_Time_ZonedDateTime_toPlainDateTime(v_dt_2321_);
    lean_dec_ref(v_dt_2321_);
    return v_res_2322_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_toDateTime___lam__0(
    mut v_timezone_2323_: *mut LeanObject,
    mut v_timestamp_2324_: *mut LeanObject,
    mut v_x_2325_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_offset_2326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_2327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_2328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: *mut LeanObject = core::ptr::null_mut();
    v_offset_2326_ = lean_ctor_get(v_timezone_2323_, 0);
    v_second_2327_ = lean_ctor_get(v_timestamp_2324_, 0);
    v_nano_2328_ = lean_ctor_get(v_timestamp_2324_, 1);
    v___x_2329_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once),
        _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0,
    );
    v___x_2330_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once),
        _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
    );
    v___x_2331_ = lean_int_mul(v_second_2327_, v___x_2330_);
    v___x_2332_ = lean_int_add(v___x_2331_, v_nano_2328_);
    lean_dec(v___x_2331_);
    v___x_2333_ = lean_int_mul(v_offset_2326_, v___x_2330_);
    v___x_2334_ = lean_int_add(v___x_2333_, v___x_2329_);
    lean_dec(v___x_2333_);
    v___x_2335_ = lean_int_add(v___x_2332_, v___x_2334_);
    lean_dec(v___x_2334_);
    lean_dec(v___x_2332_);
    v___x_2336_ = l_Std_Time_Duration_ofNanoseconds(v___x_2335_);
    lean_dec(v___x_2335_);
    v___x_2337_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_2336_);
    return v___x_2337_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_toDateTime___lam__0___boxed(
    mut v_timezone_2338_: *mut LeanObject,
    mut v_timestamp_2339_: *mut LeanObject,
    mut v_x_2340_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2341_: *mut LeanObject = core::ptr::null_mut();
    v_res_2341_ = l_Std_Time_ZonedDateTime_toDateTime___lam__0(
        v_timezone_2338_,
        v_timestamp_2339_,
        v_x_2340_,
    );
    lean_dec_ref(v_timestamp_2339_);
    lean_dec_ref(v_timezone_2338_);
    return v_res_2341_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_toDateTime(
    mut v_dt_2342_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_timestamp_2343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_timezone_2344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut LeanObject = core::ptr::null_mut();
    v_timestamp_2343_ = lean_ctor_get(v_dt_2342_, 1);
    lean_inc_ref_n(v_timestamp_2343_, 2);
    v_timezone_2344_ = lean_ctor_get(v_dt_2342_, 3);
    lean_inc_ref(v_timezone_2344_);
    lean_dec_ref(v_dt_2342_);
    v___f_2345_ = lean_alloc_closure(
        l_Std_Time_ZonedDateTime_toDateTime___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2345_, 0, v_timezone_2344_);
    lean_closure_set(v___f_2345_, 1, v_timestamp_2343_);
    v___x_2346_ = lean_mk_thunk(v___f_2345_);
    v___x_2347_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2347_, 0, v_timestamp_2343_);
    lean_ctor_set(v___x_2347_, 1, v___x_2346_);
    return v___x_2347_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_time(mut v_zdt_2348_: *mut LeanObject) -> *mut LeanObject {
    let mut v_date_2349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_time_2351_: *mut LeanObject = core::ptr::null_mut();
    v_date_2349_ = lean_ctor_get(v_zdt_2348_, 0);
    v___x_2350_ = lean_thunk_get_own(v_date_2349_);
    v_time_2351_ = lean_ctor_get(v___x_2350_, 1);
    lean_inc_ref(v_time_2351_);
    lean_dec(v___x_2350_);
    return v_time_2351_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_time___boxed(
    mut v_zdt_2352_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2353_: *mut LeanObject = core::ptr::null_mut();
    v_res_2353_ = l_Std_Time_ZonedDateTime_time(v_zdt_2352_);
    lean_dec_ref(v_zdt_2352_);
    return v_res_2353_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_year(mut v_zdt_2354_: *mut LeanObject) -> *mut LeanObject {
    let mut v_date_2355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_date_2357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_year_2358_: *mut LeanObject = core::ptr::null_mut();
    v_date_2355_ = lean_ctor_get(v_zdt_2354_, 0);
    v___x_2356_ = lean_thunk_get_own(v_date_2355_);
    v_date_2357_ = lean_ctor_get(v___x_2356_, 0);
    lean_inc_ref(v_date_2357_);
    lean_dec(v___x_2356_);
    v_year_2358_ = lean_ctor_get(v_date_2357_, 0);
    lean_inc(v_year_2358_);
    lean_dec_ref(v_date_2357_);
    return v_year_2358_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_year___boxed(
    mut v_zdt_2359_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2360_: *mut LeanObject = core::ptr::null_mut();
    v_res_2360_ = l_Std_Time_ZonedDateTime_year(v_zdt_2359_);
    lean_dec_ref(v_zdt_2359_);
    return v_res_2360_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_month(mut v_zdt_2361_: *mut LeanObject) -> *mut LeanObject {
    let mut v_date_2362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_date_2364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_month_2365_: *mut LeanObject = core::ptr::null_mut();
    v_date_2362_ = lean_ctor_get(v_zdt_2361_, 0);
    v___x_2363_ = lean_thunk_get_own(v_date_2362_);
    v_date_2364_ = lean_ctor_get(v___x_2363_, 0);
    lean_inc_ref(v_date_2364_);
    lean_dec(v___x_2363_);
    v_month_2365_ = lean_ctor_get(v_date_2364_, 1);
    lean_inc(v_month_2365_);
    lean_dec_ref(v_date_2364_);
    return v_month_2365_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_month___boxed(
    mut v_zdt_2366_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2367_: *mut LeanObject = core::ptr::null_mut();
    v_res_2367_ = l_Std_Time_ZonedDateTime_month(v_zdt_2366_);
    lean_dec_ref(v_zdt_2366_);
    return v_res_2367_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_day(mut v_zdt_2368_: *mut LeanObject) -> *mut LeanObject {
    let mut v_date_2369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_date_2371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_day_2372_: *mut LeanObject = core::ptr::null_mut();
    v_date_2369_ = lean_ctor_get(v_zdt_2368_, 0);
    v___x_2370_ = lean_thunk_get_own(v_date_2369_);
    v_date_2371_ = lean_ctor_get(v___x_2370_, 0);
    lean_inc_ref(v_date_2371_);
    lean_dec(v___x_2370_);
    v_day_2372_ = lean_ctor_get(v_date_2371_, 2);
    lean_inc(v_day_2372_);
    lean_dec_ref(v_date_2371_);
    return v_day_2372_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_day___boxed(
    mut v_zdt_2373_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2374_: *mut LeanObject = core::ptr::null_mut();
    v_res_2374_ = l_Std_Time_ZonedDateTime_day(v_zdt_2373_);
    lean_dec_ref(v_zdt_2373_);
    return v_res_2374_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_hour(mut v_zdt_2375_: *mut LeanObject) -> *mut LeanObject {
    let mut v_date_2376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_time_2378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hour_2379_: *mut LeanObject = core::ptr::null_mut();
    v_date_2376_ = lean_ctor_get(v_zdt_2375_, 0);
    v___x_2377_ = lean_thunk_get_own(v_date_2376_);
    v_time_2378_ = lean_ctor_get(v___x_2377_, 1);
    lean_inc_ref(v_time_2378_);
    lean_dec(v___x_2377_);
    v_hour_2379_ = lean_ctor_get(v_time_2378_, 0);
    lean_inc(v_hour_2379_);
    lean_dec_ref(v_time_2378_);
    return v_hour_2379_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_hour___boxed(
    mut v_zdt_2380_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2381_: *mut LeanObject = core::ptr::null_mut();
    v_res_2381_ = l_Std_Time_ZonedDateTime_hour(v_zdt_2380_);
    lean_dec_ref(v_zdt_2380_);
    return v_res_2381_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_minute(mut v_zdt_2382_: *mut LeanObject) -> *mut LeanObject {
    let mut v_date_2383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_time_2385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_minute_2386_: *mut LeanObject = core::ptr::null_mut();
    v_date_2383_ = lean_ctor_get(v_zdt_2382_, 0);
    v___x_2384_ = lean_thunk_get_own(v_date_2383_);
    v_time_2385_ = lean_ctor_get(v___x_2384_, 1);
    lean_inc_ref(v_time_2385_);
    lean_dec(v___x_2384_);
    v_minute_2386_ = lean_ctor_get(v_time_2385_, 1);
    lean_inc(v_minute_2386_);
    lean_dec_ref(v_time_2385_);
    return v_minute_2386_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_minute___boxed(
    mut v_zdt_2387_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2388_: *mut LeanObject = core::ptr::null_mut();
    v_res_2388_ = l_Std_Time_ZonedDateTime_minute(v_zdt_2387_);
    lean_dec_ref(v_zdt_2387_);
    return v_res_2388_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_second(mut v_zdt_2389_: *mut LeanObject) -> *mut LeanObject {
    let mut v_date_2390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_time_2392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_2393_: *mut LeanObject = core::ptr::null_mut();
    v_date_2390_ = lean_ctor_get(v_zdt_2389_, 0);
    v___x_2391_ = lean_thunk_get_own(v_date_2390_);
    v_time_2392_ = lean_ctor_get(v___x_2391_, 1);
    lean_inc_ref(v_time_2392_);
    lean_dec(v___x_2391_);
    v_second_2393_ = lean_ctor_get(v_time_2392_, 2);
    lean_inc(v_second_2393_);
    lean_dec_ref(v_time_2392_);
    return v_second_2393_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_second___boxed(
    mut v_zdt_2394_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2395_: *mut LeanObject = core::ptr::null_mut();
    v_res_2395_ = l_Std_Time_ZonedDateTime_second(v_zdt_2394_);
    lean_dec_ref(v_zdt_2394_);
    return v_res_2395_;
}
pub unsafe fn _init_l_Std_Time_ZonedDateTime_millisecond___closed__0() -> *mut LeanObject {
    let mut v___x_2396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: *mut LeanObject = core::ptr::null_mut();
    v___x_2396_ = lean_unsigned_to_nat(1000000);
    v___x_2397_ = lean_nat_to_int(v___x_2396_);
    return v___x_2397_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_millisecond(
    mut v_dt_2398_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_2399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_time_2401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_2402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2404_: *mut LeanObject = core::ptr::null_mut();
    v_date_2399_ = lean_ctor_get(v_dt_2398_, 0);
    v___x_2400_ = lean_thunk_get_own(v_date_2399_);
    v_time_2401_ = lean_ctor_get(v___x_2400_, 1);
    lean_inc_ref(v_time_2401_);
    lean_dec(v___x_2400_);
    v_nanosecond_2402_ = lean_ctor_get(v_time_2401_, 3);
    lean_inc(v_nanosecond_2402_);
    lean_dec_ref(v_time_2401_);
    v___x_2403_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_millisecond___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_millisecond___closed__0_once),
        _init_l_Std_Time_ZonedDateTime_millisecond___closed__0,
    );
    v___x_2404_ = lean_int_ediv(v_nanosecond_2402_, v___x_2403_);
    lean_dec(v_nanosecond_2402_);
    return v___x_2404_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_millisecond___boxed(
    mut v_dt_2405_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2406_: *mut LeanObject = core::ptr::null_mut();
    v_res_2406_ = l_Std_Time_ZonedDateTime_millisecond(v_dt_2405_);
    lean_dec_ref(v_dt_2405_);
    return v_res_2406_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_nanosecond(
    mut v_zdt_2407_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_2408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_time_2410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_2411_: *mut LeanObject = core::ptr::null_mut();
    v_date_2408_ = lean_ctor_get(v_zdt_2407_, 0);
    v___x_2409_ = lean_thunk_get_own(v_date_2408_);
    v_time_2410_ = lean_ctor_get(v___x_2409_, 1);
    lean_inc_ref(v_time_2410_);
    lean_dec(v___x_2409_);
    v_nanosecond_2411_ = lean_ctor_get(v_time_2410_, 3);
    lean_inc(v_nanosecond_2411_);
    lean_dec_ref(v_time_2410_);
    return v_nanosecond_2411_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_nanosecond___boxed(
    mut v_zdt_2412_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2413_: *mut LeanObject = core::ptr::null_mut();
    v_res_2413_ = l_Std_Time_ZonedDateTime_nanosecond(v_zdt_2412_);
    lean_dec_ref(v_zdt_2412_);
    return v_res_2413_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_offset(mut v_zdt_2414_: *mut LeanObject) -> *mut LeanObject {
    let mut v_timezone_2415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_offset_2416_: *mut LeanObject = core::ptr::null_mut();
    v_timezone_2415_ = lean_ctor_get(v_zdt_2414_, 3);
    v_offset_2416_ = lean_ctor_get(v_timezone_2415_, 0);
    lean_inc(v_offset_2416_);
    return v_offset_2416_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_offset___boxed(
    mut v_zdt_2417_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2418_: *mut LeanObject = core::ptr::null_mut();
    v_res_2418_ = l_Std_Time_ZonedDateTime_offset(v_zdt_2417_);
    lean_dec_ref(v_zdt_2417_);
    return v_res_2418_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_weekday(mut v_zdt_2419_: *mut LeanObject) -> u8 {
    let mut v_date_2420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_date_2422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2423_: u8 = 0;
    v_date_2420_ = lean_ctor_get(v_zdt_2419_, 0);
    v___x_2421_ = lean_thunk_get_own(v_date_2420_);
    v_date_2422_ = lean_ctor_get(v___x_2421_, 0);
    lean_inc_ref(v_date_2422_);
    lean_dec(v___x_2421_);
    v___x_2423_ = l_Std_Time_PlainDate_weekday(v_date_2422_);
    return v___x_2423_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_weekday___boxed(
    mut v_zdt_2424_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2425_: u8 = 0;
    let mut v_r_2426_: *mut LeanObject = core::ptr::null_mut();
    v_res_2425_ = l_Std_Time_ZonedDateTime_weekday(v_zdt_2424_);
    lean_dec_ref(v_zdt_2424_);
    v_r_2426_ = lean_box((v_res_2425_) as usize);
    return v_r_2426_;
}
pub unsafe fn _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__0() -> *mut LeanObject {
    let mut v___x_2427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2428_: *mut LeanObject = core::ptr::null_mut();
    v___x_2427_ = lean_unsigned_to_nat(4);
    v___x_2428_ = lean_nat_to_int(v___x_2427_);
    return v___x_2428_;
}
pub unsafe fn _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__1() -> *mut LeanObject {
    let mut v___x_2429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut LeanObject = core::ptr::null_mut();
    v___x_2429_ = lean_unsigned_to_nat(400);
    v___x_2430_ = lean_nat_to_int(v___x_2429_);
    return v___x_2430_;
}
pub unsafe fn _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__2() -> *mut LeanObject {
    let mut v___x_2431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: *mut LeanObject = core::ptr::null_mut();
    v___x_2431_ = lean_unsigned_to_nat(100);
    v___x_2432_ = lean_nat_to_int(v___x_2431_);
    return v___x_2432_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_dayOfYear(
    mut v_date_2433_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_2434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2436_: u8 = 0;
    let mut v___x_2437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_date_2438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2441_: u8 = 0;
    let mut v_month_2442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_day_2443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2448_: u8 = 0;
    let mut v_unused_2449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_date_2451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_year_2452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: u8 = 0;
    let mut v___x_2460_: u8 = 0;
    let mut v___x_2461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_2434_ = lean_ctor_get(v_date_2433_, 0);
                v___x_2450_ = lean_thunk_get_own(v_date_2434_);
                v_date_2451_ = lean_ctor_get(v___x_2450_, 0);
                lean_inc_ref(v_date_2451_);
                lean_dec(v___x_2450_);
                v_year_2452_ = lean_ctor_get(v_date_2451_, 0);
                lean_inc(v_year_2452_);
                lean_dec_ref(v_date_2451_);
                v___x_2453_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_dayOfYear___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_dayOfYear___closed__0_once),
                    _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__0,
                );
                v___x_2454_ = lean_int_mod(v_year_2452_, v___x_2453_);
                v___x_2455_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0,
                );
                v___x_2460_ = lean_int_dec_eq(v___x_2454_, v___x_2455_);
                lean_dec(v___x_2454_);
                if v___x_2460_ == 0 {
                    lean_dec(v_year_2452_);
                    v___y_2436_ = v___x_2460_;
                    state = 1;
                    continue;
                } else {
                    v___x_2461_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_dayOfYear___closed__2),
                        core::ptr::addr_of_mut!(
                            l_Std_Time_ZonedDateTime_dayOfYear___closed__2_once
                        ),
                        _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__2,
                    );
                    v___x_2462_ = lean_int_mod(v_year_2452_, v___x_2461_);
                    v___x_2463_ = lean_int_dec_eq(v___x_2462_, v___x_2455_);
                    lean_dec(v___x_2462_);
                    if v___x_2463_ == 0 {
                        if v___x_2460_ == 0 {
                            state = 4;
                            continue;
                        } else {
                            lean_dec(v_year_2452_);
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
                v_date_2438_ = lean_ctor_get(v___x_2437_, 0);
                v_isSharedCheck_2448_ = (!lean_is_exclusive(v___x_2437_)) as u8;
                if v_isSharedCheck_2448_ == 0 {
                    v_unused_2449_ = lean_ctor_get(v___x_2437_, 1);
                    lean_dec(v_unused_2449_);
                    v___x_2440_ = v___x_2437_;
                    v_isShared_2441_ = v_isSharedCheck_2448_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_date_2438_);
                    lean_dec(v___x_2437_);
                    v___x_2440_ = lean_box(0);
                    v_isShared_2441_ = v_isSharedCheck_2448_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_month_2442_ = lean_ctor_get(v_date_2438_, 1);
                lean_inc(v_month_2442_);
                v_day_2443_ = lean_ctor_get(v_date_2438_, 2);
                lean_inc(v_day_2443_);
                lean_dec_ref(v_date_2438_);
                if v_isShared_2441_ == 0 {
                    lean_ctor_set(v___x_2440_, 1, v_day_2443_);
                    lean_ctor_set(v___x_2440_, 0, v_month_2442_);
                    v___x_2445_ = v___x_2440_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2447_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2447_, 0, v_month_2442_);
                    lean_ctor_set(v_reuseFailAlloc_2447_, 1, v_day_2443_);
                    v___x_2445_ = v_reuseFailAlloc_2447_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2446_ = l_Std_Time_ValidDate_dayOfYear(v___y_2436_, v___x_2445_);
                lean_dec_ref(v___x_2445_);
                return v___x_2446_;
            }
            4 => {
                v___x_2457_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_dayOfYear___closed__1),
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_dayOfYear___closed__1_once),
                    _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__1,
                );
                v___x_2458_ = lean_int_mod(v_year_2452_, v___x_2457_);
                lean_dec(v_year_2452_);
                v___x_2459_ = lean_int_dec_eq(v___x_2458_, v___x_2455_);
                lean_dec(v___x_2458_);
                v___y_2436_ = v___x_2459_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_ZonedDateTime_dayOfYear___boxed(
    mut v_date_2464_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2465_: *mut LeanObject = core::ptr::null_mut();
    v_res_2465_ = l_Std_Time_ZonedDateTime_dayOfYear(v_date_2464_);
    lean_dec_ref(v_date_2464_);
    return v_res_2465_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_weekOfYear(
    mut v_date_2466_: *mut LeanObject,
    mut v_firstDay_2467_: u8,
) -> *mut LeanObject {
    let mut v_date_2468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_date_2470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: *mut LeanObject = core::ptr::null_mut();
    v_date_2468_ = lean_ctor_get(v_date_2466_, 0);
    v___x_2469_ = lean_thunk_get_own(v_date_2468_);
    v_date_2470_ = lean_ctor_get(v___x_2469_, 0);
    lean_inc_ref(v_date_2470_);
    lean_dec(v___x_2469_);
    v___x_2471_ = l_Std_Time_PlainDate_weekOfYear(v_date_2470_, v_firstDay_2467_);
    return v___x_2471_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_weekOfYear___boxed(
    mut v_date_2472_: *mut LeanObject,
    mut v_firstDay_2473_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_firstDay_boxed_2474_: u8 = 0;
    let mut v_res_2475_: *mut LeanObject = core::ptr::null_mut();
    v_firstDay_boxed_2474_ = (lean_unbox(v_firstDay_2473_) as u8);
    v_res_2475_ = l_Std_Time_ZonedDateTime_weekOfYear(v_date_2472_, v_firstDay_boxed_2474_);
    lean_dec_ref(v_date_2472_);
    return v_res_2475_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_weekYear(
    mut v_date_2476_: *mut LeanObject,
    mut v_firstDay_2477_: u8,
) -> *mut LeanObject {
    let mut v_date_2478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_date_2480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut LeanObject = core::ptr::null_mut();
    v_date_2478_ = lean_ctor_get(v_date_2476_, 0);
    v___x_2479_ = lean_thunk_get_own(v_date_2478_);
    v_date_2480_ = lean_ctor_get(v___x_2479_, 0);
    lean_inc_ref(v_date_2480_);
    lean_dec(v___x_2479_);
    v___x_2481_ = l_Std_Time_PlainDate_weekYear(v_date_2480_, v_firstDay_2477_);
    return v___x_2481_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_weekYear___boxed(
    mut v_date_2482_: *mut LeanObject,
    mut v_firstDay_2483_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_firstDay_boxed_2484_: u8 = 0;
    let mut v_res_2485_: *mut LeanObject = core::ptr::null_mut();
    v_firstDay_boxed_2484_ = (lean_unbox(v_firstDay_2483_) as u8);
    v_res_2485_ = l_Std_Time_ZonedDateTime_weekYear(v_date_2482_, v_firstDay_boxed_2484_);
    lean_dec_ref(v_date_2482_);
    return v_res_2485_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_weekOfMonth(
    mut v_date_2486_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_2487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2489_: *mut LeanObject = core::ptr::null_mut();
    v_date_2487_ = lean_ctor_get(v_date_2486_, 0);
    v___x_2488_ = lean_thunk_get_own(v_date_2487_);
    v___x_2489_ = l_Std_Time_PlainDateTime_weekOfMonth(v___x_2488_);
    lean_dec(v___x_2488_);
    return v___x_2489_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_weekOfMonth___boxed(
    mut v_date_2490_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2491_: *mut LeanObject = core::ptr::null_mut();
    v_res_2491_ = l_Std_Time_ZonedDateTime_weekOfMonth(v_date_2490_);
    lean_dec_ref(v_date_2490_);
    return v_res_2491_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_alignedWeekOfMonth(
    mut v_date_2492_: *mut LeanObject,
    mut v_firstDay_2493_: u8,
) -> *mut LeanObject {
    let mut v_date_2494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_date_2496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2497_: *mut LeanObject = core::ptr::null_mut();
    v_date_2494_ = lean_ctor_get(v_date_2492_, 0);
    v___x_2495_ = lean_thunk_get_own(v_date_2494_);
    v_date_2496_ = lean_ctor_get(v___x_2495_, 0);
    lean_inc_ref(v_date_2496_);
    lean_dec(v___x_2495_);
    v___x_2497_ = l_Std_Time_PlainDate_alignedWeekOfMonth(v_date_2496_, v_firstDay_2493_);
    return v___x_2497_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_alignedWeekOfMonth___boxed(
    mut v_date_2498_: *mut LeanObject,
    mut v_firstDay_2499_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_firstDay_boxed_2500_: u8 = 0;
    let mut v_res_2501_: *mut LeanObject = core::ptr::null_mut();
    v_firstDay_boxed_2500_ = (lean_unbox(v_firstDay_2499_) as u8);
    v_res_2501_ = l_Std_Time_ZonedDateTime_alignedWeekOfMonth(v_date_2498_, v_firstDay_boxed_2500_);
    lean_dec_ref(v_date_2498_);
    return v_res_2501_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_quarter(
    mut v_date_2502_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_2503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_date_2505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut LeanObject = core::ptr::null_mut();
    v_date_2503_ = lean_ctor_get(v_date_2502_, 0);
    v___x_2504_ = lean_thunk_get_own(v_date_2503_);
    v_date_2505_ = lean_ctor_get(v___x_2504_, 0);
    lean_inc_ref(v_date_2505_);
    lean_dec(v___x_2504_);
    v___x_2506_ = l_Std_Time_PlainDate_quarter(v_date_2505_);
    lean_dec_ref(v_date_2505_);
    return v___x_2506_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_quarter___boxed(
    mut v_date_2507_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2508_: *mut LeanObject = core::ptr::null_mut();
    v_res_2508_ = l_Std_Time_ZonedDateTime_quarter(v_date_2507_);
    lean_dec_ref(v_date_2507_);
    return v_res_2508_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_addDays___lam__0(
    mut v___y_2509_: *mut LeanObject,
    mut v___x_2510_: *mut LeanObject,
    mut v___x_2511_: *mut LeanObject,
    mut v___x_2512_: *mut LeanObject,
    mut v_x_2513_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_offset_2514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_2515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_2516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2523_: *mut LeanObject = core::ptr::null_mut();
    v_offset_2514_ = lean_ctor_get(v___y_2509_, 0);
    v_second_2515_ = lean_ctor_get(v___x_2510_, 0);
    v_nano_2516_ = lean_ctor_get(v___x_2510_, 1);
    v___x_2517_ = lean_int_mul(v_second_2515_, v___x_2511_);
    v___x_2518_ = lean_int_add(v___x_2517_, v_nano_2516_);
    lean_dec(v___x_2517_);
    v___x_2519_ = lean_int_mul(v_offset_2514_, v___x_2511_);
    v___x_2520_ = lean_int_add(v___x_2519_, v___x_2512_);
    lean_dec(v___x_2519_);
    v___x_2521_ = lean_int_add(v___x_2518_, v___x_2520_);
    lean_dec(v___x_2520_);
    lean_dec(v___x_2518_);
    v___x_2522_ = l_Std_Time_Duration_ofNanoseconds(v___x_2521_);
    lean_dec(v___x_2521_);
    v___x_2523_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_2522_);
    return v___x_2523_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_addDays___lam__0___boxed(
    mut v___y_2524_: *mut LeanObject,
    mut v___x_2525_: *mut LeanObject,
    mut v___x_2526_: *mut LeanObject,
    mut v___x_2527_: *mut LeanObject,
    mut v_x_2528_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2529_: *mut LeanObject = core::ptr::null_mut();
    v_res_2529_ = l_Std_Time_ZonedDateTime_addDays___lam__0(
        v___y_2524_,
        v___x_2525_,
        v___x_2526_,
        v___x_2527_,
        v_x_2528_,
    );
    lean_dec(v___x_2527_);
    lean_dec(v___x_2526_);
    lean_dec_ref(v___x_2525_);
    lean_dec_ref(v___y_2524_);
    return v_res_2529_;
}
pub unsafe fn _init_l_Std_Time_ZonedDateTime_addDays___closed__0() -> *mut LeanObject {
    let mut v___x_2530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: *mut LeanObject = core::ptr::null_mut();
    v___x_2530_ = lean_unsigned_to_nat(86400);
    v___x_2531_ = lean_nat_to_int(v___x_2530_);
    return v___x_2531_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_addDays(
    mut v_dt_2532_: *mut LeanObject,
    mut v_days_2533_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_timestamp_2534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rules_2535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2538_: u8 = 0;
    let mut v_second_2539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_2540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initialLocalTimeType_2541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_transitions_2542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2563_: u8 = 0;
    let mut v_unused_2564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2565_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_2534_ = lean_ctor_get(v_dt_2532_, 1);
                v_rules_2535_ = lean_ctor_get(v_dt_2532_, 2);
                v_isSharedCheck_2563_ = (!lean_is_exclusive(v_dt_2532_)) as u8;
                if v_isSharedCheck_2563_ == 0 {
                    v_unused_2564_ = lean_ctor_get(v_dt_2532_, 3);
                    lean_dec(v_unused_2564_);
                    v_unused_2565_ = lean_ctor_get(v_dt_2532_, 0);
                    lean_dec(v_unused_2565_);
                    v___x_2537_ = v_dt_2532_;
                    v_isShared_2538_ = v_isSharedCheck_2563_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_rules_2535_);
                    lean_inc(v_timestamp_2534_);
                    lean_dec(v_dt_2532_);
                    v___x_2537_ = lean_box(0);
                    v_isShared_2538_ = v_isSharedCheck_2563_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_second_2539_ = lean_ctor_get(v_timestamp_2534_, 0);
                lean_inc(v_second_2539_);
                v_nano_2540_ = lean_ctor_get(v_timestamp_2534_, 1);
                lean_inc(v_nano_2540_);
                lean_dec_ref(v_timestamp_2534_);
                v_initialLocalTimeType_2541_ = lean_ctor_get(v_rules_2535_, 0);
                v_transitions_2542_ = lean_ctor_get(v_rules_2535_, 1);
                v___x_2543_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_addDays___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_addDays___closed__0_once),
                    _init_l_Std_Time_ZonedDateTime_addDays___closed__0,
                );
                v___x_2544_ = lean_int_mul(v_days_2533_, v___x_2543_);
                v___x_2545_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0,
                );
                v___x_2546_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_2547_ = lean_int_mul(v_second_2539_, v___x_2546_);
                lean_dec(v_second_2539_);
                v___x_2548_ = lean_int_add(v___x_2547_, v_nano_2540_);
                lean_dec(v_nano_2540_);
                lean_dec(v___x_2547_);
                v___x_2549_ = lean_int_mul(v___x_2544_, v___x_2546_);
                lean_dec(v___x_2544_);
                v___x_2550_ = lean_int_add(v___x_2549_, v___x_2545_);
                lean_dec(v___x_2549_);
                v___x_2551_ = lean_int_add(v___x_2548_, v___x_2550_);
                lean_dec(v___x_2550_);
                lean_dec(v___x_2548_);
                v___x_2552_ = l_Std_Time_Duration_ofNanoseconds(v___x_2551_);
                lean_dec(v___x_2551_);
                v___x_2560_ =
                    l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_2542_, v___x_2552_);
                if lean_obj_tag(v___x_2560_) == 0 {
                    lean_dec_ref_known(v___x_2560_, 1);
                    v___x_2561_ =
                        l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_2541_);
                    v___y_2554_ = v___x_2561_;
                    state = 2;
                    continue;
                } else {
                    v_a_2562_ = lean_ctor_get(v___x_2560_, 0);
                    lean_inc(v_a_2562_);
                    lean_dec_ref_known(v___x_2560_, 1);
                    v___y_2554_ = v_a_2562_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc_ref(v___x_2552_);
                lean_inc_ref(v___y_2554_);
                v___f_2555_ = lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addDays___lam__0___boxed as *mut core::ffi::c_void,
                    5,
                    4,
                );
                lean_closure_set(v___f_2555_, 0, v___y_2554_);
                lean_closure_set(v___f_2555_, 1, v___x_2552_);
                lean_closure_set(v___f_2555_, 2, v___x_2546_);
                lean_closure_set(v___f_2555_, 3, v___x_2545_);
                v___x_2556_ = lean_mk_thunk(v___f_2555_);
                if v_isShared_2538_ == 0 {
                    lean_ctor_set(v___x_2537_, 3, v___y_2554_);
                    lean_ctor_set(v___x_2537_, 1, v___x_2552_);
                    lean_ctor_set(v___x_2537_, 0, v___x_2556_);
                    v___x_2558_ = v___x_2537_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2559_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2559_, 0, v___x_2556_);
                    lean_ctor_set(v_reuseFailAlloc_2559_, 1, v___x_2552_);
                    lean_ctor_set(v_reuseFailAlloc_2559_, 2, v_rules_2535_);
                    lean_ctor_set(v_reuseFailAlloc_2559_, 3, v___y_2554_);
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
    mut v_dt_2566_: *mut LeanObject,
    mut v_days_2567_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2568_: *mut LeanObject = core::ptr::null_mut();
    v_res_2568_ = l_Std_Time_ZonedDateTime_addDays(v_dt_2566_, v_days_2567_);
    lean_dec(v_days_2567_);
    return v_res_2568_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_subDays(
    mut v_dt_2569_: *mut LeanObject,
    mut v_days_2570_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_timestamp_2571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rules_2572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2575_: u8 = 0;
    let mut v_second_2576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_2577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initialLocalTimeType_2578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_transitions_2579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2602_: u8 = 0;
    let mut v_unused_2603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2604_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_2571_ = lean_ctor_get(v_dt_2569_, 1);
                v_rules_2572_ = lean_ctor_get(v_dt_2569_, 2);
                v_isSharedCheck_2602_ = (!lean_is_exclusive(v_dt_2569_)) as u8;
                if v_isSharedCheck_2602_ == 0 {
                    v_unused_2603_ = lean_ctor_get(v_dt_2569_, 3);
                    lean_dec(v_unused_2603_);
                    v_unused_2604_ = lean_ctor_get(v_dt_2569_, 0);
                    lean_dec(v_unused_2604_);
                    v___x_2574_ = v_dt_2569_;
                    v_isShared_2575_ = v_isSharedCheck_2602_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_rules_2572_);
                    lean_inc(v_timestamp_2571_);
                    lean_dec(v_dt_2569_);
                    v___x_2574_ = lean_box(0);
                    v_isShared_2575_ = v_isSharedCheck_2602_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_second_2576_ = lean_ctor_get(v_timestamp_2571_, 0);
                lean_inc(v_second_2576_);
                v_nano_2577_ = lean_ctor_get(v_timestamp_2571_, 1);
                lean_inc(v_nano_2577_);
                lean_dec_ref(v_timestamp_2571_);
                v_initialLocalTimeType_2578_ = lean_ctor_get(v_rules_2572_, 0);
                v_transitions_2579_ = lean_ctor_get(v_rules_2572_, 1);
                v___x_2580_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_addDays___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_addDays___closed__0_once),
                    _init_l_Std_Time_ZonedDateTime_addDays___closed__0,
                );
                v___x_2581_ = lean_int_mul(v_days_2570_, v___x_2580_);
                v___x_2582_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0,
                );
                v___x_2583_ = lean_int_neg(v___x_2581_);
                lean_dec(v___x_2581_);
                v___x_2584_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
                );
                v___x_2585_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_2586_ = lean_int_mul(v_second_2576_, v___x_2585_);
                lean_dec(v_second_2576_);
                v___x_2587_ = lean_int_add(v___x_2586_, v_nano_2577_);
                lean_dec(v_nano_2577_);
                lean_dec(v___x_2586_);
                v___x_2588_ = lean_int_mul(v___x_2583_, v___x_2585_);
                lean_dec(v___x_2583_);
                v___x_2589_ = lean_int_add(v___x_2588_, v___x_2584_);
                lean_dec(v___x_2588_);
                v___x_2590_ = lean_int_add(v___x_2587_, v___x_2589_);
                lean_dec(v___x_2589_);
                lean_dec(v___x_2587_);
                v___x_2591_ = l_Std_Time_Duration_ofNanoseconds(v___x_2590_);
                lean_dec(v___x_2590_);
                v___x_2599_ =
                    l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_2579_, v___x_2591_);
                if lean_obj_tag(v___x_2599_) == 0 {
                    lean_dec_ref_known(v___x_2599_, 1);
                    v___x_2600_ =
                        l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_2578_);
                    v___y_2593_ = v___x_2600_;
                    state = 2;
                    continue;
                } else {
                    v_a_2601_ = lean_ctor_get(v___x_2599_, 0);
                    lean_inc(v_a_2601_);
                    lean_dec_ref_known(v___x_2599_, 1);
                    v___y_2593_ = v_a_2601_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc_ref(v___x_2591_);
                lean_inc_ref(v___y_2593_);
                v___f_2594_ = lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addDays___lam__0___boxed as *mut core::ffi::c_void,
                    5,
                    4,
                );
                lean_closure_set(v___f_2594_, 0, v___y_2593_);
                lean_closure_set(v___f_2594_, 1, v___x_2591_);
                lean_closure_set(v___f_2594_, 2, v___x_2585_);
                lean_closure_set(v___f_2594_, 3, v___x_2582_);
                v___x_2595_ = lean_mk_thunk(v___f_2594_);
                if v_isShared_2575_ == 0 {
                    lean_ctor_set(v___x_2574_, 3, v___y_2593_);
                    lean_ctor_set(v___x_2574_, 1, v___x_2591_);
                    lean_ctor_set(v___x_2574_, 0, v___x_2595_);
                    v___x_2597_ = v___x_2574_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2598_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2598_, 0, v___x_2595_);
                    lean_ctor_set(v_reuseFailAlloc_2598_, 1, v___x_2591_);
                    lean_ctor_set(v_reuseFailAlloc_2598_, 2, v_rules_2572_);
                    lean_ctor_set(v_reuseFailAlloc_2598_, 3, v___y_2593_);
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
    mut v_dt_2605_: *mut LeanObject,
    mut v_days_2606_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2607_: *mut LeanObject = core::ptr::null_mut();
    v_res_2607_ = l_Std_Time_ZonedDateTime_subDays(v_dt_2605_, v_days_2606_);
    lean_dec(v_days_2606_);
    return v_res_2607_;
}
pub unsafe fn _init_l_Std_Time_ZonedDateTime_addWeeks___closed__0() -> *mut LeanObject {
    let mut v___x_2608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut LeanObject = core::ptr::null_mut();
    v___x_2608_ = lean_unsigned_to_nat(7);
    v___x_2609_ = lean_nat_to_int(v___x_2608_);
    return v___x_2609_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_addWeeks(
    mut v_dt_2610_: *mut LeanObject,
    mut v_weeks_2611_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_timestamp_2612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rules_2613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2616_: u8 = 0;
    let mut v_second_2617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_2618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initialLocalTimeType_2619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_transitions_2620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2643_: u8 = 0;
    let mut v_unused_2644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2645_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_2612_ = lean_ctor_get(v_dt_2610_, 1);
                v_rules_2613_ = lean_ctor_get(v_dt_2610_, 2);
                v_isSharedCheck_2643_ = (!lean_is_exclusive(v_dt_2610_)) as u8;
                if v_isSharedCheck_2643_ == 0 {
                    v_unused_2644_ = lean_ctor_get(v_dt_2610_, 3);
                    lean_dec(v_unused_2644_);
                    v_unused_2645_ = lean_ctor_get(v_dt_2610_, 0);
                    lean_dec(v_unused_2645_);
                    v___x_2615_ = v_dt_2610_;
                    v_isShared_2616_ = v_isSharedCheck_2643_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_rules_2613_);
                    lean_inc(v_timestamp_2612_);
                    lean_dec(v_dt_2610_);
                    v___x_2615_ = lean_box(0);
                    v_isShared_2616_ = v_isSharedCheck_2643_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_second_2617_ = lean_ctor_get(v_timestamp_2612_, 0);
                lean_inc(v_second_2617_);
                v_nano_2618_ = lean_ctor_get(v_timestamp_2612_, 1);
                lean_inc(v_nano_2618_);
                lean_dec_ref(v_timestamp_2612_);
                v_initialLocalTimeType_2619_ = lean_ctor_get(v_rules_2613_, 0);
                v_transitions_2620_ = lean_ctor_get(v_rules_2613_, 1);
                v___x_2621_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_addWeeks___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_addWeeks___closed__0_once),
                    _init_l_Std_Time_ZonedDateTime_addWeeks___closed__0,
                );
                v___x_2622_ = lean_int_mul(v_weeks_2611_, v___x_2621_);
                v___x_2623_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_addDays___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_addDays___closed__0_once),
                    _init_l_Std_Time_ZonedDateTime_addDays___closed__0,
                );
                v___x_2624_ = lean_int_mul(v___x_2622_, v___x_2623_);
                lean_dec(v___x_2622_);
                v___x_2625_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0,
                );
                v___x_2626_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_2627_ = lean_int_mul(v_second_2617_, v___x_2626_);
                lean_dec(v_second_2617_);
                v___x_2628_ = lean_int_add(v___x_2627_, v_nano_2618_);
                lean_dec(v_nano_2618_);
                lean_dec(v___x_2627_);
                v___x_2629_ = lean_int_mul(v___x_2624_, v___x_2626_);
                lean_dec(v___x_2624_);
                v___x_2630_ = lean_int_add(v___x_2629_, v___x_2625_);
                lean_dec(v___x_2629_);
                v___x_2631_ = lean_int_add(v___x_2628_, v___x_2630_);
                lean_dec(v___x_2630_);
                lean_dec(v___x_2628_);
                v___x_2632_ = l_Std_Time_Duration_ofNanoseconds(v___x_2631_);
                lean_dec(v___x_2631_);
                v___x_2640_ =
                    l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_2620_, v___x_2632_);
                if lean_obj_tag(v___x_2640_) == 0 {
                    lean_dec_ref_known(v___x_2640_, 1);
                    v___x_2641_ =
                        l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_2619_);
                    v___y_2634_ = v___x_2641_;
                    state = 2;
                    continue;
                } else {
                    v_a_2642_ = lean_ctor_get(v___x_2640_, 0);
                    lean_inc(v_a_2642_);
                    lean_dec_ref_known(v___x_2640_, 1);
                    v___y_2634_ = v_a_2642_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc_ref(v___x_2632_);
                lean_inc_ref(v___y_2634_);
                v___f_2635_ = lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addDays___lam__0___boxed as *mut core::ffi::c_void,
                    5,
                    4,
                );
                lean_closure_set(v___f_2635_, 0, v___y_2634_);
                lean_closure_set(v___f_2635_, 1, v___x_2632_);
                lean_closure_set(v___f_2635_, 2, v___x_2626_);
                lean_closure_set(v___f_2635_, 3, v___x_2625_);
                v___x_2636_ = lean_mk_thunk(v___f_2635_);
                if v_isShared_2616_ == 0 {
                    lean_ctor_set(v___x_2615_, 3, v___y_2634_);
                    lean_ctor_set(v___x_2615_, 1, v___x_2632_);
                    lean_ctor_set(v___x_2615_, 0, v___x_2636_);
                    v___x_2638_ = v___x_2615_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2639_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2639_, 0, v___x_2636_);
                    lean_ctor_set(v_reuseFailAlloc_2639_, 1, v___x_2632_);
                    lean_ctor_set(v_reuseFailAlloc_2639_, 2, v_rules_2613_);
                    lean_ctor_set(v_reuseFailAlloc_2639_, 3, v___y_2634_);
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
    mut v_dt_2646_: *mut LeanObject,
    mut v_weeks_2647_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2648_: *mut LeanObject = core::ptr::null_mut();
    v_res_2648_ = l_Std_Time_ZonedDateTime_addWeeks(v_dt_2646_, v_weeks_2647_);
    lean_dec(v_weeks_2647_);
    return v_res_2648_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_subWeeks(
    mut v_dt_2649_: *mut LeanObject,
    mut v_weeks_2650_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_timestamp_2651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rules_2652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2655_: u8 = 0;
    let mut v_second_2656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_2657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initialLocalTimeType_2658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_transitions_2659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2684_: u8 = 0;
    let mut v_unused_2685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2686_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_2651_ = lean_ctor_get(v_dt_2649_, 1);
                v_rules_2652_ = lean_ctor_get(v_dt_2649_, 2);
                v_isSharedCheck_2684_ = (!lean_is_exclusive(v_dt_2649_)) as u8;
                if v_isSharedCheck_2684_ == 0 {
                    v_unused_2685_ = lean_ctor_get(v_dt_2649_, 3);
                    lean_dec(v_unused_2685_);
                    v_unused_2686_ = lean_ctor_get(v_dt_2649_, 0);
                    lean_dec(v_unused_2686_);
                    v___x_2654_ = v_dt_2649_;
                    v_isShared_2655_ = v_isSharedCheck_2684_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_rules_2652_);
                    lean_inc(v_timestamp_2651_);
                    lean_dec(v_dt_2649_);
                    v___x_2654_ = lean_box(0);
                    v_isShared_2655_ = v_isSharedCheck_2684_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_second_2656_ = lean_ctor_get(v_timestamp_2651_, 0);
                lean_inc(v_second_2656_);
                v_nano_2657_ = lean_ctor_get(v_timestamp_2651_, 1);
                lean_inc(v_nano_2657_);
                lean_dec_ref(v_timestamp_2651_);
                v_initialLocalTimeType_2658_ = lean_ctor_get(v_rules_2652_, 0);
                v_transitions_2659_ = lean_ctor_get(v_rules_2652_, 1);
                v___x_2660_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_addWeeks___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_addWeeks___closed__0_once),
                    _init_l_Std_Time_ZonedDateTime_addWeeks___closed__0,
                );
                v___x_2661_ = lean_int_mul(v_weeks_2650_, v___x_2660_);
                v___x_2662_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_addDays___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_addDays___closed__0_once),
                    _init_l_Std_Time_ZonedDateTime_addDays___closed__0,
                );
                v___x_2663_ = lean_int_mul(v___x_2661_, v___x_2662_);
                lean_dec(v___x_2661_);
                v___x_2664_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0,
                );
                v___x_2665_ = lean_int_neg(v___x_2663_);
                lean_dec(v___x_2663_);
                v___x_2666_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
                );
                v___x_2667_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_2668_ = lean_int_mul(v_second_2656_, v___x_2667_);
                lean_dec(v_second_2656_);
                v___x_2669_ = lean_int_add(v___x_2668_, v_nano_2657_);
                lean_dec(v_nano_2657_);
                lean_dec(v___x_2668_);
                v___x_2670_ = lean_int_mul(v___x_2665_, v___x_2667_);
                lean_dec(v___x_2665_);
                v___x_2671_ = lean_int_add(v___x_2670_, v___x_2666_);
                lean_dec(v___x_2670_);
                v___x_2672_ = lean_int_add(v___x_2669_, v___x_2671_);
                lean_dec(v___x_2671_);
                lean_dec(v___x_2669_);
                v___x_2673_ = l_Std_Time_Duration_ofNanoseconds(v___x_2672_);
                lean_dec(v___x_2672_);
                v___x_2681_ =
                    l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_2659_, v___x_2673_);
                if lean_obj_tag(v___x_2681_) == 0 {
                    lean_dec_ref_known(v___x_2681_, 1);
                    v___x_2682_ =
                        l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_2658_);
                    v___y_2675_ = v___x_2682_;
                    state = 2;
                    continue;
                } else {
                    v_a_2683_ = lean_ctor_get(v___x_2681_, 0);
                    lean_inc(v_a_2683_);
                    lean_dec_ref_known(v___x_2681_, 1);
                    v___y_2675_ = v_a_2683_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc_ref(v___x_2673_);
                lean_inc_ref(v___y_2675_);
                v___f_2676_ = lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addDays___lam__0___boxed as *mut core::ffi::c_void,
                    5,
                    4,
                );
                lean_closure_set(v___f_2676_, 0, v___y_2675_);
                lean_closure_set(v___f_2676_, 1, v___x_2673_);
                lean_closure_set(v___f_2676_, 2, v___x_2667_);
                lean_closure_set(v___f_2676_, 3, v___x_2664_);
                v___x_2677_ = lean_mk_thunk(v___f_2676_);
                if v_isShared_2655_ == 0 {
                    lean_ctor_set(v___x_2654_, 3, v___y_2675_);
                    lean_ctor_set(v___x_2654_, 1, v___x_2673_);
                    lean_ctor_set(v___x_2654_, 0, v___x_2677_);
                    v___x_2679_ = v___x_2654_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2680_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2680_, 0, v___x_2677_);
                    lean_ctor_set(v_reuseFailAlloc_2680_, 1, v___x_2673_);
                    lean_ctor_set(v_reuseFailAlloc_2680_, 2, v_rules_2652_);
                    lean_ctor_set(v_reuseFailAlloc_2680_, 3, v___y_2675_);
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
    mut v_dt_2687_: *mut LeanObject,
    mut v_weeks_2688_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2689_: *mut LeanObject = core::ptr::null_mut();
    v_res_2689_ = l_Std_Time_ZonedDateTime_subWeeks(v_dt_2687_, v_weeks_2688_);
    lean_dec(v_weeks_2688_);
    return v_res_2689_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_addMonthsClip___lam__0(
    mut v___x_2690_: *mut LeanObject,
    mut v_x_2691_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc_ref(v___x_2690_);
    return v___x_2690_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed(
    mut v___x_2692_: *mut LeanObject,
    mut v_x_2693_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2694_: *mut LeanObject = core::ptr::null_mut();
    v_res_2694_ = l_Std_Time_ZonedDateTime_addMonthsClip___lam__0(v___x_2692_, v_x_2693_);
    lean_dec_ref(v___x_2692_);
    return v_res_2694_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_addMonthsClip(
    mut v_dt_2695_: *mut LeanObject,
    mut v_months_2696_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_2697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rules_2698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2701_: u8 = 0;
    let mut v___x_2702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_wt_2704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ltt_2705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tz_2706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_offset_2707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_2708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_2709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2724_: u8 = 0;
    let mut v_unused_2725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2726_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_2697_ = lean_ctor_get(v_dt_2695_, 0);
                v_rules_2698_ = lean_ctor_get(v_dt_2695_, 2);
                v_isSharedCheck_2724_ = (!lean_is_exclusive(v_dt_2695_)) as u8;
                if v_isSharedCheck_2724_ == 0 {
                    v_unused_2725_ = lean_ctor_get(v_dt_2695_, 3);
                    lean_dec(v_unused_2725_);
                    v_unused_2726_ = lean_ctor_get(v_dt_2695_, 1);
                    lean_dec(v_unused_2726_);
                    v___x_2700_ = v_dt_2695_;
                    v_isShared_2701_ = v_isSharedCheck_2724_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_rules_2698_);
                    lean_inc(v_date_2697_);
                    lean_dec(v_dt_2695_);
                    v___x_2700_ = lean_box(0);
                    v_isShared_2701_ = v_isSharedCheck_2724_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2702_ = lean_thunk_get_own(v_date_2697_);
                lean_dec_ref(v_date_2697_);
                v___x_2703_ = l_Std_Time_PlainDateTime_addMonthsClip(v___x_2702_, v_months_2696_);
                lean_inc_ref(v___x_2703_);
                v_wt_2704_ = l_Std_Time_PlainDateTime_toWallTime(v___x_2703_);
                lean_inc_ref(v_rules_2698_);
                v_ltt_2705_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(
                    v_rules_2698_,
                    v_wt_2704_,
                );
                v_tz_2706_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_2705_);
                lean_dec_ref(v_ltt_2705_);
                v_offset_2707_ = lean_ctor_get(v_tz_2706_, 0);
                lean_inc(v_offset_2707_);
                v_second_2708_ = lean_ctor_get(v_wt_2704_, 0);
                lean_inc(v_second_2708_);
                v_nano_2709_ = lean_ctor_get(v_wt_2704_, 1);
                lean_inc(v_nano_2709_);
                lean_dec_ref(v_wt_2704_);
                v___f_2710_ = lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_2710_, 0, v___x_2703_);
                v___x_2711_ = lean_mk_thunk(v___f_2710_);
                v___x_2712_ = lean_int_neg(v_offset_2707_);
                lean_dec(v_offset_2707_);
                v___x_2713_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
                );
                v___x_2714_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_2715_ = lean_int_mul(v_second_2708_, v___x_2714_);
                lean_dec(v_second_2708_);
                v___x_2716_ = lean_int_add(v___x_2715_, v_nano_2709_);
                lean_dec(v_nano_2709_);
                lean_dec(v___x_2715_);
                v___x_2717_ = lean_int_mul(v___x_2712_, v___x_2714_);
                lean_dec(v___x_2712_);
                v___x_2718_ = lean_int_add(v___x_2717_, v___x_2713_);
                lean_dec(v___x_2717_);
                v___x_2719_ = lean_int_add(v___x_2716_, v___x_2718_);
                lean_dec(v___x_2718_);
                lean_dec(v___x_2716_);
                v___x_2720_ = l_Std_Time_Duration_ofNanoseconds(v___x_2719_);
                lean_dec(v___x_2719_);
                if v_isShared_2701_ == 0 {
                    lean_ctor_set(v___x_2700_, 3, v_tz_2706_);
                    lean_ctor_set(v___x_2700_, 1, v___x_2720_);
                    lean_ctor_set(v___x_2700_, 0, v___x_2711_);
                    v___x_2722_ = v___x_2700_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2723_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2723_, 0, v___x_2711_);
                    lean_ctor_set(v_reuseFailAlloc_2723_, 1, v___x_2720_);
                    lean_ctor_set(v_reuseFailAlloc_2723_, 2, v_rules_2698_);
                    lean_ctor_set(v_reuseFailAlloc_2723_, 3, v_tz_2706_);
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
    mut v_dt_2727_: *mut LeanObject,
    mut v_months_2728_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2729_: *mut LeanObject = core::ptr::null_mut();
    v_res_2729_ = l_Std_Time_ZonedDateTime_addMonthsClip(v_dt_2727_, v_months_2728_);
    lean_dec(v_months_2728_);
    return v_res_2729_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_subMonthsClip(
    mut v_dt_2730_: *mut LeanObject,
    mut v_months_2731_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_2732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rules_2733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2736_: u8 = 0;
    let mut v___x_2737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_date_2738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_time_2739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2742_: u8 = 0;
    let mut v___x_2743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_wt_2747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ltt_2748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tz_2749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_offset_2750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_2751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_2752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2768_: u8 = 0;
    let mut v_isSharedCheck_2769_: u8 = 0;
    let mut v_unused_2770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2771_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_2732_ = lean_ctor_get(v_dt_2730_, 0);
                v_rules_2733_ = lean_ctor_get(v_dt_2730_, 2);
                v_isSharedCheck_2769_ = (!lean_is_exclusive(v_dt_2730_)) as u8;
                if v_isSharedCheck_2769_ == 0 {
                    v_unused_2770_ = lean_ctor_get(v_dt_2730_, 3);
                    lean_dec(v_unused_2770_);
                    v_unused_2771_ = lean_ctor_get(v_dt_2730_, 1);
                    lean_dec(v_unused_2771_);
                    v___x_2735_ = v_dt_2730_;
                    v_isShared_2736_ = v_isSharedCheck_2769_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_rules_2733_);
                    lean_inc(v_date_2732_);
                    lean_dec(v_dt_2730_);
                    v___x_2735_ = lean_box(0);
                    v_isShared_2736_ = v_isSharedCheck_2769_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2737_ = lean_thunk_get_own(v_date_2732_);
                lean_dec_ref(v_date_2732_);
                v_date_2738_ = lean_ctor_get(v___x_2737_, 0);
                v_time_2739_ = lean_ctor_get(v___x_2737_, 1);
                v_isSharedCheck_2768_ = (!lean_is_exclusive(v___x_2737_)) as u8;
                if v_isSharedCheck_2768_ == 0 {
                    v___x_2741_ = v___x_2737_;
                    v_isShared_2742_ = v_isSharedCheck_2768_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_time_2739_);
                    lean_inc(v_date_2738_);
                    lean_dec(v___x_2737_);
                    v___x_2741_ = lean_box(0);
                    v_isShared_2742_ = v_isSharedCheck_2768_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2743_ = lean_int_neg(v_months_2731_);
                v___x_2744_ = l_Std_Time_PlainDate_addMonthsClip(v_date_2738_, v___x_2743_);
                lean_dec(v___x_2743_);
                if v_isShared_2742_ == 0 {
                    lean_ctor_set(v___x_2741_, 0, v___x_2744_);
                    v___x_2746_ = v___x_2741_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2767_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2767_, 0, v___x_2744_);
                    lean_ctor_set(v_reuseFailAlloc_2767_, 1, v_time_2739_);
                    v___x_2746_ = v_reuseFailAlloc_2767_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_inc_ref(v___x_2746_);
                v_wt_2747_ = l_Std_Time_PlainDateTime_toWallTime(v___x_2746_);
                lean_inc_ref(v_rules_2733_);
                v_ltt_2748_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(
                    v_rules_2733_,
                    v_wt_2747_,
                );
                v_tz_2749_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_2748_);
                lean_dec_ref(v_ltt_2748_);
                v_offset_2750_ = lean_ctor_get(v_tz_2749_, 0);
                lean_inc(v_offset_2750_);
                v_second_2751_ = lean_ctor_get(v_wt_2747_, 0);
                lean_inc(v_second_2751_);
                v_nano_2752_ = lean_ctor_get(v_wt_2747_, 1);
                lean_inc(v_nano_2752_);
                lean_dec_ref(v_wt_2747_);
                v___f_2753_ = lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_2753_, 0, v___x_2746_);
                v___x_2754_ = lean_mk_thunk(v___f_2753_);
                v___x_2755_ = lean_int_neg(v_offset_2750_);
                lean_dec(v_offset_2750_);
                v___x_2756_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
                );
                v___x_2757_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_2758_ = lean_int_mul(v_second_2751_, v___x_2757_);
                lean_dec(v_second_2751_);
                v___x_2759_ = lean_int_add(v___x_2758_, v_nano_2752_);
                lean_dec(v_nano_2752_);
                lean_dec(v___x_2758_);
                v___x_2760_ = lean_int_mul(v___x_2755_, v___x_2757_);
                lean_dec(v___x_2755_);
                v___x_2761_ = lean_int_add(v___x_2760_, v___x_2756_);
                lean_dec(v___x_2760_);
                v___x_2762_ = lean_int_add(v___x_2759_, v___x_2761_);
                lean_dec(v___x_2761_);
                lean_dec(v___x_2759_);
                v___x_2763_ = l_Std_Time_Duration_ofNanoseconds(v___x_2762_);
                lean_dec(v___x_2762_);
                if v_isShared_2736_ == 0 {
                    lean_ctor_set(v___x_2735_, 3, v_tz_2749_);
                    lean_ctor_set(v___x_2735_, 1, v___x_2763_);
                    lean_ctor_set(v___x_2735_, 0, v___x_2754_);
                    v___x_2765_ = v___x_2735_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2766_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2766_, 0, v___x_2754_);
                    lean_ctor_set(v_reuseFailAlloc_2766_, 1, v___x_2763_);
                    lean_ctor_set(v_reuseFailAlloc_2766_, 2, v_rules_2733_);
                    lean_ctor_set(v_reuseFailAlloc_2766_, 3, v_tz_2749_);
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
    mut v_dt_2772_: *mut LeanObject,
    mut v_months_2773_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2774_: *mut LeanObject = core::ptr::null_mut();
    v_res_2774_ = l_Std_Time_ZonedDateTime_subMonthsClip(v_dt_2772_, v_months_2773_);
    lean_dec(v_months_2773_);
    return v_res_2774_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_addMonthsRollOver(
    mut v_dt_2775_: *mut LeanObject,
    mut v_months_2776_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_2777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rules_2778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2781_: u8 = 0;
    let mut v___x_2782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_wt_2784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ltt_2785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tz_2786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_offset_2787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_2788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_2789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2804_: u8 = 0;
    let mut v_unused_2805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2806_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_2777_ = lean_ctor_get(v_dt_2775_, 0);
                v_rules_2778_ = lean_ctor_get(v_dt_2775_, 2);
                v_isSharedCheck_2804_ = (!lean_is_exclusive(v_dt_2775_)) as u8;
                if v_isSharedCheck_2804_ == 0 {
                    v_unused_2805_ = lean_ctor_get(v_dt_2775_, 3);
                    lean_dec(v_unused_2805_);
                    v_unused_2806_ = lean_ctor_get(v_dt_2775_, 1);
                    lean_dec(v_unused_2806_);
                    v___x_2780_ = v_dt_2775_;
                    v_isShared_2781_ = v_isSharedCheck_2804_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_rules_2778_);
                    lean_inc(v_date_2777_);
                    lean_dec(v_dt_2775_);
                    v___x_2780_ = lean_box(0);
                    v_isShared_2781_ = v_isSharedCheck_2804_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2782_ = lean_thunk_get_own(v_date_2777_);
                lean_dec_ref(v_date_2777_);
                v___x_2783_ =
                    l_Std_Time_PlainDateTime_addMonthsRollOver(v___x_2782_, v_months_2776_);
                lean_inc_ref(v___x_2783_);
                v_wt_2784_ = l_Std_Time_PlainDateTime_toWallTime(v___x_2783_);
                lean_inc_ref(v_rules_2778_);
                v_ltt_2785_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(
                    v_rules_2778_,
                    v_wt_2784_,
                );
                v_tz_2786_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_2785_);
                lean_dec_ref(v_ltt_2785_);
                v_offset_2787_ = lean_ctor_get(v_tz_2786_, 0);
                lean_inc(v_offset_2787_);
                v_second_2788_ = lean_ctor_get(v_wt_2784_, 0);
                lean_inc(v_second_2788_);
                v_nano_2789_ = lean_ctor_get(v_wt_2784_, 1);
                lean_inc(v_nano_2789_);
                lean_dec_ref(v_wt_2784_);
                v___f_2790_ = lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_2790_, 0, v___x_2783_);
                v___x_2791_ = lean_mk_thunk(v___f_2790_);
                v___x_2792_ = lean_int_neg(v_offset_2787_);
                lean_dec(v_offset_2787_);
                v___x_2793_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
                );
                v___x_2794_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_2795_ = lean_int_mul(v_second_2788_, v___x_2794_);
                lean_dec(v_second_2788_);
                v___x_2796_ = lean_int_add(v___x_2795_, v_nano_2789_);
                lean_dec(v_nano_2789_);
                lean_dec(v___x_2795_);
                v___x_2797_ = lean_int_mul(v___x_2792_, v___x_2794_);
                lean_dec(v___x_2792_);
                v___x_2798_ = lean_int_add(v___x_2797_, v___x_2793_);
                lean_dec(v___x_2797_);
                v___x_2799_ = lean_int_add(v___x_2796_, v___x_2798_);
                lean_dec(v___x_2798_);
                lean_dec(v___x_2796_);
                v___x_2800_ = l_Std_Time_Duration_ofNanoseconds(v___x_2799_);
                lean_dec(v___x_2799_);
                if v_isShared_2781_ == 0 {
                    lean_ctor_set(v___x_2780_, 3, v_tz_2786_);
                    lean_ctor_set(v___x_2780_, 1, v___x_2800_);
                    lean_ctor_set(v___x_2780_, 0, v___x_2791_);
                    v___x_2802_ = v___x_2780_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2803_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2803_, 0, v___x_2791_);
                    lean_ctor_set(v_reuseFailAlloc_2803_, 1, v___x_2800_);
                    lean_ctor_set(v_reuseFailAlloc_2803_, 2, v_rules_2778_);
                    lean_ctor_set(v_reuseFailAlloc_2803_, 3, v_tz_2786_);
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
    mut v_dt_2807_: *mut LeanObject,
    mut v_months_2808_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2809_: *mut LeanObject = core::ptr::null_mut();
    v_res_2809_ = l_Std_Time_ZonedDateTime_addMonthsRollOver(v_dt_2807_, v_months_2808_);
    lean_dec(v_months_2808_);
    return v_res_2809_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_subMonthsRollOver(
    mut v_dt_2810_: *mut LeanObject,
    mut v_months_2811_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_2812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rules_2813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2816_: u8 = 0;
    let mut v___x_2817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_date_2818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_time_2819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2822_: u8 = 0;
    let mut v___x_2823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_wt_2827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ltt_2828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tz_2829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_offset_2830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_2831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_2832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2848_: u8 = 0;
    let mut v_isSharedCheck_2849_: u8 = 0;
    let mut v_unused_2850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2851_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_2812_ = lean_ctor_get(v_dt_2810_, 0);
                v_rules_2813_ = lean_ctor_get(v_dt_2810_, 2);
                v_isSharedCheck_2849_ = (!lean_is_exclusive(v_dt_2810_)) as u8;
                if v_isSharedCheck_2849_ == 0 {
                    v_unused_2850_ = lean_ctor_get(v_dt_2810_, 3);
                    lean_dec(v_unused_2850_);
                    v_unused_2851_ = lean_ctor_get(v_dt_2810_, 1);
                    lean_dec(v_unused_2851_);
                    v___x_2815_ = v_dt_2810_;
                    v_isShared_2816_ = v_isSharedCheck_2849_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_rules_2813_);
                    lean_inc(v_date_2812_);
                    lean_dec(v_dt_2810_);
                    v___x_2815_ = lean_box(0);
                    v_isShared_2816_ = v_isSharedCheck_2849_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2817_ = lean_thunk_get_own(v_date_2812_);
                lean_dec_ref(v_date_2812_);
                v_date_2818_ = lean_ctor_get(v___x_2817_, 0);
                v_time_2819_ = lean_ctor_get(v___x_2817_, 1);
                v_isSharedCheck_2848_ = (!lean_is_exclusive(v___x_2817_)) as u8;
                if v_isSharedCheck_2848_ == 0 {
                    v___x_2821_ = v___x_2817_;
                    v_isShared_2822_ = v_isSharedCheck_2848_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_time_2819_);
                    lean_inc(v_date_2818_);
                    lean_dec(v___x_2817_);
                    v___x_2821_ = lean_box(0);
                    v_isShared_2822_ = v_isSharedCheck_2848_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2823_ = lean_int_neg(v_months_2811_);
                v___x_2824_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_2818_, v___x_2823_);
                lean_dec(v___x_2823_);
                if v_isShared_2822_ == 0 {
                    lean_ctor_set(v___x_2821_, 0, v___x_2824_);
                    v___x_2826_ = v___x_2821_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2847_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2847_, 0, v___x_2824_);
                    lean_ctor_set(v_reuseFailAlloc_2847_, 1, v_time_2819_);
                    v___x_2826_ = v_reuseFailAlloc_2847_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_inc_ref(v___x_2826_);
                v_wt_2827_ = l_Std_Time_PlainDateTime_toWallTime(v___x_2826_);
                lean_inc_ref(v_rules_2813_);
                v_ltt_2828_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(
                    v_rules_2813_,
                    v_wt_2827_,
                );
                v_tz_2829_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_2828_);
                lean_dec_ref(v_ltt_2828_);
                v_offset_2830_ = lean_ctor_get(v_tz_2829_, 0);
                lean_inc(v_offset_2830_);
                v_second_2831_ = lean_ctor_get(v_wt_2827_, 0);
                lean_inc(v_second_2831_);
                v_nano_2832_ = lean_ctor_get(v_wt_2827_, 1);
                lean_inc(v_nano_2832_);
                lean_dec_ref(v_wt_2827_);
                v___f_2833_ = lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_2833_, 0, v___x_2826_);
                v___x_2834_ = lean_mk_thunk(v___f_2833_);
                v___x_2835_ = lean_int_neg(v_offset_2830_);
                lean_dec(v_offset_2830_);
                v___x_2836_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
                );
                v___x_2837_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_2838_ = lean_int_mul(v_second_2831_, v___x_2837_);
                lean_dec(v_second_2831_);
                v___x_2839_ = lean_int_add(v___x_2838_, v_nano_2832_);
                lean_dec(v_nano_2832_);
                lean_dec(v___x_2838_);
                v___x_2840_ = lean_int_mul(v___x_2835_, v___x_2837_);
                lean_dec(v___x_2835_);
                v___x_2841_ = lean_int_add(v___x_2840_, v___x_2836_);
                lean_dec(v___x_2840_);
                v___x_2842_ = lean_int_add(v___x_2839_, v___x_2841_);
                lean_dec(v___x_2841_);
                lean_dec(v___x_2839_);
                v___x_2843_ = l_Std_Time_Duration_ofNanoseconds(v___x_2842_);
                lean_dec(v___x_2842_);
                if v_isShared_2816_ == 0 {
                    lean_ctor_set(v___x_2815_, 3, v_tz_2829_);
                    lean_ctor_set(v___x_2815_, 1, v___x_2843_);
                    lean_ctor_set(v___x_2815_, 0, v___x_2834_);
                    v___x_2845_ = v___x_2815_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2846_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2846_, 0, v___x_2834_);
                    lean_ctor_set(v_reuseFailAlloc_2846_, 1, v___x_2843_);
                    lean_ctor_set(v_reuseFailAlloc_2846_, 2, v_rules_2813_);
                    lean_ctor_set(v_reuseFailAlloc_2846_, 3, v_tz_2829_);
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
    mut v_dt_2852_: *mut LeanObject,
    mut v_months_2853_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2854_: *mut LeanObject = core::ptr::null_mut();
    v_res_2854_ = l_Std_Time_ZonedDateTime_subMonthsRollOver(v_dt_2852_, v_months_2853_);
    lean_dec(v_months_2853_);
    return v_res_2854_;
}
pub unsafe fn _init_l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0() -> *mut LeanObject {
    let mut v___x_2855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2856_: *mut LeanObject = core::ptr::null_mut();
    v___x_2855_ = lean_unsigned_to_nat(12);
    v___x_2856_ = lean_nat_to_int(v___x_2855_);
    return v___x_2856_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_addYearsRollOver(
    mut v_dt_2857_: *mut LeanObject,
    mut v_years_2858_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_2859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rules_2860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2863_: u8 = 0;
    let mut v___x_2864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_date_2865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_time_2866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2869_: u8 = 0;
    let mut v___x_2870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_wt_2875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ltt_2876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tz_2877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_offset_2878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_2879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_2880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2896_: u8 = 0;
    let mut v_isSharedCheck_2897_: u8 = 0;
    let mut v_unused_2898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2899_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_2859_ = lean_ctor_get(v_dt_2857_, 0);
                v_rules_2860_ = lean_ctor_get(v_dt_2857_, 2);
                v_isSharedCheck_2897_ = (!lean_is_exclusive(v_dt_2857_)) as u8;
                if v_isSharedCheck_2897_ == 0 {
                    v_unused_2898_ = lean_ctor_get(v_dt_2857_, 3);
                    lean_dec(v_unused_2898_);
                    v_unused_2899_ = lean_ctor_get(v_dt_2857_, 1);
                    lean_dec(v_unused_2899_);
                    v___x_2862_ = v_dt_2857_;
                    v_isShared_2863_ = v_isSharedCheck_2897_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_rules_2860_);
                    lean_inc(v_date_2859_);
                    lean_dec(v_dt_2857_);
                    v___x_2862_ = lean_box(0);
                    v_isShared_2863_ = v_isSharedCheck_2897_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2864_ = lean_thunk_get_own(v_date_2859_);
                lean_dec_ref(v_date_2859_);
                v_date_2865_ = lean_ctor_get(v___x_2864_, 0);
                v_time_2866_ = lean_ctor_get(v___x_2864_, 1);
                v_isSharedCheck_2896_ = (!lean_is_exclusive(v___x_2864_)) as u8;
                if v_isSharedCheck_2896_ == 0 {
                    v___x_2868_ = v___x_2864_;
                    v_isShared_2869_ = v_isSharedCheck_2896_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_time_2866_);
                    lean_inc(v_date_2865_);
                    lean_dec(v___x_2864_);
                    v___x_2868_ = lean_box(0);
                    v_isShared_2869_ = v_isSharedCheck_2896_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2870_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0,
                );
                v___x_2871_ = lean_int_mul(v_years_2858_, v___x_2870_);
                v___x_2872_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_2865_, v___x_2871_);
                lean_dec(v___x_2871_);
                if v_isShared_2869_ == 0 {
                    lean_ctor_set(v___x_2868_, 0, v___x_2872_);
                    v___x_2874_ = v___x_2868_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2895_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2895_, 0, v___x_2872_);
                    lean_ctor_set(v_reuseFailAlloc_2895_, 1, v_time_2866_);
                    v___x_2874_ = v_reuseFailAlloc_2895_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_inc_ref(v___x_2874_);
                v_wt_2875_ = l_Std_Time_PlainDateTime_toWallTime(v___x_2874_);
                lean_inc_ref(v_rules_2860_);
                v_ltt_2876_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(
                    v_rules_2860_,
                    v_wt_2875_,
                );
                v_tz_2877_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_2876_);
                lean_dec_ref(v_ltt_2876_);
                v_offset_2878_ = lean_ctor_get(v_tz_2877_, 0);
                lean_inc(v_offset_2878_);
                v_second_2879_ = lean_ctor_get(v_wt_2875_, 0);
                lean_inc(v_second_2879_);
                v_nano_2880_ = lean_ctor_get(v_wt_2875_, 1);
                lean_inc(v_nano_2880_);
                lean_dec_ref(v_wt_2875_);
                v___f_2881_ = lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_2881_, 0, v___x_2874_);
                v___x_2882_ = lean_mk_thunk(v___f_2881_);
                v___x_2883_ = lean_int_neg(v_offset_2878_);
                lean_dec(v_offset_2878_);
                v___x_2884_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
                );
                v___x_2885_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_2886_ = lean_int_mul(v_second_2879_, v___x_2885_);
                lean_dec(v_second_2879_);
                v___x_2887_ = lean_int_add(v___x_2886_, v_nano_2880_);
                lean_dec(v_nano_2880_);
                lean_dec(v___x_2886_);
                v___x_2888_ = lean_int_mul(v___x_2883_, v___x_2885_);
                lean_dec(v___x_2883_);
                v___x_2889_ = lean_int_add(v___x_2888_, v___x_2884_);
                lean_dec(v___x_2888_);
                v___x_2890_ = lean_int_add(v___x_2887_, v___x_2889_);
                lean_dec(v___x_2889_);
                lean_dec(v___x_2887_);
                v___x_2891_ = l_Std_Time_Duration_ofNanoseconds(v___x_2890_);
                lean_dec(v___x_2890_);
                if v_isShared_2863_ == 0 {
                    lean_ctor_set(v___x_2862_, 3, v_tz_2877_);
                    lean_ctor_set(v___x_2862_, 1, v___x_2891_);
                    lean_ctor_set(v___x_2862_, 0, v___x_2882_);
                    v___x_2893_ = v___x_2862_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2894_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2894_, 0, v___x_2882_);
                    lean_ctor_set(v_reuseFailAlloc_2894_, 1, v___x_2891_);
                    lean_ctor_set(v_reuseFailAlloc_2894_, 2, v_rules_2860_);
                    lean_ctor_set(v_reuseFailAlloc_2894_, 3, v_tz_2877_);
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
    mut v_dt_2900_: *mut LeanObject,
    mut v_years_2901_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2902_: *mut LeanObject = core::ptr::null_mut();
    v_res_2902_ = l_Std_Time_ZonedDateTime_addYearsRollOver(v_dt_2900_, v_years_2901_);
    lean_dec(v_years_2901_);
    return v_res_2902_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_addYearsClip(
    mut v_dt_2903_: *mut LeanObject,
    mut v_years_2904_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_2905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rules_2906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2909_: u8 = 0;
    let mut v___x_2910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_date_2911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_time_2912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2915_: u8 = 0;
    let mut v___x_2916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_wt_2921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ltt_2922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tz_2923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_offset_2924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_2925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_2926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2942_: u8 = 0;
    let mut v_isSharedCheck_2943_: u8 = 0;
    let mut v_unused_2944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2945_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_2905_ = lean_ctor_get(v_dt_2903_, 0);
                v_rules_2906_ = lean_ctor_get(v_dt_2903_, 2);
                v_isSharedCheck_2943_ = (!lean_is_exclusive(v_dt_2903_)) as u8;
                if v_isSharedCheck_2943_ == 0 {
                    v_unused_2944_ = lean_ctor_get(v_dt_2903_, 3);
                    lean_dec(v_unused_2944_);
                    v_unused_2945_ = lean_ctor_get(v_dt_2903_, 1);
                    lean_dec(v_unused_2945_);
                    v___x_2908_ = v_dt_2903_;
                    v_isShared_2909_ = v_isSharedCheck_2943_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_rules_2906_);
                    lean_inc(v_date_2905_);
                    lean_dec(v_dt_2903_);
                    v___x_2908_ = lean_box(0);
                    v_isShared_2909_ = v_isSharedCheck_2943_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2910_ = lean_thunk_get_own(v_date_2905_);
                lean_dec_ref(v_date_2905_);
                v_date_2911_ = lean_ctor_get(v___x_2910_, 0);
                v_time_2912_ = lean_ctor_get(v___x_2910_, 1);
                v_isSharedCheck_2942_ = (!lean_is_exclusive(v___x_2910_)) as u8;
                if v_isSharedCheck_2942_ == 0 {
                    v___x_2914_ = v___x_2910_;
                    v_isShared_2915_ = v_isSharedCheck_2942_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_time_2912_);
                    lean_inc(v_date_2911_);
                    lean_dec(v___x_2910_);
                    v___x_2914_ = lean_box(0);
                    v_isShared_2915_ = v_isSharedCheck_2942_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2916_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0,
                );
                v___x_2917_ = lean_int_mul(v_years_2904_, v___x_2916_);
                v___x_2918_ = l_Std_Time_PlainDate_addMonthsClip(v_date_2911_, v___x_2917_);
                lean_dec(v___x_2917_);
                if v_isShared_2915_ == 0 {
                    lean_ctor_set(v___x_2914_, 0, v___x_2918_);
                    v___x_2920_ = v___x_2914_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2941_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2941_, 0, v___x_2918_);
                    lean_ctor_set(v_reuseFailAlloc_2941_, 1, v_time_2912_);
                    v___x_2920_ = v_reuseFailAlloc_2941_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_inc_ref(v___x_2920_);
                v_wt_2921_ = l_Std_Time_PlainDateTime_toWallTime(v___x_2920_);
                lean_inc_ref(v_rules_2906_);
                v_ltt_2922_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(
                    v_rules_2906_,
                    v_wt_2921_,
                );
                v_tz_2923_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_2922_);
                lean_dec_ref(v_ltt_2922_);
                v_offset_2924_ = lean_ctor_get(v_tz_2923_, 0);
                lean_inc(v_offset_2924_);
                v_second_2925_ = lean_ctor_get(v_wt_2921_, 0);
                lean_inc(v_second_2925_);
                v_nano_2926_ = lean_ctor_get(v_wt_2921_, 1);
                lean_inc(v_nano_2926_);
                lean_dec_ref(v_wt_2921_);
                v___f_2927_ = lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_2927_, 0, v___x_2920_);
                v___x_2928_ = lean_mk_thunk(v___f_2927_);
                v___x_2929_ = lean_int_neg(v_offset_2924_);
                lean_dec(v_offset_2924_);
                v___x_2930_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
                );
                v___x_2931_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_2932_ = lean_int_mul(v_second_2925_, v___x_2931_);
                lean_dec(v_second_2925_);
                v___x_2933_ = lean_int_add(v___x_2932_, v_nano_2926_);
                lean_dec(v_nano_2926_);
                lean_dec(v___x_2932_);
                v___x_2934_ = lean_int_mul(v___x_2929_, v___x_2931_);
                lean_dec(v___x_2929_);
                v___x_2935_ = lean_int_add(v___x_2934_, v___x_2930_);
                lean_dec(v___x_2934_);
                v___x_2936_ = lean_int_add(v___x_2933_, v___x_2935_);
                lean_dec(v___x_2935_);
                lean_dec(v___x_2933_);
                v___x_2937_ = l_Std_Time_Duration_ofNanoseconds(v___x_2936_);
                lean_dec(v___x_2936_);
                if v_isShared_2909_ == 0 {
                    lean_ctor_set(v___x_2908_, 3, v_tz_2923_);
                    lean_ctor_set(v___x_2908_, 1, v___x_2937_);
                    lean_ctor_set(v___x_2908_, 0, v___x_2928_);
                    v___x_2939_ = v___x_2908_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2940_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2940_, 0, v___x_2928_);
                    lean_ctor_set(v_reuseFailAlloc_2940_, 1, v___x_2937_);
                    lean_ctor_set(v_reuseFailAlloc_2940_, 2, v_rules_2906_);
                    lean_ctor_set(v_reuseFailAlloc_2940_, 3, v_tz_2923_);
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
    mut v_dt_2946_: *mut LeanObject,
    mut v_years_2947_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2948_: *mut LeanObject = core::ptr::null_mut();
    v_res_2948_ = l_Std_Time_ZonedDateTime_addYearsClip(v_dt_2946_, v_years_2947_);
    lean_dec(v_years_2947_);
    return v_res_2948_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_subYearsClip(
    mut v_dt_2949_: *mut LeanObject,
    mut v_years_2950_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_2951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rules_2952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2955_: u8 = 0;
    let mut v___x_2956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_date_2957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_time_2958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2961_: u8 = 0;
    let mut v___x_2962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_wt_2968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ltt_2969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tz_2970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_offset_2971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_2972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_2973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2989_: u8 = 0;
    let mut v_isSharedCheck_2990_: u8 = 0;
    let mut v_unused_2991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2992_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_2951_ = lean_ctor_get(v_dt_2949_, 0);
                v_rules_2952_ = lean_ctor_get(v_dt_2949_, 2);
                v_isSharedCheck_2990_ = (!lean_is_exclusive(v_dt_2949_)) as u8;
                if v_isSharedCheck_2990_ == 0 {
                    v_unused_2991_ = lean_ctor_get(v_dt_2949_, 3);
                    lean_dec(v_unused_2991_);
                    v_unused_2992_ = lean_ctor_get(v_dt_2949_, 1);
                    lean_dec(v_unused_2992_);
                    v___x_2954_ = v_dt_2949_;
                    v_isShared_2955_ = v_isSharedCheck_2990_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_rules_2952_);
                    lean_inc(v_date_2951_);
                    lean_dec(v_dt_2949_);
                    v___x_2954_ = lean_box(0);
                    v_isShared_2955_ = v_isSharedCheck_2990_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2956_ = lean_thunk_get_own(v_date_2951_);
                lean_dec_ref(v_date_2951_);
                v_date_2957_ = lean_ctor_get(v___x_2956_, 0);
                v_time_2958_ = lean_ctor_get(v___x_2956_, 1);
                v_isSharedCheck_2989_ = (!lean_is_exclusive(v___x_2956_)) as u8;
                if v_isSharedCheck_2989_ == 0 {
                    v___x_2960_ = v___x_2956_;
                    v_isShared_2961_ = v_isSharedCheck_2989_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_time_2958_);
                    lean_inc(v_date_2957_);
                    lean_dec(v___x_2956_);
                    v___x_2960_ = lean_box(0);
                    v_isShared_2961_ = v_isSharedCheck_2989_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2962_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0,
                );
                v___x_2963_ = lean_int_mul(v_years_2950_, v___x_2962_);
                v___x_2964_ = lean_int_neg(v___x_2963_);
                lean_dec(v___x_2963_);
                v___x_2965_ = l_Std_Time_PlainDate_addMonthsClip(v_date_2957_, v___x_2964_);
                lean_dec(v___x_2964_);
                if v_isShared_2961_ == 0 {
                    lean_ctor_set(v___x_2960_, 0, v___x_2965_);
                    v___x_2967_ = v___x_2960_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2988_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2988_, 0, v___x_2965_);
                    lean_ctor_set(v_reuseFailAlloc_2988_, 1, v_time_2958_);
                    v___x_2967_ = v_reuseFailAlloc_2988_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_inc_ref(v___x_2967_);
                v_wt_2968_ = l_Std_Time_PlainDateTime_toWallTime(v___x_2967_);
                lean_inc_ref(v_rules_2952_);
                v_ltt_2969_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(
                    v_rules_2952_,
                    v_wt_2968_,
                );
                v_tz_2970_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_2969_);
                lean_dec_ref(v_ltt_2969_);
                v_offset_2971_ = lean_ctor_get(v_tz_2970_, 0);
                lean_inc(v_offset_2971_);
                v_second_2972_ = lean_ctor_get(v_wt_2968_, 0);
                lean_inc(v_second_2972_);
                v_nano_2973_ = lean_ctor_get(v_wt_2968_, 1);
                lean_inc(v_nano_2973_);
                lean_dec_ref(v_wt_2968_);
                v___f_2974_ = lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_2974_, 0, v___x_2967_);
                v___x_2975_ = lean_mk_thunk(v___f_2974_);
                v___x_2976_ = lean_int_neg(v_offset_2971_);
                lean_dec(v_offset_2971_);
                v___x_2977_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
                );
                v___x_2978_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_2979_ = lean_int_mul(v_second_2972_, v___x_2978_);
                lean_dec(v_second_2972_);
                v___x_2980_ = lean_int_add(v___x_2979_, v_nano_2973_);
                lean_dec(v_nano_2973_);
                lean_dec(v___x_2979_);
                v___x_2981_ = lean_int_mul(v___x_2976_, v___x_2978_);
                lean_dec(v___x_2976_);
                v___x_2982_ = lean_int_add(v___x_2981_, v___x_2977_);
                lean_dec(v___x_2981_);
                v___x_2983_ = lean_int_add(v___x_2980_, v___x_2982_);
                lean_dec(v___x_2982_);
                lean_dec(v___x_2980_);
                v___x_2984_ = l_Std_Time_Duration_ofNanoseconds(v___x_2983_);
                lean_dec(v___x_2983_);
                if v_isShared_2955_ == 0 {
                    lean_ctor_set(v___x_2954_, 3, v_tz_2970_);
                    lean_ctor_set(v___x_2954_, 1, v___x_2984_);
                    lean_ctor_set(v___x_2954_, 0, v___x_2975_);
                    v___x_2986_ = v___x_2954_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2987_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2987_, 0, v___x_2975_);
                    lean_ctor_set(v_reuseFailAlloc_2987_, 1, v___x_2984_);
                    lean_ctor_set(v_reuseFailAlloc_2987_, 2, v_rules_2952_);
                    lean_ctor_set(v_reuseFailAlloc_2987_, 3, v_tz_2970_);
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
    mut v_dt_2993_: *mut LeanObject,
    mut v_years_2994_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2995_: *mut LeanObject = core::ptr::null_mut();
    v_res_2995_ = l_Std_Time_ZonedDateTime_subYearsClip(v_dt_2993_, v_years_2994_);
    lean_dec(v_years_2994_);
    return v_res_2995_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_subYearsRollOver(
    mut v_dt_2996_: *mut LeanObject,
    mut v_years_2997_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_2998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rules_2999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3002_: u8 = 0;
    let mut v___x_3003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_date_3004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_time_3005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3008_: u8 = 0;
    let mut v___x_3009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_wt_3015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ltt_3016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tz_3017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_offset_3018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_3019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_3020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3036_: u8 = 0;
    let mut v_isSharedCheck_3037_: u8 = 0;
    let mut v_unused_3038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3039_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_2998_ = lean_ctor_get(v_dt_2996_, 0);
                v_rules_2999_ = lean_ctor_get(v_dt_2996_, 2);
                v_isSharedCheck_3037_ = (!lean_is_exclusive(v_dt_2996_)) as u8;
                if v_isSharedCheck_3037_ == 0 {
                    v_unused_3038_ = lean_ctor_get(v_dt_2996_, 3);
                    lean_dec(v_unused_3038_);
                    v_unused_3039_ = lean_ctor_get(v_dt_2996_, 1);
                    lean_dec(v_unused_3039_);
                    v___x_3001_ = v_dt_2996_;
                    v_isShared_3002_ = v_isSharedCheck_3037_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_rules_2999_);
                    lean_inc(v_date_2998_);
                    lean_dec(v_dt_2996_);
                    v___x_3001_ = lean_box(0);
                    v_isShared_3002_ = v_isSharedCheck_3037_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3003_ = lean_thunk_get_own(v_date_2998_);
                lean_dec_ref(v_date_2998_);
                v_date_3004_ = lean_ctor_get(v___x_3003_, 0);
                v_time_3005_ = lean_ctor_get(v___x_3003_, 1);
                v_isSharedCheck_3036_ = (!lean_is_exclusive(v___x_3003_)) as u8;
                if v_isSharedCheck_3036_ == 0 {
                    v___x_3007_ = v___x_3003_;
                    v_isShared_3008_ = v_isSharedCheck_3036_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_time_3005_);
                    lean_inc(v_date_3004_);
                    lean_dec(v___x_3003_);
                    v___x_3007_ = lean_box(0);
                    v_isShared_3008_ = v_isSharedCheck_3036_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3009_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0,
                );
                v___x_3010_ = lean_int_mul(v_years_2997_, v___x_3009_);
                v___x_3011_ = lean_int_neg(v___x_3010_);
                lean_dec(v___x_3010_);
                v___x_3012_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_3004_, v___x_3011_);
                lean_dec(v___x_3011_);
                if v_isShared_3008_ == 0 {
                    lean_ctor_set(v___x_3007_, 0, v___x_3012_);
                    v___x_3014_ = v___x_3007_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3035_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3035_, 0, v___x_3012_);
                    lean_ctor_set(v_reuseFailAlloc_3035_, 1, v_time_3005_);
                    v___x_3014_ = v_reuseFailAlloc_3035_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_inc_ref(v___x_3014_);
                v_wt_3015_ = l_Std_Time_PlainDateTime_toWallTime(v___x_3014_);
                lean_inc_ref(v_rules_2999_);
                v_ltt_3016_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(
                    v_rules_2999_,
                    v_wt_3015_,
                );
                v_tz_3017_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_3016_);
                lean_dec_ref(v_ltt_3016_);
                v_offset_3018_ = lean_ctor_get(v_tz_3017_, 0);
                lean_inc(v_offset_3018_);
                v_second_3019_ = lean_ctor_get(v_wt_3015_, 0);
                lean_inc(v_second_3019_);
                v_nano_3020_ = lean_ctor_get(v_wt_3015_, 1);
                lean_inc(v_nano_3020_);
                lean_dec_ref(v_wt_3015_);
                v___f_3021_ = lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_3021_, 0, v___x_3014_);
                v___x_3022_ = lean_mk_thunk(v___f_3021_);
                v___x_3023_ = lean_int_neg(v_offset_3018_);
                lean_dec(v_offset_3018_);
                v___x_3024_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
                );
                v___x_3025_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3026_ = lean_int_mul(v_second_3019_, v___x_3025_);
                lean_dec(v_second_3019_);
                v___x_3027_ = lean_int_add(v___x_3026_, v_nano_3020_);
                lean_dec(v_nano_3020_);
                lean_dec(v___x_3026_);
                v___x_3028_ = lean_int_mul(v___x_3023_, v___x_3025_);
                lean_dec(v___x_3023_);
                v___x_3029_ = lean_int_add(v___x_3028_, v___x_3024_);
                lean_dec(v___x_3028_);
                v___x_3030_ = lean_int_add(v___x_3027_, v___x_3029_);
                lean_dec(v___x_3029_);
                lean_dec(v___x_3027_);
                v___x_3031_ = l_Std_Time_Duration_ofNanoseconds(v___x_3030_);
                lean_dec(v___x_3030_);
                if v_isShared_3002_ == 0 {
                    lean_ctor_set(v___x_3001_, 3, v_tz_3017_);
                    lean_ctor_set(v___x_3001_, 1, v___x_3031_);
                    lean_ctor_set(v___x_3001_, 0, v___x_3022_);
                    v___x_3033_ = v___x_3001_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3034_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3034_, 0, v___x_3022_);
                    lean_ctor_set(v_reuseFailAlloc_3034_, 1, v___x_3031_);
                    lean_ctor_set(v_reuseFailAlloc_3034_, 2, v_rules_2999_);
                    lean_ctor_set(v_reuseFailAlloc_3034_, 3, v_tz_3017_);
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
    mut v_dt_3040_: *mut LeanObject,
    mut v_years_3041_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3042_: *mut LeanObject = core::ptr::null_mut();
    v_res_3042_ = l_Std_Time_ZonedDateTime_subYearsRollOver(v_dt_3040_, v_years_3041_);
    lean_dec(v_years_3041_);
    return v_res_3042_;
}
pub unsafe fn _init_l_Std_Time_ZonedDateTime_addHours___closed__0() -> *mut LeanObject {
    let mut v___x_3043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: *mut LeanObject = core::ptr::null_mut();
    v___x_3043_ = lean_unsigned_to_nat(3600);
    v___x_3044_ = lean_nat_to_int(v___x_3043_);
    return v___x_3044_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_addHours(
    mut v_dt_3045_: *mut LeanObject,
    mut v_hours_3046_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_timestamp_3047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rules_3048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3051_: u8 = 0;
    let mut v_second_3052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_3053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initialLocalTimeType_3054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_transitions_3055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3076_: u8 = 0;
    let mut v_unused_3077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3078_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_3047_ = lean_ctor_get(v_dt_3045_, 1);
                v_rules_3048_ = lean_ctor_get(v_dt_3045_, 2);
                v_isSharedCheck_3076_ = (!lean_is_exclusive(v_dt_3045_)) as u8;
                if v_isSharedCheck_3076_ == 0 {
                    v_unused_3077_ = lean_ctor_get(v_dt_3045_, 3);
                    lean_dec(v_unused_3077_);
                    v_unused_3078_ = lean_ctor_get(v_dt_3045_, 0);
                    lean_dec(v_unused_3078_);
                    v___x_3050_ = v_dt_3045_;
                    v_isShared_3051_ = v_isSharedCheck_3076_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_rules_3048_);
                    lean_inc(v_timestamp_3047_);
                    lean_dec(v_dt_3045_);
                    v___x_3050_ = lean_box(0);
                    v_isShared_3051_ = v_isSharedCheck_3076_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_second_3052_ = lean_ctor_get(v_timestamp_3047_, 0);
                lean_inc(v_second_3052_);
                v_nano_3053_ = lean_ctor_get(v_timestamp_3047_, 1);
                lean_inc(v_nano_3053_);
                lean_dec_ref(v_timestamp_3047_);
                v_initialLocalTimeType_3054_ = lean_ctor_get(v_rules_3048_, 0);
                v_transitions_3055_ = lean_ctor_get(v_rules_3048_, 1);
                v___x_3056_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_addHours___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_addHours___closed__0_once),
                    _init_l_Std_Time_ZonedDateTime_addHours___closed__0,
                );
                v___x_3057_ = lean_int_mul(v_hours_3046_, v___x_3056_);
                v___x_3058_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0,
                );
                v___x_3059_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3060_ = lean_int_mul(v_second_3052_, v___x_3059_);
                lean_dec(v_second_3052_);
                v___x_3061_ = lean_int_add(v___x_3060_, v_nano_3053_);
                lean_dec(v_nano_3053_);
                lean_dec(v___x_3060_);
                v___x_3062_ = lean_int_mul(v___x_3057_, v___x_3059_);
                lean_dec(v___x_3057_);
                v___x_3063_ = lean_int_add(v___x_3062_, v___x_3058_);
                lean_dec(v___x_3062_);
                v___x_3064_ = lean_int_add(v___x_3061_, v___x_3063_);
                lean_dec(v___x_3063_);
                lean_dec(v___x_3061_);
                v___x_3065_ = l_Std_Time_Duration_ofNanoseconds(v___x_3064_);
                lean_dec(v___x_3064_);
                v___x_3073_ =
                    l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_3055_, v___x_3065_);
                if lean_obj_tag(v___x_3073_) == 0 {
                    lean_dec_ref_known(v___x_3073_, 1);
                    v___x_3074_ =
                        l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_3054_);
                    v___y_3067_ = v___x_3074_;
                    state = 2;
                    continue;
                } else {
                    v_a_3075_ = lean_ctor_get(v___x_3073_, 0);
                    lean_inc(v_a_3075_);
                    lean_dec_ref_known(v___x_3073_, 1);
                    v___y_3067_ = v_a_3075_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc_ref(v___x_3065_);
                lean_inc_ref(v___y_3067_);
                v___f_3068_ = lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addDays___lam__0___boxed as *mut core::ffi::c_void,
                    5,
                    4,
                );
                lean_closure_set(v___f_3068_, 0, v___y_3067_);
                lean_closure_set(v___f_3068_, 1, v___x_3065_);
                lean_closure_set(v___f_3068_, 2, v___x_3059_);
                lean_closure_set(v___f_3068_, 3, v___x_3058_);
                v___x_3069_ = lean_mk_thunk(v___f_3068_);
                if v_isShared_3051_ == 0 {
                    lean_ctor_set(v___x_3050_, 3, v___y_3067_);
                    lean_ctor_set(v___x_3050_, 1, v___x_3065_);
                    lean_ctor_set(v___x_3050_, 0, v___x_3069_);
                    v___x_3071_ = v___x_3050_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3072_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3072_, 0, v___x_3069_);
                    lean_ctor_set(v_reuseFailAlloc_3072_, 1, v___x_3065_);
                    lean_ctor_set(v_reuseFailAlloc_3072_, 2, v_rules_3048_);
                    lean_ctor_set(v_reuseFailAlloc_3072_, 3, v___y_3067_);
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
    mut v_dt_3079_: *mut LeanObject,
    mut v_hours_3080_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3081_: *mut LeanObject = core::ptr::null_mut();
    v_res_3081_ = l_Std_Time_ZonedDateTime_addHours(v_dt_3079_, v_hours_3080_);
    lean_dec(v_hours_3080_);
    return v_res_3081_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_subHours(
    mut v_dt_3082_: *mut LeanObject,
    mut v_hours_3083_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_timestamp_3084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rules_3085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3088_: u8 = 0;
    let mut v_second_3089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_3090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initialLocalTimeType_3091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_transitions_3092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3115_: u8 = 0;
    let mut v_unused_3116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3117_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_3084_ = lean_ctor_get(v_dt_3082_, 1);
                v_rules_3085_ = lean_ctor_get(v_dt_3082_, 2);
                v_isSharedCheck_3115_ = (!lean_is_exclusive(v_dt_3082_)) as u8;
                if v_isSharedCheck_3115_ == 0 {
                    v_unused_3116_ = lean_ctor_get(v_dt_3082_, 3);
                    lean_dec(v_unused_3116_);
                    v_unused_3117_ = lean_ctor_get(v_dt_3082_, 0);
                    lean_dec(v_unused_3117_);
                    v___x_3087_ = v_dt_3082_;
                    v_isShared_3088_ = v_isSharedCheck_3115_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_rules_3085_);
                    lean_inc(v_timestamp_3084_);
                    lean_dec(v_dt_3082_);
                    v___x_3087_ = lean_box(0);
                    v_isShared_3088_ = v_isSharedCheck_3115_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_second_3089_ = lean_ctor_get(v_timestamp_3084_, 0);
                lean_inc(v_second_3089_);
                v_nano_3090_ = lean_ctor_get(v_timestamp_3084_, 1);
                lean_inc(v_nano_3090_);
                lean_dec_ref(v_timestamp_3084_);
                v_initialLocalTimeType_3091_ = lean_ctor_get(v_rules_3085_, 0);
                v_transitions_3092_ = lean_ctor_get(v_rules_3085_, 1);
                v___x_3093_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_addHours___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_addHours___closed__0_once),
                    _init_l_Std_Time_ZonedDateTime_addHours___closed__0,
                );
                v___x_3094_ = lean_int_mul(v_hours_3083_, v___x_3093_);
                v___x_3095_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0,
                );
                v___x_3096_ = lean_int_neg(v___x_3094_);
                lean_dec(v___x_3094_);
                v___x_3097_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
                );
                v___x_3098_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3099_ = lean_int_mul(v_second_3089_, v___x_3098_);
                lean_dec(v_second_3089_);
                v___x_3100_ = lean_int_add(v___x_3099_, v_nano_3090_);
                lean_dec(v_nano_3090_);
                lean_dec(v___x_3099_);
                v___x_3101_ = lean_int_mul(v___x_3096_, v___x_3098_);
                lean_dec(v___x_3096_);
                v___x_3102_ = lean_int_add(v___x_3101_, v___x_3097_);
                lean_dec(v___x_3101_);
                v___x_3103_ = lean_int_add(v___x_3100_, v___x_3102_);
                lean_dec(v___x_3102_);
                lean_dec(v___x_3100_);
                v___x_3104_ = l_Std_Time_Duration_ofNanoseconds(v___x_3103_);
                lean_dec(v___x_3103_);
                v___x_3112_ =
                    l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_3092_, v___x_3104_);
                if lean_obj_tag(v___x_3112_) == 0 {
                    lean_dec_ref_known(v___x_3112_, 1);
                    v___x_3113_ =
                        l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_3091_);
                    v___y_3106_ = v___x_3113_;
                    state = 2;
                    continue;
                } else {
                    v_a_3114_ = lean_ctor_get(v___x_3112_, 0);
                    lean_inc(v_a_3114_);
                    lean_dec_ref_known(v___x_3112_, 1);
                    v___y_3106_ = v_a_3114_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc_ref(v___x_3104_);
                lean_inc_ref(v___y_3106_);
                v___f_3107_ = lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addDays___lam__0___boxed as *mut core::ffi::c_void,
                    5,
                    4,
                );
                lean_closure_set(v___f_3107_, 0, v___y_3106_);
                lean_closure_set(v___f_3107_, 1, v___x_3104_);
                lean_closure_set(v___f_3107_, 2, v___x_3098_);
                lean_closure_set(v___f_3107_, 3, v___x_3095_);
                v___x_3108_ = lean_mk_thunk(v___f_3107_);
                if v_isShared_3088_ == 0 {
                    lean_ctor_set(v___x_3087_, 3, v___y_3106_);
                    lean_ctor_set(v___x_3087_, 1, v___x_3104_);
                    lean_ctor_set(v___x_3087_, 0, v___x_3108_);
                    v___x_3110_ = v___x_3087_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3111_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3111_, 0, v___x_3108_);
                    lean_ctor_set(v_reuseFailAlloc_3111_, 1, v___x_3104_);
                    lean_ctor_set(v_reuseFailAlloc_3111_, 2, v_rules_3085_);
                    lean_ctor_set(v_reuseFailAlloc_3111_, 3, v___y_3106_);
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
    mut v_dt_3118_: *mut LeanObject,
    mut v_hours_3119_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3120_: *mut LeanObject = core::ptr::null_mut();
    v_res_3120_ = l_Std_Time_ZonedDateTime_subHours(v_dt_3118_, v_hours_3119_);
    lean_dec(v_hours_3119_);
    return v_res_3120_;
}
pub unsafe fn _init_l_Std_Time_ZonedDateTime_addMinutes___closed__0() -> *mut LeanObject {
    let mut v___x_3121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3122_: *mut LeanObject = core::ptr::null_mut();
    v___x_3121_ = lean_unsigned_to_nat(60);
    v___x_3122_ = lean_nat_to_int(v___x_3121_);
    return v___x_3122_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_addMinutes(
    mut v_dt_3123_: *mut LeanObject,
    mut v_minutes_3124_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_timestamp_3125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rules_3126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3129_: u8 = 0;
    let mut v_second_3130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_3131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initialLocalTimeType_3132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_transitions_3133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3154_: u8 = 0;
    let mut v_unused_3155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3156_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_3125_ = lean_ctor_get(v_dt_3123_, 1);
                v_rules_3126_ = lean_ctor_get(v_dt_3123_, 2);
                v_isSharedCheck_3154_ = (!lean_is_exclusive(v_dt_3123_)) as u8;
                if v_isSharedCheck_3154_ == 0 {
                    v_unused_3155_ = lean_ctor_get(v_dt_3123_, 3);
                    lean_dec(v_unused_3155_);
                    v_unused_3156_ = lean_ctor_get(v_dt_3123_, 0);
                    lean_dec(v_unused_3156_);
                    v___x_3128_ = v_dt_3123_;
                    v_isShared_3129_ = v_isSharedCheck_3154_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_rules_3126_);
                    lean_inc(v_timestamp_3125_);
                    lean_dec(v_dt_3123_);
                    v___x_3128_ = lean_box(0);
                    v_isShared_3129_ = v_isSharedCheck_3154_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_second_3130_ = lean_ctor_get(v_timestamp_3125_, 0);
                lean_inc(v_second_3130_);
                v_nano_3131_ = lean_ctor_get(v_timestamp_3125_, 1);
                lean_inc(v_nano_3131_);
                lean_dec_ref(v_timestamp_3125_);
                v_initialLocalTimeType_3132_ = lean_ctor_get(v_rules_3126_, 0);
                v_transitions_3133_ = lean_ctor_get(v_rules_3126_, 1);
                v___x_3134_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_addMinutes___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_addMinutes___closed__0_once),
                    _init_l_Std_Time_ZonedDateTime_addMinutes___closed__0,
                );
                v___x_3135_ = lean_int_mul(v_minutes_3124_, v___x_3134_);
                v___x_3136_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0,
                );
                v___x_3137_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3138_ = lean_int_mul(v_second_3130_, v___x_3137_);
                lean_dec(v_second_3130_);
                v___x_3139_ = lean_int_add(v___x_3138_, v_nano_3131_);
                lean_dec(v_nano_3131_);
                lean_dec(v___x_3138_);
                v___x_3140_ = lean_int_mul(v___x_3135_, v___x_3137_);
                lean_dec(v___x_3135_);
                v___x_3141_ = lean_int_add(v___x_3140_, v___x_3136_);
                lean_dec(v___x_3140_);
                v___x_3142_ = lean_int_add(v___x_3139_, v___x_3141_);
                lean_dec(v___x_3141_);
                lean_dec(v___x_3139_);
                v___x_3143_ = l_Std_Time_Duration_ofNanoseconds(v___x_3142_);
                lean_dec(v___x_3142_);
                v___x_3151_ =
                    l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_3133_, v___x_3143_);
                if lean_obj_tag(v___x_3151_) == 0 {
                    lean_dec_ref_known(v___x_3151_, 1);
                    v___x_3152_ =
                        l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_3132_);
                    v___y_3145_ = v___x_3152_;
                    state = 2;
                    continue;
                } else {
                    v_a_3153_ = lean_ctor_get(v___x_3151_, 0);
                    lean_inc(v_a_3153_);
                    lean_dec_ref_known(v___x_3151_, 1);
                    v___y_3145_ = v_a_3153_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc_ref(v___x_3143_);
                lean_inc_ref(v___y_3145_);
                v___f_3146_ = lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addDays___lam__0___boxed as *mut core::ffi::c_void,
                    5,
                    4,
                );
                lean_closure_set(v___f_3146_, 0, v___y_3145_);
                lean_closure_set(v___f_3146_, 1, v___x_3143_);
                lean_closure_set(v___f_3146_, 2, v___x_3137_);
                lean_closure_set(v___f_3146_, 3, v___x_3136_);
                v___x_3147_ = lean_mk_thunk(v___f_3146_);
                if v_isShared_3129_ == 0 {
                    lean_ctor_set(v___x_3128_, 3, v___y_3145_);
                    lean_ctor_set(v___x_3128_, 1, v___x_3143_);
                    lean_ctor_set(v___x_3128_, 0, v___x_3147_);
                    v___x_3149_ = v___x_3128_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3150_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3150_, 0, v___x_3147_);
                    lean_ctor_set(v_reuseFailAlloc_3150_, 1, v___x_3143_);
                    lean_ctor_set(v_reuseFailAlloc_3150_, 2, v_rules_3126_);
                    lean_ctor_set(v_reuseFailAlloc_3150_, 3, v___y_3145_);
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
    mut v_dt_3157_: *mut LeanObject,
    mut v_minutes_3158_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3159_: *mut LeanObject = core::ptr::null_mut();
    v_res_3159_ = l_Std_Time_ZonedDateTime_addMinutes(v_dt_3157_, v_minutes_3158_);
    lean_dec(v_minutes_3158_);
    return v_res_3159_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_subMinutes(
    mut v_dt_3160_: *mut LeanObject,
    mut v_minutes_3161_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_timestamp_3162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rules_3163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3166_: u8 = 0;
    let mut v_second_3167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_3168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initialLocalTimeType_3169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_transitions_3170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3193_: u8 = 0;
    let mut v_unused_3194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3195_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_3162_ = lean_ctor_get(v_dt_3160_, 1);
                v_rules_3163_ = lean_ctor_get(v_dt_3160_, 2);
                v_isSharedCheck_3193_ = (!lean_is_exclusive(v_dt_3160_)) as u8;
                if v_isSharedCheck_3193_ == 0 {
                    v_unused_3194_ = lean_ctor_get(v_dt_3160_, 3);
                    lean_dec(v_unused_3194_);
                    v_unused_3195_ = lean_ctor_get(v_dt_3160_, 0);
                    lean_dec(v_unused_3195_);
                    v___x_3165_ = v_dt_3160_;
                    v_isShared_3166_ = v_isSharedCheck_3193_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_rules_3163_);
                    lean_inc(v_timestamp_3162_);
                    lean_dec(v_dt_3160_);
                    v___x_3165_ = lean_box(0);
                    v_isShared_3166_ = v_isSharedCheck_3193_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_second_3167_ = lean_ctor_get(v_timestamp_3162_, 0);
                lean_inc(v_second_3167_);
                v_nano_3168_ = lean_ctor_get(v_timestamp_3162_, 1);
                lean_inc(v_nano_3168_);
                lean_dec_ref(v_timestamp_3162_);
                v_initialLocalTimeType_3169_ = lean_ctor_get(v_rules_3163_, 0);
                v_transitions_3170_ = lean_ctor_get(v_rules_3163_, 1);
                v___x_3171_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_addMinutes___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_addMinutes___closed__0_once),
                    _init_l_Std_Time_ZonedDateTime_addMinutes___closed__0,
                );
                v___x_3172_ = lean_int_mul(v_minutes_3161_, v___x_3171_);
                v___x_3173_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0,
                );
                v___x_3174_ = lean_int_neg(v___x_3172_);
                lean_dec(v___x_3172_);
                v___x_3175_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
                );
                v___x_3176_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3177_ = lean_int_mul(v_second_3167_, v___x_3176_);
                lean_dec(v_second_3167_);
                v___x_3178_ = lean_int_add(v___x_3177_, v_nano_3168_);
                lean_dec(v_nano_3168_);
                lean_dec(v___x_3177_);
                v___x_3179_ = lean_int_mul(v___x_3174_, v___x_3176_);
                lean_dec(v___x_3174_);
                v___x_3180_ = lean_int_add(v___x_3179_, v___x_3175_);
                lean_dec(v___x_3179_);
                v___x_3181_ = lean_int_add(v___x_3178_, v___x_3180_);
                lean_dec(v___x_3180_);
                lean_dec(v___x_3178_);
                v___x_3182_ = l_Std_Time_Duration_ofNanoseconds(v___x_3181_);
                lean_dec(v___x_3181_);
                v___x_3190_ =
                    l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_3170_, v___x_3182_);
                if lean_obj_tag(v___x_3190_) == 0 {
                    lean_dec_ref_known(v___x_3190_, 1);
                    v___x_3191_ =
                        l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_3169_);
                    v___y_3184_ = v___x_3191_;
                    state = 2;
                    continue;
                } else {
                    v_a_3192_ = lean_ctor_get(v___x_3190_, 0);
                    lean_inc(v_a_3192_);
                    lean_dec_ref_known(v___x_3190_, 1);
                    v___y_3184_ = v_a_3192_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc_ref(v___x_3182_);
                lean_inc_ref(v___y_3184_);
                v___f_3185_ = lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addDays___lam__0___boxed as *mut core::ffi::c_void,
                    5,
                    4,
                );
                lean_closure_set(v___f_3185_, 0, v___y_3184_);
                lean_closure_set(v___f_3185_, 1, v___x_3182_);
                lean_closure_set(v___f_3185_, 2, v___x_3176_);
                lean_closure_set(v___f_3185_, 3, v___x_3173_);
                v___x_3186_ = lean_mk_thunk(v___f_3185_);
                if v_isShared_3166_ == 0 {
                    lean_ctor_set(v___x_3165_, 3, v___y_3184_);
                    lean_ctor_set(v___x_3165_, 1, v___x_3182_);
                    lean_ctor_set(v___x_3165_, 0, v___x_3186_);
                    v___x_3188_ = v___x_3165_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3189_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3189_, 0, v___x_3186_);
                    lean_ctor_set(v_reuseFailAlloc_3189_, 1, v___x_3182_);
                    lean_ctor_set(v_reuseFailAlloc_3189_, 2, v_rules_3163_);
                    lean_ctor_set(v_reuseFailAlloc_3189_, 3, v___y_3184_);
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
    mut v_dt_3196_: *mut LeanObject,
    mut v_minutes_3197_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3198_: *mut LeanObject = core::ptr::null_mut();
    v_res_3198_ = l_Std_Time_ZonedDateTime_subMinutes(v_dt_3196_, v_minutes_3197_);
    lean_dec(v_minutes_3197_);
    return v_res_3198_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_addMilliseconds___lam__0(
    mut v___y_3199_: *mut LeanObject,
    mut v___x_3200_: *mut LeanObject,
    mut v___x_3201_: *mut LeanObject,
    mut v_x_3202_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_offset_3203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_3204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_3205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut LeanObject = core::ptr::null_mut();
    v_offset_3203_ = lean_ctor_get(v___y_3199_, 0);
    v_second_3204_ = lean_ctor_get(v___x_3200_, 0);
    v_nano_3205_ = lean_ctor_get(v___x_3200_, 1);
    v___x_3206_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once),
        _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0,
    );
    v___x_3207_ = lean_int_mul(v_second_3204_, v___x_3201_);
    v___x_3208_ = lean_int_add(v___x_3207_, v_nano_3205_);
    lean_dec(v___x_3207_);
    v___x_3209_ = lean_int_mul(v_offset_3203_, v___x_3201_);
    v___x_3210_ = lean_int_add(v___x_3209_, v___x_3206_);
    lean_dec(v___x_3209_);
    v___x_3211_ = lean_int_add(v___x_3208_, v___x_3210_);
    lean_dec(v___x_3210_);
    lean_dec(v___x_3208_);
    v___x_3212_ = l_Std_Time_Duration_ofNanoseconds(v___x_3211_);
    lean_dec(v___x_3211_);
    v___x_3213_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_3212_);
    return v___x_3213_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_addMilliseconds___lam__0___boxed(
    mut v___y_3214_: *mut LeanObject,
    mut v___x_3215_: *mut LeanObject,
    mut v___x_3216_: *mut LeanObject,
    mut v_x_3217_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3218_: *mut LeanObject = core::ptr::null_mut();
    v_res_3218_ = l_Std_Time_ZonedDateTime_addMilliseconds___lam__0(
        v___y_3214_,
        v___x_3215_,
        v___x_3216_,
        v_x_3217_,
    );
    lean_dec(v___x_3216_);
    lean_dec_ref(v___x_3215_);
    lean_dec_ref(v___y_3214_);
    return v_res_3218_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_addMilliseconds(
    mut v_dt_3219_: *mut LeanObject,
    mut v_milliseconds_3220_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_timestamp_3221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rules_3222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3225_: u8 = 0;
    let mut v_second_3226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_3227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_3231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_3232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initialLocalTimeType_3233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_transitions_3234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3252_: u8 = 0;
    let mut v_unused_3253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3254_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_3221_ = lean_ctor_get(v_dt_3219_, 1);
                v_rules_3222_ = lean_ctor_get(v_dt_3219_, 2);
                v_isSharedCheck_3252_ = (!lean_is_exclusive(v_dt_3219_)) as u8;
                if v_isSharedCheck_3252_ == 0 {
                    v_unused_3253_ = lean_ctor_get(v_dt_3219_, 3);
                    lean_dec(v_unused_3253_);
                    v_unused_3254_ = lean_ctor_get(v_dt_3219_, 0);
                    lean_dec(v_unused_3254_);
                    v___x_3224_ = v_dt_3219_;
                    v_isShared_3225_ = v_isSharedCheck_3252_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_rules_3222_);
                    lean_inc(v_timestamp_3221_);
                    lean_dec(v_dt_3219_);
                    v___x_3224_ = lean_box(0);
                    v_isShared_3225_ = v_isSharedCheck_3252_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_second_3226_ = lean_ctor_get(v_timestamp_3221_, 0);
                lean_inc(v_second_3226_);
                v_nano_3227_ = lean_ctor_get(v_timestamp_3221_, 1);
                lean_inc(v_nano_3227_);
                lean_dec_ref(v_timestamp_3221_);
                v___x_3228_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_millisecond___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_millisecond___closed__0_once),
                    _init_l_Std_Time_ZonedDateTime_millisecond___closed__0,
                );
                v___x_3229_ = lean_int_mul(v_milliseconds_3220_, v___x_3228_);
                v___x_3230_ = l_Std_Time_Duration_ofNanoseconds(v___x_3229_);
                lean_dec(v___x_3229_);
                v_second_3231_ = lean_ctor_get(v___x_3230_, 0);
                lean_inc(v_second_3231_);
                v_nano_3232_ = lean_ctor_get(v___x_3230_, 1);
                lean_inc(v_nano_3232_);
                lean_dec_ref(v___x_3230_);
                v_initialLocalTimeType_3233_ = lean_ctor_get(v_rules_3222_, 0);
                v_transitions_3234_ = lean_ctor_get(v_rules_3222_, 1);
                v___x_3235_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3236_ = lean_int_mul(v_second_3226_, v___x_3235_);
                lean_dec(v_second_3226_);
                v___x_3237_ = lean_int_add(v___x_3236_, v_nano_3227_);
                lean_dec(v_nano_3227_);
                lean_dec(v___x_3236_);
                v___x_3238_ = lean_int_mul(v_second_3231_, v___x_3235_);
                lean_dec(v_second_3231_);
                v___x_3239_ = lean_int_add(v___x_3238_, v_nano_3232_);
                lean_dec(v_nano_3232_);
                lean_dec(v___x_3238_);
                v___x_3240_ = lean_int_add(v___x_3237_, v___x_3239_);
                lean_dec(v___x_3239_);
                lean_dec(v___x_3237_);
                v___x_3241_ = l_Std_Time_Duration_ofNanoseconds(v___x_3240_);
                lean_dec(v___x_3240_);
                v___x_3249_ =
                    l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_3234_, v___x_3241_);
                if lean_obj_tag(v___x_3249_) == 0 {
                    lean_dec_ref_known(v___x_3249_, 1);
                    v___x_3250_ =
                        l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_3233_);
                    v___y_3243_ = v___x_3250_;
                    state = 2;
                    continue;
                } else {
                    v_a_3251_ = lean_ctor_get(v___x_3249_, 0);
                    lean_inc(v_a_3251_);
                    lean_dec_ref_known(v___x_3249_, 1);
                    v___y_3243_ = v_a_3251_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc_ref(v___x_3241_);
                lean_inc_ref(v___y_3243_);
                v___f_3244_ = lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addMilliseconds___lam__0___boxed
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                lean_closure_set(v___f_3244_, 0, v___y_3243_);
                lean_closure_set(v___f_3244_, 1, v___x_3241_);
                lean_closure_set(v___f_3244_, 2, v___x_3235_);
                v___x_3245_ = lean_mk_thunk(v___f_3244_);
                if v_isShared_3225_ == 0 {
                    lean_ctor_set(v___x_3224_, 3, v___y_3243_);
                    lean_ctor_set(v___x_3224_, 1, v___x_3241_);
                    lean_ctor_set(v___x_3224_, 0, v___x_3245_);
                    v___x_3247_ = v___x_3224_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3248_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3248_, 0, v___x_3245_);
                    lean_ctor_set(v_reuseFailAlloc_3248_, 1, v___x_3241_);
                    lean_ctor_set(v_reuseFailAlloc_3248_, 2, v_rules_3222_);
                    lean_ctor_set(v_reuseFailAlloc_3248_, 3, v___y_3243_);
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
    mut v_dt_3255_: *mut LeanObject,
    mut v_milliseconds_3256_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3257_: *mut LeanObject = core::ptr::null_mut();
    v_res_3257_ = l_Std_Time_ZonedDateTime_addMilliseconds(v_dt_3255_, v_milliseconds_3256_);
    lean_dec(v_milliseconds_3256_);
    return v_res_3257_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_subMilliseconds(
    mut v_dt_3258_: *mut LeanObject,
    mut v_milliseconds_3259_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_timestamp_3260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rules_3261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3264_: u8 = 0;
    let mut v___x_3265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_3268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_3269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_3270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_3271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initialLocalTimeType_3272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_transitions_3273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3293_: u8 = 0;
    let mut v_unused_3294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3295_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_3260_ = lean_ctor_get(v_dt_3258_, 1);
                v_rules_3261_ = lean_ctor_get(v_dt_3258_, 2);
                v_isSharedCheck_3293_ = (!lean_is_exclusive(v_dt_3258_)) as u8;
                if v_isSharedCheck_3293_ == 0 {
                    v_unused_3294_ = lean_ctor_get(v_dt_3258_, 3);
                    lean_dec(v_unused_3294_);
                    v_unused_3295_ = lean_ctor_get(v_dt_3258_, 0);
                    lean_dec(v_unused_3295_);
                    v___x_3263_ = v_dt_3258_;
                    v_isShared_3264_ = v_isSharedCheck_3293_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_rules_3261_);
                    lean_inc(v_timestamp_3260_);
                    lean_dec(v_dt_3258_);
                    v___x_3263_ = lean_box(0);
                    v_isShared_3264_ = v_isSharedCheck_3293_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3265_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_millisecond___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_millisecond___closed__0_once),
                    _init_l_Std_Time_ZonedDateTime_millisecond___closed__0,
                );
                v___x_3266_ = lean_int_mul(v_milliseconds_3259_, v___x_3265_);
                v___x_3267_ = l_Std_Time_Duration_ofNanoseconds(v___x_3266_);
                lean_dec(v___x_3266_);
                v_second_3268_ = lean_ctor_get(v___x_3267_, 0);
                lean_inc(v_second_3268_);
                v_nano_3269_ = lean_ctor_get(v___x_3267_, 1);
                lean_inc(v_nano_3269_);
                lean_dec_ref(v___x_3267_);
                v_second_3270_ = lean_ctor_get(v_timestamp_3260_, 0);
                lean_inc(v_second_3270_);
                v_nano_3271_ = lean_ctor_get(v_timestamp_3260_, 1);
                lean_inc(v_nano_3271_);
                lean_dec_ref(v_timestamp_3260_);
                v_initialLocalTimeType_3272_ = lean_ctor_get(v_rules_3261_, 0);
                v_transitions_3273_ = lean_ctor_get(v_rules_3261_, 1);
                v___x_3274_ = lean_int_neg(v_second_3268_);
                lean_dec(v_second_3268_);
                v___x_3275_ = lean_int_neg(v_nano_3269_);
                lean_dec(v_nano_3269_);
                v___x_3276_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3277_ = lean_int_mul(v_second_3270_, v___x_3276_);
                lean_dec(v_second_3270_);
                v___x_3278_ = lean_int_add(v___x_3277_, v_nano_3271_);
                lean_dec(v_nano_3271_);
                lean_dec(v___x_3277_);
                v___x_3279_ = lean_int_mul(v___x_3274_, v___x_3276_);
                lean_dec(v___x_3274_);
                v___x_3280_ = lean_int_add(v___x_3279_, v___x_3275_);
                lean_dec(v___x_3275_);
                lean_dec(v___x_3279_);
                v___x_3281_ = lean_int_add(v___x_3278_, v___x_3280_);
                lean_dec(v___x_3280_);
                lean_dec(v___x_3278_);
                v___x_3282_ = l_Std_Time_Duration_ofNanoseconds(v___x_3281_);
                lean_dec(v___x_3281_);
                v___x_3290_ =
                    l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_3273_, v___x_3282_);
                if lean_obj_tag(v___x_3290_) == 0 {
                    lean_dec_ref_known(v___x_3290_, 1);
                    v___x_3291_ =
                        l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_3272_);
                    v___y_3284_ = v___x_3291_;
                    state = 2;
                    continue;
                } else {
                    v_a_3292_ = lean_ctor_get(v___x_3290_, 0);
                    lean_inc(v_a_3292_);
                    lean_dec_ref_known(v___x_3290_, 1);
                    v___y_3284_ = v_a_3292_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc_ref(v___x_3282_);
                lean_inc_ref(v___y_3284_);
                v___f_3285_ = lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addMilliseconds___lam__0___boxed
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                lean_closure_set(v___f_3285_, 0, v___y_3284_);
                lean_closure_set(v___f_3285_, 1, v___x_3282_);
                lean_closure_set(v___f_3285_, 2, v___x_3276_);
                v___x_3286_ = lean_mk_thunk(v___f_3285_);
                if v_isShared_3264_ == 0 {
                    lean_ctor_set(v___x_3263_, 3, v___y_3284_);
                    lean_ctor_set(v___x_3263_, 1, v___x_3282_);
                    lean_ctor_set(v___x_3263_, 0, v___x_3286_);
                    v___x_3288_ = v___x_3263_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3289_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3289_, 0, v___x_3286_);
                    lean_ctor_set(v_reuseFailAlloc_3289_, 1, v___x_3282_);
                    lean_ctor_set(v_reuseFailAlloc_3289_, 2, v_rules_3261_);
                    lean_ctor_set(v_reuseFailAlloc_3289_, 3, v___y_3284_);
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
    mut v_dt_3296_: *mut LeanObject,
    mut v_milliseconds_3297_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3298_: *mut LeanObject = core::ptr::null_mut();
    v_res_3298_ = l_Std_Time_ZonedDateTime_subMilliseconds(v_dt_3296_, v_milliseconds_3297_);
    lean_dec(v_milliseconds_3297_);
    return v_res_3298_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_addSeconds(
    mut v_dt_3299_: *mut LeanObject,
    mut v_seconds_3300_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_timestamp_3301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rules_3302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3305_: u8 = 0;
    let mut v_second_3306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_3307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initialLocalTimeType_3308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_transitions_3309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3328_: u8 = 0;
    let mut v_unused_3329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3330_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_3301_ = lean_ctor_get(v_dt_3299_, 1);
                v_rules_3302_ = lean_ctor_get(v_dt_3299_, 2);
                v_isSharedCheck_3328_ = (!lean_is_exclusive(v_dt_3299_)) as u8;
                if v_isSharedCheck_3328_ == 0 {
                    v_unused_3329_ = lean_ctor_get(v_dt_3299_, 3);
                    lean_dec(v_unused_3329_);
                    v_unused_3330_ = lean_ctor_get(v_dt_3299_, 0);
                    lean_dec(v_unused_3330_);
                    v___x_3304_ = v_dt_3299_;
                    v_isShared_3305_ = v_isSharedCheck_3328_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_rules_3302_);
                    lean_inc(v_timestamp_3301_);
                    lean_dec(v_dt_3299_);
                    v___x_3304_ = lean_box(0);
                    v_isShared_3305_ = v_isSharedCheck_3328_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_second_3306_ = lean_ctor_get(v_timestamp_3301_, 0);
                lean_inc(v_second_3306_);
                v_nano_3307_ = lean_ctor_get(v_timestamp_3301_, 1);
                lean_inc(v_nano_3307_);
                lean_dec_ref(v_timestamp_3301_);
                v_initialLocalTimeType_3308_ = lean_ctor_get(v_rules_3302_, 0);
                v_transitions_3309_ = lean_ctor_get(v_rules_3302_, 1);
                v___x_3310_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0,
                );
                v___x_3311_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3312_ = lean_int_mul(v_second_3306_, v___x_3311_);
                lean_dec(v_second_3306_);
                v___x_3313_ = lean_int_add(v___x_3312_, v_nano_3307_);
                lean_dec(v_nano_3307_);
                lean_dec(v___x_3312_);
                v___x_3314_ = lean_int_mul(v_seconds_3300_, v___x_3311_);
                v___x_3315_ = lean_int_add(v___x_3314_, v___x_3310_);
                lean_dec(v___x_3314_);
                v___x_3316_ = lean_int_add(v___x_3313_, v___x_3315_);
                lean_dec(v___x_3315_);
                lean_dec(v___x_3313_);
                v___x_3317_ = l_Std_Time_Duration_ofNanoseconds(v___x_3316_);
                lean_dec(v___x_3316_);
                v___x_3325_ =
                    l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_3309_, v___x_3317_);
                if lean_obj_tag(v___x_3325_) == 0 {
                    lean_dec_ref_known(v___x_3325_, 1);
                    v___x_3326_ =
                        l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_3308_);
                    v___y_3319_ = v___x_3326_;
                    state = 2;
                    continue;
                } else {
                    v_a_3327_ = lean_ctor_get(v___x_3325_, 0);
                    lean_inc(v_a_3327_);
                    lean_dec_ref_known(v___x_3325_, 1);
                    v___y_3319_ = v_a_3327_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc_ref(v___x_3317_);
                lean_inc_ref(v___y_3319_);
                v___f_3320_ = lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addDays___lam__0___boxed as *mut core::ffi::c_void,
                    5,
                    4,
                );
                lean_closure_set(v___f_3320_, 0, v___y_3319_);
                lean_closure_set(v___f_3320_, 1, v___x_3317_);
                lean_closure_set(v___f_3320_, 2, v___x_3311_);
                lean_closure_set(v___f_3320_, 3, v___x_3310_);
                v___x_3321_ = lean_mk_thunk(v___f_3320_);
                if v_isShared_3305_ == 0 {
                    lean_ctor_set(v___x_3304_, 3, v___y_3319_);
                    lean_ctor_set(v___x_3304_, 1, v___x_3317_);
                    lean_ctor_set(v___x_3304_, 0, v___x_3321_);
                    v___x_3323_ = v___x_3304_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3324_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3324_, 0, v___x_3321_);
                    lean_ctor_set(v_reuseFailAlloc_3324_, 1, v___x_3317_);
                    lean_ctor_set(v_reuseFailAlloc_3324_, 2, v_rules_3302_);
                    lean_ctor_set(v_reuseFailAlloc_3324_, 3, v___y_3319_);
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
    mut v_dt_3331_: *mut LeanObject,
    mut v_seconds_3332_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3333_: *mut LeanObject = core::ptr::null_mut();
    v_res_3333_ = l_Std_Time_ZonedDateTime_addSeconds(v_dt_3331_, v_seconds_3332_);
    lean_dec(v_seconds_3332_);
    return v_res_3333_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_subSeconds(
    mut v_dt_3334_: *mut LeanObject,
    mut v_seconds_3335_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_timestamp_3336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rules_3337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3340_: u8 = 0;
    let mut v_second_3341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_3342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initialLocalTimeType_3343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_transitions_3344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3365_: u8 = 0;
    let mut v_unused_3366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3367_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_3336_ = lean_ctor_get(v_dt_3334_, 1);
                v_rules_3337_ = lean_ctor_get(v_dt_3334_, 2);
                v_isSharedCheck_3365_ = (!lean_is_exclusive(v_dt_3334_)) as u8;
                if v_isSharedCheck_3365_ == 0 {
                    v_unused_3366_ = lean_ctor_get(v_dt_3334_, 3);
                    lean_dec(v_unused_3366_);
                    v_unused_3367_ = lean_ctor_get(v_dt_3334_, 0);
                    lean_dec(v_unused_3367_);
                    v___x_3339_ = v_dt_3334_;
                    v_isShared_3340_ = v_isSharedCheck_3365_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_rules_3337_);
                    lean_inc(v_timestamp_3336_);
                    lean_dec(v_dt_3334_);
                    v___x_3339_ = lean_box(0);
                    v_isShared_3340_ = v_isSharedCheck_3365_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_second_3341_ = lean_ctor_get(v_timestamp_3336_, 0);
                lean_inc(v_second_3341_);
                v_nano_3342_ = lean_ctor_get(v_timestamp_3336_, 1);
                lean_inc(v_nano_3342_);
                lean_dec_ref(v_timestamp_3336_);
                v_initialLocalTimeType_3343_ = lean_ctor_get(v_rules_3337_, 0);
                v_transitions_3344_ = lean_ctor_get(v_rules_3337_, 1);
                v___x_3345_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0,
                );
                v___x_3346_ = lean_int_neg(v_seconds_3335_);
                v___x_3347_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
                );
                v___x_3348_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3349_ = lean_int_mul(v_second_3341_, v___x_3348_);
                lean_dec(v_second_3341_);
                v___x_3350_ = lean_int_add(v___x_3349_, v_nano_3342_);
                lean_dec(v_nano_3342_);
                lean_dec(v___x_3349_);
                v___x_3351_ = lean_int_mul(v___x_3346_, v___x_3348_);
                lean_dec(v___x_3346_);
                v___x_3352_ = lean_int_add(v___x_3351_, v___x_3347_);
                lean_dec(v___x_3351_);
                v___x_3353_ = lean_int_add(v___x_3350_, v___x_3352_);
                lean_dec(v___x_3352_);
                lean_dec(v___x_3350_);
                v___x_3354_ = l_Std_Time_Duration_ofNanoseconds(v___x_3353_);
                lean_dec(v___x_3353_);
                v___x_3362_ =
                    l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_3344_, v___x_3354_);
                if lean_obj_tag(v___x_3362_) == 0 {
                    lean_dec_ref_known(v___x_3362_, 1);
                    v___x_3363_ =
                        l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_3343_);
                    v___y_3356_ = v___x_3363_;
                    state = 2;
                    continue;
                } else {
                    v_a_3364_ = lean_ctor_get(v___x_3362_, 0);
                    lean_inc(v_a_3364_);
                    lean_dec_ref_known(v___x_3362_, 1);
                    v___y_3356_ = v_a_3364_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc_ref(v___x_3354_);
                lean_inc_ref(v___y_3356_);
                v___f_3357_ = lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addDays___lam__0___boxed as *mut core::ffi::c_void,
                    5,
                    4,
                );
                lean_closure_set(v___f_3357_, 0, v___y_3356_);
                lean_closure_set(v___f_3357_, 1, v___x_3354_);
                lean_closure_set(v___f_3357_, 2, v___x_3348_);
                lean_closure_set(v___f_3357_, 3, v___x_3345_);
                v___x_3358_ = lean_mk_thunk(v___f_3357_);
                if v_isShared_3340_ == 0 {
                    lean_ctor_set(v___x_3339_, 3, v___y_3356_);
                    lean_ctor_set(v___x_3339_, 1, v___x_3354_);
                    lean_ctor_set(v___x_3339_, 0, v___x_3358_);
                    v___x_3360_ = v___x_3339_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3361_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3361_, 0, v___x_3358_);
                    lean_ctor_set(v_reuseFailAlloc_3361_, 1, v___x_3354_);
                    lean_ctor_set(v_reuseFailAlloc_3361_, 2, v_rules_3337_);
                    lean_ctor_set(v_reuseFailAlloc_3361_, 3, v___y_3356_);
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
    mut v_dt_3368_: *mut LeanObject,
    mut v_seconds_3369_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3370_: *mut LeanObject = core::ptr::null_mut();
    v_res_3370_ = l_Std_Time_ZonedDateTime_subSeconds(v_dt_3368_, v_seconds_3369_);
    lean_dec(v_seconds_3369_);
    return v_res_3370_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_addNanoseconds(
    mut v_dt_3371_: *mut LeanObject,
    mut v_nanoseconds_3372_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_timestamp_3373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rules_3374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3377_: u8 = 0;
    let mut v_second_3378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_3379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_3381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_3382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initialLocalTimeType_3383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_transitions_3384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3402_: u8 = 0;
    let mut v_unused_3403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3404_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_3373_ = lean_ctor_get(v_dt_3371_, 1);
                v_rules_3374_ = lean_ctor_get(v_dt_3371_, 2);
                v_isSharedCheck_3402_ = (!lean_is_exclusive(v_dt_3371_)) as u8;
                if v_isSharedCheck_3402_ == 0 {
                    v_unused_3403_ = lean_ctor_get(v_dt_3371_, 3);
                    lean_dec(v_unused_3403_);
                    v_unused_3404_ = lean_ctor_get(v_dt_3371_, 0);
                    lean_dec(v_unused_3404_);
                    v___x_3376_ = v_dt_3371_;
                    v_isShared_3377_ = v_isSharedCheck_3402_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_rules_3374_);
                    lean_inc(v_timestamp_3373_);
                    lean_dec(v_dt_3371_);
                    v___x_3376_ = lean_box(0);
                    v_isShared_3377_ = v_isSharedCheck_3402_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_second_3378_ = lean_ctor_get(v_timestamp_3373_, 0);
                lean_inc(v_second_3378_);
                v_nano_3379_ = lean_ctor_get(v_timestamp_3373_, 1);
                lean_inc(v_nano_3379_);
                lean_dec_ref(v_timestamp_3373_);
                v___x_3380_ = l_Std_Time_Duration_ofNanoseconds(v_nanoseconds_3372_);
                v_second_3381_ = lean_ctor_get(v___x_3380_, 0);
                lean_inc(v_second_3381_);
                v_nano_3382_ = lean_ctor_get(v___x_3380_, 1);
                lean_inc(v_nano_3382_);
                lean_dec_ref(v___x_3380_);
                v_initialLocalTimeType_3383_ = lean_ctor_get(v_rules_3374_, 0);
                v_transitions_3384_ = lean_ctor_get(v_rules_3374_, 1);
                v___x_3385_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3386_ = lean_int_mul(v_second_3378_, v___x_3385_);
                lean_dec(v_second_3378_);
                v___x_3387_ = lean_int_add(v___x_3386_, v_nano_3379_);
                lean_dec(v_nano_3379_);
                lean_dec(v___x_3386_);
                v___x_3388_ = lean_int_mul(v_second_3381_, v___x_3385_);
                lean_dec(v_second_3381_);
                v___x_3389_ = lean_int_add(v___x_3388_, v_nano_3382_);
                lean_dec(v_nano_3382_);
                lean_dec(v___x_3388_);
                v___x_3390_ = lean_int_add(v___x_3387_, v___x_3389_);
                lean_dec(v___x_3389_);
                lean_dec(v___x_3387_);
                v___x_3391_ = l_Std_Time_Duration_ofNanoseconds(v___x_3390_);
                lean_dec(v___x_3390_);
                v___x_3399_ =
                    l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_3384_, v___x_3391_);
                if lean_obj_tag(v___x_3399_) == 0 {
                    lean_dec_ref_known(v___x_3399_, 1);
                    v___x_3400_ =
                        l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_3383_);
                    v___y_3393_ = v___x_3400_;
                    state = 2;
                    continue;
                } else {
                    v_a_3401_ = lean_ctor_get(v___x_3399_, 0);
                    lean_inc(v_a_3401_);
                    lean_dec_ref_known(v___x_3399_, 1);
                    v___y_3393_ = v_a_3401_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc_ref(v___x_3391_);
                lean_inc_ref(v___y_3393_);
                v___f_3394_ = lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addMilliseconds___lam__0___boxed
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                lean_closure_set(v___f_3394_, 0, v___y_3393_);
                lean_closure_set(v___f_3394_, 1, v___x_3391_);
                lean_closure_set(v___f_3394_, 2, v___x_3385_);
                v___x_3395_ = lean_mk_thunk(v___f_3394_);
                if v_isShared_3377_ == 0 {
                    lean_ctor_set(v___x_3376_, 3, v___y_3393_);
                    lean_ctor_set(v___x_3376_, 1, v___x_3391_);
                    lean_ctor_set(v___x_3376_, 0, v___x_3395_);
                    v___x_3397_ = v___x_3376_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3398_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3398_, 0, v___x_3395_);
                    lean_ctor_set(v_reuseFailAlloc_3398_, 1, v___x_3391_);
                    lean_ctor_set(v_reuseFailAlloc_3398_, 2, v_rules_3374_);
                    lean_ctor_set(v_reuseFailAlloc_3398_, 3, v___y_3393_);
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
    mut v_dt_3405_: *mut LeanObject,
    mut v_nanoseconds_3406_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3407_: *mut LeanObject = core::ptr::null_mut();
    v_res_3407_ = l_Std_Time_ZonedDateTime_addNanoseconds(v_dt_3405_, v_nanoseconds_3406_);
    lean_dec(v_nanoseconds_3406_);
    return v_res_3407_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_subNanoseconds(
    mut v_dt_3408_: *mut LeanObject,
    mut v_nanoseconds_3409_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_timestamp_3410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rules_3411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3414_: u8 = 0;
    let mut v___x_3415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_3416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_3417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_3418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_3419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initialLocalTimeType_3420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_transitions_3421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3441_: u8 = 0;
    let mut v_unused_3442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3443_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_3410_ = lean_ctor_get(v_dt_3408_, 1);
                v_rules_3411_ = lean_ctor_get(v_dt_3408_, 2);
                v_isSharedCheck_3441_ = (!lean_is_exclusive(v_dt_3408_)) as u8;
                if v_isSharedCheck_3441_ == 0 {
                    v_unused_3442_ = lean_ctor_get(v_dt_3408_, 3);
                    lean_dec(v_unused_3442_);
                    v_unused_3443_ = lean_ctor_get(v_dt_3408_, 0);
                    lean_dec(v_unused_3443_);
                    v___x_3413_ = v_dt_3408_;
                    v_isShared_3414_ = v_isSharedCheck_3441_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_rules_3411_);
                    lean_inc(v_timestamp_3410_);
                    lean_dec(v_dt_3408_);
                    v___x_3413_ = lean_box(0);
                    v_isShared_3414_ = v_isSharedCheck_3441_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3415_ = l_Std_Time_Duration_ofNanoseconds(v_nanoseconds_3409_);
                v_second_3416_ = lean_ctor_get(v___x_3415_, 0);
                lean_inc(v_second_3416_);
                v_nano_3417_ = lean_ctor_get(v___x_3415_, 1);
                lean_inc(v_nano_3417_);
                lean_dec_ref(v___x_3415_);
                v_second_3418_ = lean_ctor_get(v_timestamp_3410_, 0);
                lean_inc(v_second_3418_);
                v_nano_3419_ = lean_ctor_get(v_timestamp_3410_, 1);
                lean_inc(v_nano_3419_);
                lean_dec_ref(v_timestamp_3410_);
                v_initialLocalTimeType_3420_ = lean_ctor_get(v_rules_3411_, 0);
                v_transitions_3421_ = lean_ctor_get(v_rules_3411_, 1);
                v___x_3422_ = lean_int_neg(v_second_3416_);
                lean_dec(v_second_3416_);
                v___x_3423_ = lean_int_neg(v_nano_3417_);
                lean_dec(v_nano_3417_);
                v___x_3424_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3425_ = lean_int_mul(v_second_3418_, v___x_3424_);
                lean_dec(v_second_3418_);
                v___x_3426_ = lean_int_add(v___x_3425_, v_nano_3419_);
                lean_dec(v_nano_3419_);
                lean_dec(v___x_3425_);
                v___x_3427_ = lean_int_mul(v___x_3422_, v___x_3424_);
                lean_dec(v___x_3422_);
                v___x_3428_ = lean_int_add(v___x_3427_, v___x_3423_);
                lean_dec(v___x_3423_);
                lean_dec(v___x_3427_);
                v___x_3429_ = lean_int_add(v___x_3426_, v___x_3428_);
                lean_dec(v___x_3428_);
                lean_dec(v___x_3426_);
                v___x_3430_ = l_Std_Time_Duration_ofNanoseconds(v___x_3429_);
                lean_dec(v___x_3429_);
                v___x_3438_ =
                    l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_3421_, v___x_3430_);
                if lean_obj_tag(v___x_3438_) == 0 {
                    lean_dec_ref_known(v___x_3438_, 1);
                    v___x_3439_ =
                        l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_3420_);
                    v___y_3432_ = v___x_3439_;
                    state = 2;
                    continue;
                } else {
                    v_a_3440_ = lean_ctor_get(v___x_3438_, 0);
                    lean_inc(v_a_3440_);
                    lean_dec_ref_known(v___x_3438_, 1);
                    v___y_3432_ = v_a_3440_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc_ref(v___x_3430_);
                lean_inc_ref(v___y_3432_);
                v___f_3433_ = lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addMilliseconds___lam__0___boxed
                        as *mut core::ffi::c_void,
                    4,
                    3,
                );
                lean_closure_set(v___f_3433_, 0, v___y_3432_);
                lean_closure_set(v___f_3433_, 1, v___x_3430_);
                lean_closure_set(v___f_3433_, 2, v___x_3424_);
                v___x_3434_ = lean_mk_thunk(v___f_3433_);
                if v_isShared_3414_ == 0 {
                    lean_ctor_set(v___x_3413_, 3, v___y_3432_);
                    lean_ctor_set(v___x_3413_, 1, v___x_3430_);
                    lean_ctor_set(v___x_3413_, 0, v___x_3434_);
                    v___x_3436_ = v___x_3413_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3437_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3437_, 0, v___x_3434_);
                    lean_ctor_set(v_reuseFailAlloc_3437_, 1, v___x_3430_);
                    lean_ctor_set(v_reuseFailAlloc_3437_, 2, v_rules_3411_);
                    lean_ctor_set(v_reuseFailAlloc_3437_, 3, v___y_3432_);
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
    mut v_dt_3444_: *mut LeanObject,
    mut v_nanoseconds_3445_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3446_: *mut LeanObject = core::ptr::null_mut();
    v_res_3446_ = l_Std_Time_ZonedDateTime_subNanoseconds(v_dt_3444_, v_nanoseconds_3445_);
    lean_dec(v_nanoseconds_3445_);
    return v_res_3446_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_era(mut v_date_3447_: *mut LeanObject) -> u8 {
    let mut v_date_3448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_date_3450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_year_3451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: u8 = 0;
    v_date_3448_ = lean_ctor_get(v_date_3447_, 0);
    v___x_3449_ = lean_thunk_get_own(v_date_3448_);
    v_date_3450_ = lean_ctor_get(v___x_3449_, 0);
    lean_inc_ref(v_date_3450_);
    lean_dec(v___x_3449_);
    v_year_3451_ = lean_ctor_get(v_date_3450_, 0);
    lean_inc(v_year_3451_);
    lean_dec_ref(v_date_3450_);
    v___x_3452_ = l_Std_Time_Year_Offset_era(v_year_3451_);
    lean_dec(v_year_3451_);
    return v___x_3452_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_era___boxed(
    mut v_date_3453_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3454_: u8 = 0;
    let mut v_r_3455_: *mut LeanObject = core::ptr::null_mut();
    v_res_3454_ = l_Std_Time_ZonedDateTime_era(v_date_3453_);
    lean_dec_ref(v_date_3453_);
    v_r_3455_ = lean_box((v_res_3454_) as usize);
    return v_r_3455_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_withWeekday(
    mut v_dt_3456_: *mut LeanObject,
    mut v_desiredWeekday_3457_: u8,
) -> *mut LeanObject {
    let mut v_date_3458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rules_3459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3462_: u8 = 0;
    let mut v_date_3463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_wt_3465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ltt_3466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tz_3467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_offset_3468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_3469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_3470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3485_: u8 = 0;
    let mut v_unused_3486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3487_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_3458_ = lean_ctor_get(v_dt_3456_, 0);
                v_rules_3459_ = lean_ctor_get(v_dt_3456_, 2);
                v_isSharedCheck_3485_ = (!lean_is_exclusive(v_dt_3456_)) as u8;
                if v_isSharedCheck_3485_ == 0 {
                    v_unused_3486_ = lean_ctor_get(v_dt_3456_, 3);
                    lean_dec(v_unused_3486_);
                    v_unused_3487_ = lean_ctor_get(v_dt_3456_, 1);
                    lean_dec(v_unused_3487_);
                    v___x_3461_ = v_dt_3456_;
                    v_isShared_3462_ = v_isSharedCheck_3485_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_rules_3459_);
                    lean_inc(v_date_3458_);
                    lean_dec(v_dt_3456_);
                    v___x_3461_ = lean_box(0);
                    v_isShared_3462_ = v_isSharedCheck_3485_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_date_3463_ = lean_thunk_get_own(v_date_3458_);
                lean_dec_ref(v_date_3458_);
                v___x_3464_ =
                    l_Std_Time_PlainDateTime_withWeekday(v_date_3463_, v_desiredWeekday_3457_);
                lean_inc_ref(v___x_3464_);
                v_wt_3465_ = l_Std_Time_PlainDateTime_toWallTime(v___x_3464_);
                lean_inc_ref(v_rules_3459_);
                v_ltt_3466_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(
                    v_rules_3459_,
                    v_wt_3465_,
                );
                v_tz_3467_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_3466_);
                lean_dec_ref(v_ltt_3466_);
                v_offset_3468_ = lean_ctor_get(v_tz_3467_, 0);
                lean_inc(v_offset_3468_);
                v_second_3469_ = lean_ctor_get(v_wt_3465_, 0);
                lean_inc(v_second_3469_);
                v_nano_3470_ = lean_ctor_get(v_wt_3465_, 1);
                lean_inc(v_nano_3470_);
                lean_dec_ref(v_wt_3465_);
                v___f_3471_ = lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_3471_, 0, v___x_3464_);
                v___x_3472_ = lean_mk_thunk(v___f_3471_);
                v___x_3473_ = lean_int_neg(v_offset_3468_);
                lean_dec(v_offset_3468_);
                v___x_3474_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
                );
                v___x_3475_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3476_ = lean_int_mul(v_second_3469_, v___x_3475_);
                lean_dec(v_second_3469_);
                v___x_3477_ = lean_int_add(v___x_3476_, v_nano_3470_);
                lean_dec(v_nano_3470_);
                lean_dec(v___x_3476_);
                v___x_3478_ = lean_int_mul(v___x_3473_, v___x_3475_);
                lean_dec(v___x_3473_);
                v___x_3479_ = lean_int_add(v___x_3478_, v___x_3474_);
                lean_dec(v___x_3478_);
                v___x_3480_ = lean_int_add(v___x_3477_, v___x_3479_);
                lean_dec(v___x_3479_);
                lean_dec(v___x_3477_);
                v___x_3481_ = l_Std_Time_Duration_ofNanoseconds(v___x_3480_);
                lean_dec(v___x_3480_);
                if v_isShared_3462_ == 0 {
                    lean_ctor_set(v___x_3461_, 3, v_tz_3467_);
                    lean_ctor_set(v___x_3461_, 1, v___x_3481_);
                    lean_ctor_set(v___x_3461_, 0, v___x_3472_);
                    v___x_3483_ = v___x_3461_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3484_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3484_, 0, v___x_3472_);
                    lean_ctor_set(v_reuseFailAlloc_3484_, 1, v___x_3481_);
                    lean_ctor_set(v_reuseFailAlloc_3484_, 2, v_rules_3459_);
                    lean_ctor_set(v_reuseFailAlloc_3484_, 3, v_tz_3467_);
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
    mut v_dt_3488_: *mut LeanObject,
    mut v_desiredWeekday_3489_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_desiredWeekday_boxed_3490_: u8 = 0;
    let mut v_res_3491_: *mut LeanObject = core::ptr::null_mut();
    v_desiredWeekday_boxed_3490_ = (lean_unbox(v_desiredWeekday_3489_) as u8);
    v_res_3491_ = l_Std_Time_ZonedDateTime_withWeekday(v_dt_3488_, v_desiredWeekday_boxed_3490_);
    return v_res_3491_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_withDaysClip(
    mut v_dt_3492_: *mut LeanObject,
    mut v_days_3493_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_3494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rules_3495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3498_: u8 = 0;
    let mut v_date_3499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_time_3502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3505_: u8 = 0;
    let mut v___x_3507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_wt_3508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ltt_3509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tz_3510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_offset_3511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_3512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_3513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3529_: u8 = 0;
    let mut v_unused_3530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_date_3531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_year_3532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_month_3533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3536_: u8 = 0;
    let mut v___y_3538_: u8 = 0;
    let mut v_max_3539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3540_: u8 = 0;
    let mut v___x_3542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3553_: u8 = 0;
    let mut v___x_3554_: u8 = 0;
    let mut v___x_3555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3557_: u8 = 0;
    let mut v_isSharedCheck_3558_: u8 = 0;
    let mut v_unused_3559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3560_: u8 = 0;
    let mut v_unused_3561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3562_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_3494_ = lean_ctor_get(v_dt_3492_, 0);
                v_rules_3495_ = lean_ctor_get(v_dt_3492_, 2);
                v_isSharedCheck_3560_ = (!lean_is_exclusive(v_dt_3492_)) as u8;
                if v_isSharedCheck_3560_ == 0 {
                    v_unused_3561_ = lean_ctor_get(v_dt_3492_, 3);
                    lean_dec(v_unused_3561_);
                    v_unused_3562_ = lean_ctor_get(v_dt_3492_, 1);
                    lean_dec(v_unused_3562_);
                    v___x_3497_ = v_dt_3492_;
                    v_isShared_3498_ = v_isSharedCheck_3560_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_rules_3495_);
                    lean_inc(v_date_3494_);
                    lean_dec(v_dt_3492_);
                    v___x_3497_ = lean_box(0);
                    v_isShared_3498_ = v_isSharedCheck_3560_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_date_3499_ = lean_thunk_get_own(v_date_3494_);
                lean_dec_ref(v_date_3494_);
                v_date_3531_ = lean_ctor_get(v_date_3499_, 0);
                lean_inc_ref(v_date_3531_);
                v_year_3532_ = lean_ctor_get(v_date_3531_, 0);
                v_month_3533_ = lean_ctor_get(v_date_3531_, 1);
                v_isSharedCheck_3558_ = (!lean_is_exclusive(v_date_3531_)) as u8;
                if v_isSharedCheck_3558_ == 0 {
                    v_unused_3559_ = lean_ctor_get(v_date_3531_, 2);
                    lean_dec(v_unused_3559_);
                    v___x_3535_ = v_date_3531_;
                    v_isShared_3536_ = v_isSharedCheck_3558_;
                    state = 6;
                    continue;
                } else {
                    lean_inc(v_month_3533_);
                    lean_inc(v_year_3532_);
                    lean_dec(v_date_3531_);
                    v___x_3535_ = lean_box(0);
                    v_isShared_3536_ = v_isSharedCheck_3558_;
                    state = 6;
                    continue;
                }
            }
            2 => {
                v_time_3502_ = lean_ctor_get(v_date_3499_, 1);
                v_isSharedCheck_3529_ = (!lean_is_exclusive(v_date_3499_)) as u8;
                if v_isSharedCheck_3529_ == 0 {
                    v_unused_3530_ = lean_ctor_get(v_date_3499_, 0);
                    lean_dec(v_unused_3530_);
                    v___x_3504_ = v_date_3499_;
                    v_isShared_3505_ = v_isSharedCheck_3529_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_time_3502_);
                    lean_dec(v_date_3499_);
                    v___x_3504_ = lean_box(0);
                    v_isShared_3505_ = v_isSharedCheck_3529_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3505_ == 0 {
                    lean_ctor_set(v___x_3504_, 0, v___y_3501_);
                    v___x_3507_ = v___x_3504_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3528_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3528_, 0, v___y_3501_);
                    lean_ctor_set(v_reuseFailAlloc_3528_, 1, v_time_3502_);
                    v___x_3507_ = v_reuseFailAlloc_3528_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                lean_inc_ref(v___x_3507_);
                v_wt_3508_ = l_Std_Time_PlainDateTime_toWallTime(v___x_3507_);
                lean_inc_ref(v_rules_3495_);
                v_ltt_3509_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(
                    v_rules_3495_,
                    v_wt_3508_,
                );
                v_tz_3510_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_3509_);
                lean_dec_ref(v_ltt_3509_);
                v_offset_3511_ = lean_ctor_get(v_tz_3510_, 0);
                lean_inc(v_offset_3511_);
                v_second_3512_ = lean_ctor_get(v_wt_3508_, 0);
                lean_inc(v_second_3512_);
                v_nano_3513_ = lean_ctor_get(v_wt_3508_, 1);
                lean_inc(v_nano_3513_);
                lean_dec_ref(v_wt_3508_);
                v___f_3514_ = lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_3514_, 0, v___x_3507_);
                v___x_3515_ = lean_mk_thunk(v___f_3514_);
                v___x_3516_ = lean_int_neg(v_offset_3511_);
                lean_dec(v_offset_3511_);
                v___x_3517_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
                );
                v___x_3518_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3519_ = lean_int_mul(v_second_3512_, v___x_3518_);
                lean_dec(v_second_3512_);
                v___x_3520_ = lean_int_add(v___x_3519_, v_nano_3513_);
                lean_dec(v_nano_3513_);
                lean_dec(v___x_3519_);
                v___x_3521_ = lean_int_mul(v___x_3516_, v___x_3518_);
                lean_dec(v___x_3516_);
                v___x_3522_ = lean_int_add(v___x_3521_, v___x_3517_);
                lean_dec(v___x_3521_);
                v___x_3523_ = lean_int_add(v___x_3520_, v___x_3522_);
                lean_dec(v___x_3522_);
                lean_dec(v___x_3520_);
                v___x_3524_ = l_Std_Time_Duration_ofNanoseconds(v___x_3523_);
                lean_dec(v___x_3523_);
                if v_isShared_3498_ == 0 {
                    lean_ctor_set(v___x_3497_, 3, v_tz_3510_);
                    lean_ctor_set(v___x_3497_, 1, v___x_3524_);
                    lean_ctor_set(v___x_3497_, 0, v___x_3515_);
                    v___x_3526_ = v___x_3497_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3527_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3527_, 0, v___x_3515_);
                    lean_ctor_set(v_reuseFailAlloc_3527_, 1, v___x_3524_);
                    lean_ctor_set(v_reuseFailAlloc_3527_, 2, v_rules_3495_);
                    lean_ctor_set(v_reuseFailAlloc_3527_, 3, v_tz_3510_);
                    v___x_3526_ = v_reuseFailAlloc_3527_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3526_;
            }
            6 => {
                v___x_3547_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_dayOfYear___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_dayOfYear___closed__0_once),
                    _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__0,
                );
                v___x_3548_ = lean_int_mod(v_year_3532_, v___x_3547_);
                v___x_3549_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0,
                );
                v___x_3554_ = lean_int_dec_eq(v___x_3548_, v___x_3549_);
                lean_dec(v___x_3548_);
                if v___x_3554_ == 0 {
                    v___y_3538_ = v___x_3554_;
                    state = 7;
                    continue;
                } else {
                    v___x_3555_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_dayOfYear___closed__2),
                        core::ptr::addr_of_mut!(
                            l_Std_Time_ZonedDateTime_dayOfYear___closed__2_once
                        ),
                        _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__2,
                    );
                    v___x_3556_ = lean_int_mod(v_year_3532_, v___x_3555_);
                    v___x_3557_ = lean_int_dec_eq(v___x_3556_, v___x_3549_);
                    lean_dec(v___x_3556_);
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
                    lean_dec(v_max_3539_);
                    if v_isShared_3536_ == 0 {
                        lean_ctor_set(v___x_3535_, 2, v_days_3493_);
                        v___x_3542_ = v___x_3535_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_3543_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3543_, 0, v_year_3532_);
                        lean_ctor_set(v_reuseFailAlloc_3543_, 1, v_month_3533_);
                        lean_ctor_set(v_reuseFailAlloc_3543_, 2, v_days_3493_);
                        v___x_3542_ = v_reuseFailAlloc_3543_;
                        state = 8;
                        continue;
                    }
                } else {
                    lean_dec(v_days_3493_);
                    if v_isShared_3536_ == 0 {
                        lean_ctor_set(v___x_3535_, 2, v_max_3539_);
                        v___x_3545_ = v___x_3535_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_3546_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3546_, 0, v_year_3532_);
                        lean_ctor_set(v_reuseFailAlloc_3546_, 1, v_month_3533_);
                        lean_ctor_set(v_reuseFailAlloc_3546_, 2, v_max_3539_);
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
                v___x_3551_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_dayOfYear___closed__1),
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_dayOfYear___closed__1_once),
                    _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__1,
                );
                v___x_3552_ = lean_int_mod(v_year_3532_, v___x_3551_);
                v___x_3553_ = lean_int_dec_eq(v___x_3552_, v___x_3549_);
                lean_dec(v___x_3552_);
                v___y_3538_ = v___x_3553_;
                state = 7;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_ZonedDateTime_withDaysRollOver(
    mut v_dt_3563_: *mut LeanObject,
    mut v_days_3564_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_3565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rules_3566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3569_: u8 = 0;
    let mut v_date_3570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_date_3571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_time_3572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3575_: u8 = 0;
    let mut v_year_3576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_month_3577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_wt_3581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ltt_3582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tz_3583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_offset_3584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_3585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_3586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3602_: u8 = 0;
    let mut v_isSharedCheck_3603_: u8 = 0;
    let mut v_unused_3604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3605_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_3565_ = lean_ctor_get(v_dt_3563_, 0);
                v_rules_3566_ = lean_ctor_get(v_dt_3563_, 2);
                v_isSharedCheck_3603_ = (!lean_is_exclusive(v_dt_3563_)) as u8;
                if v_isSharedCheck_3603_ == 0 {
                    v_unused_3604_ = lean_ctor_get(v_dt_3563_, 3);
                    lean_dec(v_unused_3604_);
                    v_unused_3605_ = lean_ctor_get(v_dt_3563_, 1);
                    lean_dec(v_unused_3605_);
                    v___x_3568_ = v_dt_3563_;
                    v_isShared_3569_ = v_isSharedCheck_3603_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_rules_3566_);
                    lean_inc(v_date_3565_);
                    lean_dec(v_dt_3563_);
                    v___x_3568_ = lean_box(0);
                    v_isShared_3569_ = v_isSharedCheck_3603_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_date_3570_ = lean_thunk_get_own(v_date_3565_);
                lean_dec_ref(v_date_3565_);
                v_date_3571_ = lean_ctor_get(v_date_3570_, 0);
                v_time_3572_ = lean_ctor_get(v_date_3570_, 1);
                v_isSharedCheck_3602_ = (!lean_is_exclusive(v_date_3570_)) as u8;
                if v_isSharedCheck_3602_ == 0 {
                    v___x_3574_ = v_date_3570_;
                    v_isShared_3575_ = v_isSharedCheck_3602_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_time_3572_);
                    lean_inc(v_date_3571_);
                    lean_dec(v_date_3570_);
                    v___x_3574_ = lean_box(0);
                    v_isShared_3575_ = v_isSharedCheck_3602_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_year_3576_ = lean_ctor_get(v_date_3571_, 0);
                lean_inc(v_year_3576_);
                v_month_3577_ = lean_ctor_get(v_date_3571_, 1);
                lean_inc(v_month_3577_);
                lean_dec_ref(v_date_3571_);
                v___x_3578_ =
                    l_Std_Time_PlainDate_rollOver(v_year_3576_, v_month_3577_, v_days_3564_);
                if v_isShared_3575_ == 0 {
                    lean_ctor_set(v___x_3574_, 0, v___x_3578_);
                    v___x_3580_ = v___x_3574_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3601_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3601_, 0, v___x_3578_);
                    lean_ctor_set(v_reuseFailAlloc_3601_, 1, v_time_3572_);
                    v___x_3580_ = v_reuseFailAlloc_3601_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_inc_ref(v___x_3580_);
                v_wt_3581_ = l_Std_Time_PlainDateTime_toWallTime(v___x_3580_);
                lean_inc_ref(v_rules_3566_);
                v_ltt_3582_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(
                    v_rules_3566_,
                    v_wt_3581_,
                );
                v_tz_3583_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_3582_);
                lean_dec_ref(v_ltt_3582_);
                v_offset_3584_ = lean_ctor_get(v_tz_3583_, 0);
                lean_inc(v_offset_3584_);
                v_second_3585_ = lean_ctor_get(v_wt_3581_, 0);
                lean_inc(v_second_3585_);
                v_nano_3586_ = lean_ctor_get(v_wt_3581_, 1);
                lean_inc(v_nano_3586_);
                lean_dec_ref(v_wt_3581_);
                v___f_3587_ = lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_3587_, 0, v___x_3580_);
                v___x_3588_ = lean_mk_thunk(v___f_3587_);
                v___x_3589_ = lean_int_neg(v_offset_3584_);
                lean_dec(v_offset_3584_);
                v___x_3590_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
                );
                v___x_3591_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3592_ = lean_int_mul(v_second_3585_, v___x_3591_);
                lean_dec(v_second_3585_);
                v___x_3593_ = lean_int_add(v___x_3592_, v_nano_3586_);
                lean_dec(v_nano_3586_);
                lean_dec(v___x_3592_);
                v___x_3594_ = lean_int_mul(v___x_3589_, v___x_3591_);
                lean_dec(v___x_3589_);
                v___x_3595_ = lean_int_add(v___x_3594_, v___x_3590_);
                lean_dec(v___x_3594_);
                v___x_3596_ = lean_int_add(v___x_3593_, v___x_3595_);
                lean_dec(v___x_3595_);
                lean_dec(v___x_3593_);
                v___x_3597_ = l_Std_Time_Duration_ofNanoseconds(v___x_3596_);
                lean_dec(v___x_3596_);
                if v_isShared_3569_ == 0 {
                    lean_ctor_set(v___x_3568_, 3, v_tz_3583_);
                    lean_ctor_set(v___x_3568_, 1, v___x_3597_);
                    lean_ctor_set(v___x_3568_, 0, v___x_3588_);
                    v___x_3599_ = v___x_3568_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3600_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3600_, 0, v___x_3588_);
                    lean_ctor_set(v_reuseFailAlloc_3600_, 1, v___x_3597_);
                    lean_ctor_set(v_reuseFailAlloc_3600_, 2, v_rules_3566_);
                    lean_ctor_set(v_reuseFailAlloc_3600_, 3, v_tz_3583_);
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
    mut v_dt_3606_: *mut LeanObject,
    mut v_days_3607_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3608_: *mut LeanObject = core::ptr::null_mut();
    v_res_3608_ = l_Std_Time_ZonedDateTime_withDaysRollOver(v_dt_3606_, v_days_3607_);
    lean_dec(v_days_3607_);
    return v_res_3608_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_withMonthClip(
    mut v_dt_3609_: *mut LeanObject,
    mut v_month_3610_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_3611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rules_3612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3615_: u8 = 0;
    let mut v_date_3616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_time_3619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3622_: u8 = 0;
    let mut v___x_3624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_wt_3625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ltt_3626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tz_3627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_offset_3628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_3629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_3630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3646_: u8 = 0;
    let mut v_unused_3647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_date_3648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_year_3649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_day_3650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3653_: u8 = 0;
    let mut v___y_3655_: u8 = 0;
    let mut v_max_3656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3657_: u8 = 0;
    let mut v___x_3659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3670_: u8 = 0;
    let mut v___x_3671_: u8 = 0;
    let mut v___x_3672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3674_: u8 = 0;
    let mut v_isSharedCheck_3675_: u8 = 0;
    let mut v_unused_3676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3677_: u8 = 0;
    let mut v_unused_3678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3679_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_3611_ = lean_ctor_get(v_dt_3609_, 0);
                v_rules_3612_ = lean_ctor_get(v_dt_3609_, 2);
                v_isSharedCheck_3677_ = (!lean_is_exclusive(v_dt_3609_)) as u8;
                if v_isSharedCheck_3677_ == 0 {
                    v_unused_3678_ = lean_ctor_get(v_dt_3609_, 3);
                    lean_dec(v_unused_3678_);
                    v_unused_3679_ = lean_ctor_get(v_dt_3609_, 1);
                    lean_dec(v_unused_3679_);
                    v___x_3614_ = v_dt_3609_;
                    v_isShared_3615_ = v_isSharedCheck_3677_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_rules_3612_);
                    lean_inc(v_date_3611_);
                    lean_dec(v_dt_3609_);
                    v___x_3614_ = lean_box(0);
                    v_isShared_3615_ = v_isSharedCheck_3677_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_date_3616_ = lean_thunk_get_own(v_date_3611_);
                lean_dec_ref(v_date_3611_);
                v_date_3648_ = lean_ctor_get(v_date_3616_, 0);
                lean_inc_ref(v_date_3648_);
                v_year_3649_ = lean_ctor_get(v_date_3648_, 0);
                v_day_3650_ = lean_ctor_get(v_date_3648_, 2);
                v_isSharedCheck_3675_ = (!lean_is_exclusive(v_date_3648_)) as u8;
                if v_isSharedCheck_3675_ == 0 {
                    v_unused_3676_ = lean_ctor_get(v_date_3648_, 1);
                    lean_dec(v_unused_3676_);
                    v___x_3652_ = v_date_3648_;
                    v_isShared_3653_ = v_isSharedCheck_3675_;
                    state = 6;
                    continue;
                } else {
                    lean_inc(v_day_3650_);
                    lean_inc(v_year_3649_);
                    lean_dec(v_date_3648_);
                    v___x_3652_ = lean_box(0);
                    v_isShared_3653_ = v_isSharedCheck_3675_;
                    state = 6;
                    continue;
                }
            }
            2 => {
                v_time_3619_ = lean_ctor_get(v_date_3616_, 1);
                v_isSharedCheck_3646_ = (!lean_is_exclusive(v_date_3616_)) as u8;
                if v_isSharedCheck_3646_ == 0 {
                    v_unused_3647_ = lean_ctor_get(v_date_3616_, 0);
                    lean_dec(v_unused_3647_);
                    v___x_3621_ = v_date_3616_;
                    v_isShared_3622_ = v_isSharedCheck_3646_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_time_3619_);
                    lean_dec(v_date_3616_);
                    v___x_3621_ = lean_box(0);
                    v_isShared_3622_ = v_isSharedCheck_3646_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3622_ == 0 {
                    lean_ctor_set(v___x_3621_, 0, v___y_3618_);
                    v___x_3624_ = v___x_3621_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3645_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3645_, 0, v___y_3618_);
                    lean_ctor_set(v_reuseFailAlloc_3645_, 1, v_time_3619_);
                    v___x_3624_ = v_reuseFailAlloc_3645_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                lean_inc_ref(v___x_3624_);
                v_wt_3625_ = l_Std_Time_PlainDateTime_toWallTime(v___x_3624_);
                lean_inc_ref(v_rules_3612_);
                v_ltt_3626_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(
                    v_rules_3612_,
                    v_wt_3625_,
                );
                v_tz_3627_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_3626_);
                lean_dec_ref(v_ltt_3626_);
                v_offset_3628_ = lean_ctor_get(v_tz_3627_, 0);
                lean_inc(v_offset_3628_);
                v_second_3629_ = lean_ctor_get(v_wt_3625_, 0);
                lean_inc(v_second_3629_);
                v_nano_3630_ = lean_ctor_get(v_wt_3625_, 1);
                lean_inc(v_nano_3630_);
                lean_dec_ref(v_wt_3625_);
                v___f_3631_ = lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_3631_, 0, v___x_3624_);
                v___x_3632_ = lean_mk_thunk(v___f_3631_);
                v___x_3633_ = lean_int_neg(v_offset_3628_);
                lean_dec(v_offset_3628_);
                v___x_3634_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
                );
                v___x_3635_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3636_ = lean_int_mul(v_second_3629_, v___x_3635_);
                lean_dec(v_second_3629_);
                v___x_3637_ = lean_int_add(v___x_3636_, v_nano_3630_);
                lean_dec(v_nano_3630_);
                lean_dec(v___x_3636_);
                v___x_3638_ = lean_int_mul(v___x_3633_, v___x_3635_);
                lean_dec(v___x_3633_);
                v___x_3639_ = lean_int_add(v___x_3638_, v___x_3634_);
                lean_dec(v___x_3638_);
                v___x_3640_ = lean_int_add(v___x_3637_, v___x_3639_);
                lean_dec(v___x_3639_);
                lean_dec(v___x_3637_);
                v___x_3641_ = l_Std_Time_Duration_ofNanoseconds(v___x_3640_);
                lean_dec(v___x_3640_);
                if v_isShared_3615_ == 0 {
                    lean_ctor_set(v___x_3614_, 3, v_tz_3627_);
                    lean_ctor_set(v___x_3614_, 1, v___x_3641_);
                    lean_ctor_set(v___x_3614_, 0, v___x_3632_);
                    v___x_3643_ = v___x_3614_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3644_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3644_, 0, v___x_3632_);
                    lean_ctor_set(v_reuseFailAlloc_3644_, 1, v___x_3641_);
                    lean_ctor_set(v_reuseFailAlloc_3644_, 2, v_rules_3612_);
                    lean_ctor_set(v_reuseFailAlloc_3644_, 3, v_tz_3627_);
                    v___x_3643_ = v_reuseFailAlloc_3644_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3643_;
            }
            6 => {
                v___x_3664_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_dayOfYear___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_dayOfYear___closed__0_once),
                    _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__0,
                );
                v___x_3665_ = lean_int_mod(v_year_3649_, v___x_3664_);
                v___x_3666_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0,
                );
                v___x_3671_ = lean_int_dec_eq(v___x_3665_, v___x_3666_);
                lean_dec(v___x_3665_);
                if v___x_3671_ == 0 {
                    v___y_3655_ = v___x_3671_;
                    state = 7;
                    continue;
                } else {
                    v___x_3672_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_dayOfYear___closed__2),
                        core::ptr::addr_of_mut!(
                            l_Std_Time_ZonedDateTime_dayOfYear___closed__2_once
                        ),
                        _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__2,
                    );
                    v___x_3673_ = lean_int_mod(v_year_3649_, v___x_3672_);
                    v___x_3674_ = lean_int_dec_eq(v___x_3673_, v___x_3666_);
                    lean_dec(v___x_3673_);
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
                    lean_dec(v_max_3656_);
                    if v_isShared_3653_ == 0 {
                        lean_ctor_set(v___x_3652_, 1, v_month_3610_);
                        v___x_3659_ = v___x_3652_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_3660_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3660_, 0, v_year_3649_);
                        lean_ctor_set(v_reuseFailAlloc_3660_, 1, v_month_3610_);
                        lean_ctor_set(v_reuseFailAlloc_3660_, 2, v_day_3650_);
                        v___x_3659_ = v_reuseFailAlloc_3660_;
                        state = 8;
                        continue;
                    }
                } else {
                    lean_dec(v_day_3650_);
                    if v_isShared_3653_ == 0 {
                        lean_ctor_set(v___x_3652_, 2, v_max_3656_);
                        lean_ctor_set(v___x_3652_, 1, v_month_3610_);
                        v___x_3662_ = v___x_3652_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_3663_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3663_, 0, v_year_3649_);
                        lean_ctor_set(v_reuseFailAlloc_3663_, 1, v_month_3610_);
                        lean_ctor_set(v_reuseFailAlloc_3663_, 2, v_max_3656_);
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
                v___x_3668_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_dayOfYear___closed__1),
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_dayOfYear___closed__1_once),
                    _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__1,
                );
                v___x_3669_ = lean_int_mod(v_year_3649_, v___x_3668_);
                v___x_3670_ = lean_int_dec_eq(v___x_3669_, v___x_3666_);
                lean_dec(v___x_3669_);
                v___y_3655_ = v___x_3670_;
                state = 7;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_ZonedDateTime_withMonthRollOver(
    mut v_dt_3680_: *mut LeanObject,
    mut v_month_3681_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_3682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rules_3683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3686_: u8 = 0;
    let mut v_date_3687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_date_3688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_time_3689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3692_: u8 = 0;
    let mut v_year_3693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_day_3694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_wt_3698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ltt_3699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tz_3700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_offset_3701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_3702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_3703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3719_: u8 = 0;
    let mut v_isSharedCheck_3720_: u8 = 0;
    let mut v_unused_3721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3722_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_3682_ = lean_ctor_get(v_dt_3680_, 0);
                v_rules_3683_ = lean_ctor_get(v_dt_3680_, 2);
                v_isSharedCheck_3720_ = (!lean_is_exclusive(v_dt_3680_)) as u8;
                if v_isSharedCheck_3720_ == 0 {
                    v_unused_3721_ = lean_ctor_get(v_dt_3680_, 3);
                    lean_dec(v_unused_3721_);
                    v_unused_3722_ = lean_ctor_get(v_dt_3680_, 1);
                    lean_dec(v_unused_3722_);
                    v___x_3685_ = v_dt_3680_;
                    v_isShared_3686_ = v_isSharedCheck_3720_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_rules_3683_);
                    lean_inc(v_date_3682_);
                    lean_dec(v_dt_3680_);
                    v___x_3685_ = lean_box(0);
                    v_isShared_3686_ = v_isSharedCheck_3720_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_date_3687_ = lean_thunk_get_own(v_date_3682_);
                lean_dec_ref(v_date_3682_);
                v_date_3688_ = lean_ctor_get(v_date_3687_, 0);
                v_time_3689_ = lean_ctor_get(v_date_3687_, 1);
                v_isSharedCheck_3719_ = (!lean_is_exclusive(v_date_3687_)) as u8;
                if v_isSharedCheck_3719_ == 0 {
                    v___x_3691_ = v_date_3687_;
                    v_isShared_3692_ = v_isSharedCheck_3719_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_time_3689_);
                    lean_inc(v_date_3688_);
                    lean_dec(v_date_3687_);
                    v___x_3691_ = lean_box(0);
                    v_isShared_3692_ = v_isSharedCheck_3719_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_year_3693_ = lean_ctor_get(v_date_3688_, 0);
                lean_inc(v_year_3693_);
                v_day_3694_ = lean_ctor_get(v_date_3688_, 2);
                lean_inc(v_day_3694_);
                lean_dec_ref(v_date_3688_);
                v___x_3695_ =
                    l_Std_Time_PlainDate_rollOver(v_year_3693_, v_month_3681_, v_day_3694_);
                lean_dec(v_day_3694_);
                if v_isShared_3692_ == 0 {
                    lean_ctor_set(v___x_3691_, 0, v___x_3695_);
                    v___x_3697_ = v___x_3691_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3718_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3718_, 0, v___x_3695_);
                    lean_ctor_set(v_reuseFailAlloc_3718_, 1, v_time_3689_);
                    v___x_3697_ = v_reuseFailAlloc_3718_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_inc_ref(v___x_3697_);
                v_wt_3698_ = l_Std_Time_PlainDateTime_toWallTime(v___x_3697_);
                lean_inc_ref(v_rules_3683_);
                v_ltt_3699_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(
                    v_rules_3683_,
                    v_wt_3698_,
                );
                v_tz_3700_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_3699_);
                lean_dec_ref(v_ltt_3699_);
                v_offset_3701_ = lean_ctor_get(v_tz_3700_, 0);
                lean_inc(v_offset_3701_);
                v_second_3702_ = lean_ctor_get(v_wt_3698_, 0);
                lean_inc(v_second_3702_);
                v_nano_3703_ = lean_ctor_get(v_wt_3698_, 1);
                lean_inc(v_nano_3703_);
                lean_dec_ref(v_wt_3698_);
                v___f_3704_ = lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_3704_, 0, v___x_3697_);
                v___x_3705_ = lean_mk_thunk(v___f_3704_);
                v___x_3706_ = lean_int_neg(v_offset_3701_);
                lean_dec(v_offset_3701_);
                v___x_3707_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
                );
                v___x_3708_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3709_ = lean_int_mul(v_second_3702_, v___x_3708_);
                lean_dec(v_second_3702_);
                v___x_3710_ = lean_int_add(v___x_3709_, v_nano_3703_);
                lean_dec(v_nano_3703_);
                lean_dec(v___x_3709_);
                v___x_3711_ = lean_int_mul(v___x_3706_, v___x_3708_);
                lean_dec(v___x_3706_);
                v___x_3712_ = lean_int_add(v___x_3711_, v___x_3707_);
                lean_dec(v___x_3711_);
                v___x_3713_ = lean_int_add(v___x_3710_, v___x_3712_);
                lean_dec(v___x_3712_);
                lean_dec(v___x_3710_);
                v___x_3714_ = l_Std_Time_Duration_ofNanoseconds(v___x_3713_);
                lean_dec(v___x_3713_);
                if v_isShared_3686_ == 0 {
                    lean_ctor_set(v___x_3685_, 3, v_tz_3700_);
                    lean_ctor_set(v___x_3685_, 1, v___x_3714_);
                    lean_ctor_set(v___x_3685_, 0, v___x_3705_);
                    v___x_3716_ = v___x_3685_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3717_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3717_, 0, v___x_3705_);
                    lean_ctor_set(v_reuseFailAlloc_3717_, 1, v___x_3714_);
                    lean_ctor_set(v_reuseFailAlloc_3717_, 2, v_rules_3683_);
                    lean_ctor_set(v_reuseFailAlloc_3717_, 3, v_tz_3700_);
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
    mut v_dt_3723_: *mut LeanObject,
    mut v_year_3724_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_3725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rules_3726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3729_: u8 = 0;
    let mut v_date_3730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_time_3733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3736_: u8 = 0;
    let mut v___x_3738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_wt_3739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ltt_3740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tz_3741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_offset_3742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_3743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_3744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3760_: u8 = 0;
    let mut v_unused_3761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_date_3762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_month_3763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_day_3764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3767_: u8 = 0;
    let mut v___y_3769_: u8 = 0;
    let mut v_max_3770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3771_: u8 = 0;
    let mut v___x_3773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3784_: u8 = 0;
    let mut v___x_3785_: u8 = 0;
    let mut v___x_3786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3788_: u8 = 0;
    let mut v_isSharedCheck_3789_: u8 = 0;
    let mut v_unused_3790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3791_: u8 = 0;
    let mut v_unused_3792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3793_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_3725_ = lean_ctor_get(v_dt_3723_, 0);
                v_rules_3726_ = lean_ctor_get(v_dt_3723_, 2);
                v_isSharedCheck_3791_ = (!lean_is_exclusive(v_dt_3723_)) as u8;
                if v_isSharedCheck_3791_ == 0 {
                    v_unused_3792_ = lean_ctor_get(v_dt_3723_, 3);
                    lean_dec(v_unused_3792_);
                    v_unused_3793_ = lean_ctor_get(v_dt_3723_, 1);
                    lean_dec(v_unused_3793_);
                    v___x_3728_ = v_dt_3723_;
                    v_isShared_3729_ = v_isSharedCheck_3791_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_rules_3726_);
                    lean_inc(v_date_3725_);
                    lean_dec(v_dt_3723_);
                    v___x_3728_ = lean_box(0);
                    v_isShared_3729_ = v_isSharedCheck_3791_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_date_3730_ = lean_thunk_get_own(v_date_3725_);
                lean_dec_ref(v_date_3725_);
                v_date_3762_ = lean_ctor_get(v_date_3730_, 0);
                lean_inc_ref(v_date_3762_);
                v_month_3763_ = lean_ctor_get(v_date_3762_, 1);
                v_day_3764_ = lean_ctor_get(v_date_3762_, 2);
                v_isSharedCheck_3789_ = (!lean_is_exclusive(v_date_3762_)) as u8;
                if v_isSharedCheck_3789_ == 0 {
                    v_unused_3790_ = lean_ctor_get(v_date_3762_, 0);
                    lean_dec(v_unused_3790_);
                    v___x_3766_ = v_date_3762_;
                    v_isShared_3767_ = v_isSharedCheck_3789_;
                    state = 6;
                    continue;
                } else {
                    lean_inc(v_day_3764_);
                    lean_inc(v_month_3763_);
                    lean_dec(v_date_3762_);
                    v___x_3766_ = lean_box(0);
                    v_isShared_3767_ = v_isSharedCheck_3789_;
                    state = 6;
                    continue;
                }
            }
            2 => {
                v_time_3733_ = lean_ctor_get(v_date_3730_, 1);
                v_isSharedCheck_3760_ = (!lean_is_exclusive(v_date_3730_)) as u8;
                if v_isSharedCheck_3760_ == 0 {
                    v_unused_3761_ = lean_ctor_get(v_date_3730_, 0);
                    lean_dec(v_unused_3761_);
                    v___x_3735_ = v_date_3730_;
                    v_isShared_3736_ = v_isSharedCheck_3760_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_time_3733_);
                    lean_dec(v_date_3730_);
                    v___x_3735_ = lean_box(0);
                    v_isShared_3736_ = v_isSharedCheck_3760_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3736_ == 0 {
                    lean_ctor_set(v___x_3735_, 0, v___y_3732_);
                    v___x_3738_ = v___x_3735_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3759_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3759_, 0, v___y_3732_);
                    lean_ctor_set(v_reuseFailAlloc_3759_, 1, v_time_3733_);
                    v___x_3738_ = v_reuseFailAlloc_3759_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                lean_inc_ref(v___x_3738_);
                v_wt_3739_ = l_Std_Time_PlainDateTime_toWallTime(v___x_3738_);
                lean_inc_ref(v_rules_3726_);
                v_ltt_3740_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(
                    v_rules_3726_,
                    v_wt_3739_,
                );
                v_tz_3741_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_3740_);
                lean_dec_ref(v_ltt_3740_);
                v_offset_3742_ = lean_ctor_get(v_tz_3741_, 0);
                lean_inc(v_offset_3742_);
                v_second_3743_ = lean_ctor_get(v_wt_3739_, 0);
                lean_inc(v_second_3743_);
                v_nano_3744_ = lean_ctor_get(v_wt_3739_, 1);
                lean_inc(v_nano_3744_);
                lean_dec_ref(v_wt_3739_);
                v___f_3745_ = lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_3745_, 0, v___x_3738_);
                v___x_3746_ = lean_mk_thunk(v___f_3745_);
                v___x_3747_ = lean_int_neg(v_offset_3742_);
                lean_dec(v_offset_3742_);
                v___x_3748_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
                );
                v___x_3749_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3750_ = lean_int_mul(v_second_3743_, v___x_3749_);
                lean_dec(v_second_3743_);
                v___x_3751_ = lean_int_add(v___x_3750_, v_nano_3744_);
                lean_dec(v_nano_3744_);
                lean_dec(v___x_3750_);
                v___x_3752_ = lean_int_mul(v___x_3747_, v___x_3749_);
                lean_dec(v___x_3747_);
                v___x_3753_ = lean_int_add(v___x_3752_, v___x_3748_);
                lean_dec(v___x_3752_);
                v___x_3754_ = lean_int_add(v___x_3751_, v___x_3753_);
                lean_dec(v___x_3753_);
                lean_dec(v___x_3751_);
                v___x_3755_ = l_Std_Time_Duration_ofNanoseconds(v___x_3754_);
                lean_dec(v___x_3754_);
                if v_isShared_3729_ == 0 {
                    lean_ctor_set(v___x_3728_, 3, v_tz_3741_);
                    lean_ctor_set(v___x_3728_, 1, v___x_3755_);
                    lean_ctor_set(v___x_3728_, 0, v___x_3746_);
                    v___x_3757_ = v___x_3728_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3758_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3758_, 0, v___x_3746_);
                    lean_ctor_set(v_reuseFailAlloc_3758_, 1, v___x_3755_);
                    lean_ctor_set(v_reuseFailAlloc_3758_, 2, v_rules_3726_);
                    lean_ctor_set(v_reuseFailAlloc_3758_, 3, v_tz_3741_);
                    v___x_3757_ = v_reuseFailAlloc_3758_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3757_;
            }
            6 => {
                v___x_3778_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_dayOfYear___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_dayOfYear___closed__0_once),
                    _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__0,
                );
                v___x_3779_ = lean_int_mod(v_year_3724_, v___x_3778_);
                v___x_3780_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0,
                );
                v___x_3785_ = lean_int_dec_eq(v___x_3779_, v___x_3780_);
                lean_dec(v___x_3779_);
                if v___x_3785_ == 0 {
                    v___y_3769_ = v___x_3785_;
                    state = 7;
                    continue;
                } else {
                    v___x_3786_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_dayOfYear___closed__2),
                        core::ptr::addr_of_mut!(
                            l_Std_Time_ZonedDateTime_dayOfYear___closed__2_once
                        ),
                        _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__2,
                    );
                    v___x_3787_ = lean_int_mod(v_year_3724_, v___x_3786_);
                    v___x_3788_ = lean_int_dec_eq(v___x_3787_, v___x_3780_);
                    lean_dec(v___x_3787_);
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
                    lean_dec(v_max_3770_);
                    if v_isShared_3767_ == 0 {
                        lean_ctor_set(v___x_3766_, 0, v_year_3724_);
                        v___x_3773_ = v___x_3766_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_3774_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3774_, 0, v_year_3724_);
                        lean_ctor_set(v_reuseFailAlloc_3774_, 1, v_month_3763_);
                        lean_ctor_set(v_reuseFailAlloc_3774_, 2, v_day_3764_);
                        v___x_3773_ = v_reuseFailAlloc_3774_;
                        state = 8;
                        continue;
                    }
                } else {
                    lean_dec(v_day_3764_);
                    if v_isShared_3767_ == 0 {
                        lean_ctor_set(v___x_3766_, 2, v_max_3770_);
                        lean_ctor_set(v___x_3766_, 0, v_year_3724_);
                        v___x_3776_ = v___x_3766_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_3777_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3777_, 0, v_year_3724_);
                        lean_ctor_set(v_reuseFailAlloc_3777_, 1, v_month_3763_);
                        lean_ctor_set(v_reuseFailAlloc_3777_, 2, v_max_3770_);
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
                v___x_3782_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_dayOfYear___closed__1),
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_dayOfYear___closed__1_once),
                    _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__1,
                );
                v___x_3783_ = lean_int_mod(v_year_3724_, v___x_3782_);
                v___x_3784_ = lean_int_dec_eq(v___x_3783_, v___x_3780_);
                lean_dec(v___x_3783_);
                v___y_3769_ = v___x_3784_;
                state = 7;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_ZonedDateTime_withYearRollOver(
    mut v_dt_3794_: *mut LeanObject,
    mut v_year_3795_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_3796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rules_3797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3800_: u8 = 0;
    let mut v_date_3801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_date_3802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_time_3803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3806_: u8 = 0;
    let mut v_month_3807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_day_3808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_wt_3812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ltt_3813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tz_3814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_offset_3815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_3816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_3817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3833_: u8 = 0;
    let mut v_isSharedCheck_3834_: u8 = 0;
    let mut v_unused_3835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3836_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_3796_ = lean_ctor_get(v_dt_3794_, 0);
                v_rules_3797_ = lean_ctor_get(v_dt_3794_, 2);
                v_isSharedCheck_3834_ = (!lean_is_exclusive(v_dt_3794_)) as u8;
                if v_isSharedCheck_3834_ == 0 {
                    v_unused_3835_ = lean_ctor_get(v_dt_3794_, 3);
                    lean_dec(v_unused_3835_);
                    v_unused_3836_ = lean_ctor_get(v_dt_3794_, 1);
                    lean_dec(v_unused_3836_);
                    v___x_3799_ = v_dt_3794_;
                    v_isShared_3800_ = v_isSharedCheck_3834_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_rules_3797_);
                    lean_inc(v_date_3796_);
                    lean_dec(v_dt_3794_);
                    v___x_3799_ = lean_box(0);
                    v_isShared_3800_ = v_isSharedCheck_3834_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_date_3801_ = lean_thunk_get_own(v_date_3796_);
                lean_dec_ref(v_date_3796_);
                v_date_3802_ = lean_ctor_get(v_date_3801_, 0);
                v_time_3803_ = lean_ctor_get(v_date_3801_, 1);
                v_isSharedCheck_3833_ = (!lean_is_exclusive(v_date_3801_)) as u8;
                if v_isSharedCheck_3833_ == 0 {
                    v___x_3805_ = v_date_3801_;
                    v_isShared_3806_ = v_isSharedCheck_3833_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_time_3803_);
                    lean_inc(v_date_3802_);
                    lean_dec(v_date_3801_);
                    v___x_3805_ = lean_box(0);
                    v_isShared_3806_ = v_isSharedCheck_3833_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_month_3807_ = lean_ctor_get(v_date_3802_, 1);
                lean_inc(v_month_3807_);
                v_day_3808_ = lean_ctor_get(v_date_3802_, 2);
                lean_inc(v_day_3808_);
                lean_dec_ref(v_date_3802_);
                v___x_3809_ =
                    l_Std_Time_PlainDate_rollOver(v_year_3795_, v_month_3807_, v_day_3808_);
                lean_dec(v_day_3808_);
                if v_isShared_3806_ == 0 {
                    lean_ctor_set(v___x_3805_, 0, v___x_3809_);
                    v___x_3811_ = v___x_3805_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3832_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3832_, 0, v___x_3809_);
                    lean_ctor_set(v_reuseFailAlloc_3832_, 1, v_time_3803_);
                    v___x_3811_ = v_reuseFailAlloc_3832_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_inc_ref(v___x_3811_);
                v_wt_3812_ = l_Std_Time_PlainDateTime_toWallTime(v___x_3811_);
                lean_inc_ref(v_rules_3797_);
                v_ltt_3813_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(
                    v_rules_3797_,
                    v_wt_3812_,
                );
                v_tz_3814_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_3813_);
                lean_dec_ref(v_ltt_3813_);
                v_offset_3815_ = lean_ctor_get(v_tz_3814_, 0);
                lean_inc(v_offset_3815_);
                v_second_3816_ = lean_ctor_get(v_wt_3812_, 0);
                lean_inc(v_second_3816_);
                v_nano_3817_ = lean_ctor_get(v_wt_3812_, 1);
                lean_inc(v_nano_3817_);
                lean_dec_ref(v_wt_3812_);
                v___f_3818_ = lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_3818_, 0, v___x_3811_);
                v___x_3819_ = lean_mk_thunk(v___f_3818_);
                v___x_3820_ = lean_int_neg(v_offset_3815_);
                lean_dec(v_offset_3815_);
                v___x_3821_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
                );
                v___x_3822_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3823_ = lean_int_mul(v_second_3816_, v___x_3822_);
                lean_dec(v_second_3816_);
                v___x_3824_ = lean_int_add(v___x_3823_, v_nano_3817_);
                lean_dec(v_nano_3817_);
                lean_dec(v___x_3823_);
                v___x_3825_ = lean_int_mul(v___x_3820_, v___x_3822_);
                lean_dec(v___x_3820_);
                v___x_3826_ = lean_int_add(v___x_3825_, v___x_3821_);
                lean_dec(v___x_3825_);
                v___x_3827_ = lean_int_add(v___x_3824_, v___x_3826_);
                lean_dec(v___x_3826_);
                lean_dec(v___x_3824_);
                v___x_3828_ = l_Std_Time_Duration_ofNanoseconds(v___x_3827_);
                lean_dec(v___x_3827_);
                if v_isShared_3800_ == 0 {
                    lean_ctor_set(v___x_3799_, 3, v_tz_3814_);
                    lean_ctor_set(v___x_3799_, 1, v___x_3828_);
                    lean_ctor_set(v___x_3799_, 0, v___x_3819_);
                    v___x_3830_ = v___x_3799_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3831_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3831_, 0, v___x_3819_);
                    lean_ctor_set(v_reuseFailAlloc_3831_, 1, v___x_3828_);
                    lean_ctor_set(v_reuseFailAlloc_3831_, 2, v_rules_3797_);
                    lean_ctor_set(v_reuseFailAlloc_3831_, 3, v_tz_3814_);
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
    mut v_dt_3837_: *mut LeanObject,
    mut v_hour_3838_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_3839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rules_3840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3843_: u8 = 0;
    let mut v_date_3844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_time_3845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_date_3846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3849_: u8 = 0;
    let mut v_minute_3850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_3851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_3852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3855_: u8 = 0;
    let mut v___x_3857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_wt_3860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ltt_3861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tz_3862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_offset_3863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_3864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_3865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3882_: u8 = 0;
    let mut v_unused_3883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3884_: u8 = 0;
    let mut v_isSharedCheck_3885_: u8 = 0;
    let mut v_unused_3886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3887_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_3839_ = lean_ctor_get(v_dt_3837_, 0);
                v_rules_3840_ = lean_ctor_get(v_dt_3837_, 2);
                v_isSharedCheck_3885_ = (!lean_is_exclusive(v_dt_3837_)) as u8;
                if v_isSharedCheck_3885_ == 0 {
                    v_unused_3886_ = lean_ctor_get(v_dt_3837_, 3);
                    lean_dec(v_unused_3886_);
                    v_unused_3887_ = lean_ctor_get(v_dt_3837_, 1);
                    lean_dec(v_unused_3887_);
                    v___x_3842_ = v_dt_3837_;
                    v_isShared_3843_ = v_isSharedCheck_3885_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_rules_3840_);
                    lean_inc(v_date_3839_);
                    lean_dec(v_dt_3837_);
                    v___x_3842_ = lean_box(0);
                    v_isShared_3843_ = v_isSharedCheck_3885_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_date_3844_ = lean_thunk_get_own(v_date_3839_);
                lean_dec_ref(v_date_3839_);
                v_time_3845_ = lean_ctor_get(v_date_3844_, 1);
                v_date_3846_ = lean_ctor_get(v_date_3844_, 0);
                v_isSharedCheck_3884_ = (!lean_is_exclusive(v_date_3844_)) as u8;
                if v_isSharedCheck_3884_ == 0 {
                    v___x_3848_ = v_date_3844_;
                    v_isShared_3849_ = v_isSharedCheck_3884_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_time_3845_);
                    lean_inc(v_date_3846_);
                    lean_dec(v_date_3844_);
                    v___x_3848_ = lean_box(0);
                    v_isShared_3849_ = v_isSharedCheck_3884_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_minute_3850_ = lean_ctor_get(v_time_3845_, 1);
                v_second_3851_ = lean_ctor_get(v_time_3845_, 2);
                v_nanosecond_3852_ = lean_ctor_get(v_time_3845_, 3);
                v_isSharedCheck_3882_ = (!lean_is_exclusive(v_time_3845_)) as u8;
                if v_isSharedCheck_3882_ == 0 {
                    v_unused_3883_ = lean_ctor_get(v_time_3845_, 0);
                    lean_dec(v_unused_3883_);
                    v___x_3854_ = v_time_3845_;
                    v_isShared_3855_ = v_isSharedCheck_3882_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_nanosecond_3852_);
                    lean_inc(v_second_3851_);
                    lean_inc(v_minute_3850_);
                    lean_dec(v_time_3845_);
                    v___x_3854_ = lean_box(0);
                    v_isShared_3855_ = v_isSharedCheck_3882_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3855_ == 0 {
                    lean_ctor_set(v___x_3854_, 0, v_hour_3838_);
                    v___x_3857_ = v___x_3854_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3881_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3881_, 0, v_hour_3838_);
                    lean_ctor_set(v_reuseFailAlloc_3881_, 1, v_minute_3850_);
                    lean_ctor_set(v_reuseFailAlloc_3881_, 2, v_second_3851_);
                    lean_ctor_set(v_reuseFailAlloc_3881_, 3, v_nanosecond_3852_);
                    v___x_3857_ = v_reuseFailAlloc_3881_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3849_ == 0 {
                    lean_ctor_set(v___x_3848_, 1, v___x_3857_);
                    v___x_3859_ = v___x_3848_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3880_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3880_, 0, v_date_3846_);
                    lean_ctor_set(v_reuseFailAlloc_3880_, 1, v___x_3857_);
                    v___x_3859_ = v_reuseFailAlloc_3880_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                lean_inc_ref(v___x_3859_);
                v_wt_3860_ = l_Std_Time_PlainDateTime_toWallTime(v___x_3859_);
                lean_inc_ref(v_rules_3840_);
                v_ltt_3861_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(
                    v_rules_3840_,
                    v_wt_3860_,
                );
                v_tz_3862_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_3861_);
                lean_dec_ref(v_ltt_3861_);
                v_offset_3863_ = lean_ctor_get(v_tz_3862_, 0);
                lean_inc(v_offset_3863_);
                v_second_3864_ = lean_ctor_get(v_wt_3860_, 0);
                lean_inc(v_second_3864_);
                v_nano_3865_ = lean_ctor_get(v_wt_3860_, 1);
                lean_inc(v_nano_3865_);
                lean_dec_ref(v_wt_3860_);
                v___f_3866_ = lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_3866_, 0, v___x_3859_);
                v___x_3867_ = lean_mk_thunk(v___f_3866_);
                v___x_3868_ = lean_int_neg(v_offset_3863_);
                lean_dec(v_offset_3863_);
                v___x_3869_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
                );
                v___x_3870_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3871_ = lean_int_mul(v_second_3864_, v___x_3870_);
                lean_dec(v_second_3864_);
                v___x_3872_ = lean_int_add(v___x_3871_, v_nano_3865_);
                lean_dec(v_nano_3865_);
                lean_dec(v___x_3871_);
                v___x_3873_ = lean_int_mul(v___x_3868_, v___x_3870_);
                lean_dec(v___x_3868_);
                v___x_3874_ = lean_int_add(v___x_3873_, v___x_3869_);
                lean_dec(v___x_3873_);
                v___x_3875_ = lean_int_add(v___x_3872_, v___x_3874_);
                lean_dec(v___x_3874_);
                lean_dec(v___x_3872_);
                v___x_3876_ = l_Std_Time_Duration_ofNanoseconds(v___x_3875_);
                lean_dec(v___x_3875_);
                if v_isShared_3843_ == 0 {
                    lean_ctor_set(v___x_3842_, 3, v_tz_3862_);
                    lean_ctor_set(v___x_3842_, 1, v___x_3876_);
                    lean_ctor_set(v___x_3842_, 0, v___x_3867_);
                    v___x_3878_ = v___x_3842_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3879_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3879_, 0, v___x_3867_);
                    lean_ctor_set(v_reuseFailAlloc_3879_, 1, v___x_3876_);
                    lean_ctor_set(v_reuseFailAlloc_3879_, 2, v_rules_3840_);
                    lean_ctor_set(v_reuseFailAlloc_3879_, 3, v_tz_3862_);
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
    mut v_dt_3888_: *mut LeanObject,
    mut v_minute_3889_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_3890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rules_3891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3894_: u8 = 0;
    let mut v_date_3895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_time_3896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_date_3897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3900_: u8 = 0;
    let mut v_hour_3901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_3902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_3903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3906_: u8 = 0;
    let mut v___x_3908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_wt_3911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ltt_3912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tz_3913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_offset_3914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_3915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_3916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3933_: u8 = 0;
    let mut v_unused_3934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3935_: u8 = 0;
    let mut v_isSharedCheck_3936_: u8 = 0;
    let mut v_unused_3937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3938_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_3890_ = lean_ctor_get(v_dt_3888_, 0);
                v_rules_3891_ = lean_ctor_get(v_dt_3888_, 2);
                v_isSharedCheck_3936_ = (!lean_is_exclusive(v_dt_3888_)) as u8;
                if v_isSharedCheck_3936_ == 0 {
                    v_unused_3937_ = lean_ctor_get(v_dt_3888_, 3);
                    lean_dec(v_unused_3937_);
                    v_unused_3938_ = lean_ctor_get(v_dt_3888_, 1);
                    lean_dec(v_unused_3938_);
                    v___x_3893_ = v_dt_3888_;
                    v_isShared_3894_ = v_isSharedCheck_3936_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_rules_3891_);
                    lean_inc(v_date_3890_);
                    lean_dec(v_dt_3888_);
                    v___x_3893_ = lean_box(0);
                    v_isShared_3894_ = v_isSharedCheck_3936_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_date_3895_ = lean_thunk_get_own(v_date_3890_);
                lean_dec_ref(v_date_3890_);
                v_time_3896_ = lean_ctor_get(v_date_3895_, 1);
                v_date_3897_ = lean_ctor_get(v_date_3895_, 0);
                v_isSharedCheck_3935_ = (!lean_is_exclusive(v_date_3895_)) as u8;
                if v_isSharedCheck_3935_ == 0 {
                    v___x_3899_ = v_date_3895_;
                    v_isShared_3900_ = v_isSharedCheck_3935_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_time_3896_);
                    lean_inc(v_date_3897_);
                    lean_dec(v_date_3895_);
                    v___x_3899_ = lean_box(0);
                    v_isShared_3900_ = v_isSharedCheck_3935_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_hour_3901_ = lean_ctor_get(v_time_3896_, 0);
                v_second_3902_ = lean_ctor_get(v_time_3896_, 2);
                v_nanosecond_3903_ = lean_ctor_get(v_time_3896_, 3);
                v_isSharedCheck_3933_ = (!lean_is_exclusive(v_time_3896_)) as u8;
                if v_isSharedCheck_3933_ == 0 {
                    v_unused_3934_ = lean_ctor_get(v_time_3896_, 1);
                    lean_dec(v_unused_3934_);
                    v___x_3905_ = v_time_3896_;
                    v_isShared_3906_ = v_isSharedCheck_3933_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_nanosecond_3903_);
                    lean_inc(v_second_3902_);
                    lean_inc(v_hour_3901_);
                    lean_dec(v_time_3896_);
                    v___x_3905_ = lean_box(0);
                    v_isShared_3906_ = v_isSharedCheck_3933_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3906_ == 0 {
                    lean_ctor_set(v___x_3905_, 1, v_minute_3889_);
                    v___x_3908_ = v___x_3905_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3932_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3932_, 0, v_hour_3901_);
                    lean_ctor_set(v_reuseFailAlloc_3932_, 1, v_minute_3889_);
                    lean_ctor_set(v_reuseFailAlloc_3932_, 2, v_second_3902_);
                    lean_ctor_set(v_reuseFailAlloc_3932_, 3, v_nanosecond_3903_);
                    v___x_3908_ = v_reuseFailAlloc_3932_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3900_ == 0 {
                    lean_ctor_set(v___x_3899_, 1, v___x_3908_);
                    v___x_3910_ = v___x_3899_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3931_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3931_, 0, v_date_3897_);
                    lean_ctor_set(v_reuseFailAlloc_3931_, 1, v___x_3908_);
                    v___x_3910_ = v_reuseFailAlloc_3931_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                lean_inc_ref(v___x_3910_);
                v_wt_3911_ = l_Std_Time_PlainDateTime_toWallTime(v___x_3910_);
                lean_inc_ref(v_rules_3891_);
                v_ltt_3912_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(
                    v_rules_3891_,
                    v_wt_3911_,
                );
                v_tz_3913_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_3912_);
                lean_dec_ref(v_ltt_3912_);
                v_offset_3914_ = lean_ctor_get(v_tz_3913_, 0);
                lean_inc(v_offset_3914_);
                v_second_3915_ = lean_ctor_get(v_wt_3911_, 0);
                lean_inc(v_second_3915_);
                v_nano_3916_ = lean_ctor_get(v_wt_3911_, 1);
                lean_inc(v_nano_3916_);
                lean_dec_ref(v_wt_3911_);
                v___f_3917_ = lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_3917_, 0, v___x_3910_);
                v___x_3918_ = lean_mk_thunk(v___f_3917_);
                v___x_3919_ = lean_int_neg(v_offset_3914_);
                lean_dec(v_offset_3914_);
                v___x_3920_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
                );
                v___x_3921_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3922_ = lean_int_mul(v_second_3915_, v___x_3921_);
                lean_dec(v_second_3915_);
                v___x_3923_ = lean_int_add(v___x_3922_, v_nano_3916_);
                lean_dec(v_nano_3916_);
                lean_dec(v___x_3922_);
                v___x_3924_ = lean_int_mul(v___x_3919_, v___x_3921_);
                lean_dec(v___x_3919_);
                v___x_3925_ = lean_int_add(v___x_3924_, v___x_3920_);
                lean_dec(v___x_3924_);
                v___x_3926_ = lean_int_add(v___x_3923_, v___x_3925_);
                lean_dec(v___x_3925_);
                lean_dec(v___x_3923_);
                v___x_3927_ = l_Std_Time_Duration_ofNanoseconds(v___x_3926_);
                lean_dec(v___x_3926_);
                if v_isShared_3894_ == 0 {
                    lean_ctor_set(v___x_3893_, 3, v_tz_3913_);
                    lean_ctor_set(v___x_3893_, 1, v___x_3927_);
                    lean_ctor_set(v___x_3893_, 0, v___x_3918_);
                    v___x_3929_ = v___x_3893_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3930_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3930_, 0, v___x_3918_);
                    lean_ctor_set(v_reuseFailAlloc_3930_, 1, v___x_3927_);
                    lean_ctor_set(v_reuseFailAlloc_3930_, 2, v_rules_3891_);
                    lean_ctor_set(v_reuseFailAlloc_3930_, 3, v_tz_3913_);
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
    mut v_dt_3939_: *mut LeanObject,
    mut v_second_3940_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_3941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rules_3942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3945_: u8 = 0;
    let mut v_date_3946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_time_3947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_date_3948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3951_: u8 = 0;
    let mut v_hour_3952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_minute_3953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_3954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3957_: u8 = 0;
    let mut v___x_3959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_wt_3962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ltt_3963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tz_3964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_offset_3965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_3966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_3967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3984_: u8 = 0;
    let mut v_unused_3985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3986_: u8 = 0;
    let mut v_isSharedCheck_3987_: u8 = 0;
    let mut v_unused_3988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3989_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_3941_ = lean_ctor_get(v_dt_3939_, 0);
                v_rules_3942_ = lean_ctor_get(v_dt_3939_, 2);
                v_isSharedCheck_3987_ = (!lean_is_exclusive(v_dt_3939_)) as u8;
                if v_isSharedCheck_3987_ == 0 {
                    v_unused_3988_ = lean_ctor_get(v_dt_3939_, 3);
                    lean_dec(v_unused_3988_);
                    v_unused_3989_ = lean_ctor_get(v_dt_3939_, 1);
                    lean_dec(v_unused_3989_);
                    v___x_3944_ = v_dt_3939_;
                    v_isShared_3945_ = v_isSharedCheck_3987_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_rules_3942_);
                    lean_inc(v_date_3941_);
                    lean_dec(v_dt_3939_);
                    v___x_3944_ = lean_box(0);
                    v_isShared_3945_ = v_isSharedCheck_3987_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_date_3946_ = lean_thunk_get_own(v_date_3941_);
                lean_dec_ref(v_date_3941_);
                v_time_3947_ = lean_ctor_get(v_date_3946_, 1);
                v_date_3948_ = lean_ctor_get(v_date_3946_, 0);
                v_isSharedCheck_3986_ = (!lean_is_exclusive(v_date_3946_)) as u8;
                if v_isSharedCheck_3986_ == 0 {
                    v___x_3950_ = v_date_3946_;
                    v_isShared_3951_ = v_isSharedCheck_3986_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_time_3947_);
                    lean_inc(v_date_3948_);
                    lean_dec(v_date_3946_);
                    v___x_3950_ = lean_box(0);
                    v_isShared_3951_ = v_isSharedCheck_3986_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_hour_3952_ = lean_ctor_get(v_time_3947_, 0);
                v_minute_3953_ = lean_ctor_get(v_time_3947_, 1);
                v_nanosecond_3954_ = lean_ctor_get(v_time_3947_, 3);
                v_isSharedCheck_3984_ = (!lean_is_exclusive(v_time_3947_)) as u8;
                if v_isSharedCheck_3984_ == 0 {
                    v_unused_3985_ = lean_ctor_get(v_time_3947_, 2);
                    lean_dec(v_unused_3985_);
                    v___x_3956_ = v_time_3947_;
                    v_isShared_3957_ = v_isSharedCheck_3984_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_nanosecond_3954_);
                    lean_inc(v_minute_3953_);
                    lean_inc(v_hour_3952_);
                    lean_dec(v_time_3947_);
                    v___x_3956_ = lean_box(0);
                    v_isShared_3957_ = v_isSharedCheck_3984_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3957_ == 0 {
                    lean_ctor_set(v___x_3956_, 2, v_second_3940_);
                    v___x_3959_ = v___x_3956_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3983_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3983_, 0, v_hour_3952_);
                    lean_ctor_set(v_reuseFailAlloc_3983_, 1, v_minute_3953_);
                    lean_ctor_set(v_reuseFailAlloc_3983_, 2, v_second_3940_);
                    lean_ctor_set(v_reuseFailAlloc_3983_, 3, v_nanosecond_3954_);
                    v___x_3959_ = v_reuseFailAlloc_3983_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3951_ == 0 {
                    lean_ctor_set(v___x_3950_, 1, v___x_3959_);
                    v___x_3961_ = v___x_3950_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3982_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3982_, 0, v_date_3948_);
                    lean_ctor_set(v_reuseFailAlloc_3982_, 1, v___x_3959_);
                    v___x_3961_ = v_reuseFailAlloc_3982_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                lean_inc_ref(v___x_3961_);
                v_wt_3962_ = l_Std_Time_PlainDateTime_toWallTime(v___x_3961_);
                lean_inc_ref(v_rules_3942_);
                v_ltt_3963_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(
                    v_rules_3942_,
                    v_wt_3962_,
                );
                v_tz_3964_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_3963_);
                lean_dec_ref(v_ltt_3963_);
                v_offset_3965_ = lean_ctor_get(v_tz_3964_, 0);
                lean_inc(v_offset_3965_);
                v_second_3966_ = lean_ctor_get(v_wt_3962_, 0);
                lean_inc(v_second_3966_);
                v_nano_3967_ = lean_ctor_get(v_wt_3962_, 1);
                lean_inc(v_nano_3967_);
                lean_dec_ref(v_wt_3962_);
                v___f_3968_ = lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_3968_, 0, v___x_3961_);
                v___x_3969_ = lean_mk_thunk(v___f_3968_);
                v___x_3970_ = lean_int_neg(v_offset_3965_);
                lean_dec(v_offset_3965_);
                v___x_3971_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
                );
                v___x_3972_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3973_ = lean_int_mul(v_second_3966_, v___x_3972_);
                lean_dec(v_second_3966_);
                v___x_3974_ = lean_int_add(v___x_3973_, v_nano_3967_);
                lean_dec(v_nano_3967_);
                lean_dec(v___x_3973_);
                v___x_3975_ = lean_int_mul(v___x_3970_, v___x_3972_);
                lean_dec(v___x_3970_);
                v___x_3976_ = lean_int_add(v___x_3975_, v___x_3971_);
                lean_dec(v___x_3975_);
                v___x_3977_ = lean_int_add(v___x_3974_, v___x_3976_);
                lean_dec(v___x_3976_);
                lean_dec(v___x_3974_);
                v___x_3978_ = l_Std_Time_Duration_ofNanoseconds(v___x_3977_);
                lean_dec(v___x_3977_);
                if v_isShared_3945_ == 0 {
                    lean_ctor_set(v___x_3944_, 3, v_tz_3964_);
                    lean_ctor_set(v___x_3944_, 1, v___x_3978_);
                    lean_ctor_set(v___x_3944_, 0, v___x_3969_);
                    v___x_3980_ = v___x_3944_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3981_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3981_, 0, v___x_3969_);
                    lean_ctor_set(v_reuseFailAlloc_3981_, 1, v___x_3978_);
                    lean_ctor_set(v_reuseFailAlloc_3981_, 2, v_rules_3942_);
                    lean_ctor_set(v_reuseFailAlloc_3981_, 3, v_tz_3964_);
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
pub unsafe fn _init_l_Std_Time_ZonedDateTime_withMilliseconds___closed__0() -> *mut LeanObject {
    let mut v___x_3990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: *mut LeanObject = core::ptr::null_mut();
    v___x_3990_ = lean_unsigned_to_nat(1000);
    v___x_3991_ = lean_nat_to_int(v___x_3990_);
    return v___x_3991_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_withMilliseconds(
    mut v_dt_3992_: *mut LeanObject,
    mut v_millis_3993_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_3994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rules_3995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3998_: u8 = 0;
    let mut v_date_3999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_time_4000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_date_4001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4004_: u8 = 0;
    let mut v_hour_4005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_minute_4006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_4007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_4008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4011_: u8 = 0;
    let mut v___x_4012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_wt_4021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ltt_4022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tz_4023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_offset_4024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_4025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_4026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4043_: u8 = 0;
    let mut v_isSharedCheck_4044_: u8 = 0;
    let mut v_isSharedCheck_4045_: u8 = 0;
    let mut v_unused_4046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4047_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_3994_ = lean_ctor_get(v_dt_3992_, 0);
                v_rules_3995_ = lean_ctor_get(v_dt_3992_, 2);
                v_isSharedCheck_4045_ = (!lean_is_exclusive(v_dt_3992_)) as u8;
                if v_isSharedCheck_4045_ == 0 {
                    v_unused_4046_ = lean_ctor_get(v_dt_3992_, 3);
                    lean_dec(v_unused_4046_);
                    v_unused_4047_ = lean_ctor_get(v_dt_3992_, 1);
                    lean_dec(v_unused_4047_);
                    v___x_3997_ = v_dt_3992_;
                    v_isShared_3998_ = v_isSharedCheck_4045_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_rules_3995_);
                    lean_inc(v_date_3994_);
                    lean_dec(v_dt_3992_);
                    v___x_3997_ = lean_box(0);
                    v_isShared_3998_ = v_isSharedCheck_4045_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_date_3999_ = lean_thunk_get_own(v_date_3994_);
                lean_dec_ref(v_date_3994_);
                v_time_4000_ = lean_ctor_get(v_date_3999_, 1);
                v_date_4001_ = lean_ctor_get(v_date_3999_, 0);
                v_isSharedCheck_4044_ = (!lean_is_exclusive(v_date_3999_)) as u8;
                if v_isSharedCheck_4044_ == 0 {
                    v___x_4003_ = v_date_3999_;
                    v_isShared_4004_ = v_isSharedCheck_4044_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_time_4000_);
                    lean_inc(v_date_4001_);
                    lean_dec(v_date_3999_);
                    v___x_4003_ = lean_box(0);
                    v_isShared_4004_ = v_isSharedCheck_4044_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_hour_4005_ = lean_ctor_get(v_time_4000_, 0);
                v_minute_4006_ = lean_ctor_get(v_time_4000_, 1);
                v_second_4007_ = lean_ctor_get(v_time_4000_, 2);
                v_nanosecond_4008_ = lean_ctor_get(v_time_4000_, 3);
                v_isSharedCheck_4043_ = (!lean_is_exclusive(v_time_4000_)) as u8;
                if v_isSharedCheck_4043_ == 0 {
                    v___x_4010_ = v_time_4000_;
                    v_isShared_4011_ = v_isSharedCheck_4043_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_nanosecond_4008_);
                    lean_inc(v_second_4007_);
                    lean_inc(v_minute_4006_);
                    lean_inc(v_hour_4005_);
                    lean_dec(v_time_4000_);
                    v___x_4010_ = lean_box(0);
                    v_isShared_4011_ = v_isSharedCheck_4043_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4012_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_withMilliseconds___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_withMilliseconds___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_withMilliseconds___closed__0,
                );
                v___x_4013_ = lean_int_emod(v_nanosecond_4008_, v___x_4012_);
                lean_dec(v_nanosecond_4008_);
                v___x_4014_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_millisecond___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_millisecond___closed__0_once),
                    _init_l_Std_Time_ZonedDateTime_millisecond___closed__0,
                );
                v___x_4015_ = lean_int_mul(v_millis_3993_, v___x_4014_);
                v___x_4016_ = lean_int_add(v___x_4015_, v___x_4013_);
                lean_dec(v___x_4013_);
                lean_dec(v___x_4015_);
                if v_isShared_4011_ == 0 {
                    lean_ctor_set(v___x_4010_, 3, v___x_4016_);
                    v___x_4018_ = v___x_4010_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4042_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4042_, 0, v_hour_4005_);
                    lean_ctor_set(v_reuseFailAlloc_4042_, 1, v_minute_4006_);
                    lean_ctor_set(v_reuseFailAlloc_4042_, 2, v_second_4007_);
                    lean_ctor_set(v_reuseFailAlloc_4042_, 3, v___x_4016_);
                    v___x_4018_ = v_reuseFailAlloc_4042_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4004_ == 0 {
                    lean_ctor_set(v___x_4003_, 1, v___x_4018_);
                    v___x_4020_ = v___x_4003_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4041_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4041_, 0, v_date_4001_);
                    lean_ctor_set(v_reuseFailAlloc_4041_, 1, v___x_4018_);
                    v___x_4020_ = v_reuseFailAlloc_4041_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                lean_inc_ref(v___x_4020_);
                v_wt_4021_ = l_Std_Time_PlainDateTime_toWallTime(v___x_4020_);
                lean_inc_ref(v_rules_3995_);
                v_ltt_4022_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(
                    v_rules_3995_,
                    v_wt_4021_,
                );
                v_tz_4023_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_4022_);
                lean_dec_ref(v_ltt_4022_);
                v_offset_4024_ = lean_ctor_get(v_tz_4023_, 0);
                lean_inc(v_offset_4024_);
                v_second_4025_ = lean_ctor_get(v_wt_4021_, 0);
                lean_inc(v_second_4025_);
                v_nano_4026_ = lean_ctor_get(v_wt_4021_, 1);
                lean_inc(v_nano_4026_);
                lean_dec_ref(v_wt_4021_);
                v___f_4027_ = lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_4027_, 0, v___x_4020_);
                v___x_4028_ = lean_mk_thunk(v___f_4027_);
                v___x_4029_ = lean_int_neg(v_offset_4024_);
                lean_dec(v_offset_4024_);
                v___x_4030_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
                );
                v___x_4031_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_4032_ = lean_int_mul(v_second_4025_, v___x_4031_);
                lean_dec(v_second_4025_);
                v___x_4033_ = lean_int_add(v___x_4032_, v_nano_4026_);
                lean_dec(v_nano_4026_);
                lean_dec(v___x_4032_);
                v___x_4034_ = lean_int_mul(v___x_4029_, v___x_4031_);
                lean_dec(v___x_4029_);
                v___x_4035_ = lean_int_add(v___x_4034_, v___x_4030_);
                lean_dec(v___x_4034_);
                v___x_4036_ = lean_int_add(v___x_4033_, v___x_4035_);
                lean_dec(v___x_4035_);
                lean_dec(v___x_4033_);
                v___x_4037_ = l_Std_Time_Duration_ofNanoseconds(v___x_4036_);
                lean_dec(v___x_4036_);
                if v_isShared_3998_ == 0 {
                    lean_ctor_set(v___x_3997_, 3, v_tz_4023_);
                    lean_ctor_set(v___x_3997_, 1, v___x_4037_);
                    lean_ctor_set(v___x_3997_, 0, v___x_4028_);
                    v___x_4039_ = v___x_3997_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4040_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4040_, 0, v___x_4028_);
                    lean_ctor_set(v_reuseFailAlloc_4040_, 1, v___x_4037_);
                    lean_ctor_set(v_reuseFailAlloc_4040_, 2, v_rules_3995_);
                    lean_ctor_set(v_reuseFailAlloc_4040_, 3, v_tz_4023_);
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
    mut v_dt_4048_: *mut LeanObject,
    mut v_millis_4049_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4050_: *mut LeanObject = core::ptr::null_mut();
    v_res_4050_ = l_Std_Time_ZonedDateTime_withMilliseconds(v_dt_4048_, v_millis_4049_);
    lean_dec(v_millis_4049_);
    return v_res_4050_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_withNanoseconds(
    mut v_dt_4051_: *mut LeanObject,
    mut v_nano_4052_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_4053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rules_4054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4057_: u8 = 0;
    let mut v_date_4058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_time_4059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_date_4060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4063_: u8 = 0;
    let mut v_hour_4064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_minute_4065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_4066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4069_: u8 = 0;
    let mut v___x_4071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_wt_4074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ltt_4075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tz_4076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_offset_4077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_4078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_4079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4096_: u8 = 0;
    let mut v_unused_4097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4098_: u8 = 0;
    let mut v_isSharedCheck_4099_: u8 = 0;
    let mut v_unused_4100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4101_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_4053_ = lean_ctor_get(v_dt_4051_, 0);
                v_rules_4054_ = lean_ctor_get(v_dt_4051_, 2);
                v_isSharedCheck_4099_ = (!lean_is_exclusive(v_dt_4051_)) as u8;
                if v_isSharedCheck_4099_ == 0 {
                    v_unused_4100_ = lean_ctor_get(v_dt_4051_, 3);
                    lean_dec(v_unused_4100_);
                    v_unused_4101_ = lean_ctor_get(v_dt_4051_, 1);
                    lean_dec(v_unused_4101_);
                    v___x_4056_ = v_dt_4051_;
                    v_isShared_4057_ = v_isSharedCheck_4099_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_rules_4054_);
                    lean_inc(v_date_4053_);
                    lean_dec(v_dt_4051_);
                    v___x_4056_ = lean_box(0);
                    v_isShared_4057_ = v_isSharedCheck_4099_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_date_4058_ = lean_thunk_get_own(v_date_4053_);
                lean_dec_ref(v_date_4053_);
                v_time_4059_ = lean_ctor_get(v_date_4058_, 1);
                v_date_4060_ = lean_ctor_get(v_date_4058_, 0);
                v_isSharedCheck_4098_ = (!lean_is_exclusive(v_date_4058_)) as u8;
                if v_isSharedCheck_4098_ == 0 {
                    v___x_4062_ = v_date_4058_;
                    v_isShared_4063_ = v_isSharedCheck_4098_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_time_4059_);
                    lean_inc(v_date_4060_);
                    lean_dec(v_date_4058_);
                    v___x_4062_ = lean_box(0);
                    v_isShared_4063_ = v_isSharedCheck_4098_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_hour_4064_ = lean_ctor_get(v_time_4059_, 0);
                v_minute_4065_ = lean_ctor_get(v_time_4059_, 1);
                v_second_4066_ = lean_ctor_get(v_time_4059_, 2);
                v_isSharedCheck_4096_ = (!lean_is_exclusive(v_time_4059_)) as u8;
                if v_isSharedCheck_4096_ == 0 {
                    v_unused_4097_ = lean_ctor_get(v_time_4059_, 3);
                    lean_dec(v_unused_4097_);
                    v___x_4068_ = v_time_4059_;
                    v_isShared_4069_ = v_isSharedCheck_4096_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_second_4066_);
                    lean_inc(v_minute_4065_);
                    lean_inc(v_hour_4064_);
                    lean_dec(v_time_4059_);
                    v___x_4068_ = lean_box(0);
                    v_isShared_4069_ = v_isSharedCheck_4096_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4069_ == 0 {
                    lean_ctor_set(v___x_4068_, 3, v_nano_4052_);
                    v___x_4071_ = v___x_4068_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4095_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4095_, 0, v_hour_4064_);
                    lean_ctor_set(v_reuseFailAlloc_4095_, 1, v_minute_4065_);
                    lean_ctor_set(v_reuseFailAlloc_4095_, 2, v_second_4066_);
                    lean_ctor_set(v_reuseFailAlloc_4095_, 3, v_nano_4052_);
                    v___x_4071_ = v_reuseFailAlloc_4095_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4063_ == 0 {
                    lean_ctor_set(v___x_4062_, 1, v___x_4071_);
                    v___x_4073_ = v___x_4062_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4094_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4094_, 0, v_date_4060_);
                    lean_ctor_set(v_reuseFailAlloc_4094_, 1, v___x_4071_);
                    v___x_4073_ = v_reuseFailAlloc_4094_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                lean_inc_ref(v___x_4073_);
                v_wt_4074_ = l_Std_Time_PlainDateTime_toWallTime(v___x_4073_);
                lean_inc_ref(v_rules_4054_);
                v_ltt_4075_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(
                    v_rules_4054_,
                    v_wt_4074_,
                );
                v_tz_4076_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_4075_);
                lean_dec_ref(v_ltt_4075_);
                v_offset_4077_ = lean_ctor_get(v_tz_4076_, 0);
                lean_inc(v_offset_4077_);
                v_second_4078_ = lean_ctor_get(v_wt_4074_, 0);
                lean_inc(v_second_4078_);
                v_nano_4079_ = lean_ctor_get(v_wt_4074_, 1);
                lean_inc(v_nano_4079_);
                lean_dec_ref(v_wt_4074_);
                v___f_4080_ = lean_alloc_closure(
                    l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_4080_, 0, v___x_4073_);
                v___x_4081_ = lean_mk_thunk(v___f_4080_);
                v___x_4082_ = lean_int_neg(v_offset_4077_);
                lean_dec(v_offset_4077_);
                v___x_4083_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
                );
                v___x_4084_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_4085_ = lean_int_mul(v_second_4078_, v___x_4084_);
                lean_dec(v_second_4078_);
                v___x_4086_ = lean_int_add(v___x_4085_, v_nano_4079_);
                lean_dec(v_nano_4079_);
                lean_dec(v___x_4085_);
                v___x_4087_ = lean_int_mul(v___x_4082_, v___x_4084_);
                lean_dec(v___x_4082_);
                v___x_4088_ = lean_int_add(v___x_4087_, v___x_4083_);
                lean_dec(v___x_4087_);
                v___x_4089_ = lean_int_add(v___x_4086_, v___x_4088_);
                lean_dec(v___x_4088_);
                lean_dec(v___x_4086_);
                v___x_4090_ = l_Std_Time_Duration_ofNanoseconds(v___x_4089_);
                lean_dec(v___x_4089_);
                if v_isShared_4057_ == 0 {
                    lean_ctor_set(v___x_4056_, 3, v_tz_4076_);
                    lean_ctor_set(v___x_4056_, 1, v___x_4090_);
                    lean_ctor_set(v___x_4056_, 0, v___x_4081_);
                    v___x_4092_ = v___x_4056_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4093_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4093_, 0, v___x_4081_);
                    lean_ctor_set(v_reuseFailAlloc_4093_, 1, v___x_4090_);
                    lean_ctor_set(v_reuseFailAlloc_4093_, 2, v_rules_4054_);
                    lean_ctor_set(v_reuseFailAlloc_4093_, 3, v_tz_4076_);
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
pub unsafe fn l_Std_Time_ZonedDateTime_inLeapYear(mut v_date_4102_: *mut LeanObject) -> u8 {
    let mut v_date_4103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_date_4105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_year_4106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4113_: u8 = 0;
    let mut v___x_4114_: u8 = 0;
    let mut v___x_4115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4117_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_4103_ = lean_ctor_get(v_date_4102_, 0);
                v___x_4104_ = lean_thunk_get_own(v_date_4103_);
                v_date_4105_ = lean_ctor_get(v___x_4104_, 0);
                lean_inc_ref(v_date_4105_);
                lean_dec(v___x_4104_);
                v_year_4106_ = lean_ctor_get(v_date_4105_, 0);
                lean_inc(v_year_4106_);
                lean_dec_ref(v_date_4105_);
                v___x_4107_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_dayOfYear___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_dayOfYear___closed__0_once),
                    _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__0,
                );
                v___x_4108_ = lean_int_mod(v_year_4106_, v___x_4107_);
                v___x_4109_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0,
                );
                v___x_4114_ = lean_int_dec_eq(v___x_4108_, v___x_4109_);
                lean_dec(v___x_4108_);
                if v___x_4114_ == 0 {
                    lean_dec(v_year_4106_);
                    return v___x_4114_;
                } else {
                    v___x_4115_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_dayOfYear___closed__2),
                        core::ptr::addr_of_mut!(
                            l_Std_Time_ZonedDateTime_dayOfYear___closed__2_once
                        ),
                        _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__2,
                    );
                    v___x_4116_ = lean_int_mod(v_year_4106_, v___x_4115_);
                    v___x_4117_ = lean_int_dec_eq(v___x_4116_, v___x_4109_);
                    lean_dec(v___x_4116_);
                    if v___x_4117_ == 0 {
                        if v___x_4114_ == 0 {
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_year_4106_);
                            return v___x_4114_;
                        }
                    } else {
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4111_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_dayOfYear___closed__1),
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_dayOfYear___closed__1_once),
                    _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__1,
                );
                v___x_4112_ = lean_int_mod(v_year_4106_, v___x_4111_);
                lean_dec(v_year_4106_);
                v___x_4113_ = lean_int_dec_eq(v___x_4112_, v___x_4109_);
                lean_dec(v___x_4112_);
                return v___x_4113_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_ZonedDateTime_inLeapYear___boxed(
    mut v_date_4118_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4119_: u8 = 0;
    let mut v_r_4120_: *mut LeanObject = core::ptr::null_mut();
    v_res_4119_ = l_Std_Time_ZonedDateTime_inLeapYear(v_date_4118_);
    lean_dec_ref(v_date_4118_);
    v_r_4120_ = lean_box((v_res_4119_) as usize);
    return v_r_4120_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_toEpochDay(
    mut v_date_4121_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_4122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_date_4124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4125_: *mut LeanObject = core::ptr::null_mut();
    v_date_4122_ = lean_ctor_get(v_date_4121_, 0);
    v___x_4123_ = lean_thunk_get_own(v_date_4122_);
    v_date_4124_ = lean_ctor_get(v___x_4123_, 0);
    lean_inc_ref(v_date_4124_);
    lean_dec(v___x_4123_);
    v___x_4125_ = l_Std_Time_PlainDate_toEpochDay(v_date_4124_);
    return v___x_4125_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_toEpochDay___boxed(
    mut v_date_4126_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4127_: *mut LeanObject = core::ptr::null_mut();
    v_res_4127_ = l_Std_Time_ZonedDateTime_toEpochDay(v_date_4126_);
    lean_dec_ref(v_date_4126_);
    return v_res_4127_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_ofEpochDay(
    mut v_days_4128_: *mut LeanObject,
    mut v_time_4129_: *mut LeanObject,
    mut v_zt_4130_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_wt_4133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ltt_4134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tz_4135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_offset_4136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_4137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_4138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4150_: *mut LeanObject = core::ptr::null_mut();
    v___x_4131_ = l_Std_Time_PlainDate_ofEpochDay(v_days_4128_);
    v___x_4132_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4132_, 0, v___x_4131_);
    lean_ctor_set(v___x_4132_, 1, v_time_4129_);
    lean_inc_ref(v___x_4132_);
    v_wt_4133_ = l_Std_Time_PlainDateTime_toWallTime(v___x_4132_);
    lean_inc_ref(v_zt_4130_);
    v_ltt_4134_ =
        l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_zt_4130_, v_wt_4133_);
    v_tz_4135_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_4134_);
    lean_dec_ref(v_ltt_4134_);
    v_offset_4136_ = lean_ctor_get(v_tz_4135_, 0);
    lean_inc(v_offset_4136_);
    v_second_4137_ = lean_ctor_get(v_wt_4133_, 0);
    lean_inc(v_second_4137_);
    v_nano_4138_ = lean_ctor_get(v_wt_4133_, 1);
    lean_inc(v_nano_4138_);
    lean_dec_ref(v_wt_4133_);
    v___f_4139_ = lean_alloc_closure(
        l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_4139_, 0, v___x_4132_);
    v___x_4140_ = lean_mk_thunk(v___f_4139_);
    v___x_4141_ = lean_int_neg(v_offset_4136_);
    lean_dec(v_offset_4136_);
    v___x_4142_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once),
        _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0,
    );
    v___x_4143_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once),
        _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
    );
    v___x_4144_ = lean_int_mul(v_second_4137_, v___x_4143_);
    lean_dec(v_second_4137_);
    v___x_4145_ = lean_int_add(v___x_4144_, v_nano_4138_);
    lean_dec(v_nano_4138_);
    lean_dec(v___x_4144_);
    v___x_4146_ = lean_int_mul(v___x_4141_, v___x_4143_);
    lean_dec(v___x_4141_);
    v___x_4147_ = lean_int_add(v___x_4146_, v___x_4142_);
    lean_dec(v___x_4146_);
    v___x_4148_ = lean_int_add(v___x_4145_, v___x_4147_);
    lean_dec(v___x_4147_);
    lean_dec(v___x_4145_);
    v___x_4149_ = l_Std_Time_Duration_ofNanoseconds(v___x_4148_);
    lean_dec(v___x_4148_);
    v___x_4150_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_4150_, 0, v___x_4140_);
    lean_ctor_set(v___x_4150_, 1, v___x_4149_);
    lean_ctor_set(v___x_4150_, 2, v_zt_4130_);
    lean_ctor_set(v___x_4150_, 3, v_tz_4135_);
    return v___x_4150_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_ofEpochDay___boxed(
    mut v_days_4151_: *mut LeanObject,
    mut v_time_4152_: *mut LeanObject,
    mut v_zt_4153_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4154_: *mut LeanObject = core::ptr::null_mut();
    v_res_4154_ = l_Std_Time_ZonedDateTime_ofEpochDay(v_days_4151_, v_time_4152_, v_zt_4153_);
    lean_dec(v_days_4151_);
    return v_res_4154_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_instHSubDuration___lam__0(
    mut v_x_4183_: *mut LeanObject,
    mut v_y_4184_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_timestamp_4185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_timestamp_4186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_4187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_4188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_4189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_4190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4199_: *mut LeanObject = core::ptr::null_mut();
    v_timestamp_4185_ = lean_ctor_get(v_y_4184_, 1);
    v_timestamp_4186_ = lean_ctor_get(v_x_4183_, 1);
    v_second_4187_ = lean_ctor_get(v_timestamp_4185_, 0);
    v_nano_4188_ = lean_ctor_get(v_timestamp_4185_, 1);
    v_second_4189_ = lean_ctor_get(v_timestamp_4186_, 0);
    v_nano_4190_ = lean_ctor_get(v_timestamp_4186_, 1);
    v___x_4191_ = lean_int_neg(v_second_4187_);
    v___x_4192_ = lean_int_neg(v_nano_4188_);
    v___x_4193_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once),
        _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
    );
    v___x_4194_ = lean_int_mul(v_second_4189_, v___x_4193_);
    v___x_4195_ = lean_int_add(v___x_4194_, v_nano_4190_);
    lean_dec(v___x_4194_);
    v___x_4196_ = lean_int_mul(v___x_4191_, v___x_4193_);
    lean_dec(v___x_4191_);
    v___x_4197_ = lean_int_add(v___x_4196_, v___x_4192_);
    lean_dec(v___x_4192_);
    lean_dec(v___x_4196_);
    v___x_4198_ = lean_int_add(v___x_4195_, v___x_4197_);
    lean_dec(v___x_4197_);
    lean_dec(v___x_4195_);
    v___x_4199_ = l_Std_Time_Duration_ofNanoseconds(v___x_4198_);
    lean_dec(v___x_4198_);
    return v___x_4199_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_instHSubDuration___lam__0___boxed(
    mut v_x_4200_: *mut LeanObject,
    mut v_y_4201_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4202_: *mut LeanObject = core::ptr::null_mut();
    v_res_4202_ = l_Std_Time_ZonedDateTime_instHSubDuration___lam__0(v_x_4200_, v_y_4201_);
    lean_dec_ref(v_y_4201_);
    lean_dec_ref(v_x_4200_);
    return v_res_4202_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_instHAddDuration___lam__0(
    mut v_x_4205_: *mut LeanObject,
    mut v_y_4206_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_second_4207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_4208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nanos_4211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut LeanObject = core::ptr::null_mut();
    v_second_4207_ = lean_ctor_get(v_y_4206_, 0);
    v_nano_4208_ = lean_ctor_get(v_y_4206_, 1);
    v___x_4209_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once),
        _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
    );
    v___x_4210_ = lean_int_mul(v_second_4207_, v___x_4209_);
    v_nanos_4211_ = lean_int_add(v___x_4210_, v_nano_4208_);
    lean_dec(v___x_4210_);
    v___x_4212_ = l_Std_Time_ZonedDateTime_addNanoseconds(v_x_4205_, v_nanos_4211_);
    lean_dec(v_nanos_4211_);
    return v___x_4212_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_instHAddDuration___lam__0___boxed(
    mut v_x_4213_: *mut LeanObject,
    mut v_y_4214_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4215_: *mut LeanObject = core::ptr::null_mut();
    v_res_4215_ = l_Std_Time_ZonedDateTime_instHAddDuration___lam__0(v_x_4213_, v_y_4214_);
    lean_dec_ref(v_y_4214_);
    return v_res_4215_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_instHSubDuration__1___lam__0(
    mut v_x_4218_: *mut LeanObject,
    mut v_y_4219_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_second_4220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_4221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nanos_4224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4225_: *mut LeanObject = core::ptr::null_mut();
    v_second_4220_ = lean_ctor_get(v_y_4219_, 0);
    v_nano_4221_ = lean_ctor_get(v_y_4219_, 1);
    v___x_4222_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once),
        _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1,
    );
    v___x_4223_ = lean_int_mul(v_second_4220_, v___x_4222_);
    v_nanos_4224_ = lean_int_add(v___x_4223_, v_nano_4221_);
    lean_dec(v___x_4223_);
    v___x_4225_ = l_Std_Time_ZonedDateTime_subNanoseconds(v_x_4218_, v_nanos_4224_);
    lean_dec(v_nanos_4224_);
    return v___x_4225_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_instHSubDuration__1___lam__0___boxed(
    mut v_x_4226_: *mut LeanObject,
    mut v_y_4227_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4228_: *mut LeanObject = core::ptr::null_mut();
    v_res_4228_ = l_Std_Time_ZonedDateTime_instHSubDuration__1___lam__0(v_x_4226_, v_y_4227_);
    lean_dec_ref(v_y_4227_);
    return v_res_4228_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Time_Zoned_ZonedDateTime(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Time_Zoned_DateTime(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Zoned_ZoneRules(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Time_DateTime_PlainDateTime(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Std_Time_instInhabitedZonedDateTime___private__1 =
        _init_l_Std_Time_instInhabitedZonedDateTime___private__1();
    lean_mark_persistent(l_Std_Time_instInhabitedZonedDateTime___private__1);
    l_Std_Time_instInhabitedZonedDateTime = _init_l_Std_Time_instInhabitedZonedDateTime();
    lean_mark_persistent(l_Std_Time_instInhabitedZonedDateTime);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Time_Zoned_ZonedDateTime(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Time_Zoned_ZonedDateTime(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Time_Zoned_DateTime(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Time_Zoned_ZoneRules(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Time_DateTime_PlainDateTime(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Zoned_ZonedDateTime(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Time_Zoned_ZonedDateTime(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Time_Zoned_ZonedDateTime(builtin);
}
