// Lean compiler output
// Module: Std.Time.Format
// Imports: Std.Time.Notation.Spec Std.Time.Format.Basic Std.Time.Format.Basic
use crate::r#gen::Init::Data::Repr::l_Repr_addAppParen;
use crate::r#gen::Std::Time::Date::PlainDate::{
    l_Std_Time_PlainDate_alignedWeekOfMonth, l_Std_Time_PlainDate_dayOfYear,
    l_Std_Time_PlainDate_quarter, l_Std_Time_PlainDate_weekOfMonth,
    l_Std_Time_PlainDate_weekOfYear, l_Std_Time_PlainDate_weekYear, l_Std_Time_PlainDate_weekday,
};
use crate::r#gen::Std::Time::Date::Unit::Month::l_Std_Time_Month_Ordinal_days;
use crate::r#gen::Std::Time::Date::Unit::Year::l_Std_Time_Year_Offset_era;
use crate::r#gen::Std::Time::Date::ValidDate::l_Std_Time_ValidDate_dayOfYear;
use crate::r#gen::Std::Time::DateTime::PlainDateTime::{
    l_Std_Time_PlainDateTime_ofWallTime, l_Std_Time_PlainDateTime_toWallTime,
    l_Std_Time_PlainDateTime_weekOfMonth,
};
use crate::r#gen::Std::Time::Duration::l_Std_Time_Duration_ofNanoseconds;
use crate::r#gen::Std::Time::Format::Basic::{
    initialize_Std_Time_Format_Basic, l_Std_Time_GenericFormat_format,
    l_Std_Time_GenericFormat_formatBuilder___redArg,
    l_Std_Time_GenericFormat_formatGeneric___redArg, l_Std_Time_GenericFormat_parse,
    l_Std_Time_GenericFormat_parseBuilder___redArg, l_Std_Time_GenericFormat_spec___redArg,
    runtime_initialize_Std_Time_Format_Basic,
};
use crate::r#gen::Std::Time::Format::DateFormat::l_Std_Time_DateFormat_enUS;
use crate::r#gen::Std::Time::Notation::Spec::{
    initialize_Std_Time_Notation_Spec, runtime_initialize_Std_Time_Notation_Spec,
};
use crate::r#gen::Std::Time::Time::HourMarker::{
    l_Std_Time_HourMarker_ofOrdinal, l_Std_Time_HourMarker_toAbsolute,
};
use crate::r#gen::Std::Time::Time::PlainTime::{
    l_Std_Time_PlainTime_toMilliseconds, l_Std_Time_PlainTime_toNanoseconds,
};
use crate::r#gen::Std::Time::Time::Unit::Hour::{
    l_Std_Time_Hour_Ordinal_shiftTo1BasedHour, l_Std_Time_Hour_Ordinal_toRelative,
};
use crate::r#gen::Std::Time::Zoned::Offset::l_Std_Time_TimeZone_Offset_toIsoString;
use crate::r#gen::Std::Time::Zoned::TimeZone::{l_Std_Time_TimeZone_GMT, l_Std_Time_TimeZone_UTC};
use crate::lean_imports_rs::Init::Core::{lean_mk_thunk, lean_thunk_get_own};
use crate::lean_imports_rs::Init::Data::Int::Basic::{
    lean_int_add, lean_int_dec_eq, lean_int_dec_le, lean_int_mul, lean_int_neg, lean_nat_to_int,
};
use crate::lean_imports_rs::Init::Data::Int::DivMod::Basic::{lean_int_emod, lean_int_mod};
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Prelude::lean_nat_mod;
static mut l_Std_Time_Formats_iso8601___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Formats_iso8601___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_Formats_iso8601___closed__1_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 2,
        },
        m_objs: [(((2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Std_Time_Formats_iso8601___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_iso8601___closed__2_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_iso8601___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_iso8601___closed__3_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
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
static mut l_Std_Time_Formats_iso8601___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_iso8601___closed__4_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_iso8601___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_iso8601___closed__5_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [(((2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Std_Time_Formats_iso8601___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_iso8601___closed__6_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_iso8601___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_iso8601___closed__7_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_iso8601___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_iso8601___closed__8_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [(((2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Std_Time_Formats_iso8601___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_iso8601___closed__9_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__8_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_iso8601___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_iso8601___closed__10_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [84, 0],
    };
static mut l_Std_Time_Formats_iso8601___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_iso8601___closed__11_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__10_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_iso8601___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_iso8601___closed__12_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 17,
        },
        m_objs: [(((2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Std_Time_Formats_iso8601___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_iso8601___closed__13_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__12_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_iso8601___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_iso8601___closed__14_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [58, 0],
    };
static mut l_Std_Time_Formats_iso8601___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_iso8601___closed__15_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__14_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_iso8601___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_iso8601___closed__16_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 18,
        },
        m_objs: [(((2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Std_Time_Formats_iso8601___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_iso8601___closed__17_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__16_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_iso8601___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_iso8601___closed__18_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 19,
        },
        m_objs: [(((2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Std_Time_Formats_iso8601___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_iso8601___closed__19_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__18_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_iso8601___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__19_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_iso8601___closed__20_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0
                + 8) as u16,
            other: 0,
            tag: 27,
        },
        m_objs: [2 as *mut crate::leanh::LeanObject],
    };
static mut l_Std_Time_Formats_iso8601___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__20_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_iso8601___closed__21_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__20_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_iso8601___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__21_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_iso8601___closed__22_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__21_value)
                as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_iso8601___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__22_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_iso8601___closed__23_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__19_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__22_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_iso8601___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__23_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_iso8601___closed__24_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__15_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__23_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_iso8601___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__24_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_iso8601___closed__25_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__17_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__24_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_iso8601___closed__25: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__25_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_iso8601___closed__26_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__15_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__25_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_iso8601___closed__26: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__26_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_iso8601___closed__27_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__13_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__26_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_iso8601___closed__27: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__27_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_iso8601___closed__28_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__11_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__27_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_iso8601___closed__28: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__28_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_iso8601___closed__29_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__9_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__28_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_iso8601___closed__29: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__29_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_iso8601___closed__30_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__29_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_iso8601___closed__30: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__30_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_iso8601___closed__31_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__30_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_iso8601___closed__31: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__31_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_iso8601___closed__32_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__31_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_iso8601___closed__32: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__32_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_iso8601___closed__33_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__32_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_iso8601___closed__33: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__33_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_Formats_iso8601___closed__34_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Formats_iso8601___closed__34: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Formats_iso8601: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Time_Formats_americanDate___closed__0_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__2_value)
                as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_americanDate___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_americanDate___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_americanDate___closed__1_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_americanDate___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_americanDate___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_americanDate___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_americanDate___closed__2_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__9_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_americanDate___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_americanDate___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_americanDate___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_americanDate___closed__3_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_americanDate___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_americanDate___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_americanDate___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_americanDate___closed__4_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_americanDate___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_americanDate___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_americanDate___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_Formats_americanDate___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Formats_americanDate___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Formats_americanDate: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_Formats_europeanDate___closed__0_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_americanDate___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_europeanDate___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_europeanDate___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_europeanDate___closed__1_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_europeanDate___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_europeanDate___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_europeanDate___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_europeanDate___closed__2_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__9_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_europeanDate___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_europeanDate___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_europeanDate___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_Formats_europeanDate___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Formats_europeanDate___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Formats_europeanDate: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_Formats_time12Hour___closed__0_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 14,
        },
        m_objs: [(((2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Std_Time_Formats_time12Hour___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_time12Hour___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_time12Hour___closed__1_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_time12Hour___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_time12Hour___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_time12Hour___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_time12Hour___closed__2_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [32, 0],
    };
static mut l_Std_Time_Formats_time12Hour___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_time12Hour___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_time12Hour___closed__3_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_time12Hour___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_time12Hour___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_time12Hour___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_time12Hour___closed__4_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0
                + 8) as u16,
            other: 0,
            tag: 13,
        },
        m_objs: [0 as *mut crate::leanh::LeanObject],
    };
static mut l_Std_Time_Formats_time12Hour___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_time12Hour___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_time12Hour___closed__5_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_time12Hour___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_time12Hour___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_time12Hour___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_time12Hour___closed__6_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_time12Hour___closed__5_value)
                as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_time12Hour___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_time12Hour___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_time12Hour___closed__7_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_time12Hour___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_time12Hour___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_time12Hour___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_time12Hour___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_time12Hour___closed__8_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__19_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_time12Hour___closed__7_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_time12Hour___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_time12Hour___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_time12Hour___closed__9_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__15_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_time12Hour___closed__8_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_time12Hour___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_time12Hour___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_time12Hour___closed__10_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__17_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_time12Hour___closed__9_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_time12Hour___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_time12Hour___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_time12Hour___closed__11_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__15_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_time12Hour___closed__10_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_time12Hour___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_time12Hour___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_time12Hour___closed__12_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_time12Hour___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_time12Hour___closed__11_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_time12Hour___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_time12Hour___closed__12_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_Formats_time12Hour___closed__13_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Formats_time12Hour___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Formats_time12Hour: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Time_Formats_time24Hour___closed__0_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__19_value)
                as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_time24Hour___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_time24Hour___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_time24Hour___closed__1_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__15_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_time24Hour___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_time24Hour___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_time24Hour___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_time24Hour___closed__2_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__17_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_time24Hour___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_time24Hour___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_time24Hour___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_time24Hour___closed__3_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__15_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_time24Hour___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_time24Hour___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_time24Hour___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_time24Hour___closed__4_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__13_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_time24Hour___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_time24Hour___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_time24Hour___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_Formats_time24Hour___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Formats_time24Hour___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Formats_time24Hour: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Time_Formats_dateTime24Hour___closed__0_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
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
static mut l_Std_Time_Formats_dateTime24Hour___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_dateTime24Hour___closed__1_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_dateTime24Hour___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_dateTime24Hour___closed__2_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 20,
        },
        m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Std_Time_Formats_dateTime24Hour___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_dateTime24Hour___closed__3_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_dateTime24Hour___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_dateTime24Hour___closed__4_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__3_value)
                as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_dateTime24Hour___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_dateTime24Hour___closed__5_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_dateTime24Hour___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_dateTime24Hour___closed__6_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__19_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_dateTime24Hour___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_dateTime24Hour___closed__7_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__15_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_dateTime24Hour___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_dateTime24Hour___closed__8_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__17_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__7_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_dateTime24Hour___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_dateTime24Hour___closed__9_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__15_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__8_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_dateTime24Hour___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_dateTime24Hour___closed__10_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__13_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__9_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_dateTime24Hour___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_dateTime24Hour___closed__11_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__15_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__10_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_dateTime24Hour___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_dateTime24Hour___closed__12_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__9_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__11_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_dateTime24Hour___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_dateTime24Hour___closed__13_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__12_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_dateTime24Hour___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_dateTime24Hour___closed__14_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__13_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_dateTime24Hour___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_dateTime24Hour___closed__15_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__14_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_dateTime24Hour___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_dateTime24Hour___closed__16_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__15_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_dateTime24Hour___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__16_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_Formats_dateTime24Hour___closed__17_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Formats_dateTime24Hour___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Formats_dateTime24Hour: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_Formats_dateTimeWithZone___closed__0_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0
                + 8) as u16,
            other: 0,
            tag: 29,
        },
        m_objs: [0 as *mut crate::leanh::LeanObject],
    };
static mut l_Std_Time_Formats_dateTimeWithZone___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_dateTimeWithZone___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_dateTimeWithZone___closed__1_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_dateTimeWithZone___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_dateTimeWithZone___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_dateTimeWithZone___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_dateTimeWithZone___closed__2_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_dateTimeWithZone___closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_dateTimeWithZone___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_dateTimeWithZone___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_dateTimeWithZone___closed__3_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_dateTimeWithZone___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_dateTimeWithZone___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_dateTimeWithZone___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_dateTimeWithZone___closed__4_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_dateTimeWithZone___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_dateTimeWithZone___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_dateTimeWithZone___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_dateTimeWithZone___closed__5_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__19_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_dateTimeWithZone___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_dateTimeWithZone___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_dateTimeWithZone___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_dateTimeWithZone___closed__6_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__15_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_dateTimeWithZone___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_dateTimeWithZone___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_dateTimeWithZone___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_dateTimeWithZone___closed__7_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__17_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_dateTimeWithZone___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_dateTimeWithZone___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_dateTimeWithZone___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_dateTimeWithZone___closed__8_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__15_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_dateTimeWithZone___closed__7_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_dateTimeWithZone___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_dateTimeWithZone___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_dateTimeWithZone___closed__9_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__13_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_dateTimeWithZone___closed__8_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_dateTimeWithZone___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_dateTimeWithZone___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_dateTimeWithZone___closed__10_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__11_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_dateTimeWithZone___closed__9_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_dateTimeWithZone___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_dateTimeWithZone___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_dateTimeWithZone___closed__11_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__9_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_dateTimeWithZone___closed__10_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_dateTimeWithZone___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_dateTimeWithZone___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_dateTimeWithZone___closed__12_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_dateTimeWithZone___closed__11_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_dateTimeWithZone___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_dateTimeWithZone___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_dateTimeWithZone___closed__13_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_dateTimeWithZone___closed__12_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_dateTimeWithZone___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_dateTimeWithZone___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_dateTimeWithZone___closed__14_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_dateTimeWithZone___closed__13_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_dateTimeWithZone___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_dateTimeWithZone___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_dateTimeWithZone___closed__15_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_dateTimeWithZone___closed__14_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_dateTimeWithZone___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_dateTimeWithZone___closed__15_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_Formats_dateTimeWithZone___closed__16_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Formats_dateTimeWithZone___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Formats_dateTimeWithZone: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Formats_leanTime24Hour___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Formats_leanTime24Hour___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Formats_leanTime24Hour: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Formats_leanTime24HourNoNanos: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_Formats_leanDateTime24Hour___closed__0_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__11_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__10_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTime24Hour___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTime24Hour___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTime24Hour___closed__1_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__9_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTime24Hour___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTime24Hour___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTime24Hour___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTime24Hour___closed__2_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__4_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTime24Hour___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTime24Hour___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTime24Hour___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTime24Hour___closed__3_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__7_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTime24Hour___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTime24Hour___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTime24Hour___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTime24Hour___closed__4_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__4_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTime24Hour___closed__3_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTime24Hour___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTime24Hour___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTime24Hour___closed__5_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTime24Hour___closed__4_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTime24Hour___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTime24Hour___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_Formats_leanDateTime24Hour___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Formats_leanDateTime24Hour___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Formats_leanDateTime24Hour: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__0_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__11_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_time24Hour___closed__4_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__1_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__9_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__2_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__4_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__3_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__7_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__4_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__4_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__3_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__5_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__4_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Formats_leanDateTime24HourNoNanos: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_Formats_leanDateTimeWithZone___closed__0_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0
            + 8) as u16,
        other: 0,
        tag: 29,
    },
    m_objs: [2 as *mut crate::leanh::LeanObject],
};
static mut l_Std_Time_Formats_leanDateTimeWithZone___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZone___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithZone___closed__1_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZone___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithZone___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZone___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithZone___closed__2_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZone___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithZone___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZone___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithZone___closed__3_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZone___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithZone___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZone___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithZone___closed__4_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__1_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZone___closed__3_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithZone___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZone___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithZone___closed__5_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__19_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZone___closed__4_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithZone___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZone___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithZone___closed__6_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__15_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZone___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithZone___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZone___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithZone___closed__7_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__17_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZone___closed__6_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithZone___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZone___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithZone___closed__8_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__15_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZone___closed__7_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithZone___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZone___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithZone___closed__9_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__13_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZone___closed__8_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithZone___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZone___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithZone___closed__10_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__11_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZone___closed__9_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithZone___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZone___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithZone___closed__11_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__9_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZone___closed__10_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithZone___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZone___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithZone___closed__12_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__4_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZone___closed__11_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithZone___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZone___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithZone___closed__13_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__7_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZone___closed__12_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithZone___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZone___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithZone___closed__14_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__4_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZone___closed__13_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithZone___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZone___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithZone___closed__15_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZone___closed__14_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithZone___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZone___closed__15_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_Formats_leanDateTimeWithZone___closed__16_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Formats_leanDateTimeWithZone___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Formats_leanDateTimeWithZone: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__0_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__19_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZone___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__1_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__15_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__2_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__17_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__3_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__15_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__4_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__13_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__3_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__5_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__11_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__4_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__6_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__9_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__7_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__4_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__6_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__8_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__7_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__7_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__9_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__4_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__8_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__10_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__9_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__10_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__11_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Std_Time_Formats_leanDateTimeWithZoneNoNanos: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__0_value:
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
    m_data: [91, 0],
};
static mut l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__2_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0
            + 8) as u16,
        other: 0,
        tag: 25,
    },
    m_objs: [1 as *mut crate::leanh::LeanObject],
};
static mut l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__3_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__4_value:
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
    m_data: [93, 0],
};
static mut l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__5_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__4_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__6_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__5_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__7_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__6_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__8_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__1_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__7_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__9_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__19_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__8_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__10_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__15_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__9_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__11_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__17_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__10_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__11:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__12_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__15_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__11_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__12:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__13_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__13_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__12_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__13:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__14_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__11_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__13_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__14:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__15_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__9_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__14_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__15:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__16_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__4_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__15_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__16:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__17_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__7_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__16_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__17:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__18_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__4_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__17_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__18:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__19_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__18_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__19:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__19_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__20_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__20:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Std_Time_Formats_leanDateTimeWithIdentifier: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__0_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__8_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__1_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__1_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__2_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__19_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__3_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__15_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__4_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__17_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__3_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__5_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__15_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__4_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__6_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__13_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__7_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__11_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__6_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__8_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__9_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__7_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__9_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__4_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__8_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__10_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__7_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__9_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__11_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__4_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__10_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__11:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__12_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__11_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__12:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__12_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__13_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Time_Formats_leanDate___closed__0_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__9_value)
                as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_leanDate___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDate___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_leanDate___closed__1_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_leanDate___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_leanDate___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDate___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_leanDate___closed__2_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_leanDate___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_leanDate___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDate___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_leanDate___closed__3_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_leanDate___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_leanDate___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDate___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_leanDate___closed__4_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_leanDate___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_leanDate___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDate___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_Formats_leanDate___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Formats_leanDate___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Formats_leanDate: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Std_Time_Formats_sqlDate: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Time_Formats_longDateFormat___closed__0_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0
                + 8) as u16,
            other: 0,
            tag: 10,
        },
        m_objs: [1 as *mut crate::leanh::LeanObject],
    };
static mut l_Std_Time_Formats_longDateFormat___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_longDateFormat___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_longDateFormat___closed__1_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_longDateFormat___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_longDateFormat___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_longDateFormat___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_longDateFormat___closed__2_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [44, 32, 0],
    };
static mut l_Std_Time_Formats_longDateFormat___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_longDateFormat___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_longDateFormat___closed__3_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_longDateFormat___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_longDateFormat___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_longDateFormat___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_longDateFormat___closed__4_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Std_Time_Formats_longDateFormat___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_longDateFormat___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_longDateFormat___closed__5_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_longDateFormat___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_longDateFormat___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_longDateFormat___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_longDateFormat___closed__6_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_longDateFormat___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_longDateFormat___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_longDateFormat___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_longDateFormat___closed__7_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [(((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Std_Time_Formats_longDateFormat___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_longDateFormat___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_longDateFormat___closed__8_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_longDateFormat___closed__7_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_longDateFormat___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_longDateFormat___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_longDateFormat___closed__9_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_time12Hour___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_time24Hour___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_longDateFormat___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_longDateFormat___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_longDateFormat___closed__10_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_longDateFormat___closed__9_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_longDateFormat___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_longDateFormat___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_longDateFormat___closed__11_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_longDateFormat___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_longDateFormat___closed__10_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_longDateFormat___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_longDateFormat___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_longDateFormat___closed__12_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_longDateFormat___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_longDateFormat___closed__11_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_longDateFormat___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_longDateFormat___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_longDateFormat___closed__13_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_time12Hour___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_longDateFormat___closed__12_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_longDateFormat___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_longDateFormat___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_longDateFormat___closed__14_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_longDateFormat___closed__6_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_longDateFormat___closed__13_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_longDateFormat___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_longDateFormat___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_longDateFormat___closed__15_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_longDateFormat___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_longDateFormat___closed__14_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_longDateFormat___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_longDateFormat___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_longDateFormat___closed__16_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_longDateFormat___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_longDateFormat___closed__15_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_longDateFormat___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_longDateFormat___closed__16_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_Formats_longDateFormat___closed__17_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Formats_longDateFormat___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Formats_longDateFormat: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_Formats_ascTime___closed__0_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0
                + 8) as u16,
            other: 0,
            tag: 10,
        },
        m_objs: [0 as *mut crate::leanh::LeanObject],
    };
static mut l_Std_Time_Formats_ascTime___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_ascTime___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_ascTime___closed__1_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_ascTime___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_ascTime___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_ascTime___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_ascTime___closed__2_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Std_Time_Formats_ascTime___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_ascTime___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_ascTime___closed__3_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_ascTime___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_ascTime___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_ascTime___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_ascTime___closed__4_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_ascTime___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_ascTime___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_ascTime___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_ascTime___closed__5_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_time12Hour___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_americanDate___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_ascTime___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_ascTime___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_ascTime___closed__6_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__19_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_ascTime___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_ascTime___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_ascTime___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_ascTime___closed__7_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__15_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_ascTime___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_ascTime___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_ascTime___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_ascTime___closed__8_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__17_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_ascTime___closed__7_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_ascTime___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_ascTime___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_ascTime___closed__9_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__15_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_ascTime___closed__8_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_ascTime___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_ascTime___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_ascTime___closed__10_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__13_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_ascTime___closed__9_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_ascTime___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_ascTime___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_ascTime___closed__11_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_time12Hour___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_ascTime___closed__10_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_ascTime___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_ascTime___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_ascTime___closed__12_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_longDateFormat___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_ascTime___closed__11_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_ascTime___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_ascTime___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_ascTime___closed__13_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_time12Hour___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_ascTime___closed__12_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_ascTime___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_ascTime___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_ascTime___closed__14_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_ascTime___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_ascTime___closed__13_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_ascTime___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_ascTime___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_ascTime___closed__15_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_time12Hour___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_ascTime___closed__14_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_ascTime___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_ascTime___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_ascTime___closed__16_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_ascTime___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_ascTime___closed__15_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_ascTime___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_ascTime___closed__16_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_Formats_ascTime___closed__17_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Formats_ascTime___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Formats_ascTime: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Time_Formats_rfc822___closed__0_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 11,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_ascTime___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_rfc822___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_rfc822___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_rfc822___closed__1_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_rfc822___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_rfc822___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_rfc822___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_rfc822___closed__2_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_time12Hour___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_dateTimeWithZone___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_rfc822___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_rfc822___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_rfc822___closed__3_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__19_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_rfc822___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_rfc822___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_rfc822___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_rfc822___closed__4_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__15_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_rfc822___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_rfc822___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_rfc822___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_rfc822___closed__5_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__17_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_rfc822___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_rfc822___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_rfc822___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_rfc822___closed__6_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__15_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_rfc822___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_rfc822___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_rfc822___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_rfc822___closed__7_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__13_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_rfc822___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_rfc822___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_rfc822___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_rfc822___closed__8_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_time12Hour___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_rfc822___closed__7_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_rfc822___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_rfc822___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_rfc822___closed__9_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_rfc822___closed__8_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_rfc822___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_rfc822___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_rfc822___closed__10_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_time12Hour___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_rfc822___closed__9_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_rfc822___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_rfc822___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_rfc822___closed__11_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_ascTime___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_rfc822___closed__10_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_rfc822___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_rfc822___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_rfc822___closed__12_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_time12Hour___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_rfc822___closed__11_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_rfc822___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_rfc822___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_rfc822___closed__13_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__9_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_rfc822___closed__12_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_rfc822___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_rfc822___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_rfc822___closed__14_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_longDateFormat___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_rfc822___closed__13_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_rfc822___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_rfc822___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_rfc822___closed__15_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_rfc822___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_rfc822___closed__14_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_rfc822___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_rfc822___closed__15_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_Formats_rfc822___closed__16_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Formats_rfc822___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Formats_rfc822: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Time_Formats_rfc850___closed__0_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_rfc822___closed__9_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_rfc850___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_rfc850___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_rfc850___closed__1_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_rfc850___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_rfc850___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_rfc850___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_rfc850___closed__2_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_rfc850___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_rfc850___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_rfc850___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_rfc850___closed__3_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__9_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_rfc850___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_rfc850___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_rfc850___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_rfc850___closed__4_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_longDateFormat___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_rfc850___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_rfc850___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_rfc850___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_Formats_rfc850___closed__5_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_rfc822___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_rfc850___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_rfc850___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_rfc850___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_Formats_rfc850___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Formats_rfc850___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Formats_rfc850: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Time_TimeZone_fromTimeZone___closed__0_value: crate::leanh::LeanClosureObject<1> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Time_TimeZone_fromTimeZone___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Std_Time_TimeZone_fromTimeZone___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_fromTimeZone___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_TimeZone_fromTimeZone___closed__1_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((24 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Std_Time_TimeZone_fromTimeZone___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_fromTimeZone___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_TimeZone_fromTimeZone___closed__2_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_time12Hour___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZone___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_TimeZone_fromTimeZone___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_fromTimeZone___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_TimeZone_fromTimeZone___closed__3_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_TimeZone_fromTimeZone___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_TimeZone_fromTimeZone___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Time_TimeZone_fromTimeZone___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_fromTimeZone___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_TimeZone_fromTimeZone___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_TimeZone_fromTimeZone___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_TimeZone_Offset_fromOffset___closed__0_value:
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
    m_fun: l_Std_Time_TimeZone_Offset_fromOffset___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_TimeZone_Offset_fromOffset___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_Offset_fromOffset___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_TimeZone_Offset_fromOffset___closed__1_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0
            + 8) as u16,
        other: 0,
        tag: 28,
    },
    m_objs: [2 as *mut crate::leanh::LeanObject],
};
static mut l_Std_Time_TimeZone_Offset_fromOffset___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_Offset_fromOffset___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_TimeZone_Offset_fromOffset___closed__2_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_TimeZone_Offset_fromOffset___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_TimeZone_Offset_fromOffset___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_Offset_fromOffset___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_TimeZone_Offset_fromOffset___closed__3_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_TimeZone_Offset_fromOffset___closed__2_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_TimeZone_Offset_fromOffset___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_Offset_fromOffset___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_TimeZone_Offset_fromOffset___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_TimeZone_Offset_fromOffset___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDate_format___lam__0___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDate_format___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDate_format___lam__0___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDate_format___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDate_format___lam__0___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDate_format___lam__0___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDate_format___lam__0___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDate_format___lam__0___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_PlainDate_format___closed__0_value: crate::leanh::LeanStringObject<8> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [101, 114, 114, 111, 114, 58, 32, 0],
    };
static mut l_Std_Time_PlainDate_format___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDate_format___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_PlainDate_format___closed__1_value: crate::leanh::LeanStringObject<13> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 12,
        m_data: [105, 110, 118, 97, 108, 105, 100, 32, 116, 105, 109, 101, 0],
    };
static mut l_Std_Time_PlainDate_format___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDate_format___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_PlainDate_fromAmericanDateString___closed__0_value:
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
    m_fun: l_Std_Time_PlainDate_fromAmericanDateString___lam__0 as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_PlainDate_fromAmericanDateString___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDate_fromAmericanDateString___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_PlainDate_fromSQLDateString___closed__0_value:
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
    m_fun: l_Std_Time_PlainDate_fromSQLDateString___lam__0 as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_PlainDate_fromSQLDateString___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDate_fromSQLDateString___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_PlainDate_instToString___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_PlainDate_toLeanDateString as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_PlainDate_instToString___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDate_instToString___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_PlainDate_instToString: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDate_instToString___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_PlainDate_instRepr___lam__0___closed__0_value:
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
    m_data: [100, 97, 116, 101, 40, 34, 0],
};
static mut l_Std_Time_PlainDate_instRepr___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDate_instRepr___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_PlainDate_instRepr___lam__0___closed__1_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Std_Time_PlainDate_instRepr___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_PlainDate_instRepr___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDate_instRepr___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_PlainDate_instRepr___lam__0___closed__2_value:
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
    m_data: [34, 41, 0],
};
static mut l_Std_Time_PlainDate_instRepr___lam__0___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDate_instRepr___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_PlainDate_instRepr___lam__0___closed__3_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Std_Time_PlainDate_instRepr___lam__0___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_PlainDate_instRepr___lam__0___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDate_instRepr___lam__0___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_PlainDate_instRepr___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_PlainDate_instRepr___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_PlainDate_instRepr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDate_instRepr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_PlainDate_instRepr: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDate_instRepr___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_PlainTime_format___lam__0___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainTime_format___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainTime_fromTime24Hour___lam__0___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainTime_fromTime24Hour___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainTime_fromTime24Hour___lam__0___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainTime_fromTime24Hour___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_PlainTime_fromTime24Hour___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_PlainTime_fromTime24Hour___lam__0 as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_PlainTime_fromTime24Hour___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainTime_fromTime24Hour___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_PlainTime_fromLeanTime24Hour___closed__0_value:
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
    m_fun: l_Std_Time_PlainTime_fromLeanTime24Hour___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_PlainTime_fromLeanTime24Hour___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainTime_fromLeanTime24Hour___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_PlainTime_fromTime12Hour___lam__0___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainTime_fromTime12Hour___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_PlainTime_fromTime12Hour___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_PlainTime_fromTime12Hour___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_PlainTime_fromTime12Hour___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainTime_fromTime12Hour___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_PlainTime_instToString___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_PlainTime_toLeanTime24Hour as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_PlainTime_instToString___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainTime_instToString___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_PlainTime_instToString: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainTime_instToString___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_PlainTime_instRepr___lam__0___closed__0_value:
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
    m_data: [116, 105, 109, 101, 40, 34, 0],
};
static mut l_Std_Time_PlainTime_instRepr___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainTime_instRepr___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_PlainTime_instRepr___lam__0___closed__1_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Std_Time_PlainTime_instRepr___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_PlainTime_instRepr___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainTime_instRepr___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_PlainTime_instRepr___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_PlainTime_instRepr___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_PlainTime_instRepr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainTime_instRepr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_PlainTime_instRepr: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainTime_instRepr___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_ZonedDateTime_format___lam__0___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_ZonedDateTime_format___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_ZonedDateTime_instToString___closed__0_value:
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
    m_fun: l_Std_Time_ZonedDateTime_toLeanDateTimeWithIdentifierString as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_ZonedDateTime_instToString___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instToString___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_ZonedDateTime_instToString: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instToString___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_ZonedDateTime_instRepr___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [122, 111, 110, 101, 100, 40, 34, 0],
};
static mut l_Std_Time_ZonedDateTime_instRepr___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instRepr___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_ZonedDateTime_instRepr___lam__0___closed__1_value:
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
        core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instRepr___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_ZonedDateTime_instRepr___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instRepr___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_ZonedDateTime_instRepr___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_ZonedDateTime_instRepr___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_ZonedDateTime_instRepr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instRepr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_ZonedDateTime_instRepr: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instRepr___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_PlainDateTime_fromAscTimeString___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDateTime_fromAscTimeString___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_toAscTimeString___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDateTime_toAscTimeString___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_PlainDateTime_instToString___closed__0_value:
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
    m_fun: l_Std_Time_PlainDateTime_toLeanDateTimeString as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_PlainDateTime_instToString___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDateTime_instToString___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_PlainDateTime_instToString: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDateTime_instToString___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_PlainDateTime_instRepr___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [100, 97, 116, 101, 116, 105, 109, 101, 40, 34, 0],
};
static mut l_Std_Time_PlainDateTime_instRepr___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDateTime_instRepr___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_PlainDateTime_instRepr___lam__0___closed__1_value:
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
        core::ptr::addr_of!(l_Std_Time_PlainDateTime_instRepr___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_PlainDateTime_instRepr___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDateTime_instRepr___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_PlainDateTime_instRepr___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_PlainDateTime_instRepr___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_PlainDateTime_instRepr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDateTime_instRepr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_PlainDateTime_instRepr: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDateTime_instRepr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_Std_Time_Formats_iso8601___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_1972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: u8 = 0;
    let mut v___x_1974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1972_ = l_Std_Time_DateFormat_enUS;
    v___x_1973_ = 0;
    v___x_1974_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_1974_, 0, v___x_1972_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1974_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_1973_,
    );
    return v___x_1974_;
}
pub unsafe fn _init_l_Std_Time_Formats_iso8601___closed__34() -> *mut crate::leanh::LeanObject {
    let mut v___x_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2050_ = l_Std_Time_Formats_iso8601___closed__33;
    v___x_2051_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0_once),
        _init_l_Std_Time_Formats_iso8601___closed__0,
    );
    v___x_2052_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2052_, 0, v___x_2051_);
    crate::leanh::lean_ctor_set(v___x_2052_, 1, v___x_2050_);
    return v___x_2052_;
}
pub unsafe fn _init_l_Std_Time_Formats_iso8601() -> *mut crate::leanh::LeanObject {
    let mut v___x_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2053_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__34),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__34_once),
        _init_l_Std_Time_Formats_iso8601___closed__34,
    );
    return v___x_2053_;
}
pub unsafe fn _init_l_Std_Time_Formats_americanDate___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2069_ = l_Std_Time_Formats_americanDate___closed__4;
    v___x_2070_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0_once),
        _init_l_Std_Time_Formats_iso8601___closed__0,
    );
    v___x_2071_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2071_, 0, v___x_2070_);
    crate::leanh::lean_ctor_set(v___x_2071_, 1, v___x_2069_);
    return v___x_2071_;
}
pub unsafe fn _init_l_Std_Time_Formats_americanDate() -> *mut crate::leanh::LeanObject {
    let mut v___x_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2072_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_americanDate___closed__5),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_americanDate___closed__5_once),
        _init_l_Std_Time_Formats_americanDate___closed__5,
    );
    return v___x_2072_;
}
pub unsafe fn _init_l_Std_Time_Formats_europeanDate___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2082_ = l_Std_Time_Formats_europeanDate___closed__2;
    v___x_2083_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0_once),
        _init_l_Std_Time_Formats_iso8601___closed__0,
    );
    v___x_2084_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2084_, 0, v___x_2083_);
    crate::leanh::lean_ctor_set(v___x_2084_, 1, v___x_2082_);
    return v___x_2084_;
}
pub unsafe fn _init_l_Std_Time_Formats_europeanDate() -> *mut crate::leanh::LeanObject {
    let mut v___x_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2085_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_europeanDate___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_europeanDate___closed__3_once),
        _init_l_Std_Time_Formats_europeanDate___closed__3,
    );
    return v___x_2085_;
}
pub unsafe fn _init_l_Std_Time_Formats_time12Hour___closed__13() -> *mut crate::leanh::LeanObject {
    let mut v___x_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2118_ = l_Std_Time_Formats_time12Hour___closed__12;
    v___x_2119_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0_once),
        _init_l_Std_Time_Formats_iso8601___closed__0,
    );
    v___x_2120_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2120_, 0, v___x_2119_);
    crate::leanh::lean_ctor_set(v___x_2120_, 1, v___x_2118_);
    return v___x_2120_;
}
pub unsafe fn _init_l_Std_Time_Formats_time12Hour() -> *mut crate::leanh::LeanObject {
    let mut v___x_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2121_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_time12Hour___closed__13),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_time12Hour___closed__13_once),
        _init_l_Std_Time_Formats_time12Hour___closed__13,
    );
    return v___x_2121_;
}
pub unsafe fn _init_l_Std_Time_Formats_time24Hour___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2137_ = l_Std_Time_Formats_time24Hour___closed__4;
    v___x_2138_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0_once),
        _init_l_Std_Time_Formats_iso8601___closed__0,
    );
    v___x_2139_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2139_, 0, v___x_2138_);
    crate::leanh::lean_ctor_set(v___x_2139_, 1, v___x_2137_);
    return v___x_2139_;
}
pub unsafe fn _init_l_Std_Time_Formats_time24Hour() -> *mut crate::leanh::LeanObject {
    let mut v___x_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2140_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_time24Hour___closed__5),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_time24Hour___closed__5_once),
        _init_l_Std_Time_Formats_time24Hour___closed__5,
    );
    return v___x_2140_;
}
pub unsafe fn _init_l_Std_Time_Formats_dateTime24Hour___closed__17() -> *mut crate::leanh::LeanObject
{
    let mut v___x_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2187_ = l_Std_Time_Formats_dateTime24Hour___closed__16;
    v___x_2188_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0_once),
        _init_l_Std_Time_Formats_iso8601___closed__0,
    );
    v___x_2189_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2189_, 0, v___x_2188_);
    crate::leanh::lean_ctor_set(v___x_2189_, 1, v___x_2187_);
    return v___x_2189_;
}
pub unsafe fn _init_l_Std_Time_Formats_dateTime24Hour() -> *mut crate::leanh::LeanObject {
    let mut v___x_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2190_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_dateTime24Hour___closed__17),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_dateTime24Hour___closed__17_once),
        _init_l_Std_Time_Formats_dateTime24Hour___closed__17,
    );
    return v___x_2190_;
}
pub unsafe fn _init_l_Std_Time_Formats_dateTimeWithZone___closed__16()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2237_ = l_Std_Time_Formats_dateTimeWithZone___closed__15;
    v___x_2238_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0_once),
        _init_l_Std_Time_Formats_iso8601___closed__0,
    );
    v___x_2239_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2239_, 0, v___x_2238_);
    crate::leanh::lean_ctor_set(v___x_2239_, 1, v___x_2237_);
    return v___x_2239_;
}
pub unsafe fn _init_l_Std_Time_Formats_dateTimeWithZone() -> *mut crate::leanh::LeanObject {
    let mut v___x_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2240_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_dateTimeWithZone___closed__16),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_dateTimeWithZone___closed__16_once),
        _init_l_Std_Time_Formats_dateTimeWithZone___closed__16,
    );
    return v___x_2240_;
}
pub unsafe fn _init_l_Std_Time_Formats_leanTime24Hour___closed__0() -> *mut crate::leanh::LeanObject
{
    let mut v___x_2241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2241_ = l_Std_Time_Formats_dateTime24Hour___closed__10;
    v___x_2242_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0_once),
        _init_l_Std_Time_Formats_iso8601___closed__0,
    );
    v___x_2243_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2243_, 0, v___x_2242_);
    crate::leanh::lean_ctor_set(v___x_2243_, 1, v___x_2241_);
    return v___x_2243_;
}
pub unsafe fn _init_l_Std_Time_Formats_leanTime24Hour() -> *mut crate::leanh::LeanObject {
    let mut v___x_2244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2244_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_leanTime24Hour___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_leanTime24Hour___closed__0_once),
        _init_l_Std_Time_Formats_leanTime24Hour___closed__0,
    );
    return v___x_2244_;
}
pub unsafe fn _init_l_Std_Time_Formats_leanTime24HourNoNanos() -> *mut crate::leanh::LeanObject {
    let mut v___x_2245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2245_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_time24Hour___closed__5),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_time24Hour___closed__5_once),
        _init_l_Std_Time_Formats_time24Hour___closed__5,
    );
    return v___x_2245_;
}
pub unsafe fn _init_l_Std_Time_Formats_leanDateTime24Hour___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2264_ = l_Std_Time_Formats_leanDateTime24Hour___closed__5;
    v___x_2265_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0_once),
        _init_l_Std_Time_Formats_iso8601___closed__0,
    );
    v___x_2266_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2266_, 0, v___x_2265_);
    crate::leanh::lean_ctor_set(v___x_2266_, 1, v___x_2264_);
    return v___x_2266_;
}
pub unsafe fn _init_l_Std_Time_Formats_leanDateTime24Hour() -> *mut crate::leanh::LeanObject {
    let mut v___x_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2267_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_leanDateTime24Hour___closed__6),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_leanDateTime24Hour___closed__6_once),
        _init_l_Std_Time_Formats_leanDateTime24Hour___closed__6,
    );
    return v___x_2267_;
}
pub unsafe fn _init_l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2286_ = l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__5;
    v___x_2287_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0_once),
        _init_l_Std_Time_Formats_iso8601___closed__0,
    );
    v___x_2288_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2288_, 0, v___x_2287_);
    crate::leanh::lean_ctor_set(v___x_2288_, 1, v___x_2286_);
    return v___x_2288_;
}
pub unsafe fn _init_l_Std_Time_Formats_leanDateTime24HourNoNanos() -> *mut crate::leanh::LeanObject
{
    let mut v___x_2289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2289_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__6),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__6_once),
        _init_l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__6,
    );
    return v___x_2289_;
}
pub unsafe fn _init_l_Std_Time_Formats_leanDateTimeWithZone___closed__16()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2336_ = l_Std_Time_Formats_leanDateTimeWithZone___closed__15;
    v___x_2337_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0_once),
        _init_l_Std_Time_Formats_iso8601___closed__0,
    );
    v___x_2338_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2338_, 0, v___x_2337_);
    crate::leanh::lean_ctor_set(v___x_2338_, 1, v___x_2336_);
    return v___x_2338_;
}
pub unsafe fn _init_l_Std_Time_Formats_leanDateTimeWithZone() -> *mut crate::leanh::LeanObject {
    let mut v___x_2339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2339_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_leanDateTimeWithZone___closed__16),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_leanDateTimeWithZone___closed__16_once),
        _init_l_Std_Time_Formats_leanDateTimeWithZone___closed__16,
    );
    return v___x_2339_;
}
pub unsafe fn _init_l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2373_ = l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__10;
    v___x_2374_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0_once),
        _init_l_Std_Time_Formats_iso8601___closed__0,
    );
    v___x_2375_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2375_, 0, v___x_2374_);
    crate::leanh::lean_ctor_set(v___x_2375_, 1, v___x_2373_);
    return v___x_2375_;
}
pub unsafe fn _init_l_Std_Time_Formats_leanDateTimeWithZoneNoNanos() -> *mut crate::leanh::LeanObject
{
    let mut v___x_2376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2376_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__11),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__11_once),
        _init_l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__11,
    );
    return v___x_2376_;
}
pub unsafe fn _init_l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__20()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2429_ = l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__19;
    v___x_2430_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0_once),
        _init_l_Std_Time_Formats_iso8601___closed__0,
    );
    v___x_2431_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2431_, 0, v___x_2430_);
    crate::leanh::lean_ctor_set(v___x_2431_, 1, v___x_2429_);
    return v___x_2431_;
}
pub unsafe fn _init_l_Std_Time_Formats_leanDateTimeWithIdentifier() -> *mut crate::leanh::LeanObject
{
    let mut v___x_2432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2432_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__20),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__20_once),
        _init_l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__20,
    );
    return v___x_2432_;
}
pub unsafe fn _init_l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2472_ = l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__12;
    v___x_2473_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0_once),
        _init_l_Std_Time_Formats_iso8601___closed__0,
    );
    v___x_2474_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2474_, 0, v___x_2473_);
    crate::leanh::lean_ctor_set(v___x_2474_, 1, v___x_2472_);
    return v___x_2474_;
}
pub unsafe fn _init_l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2475_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__13),
        core::ptr::addr_of_mut!(
            l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__13_once
        ),
        _init_l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__13,
    );
    return v___x_2475_;
}
pub unsafe fn _init_l_Std_Time_Formats_leanDate___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_2491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2491_ = l_Std_Time_Formats_leanDate___closed__4;
    v___x_2492_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0_once),
        _init_l_Std_Time_Formats_iso8601___closed__0,
    );
    v___x_2493_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2493_, 0, v___x_2492_);
    crate::leanh::lean_ctor_set(v___x_2493_, 1, v___x_2491_);
    return v___x_2493_;
}
pub unsafe fn _init_l_Std_Time_Formats_leanDate() -> *mut crate::leanh::LeanObject {
    let mut v___x_2494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2494_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_leanDate___closed__5),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_leanDate___closed__5_once),
        _init_l_Std_Time_Formats_leanDate___closed__5,
    );
    return v___x_2494_;
}
pub unsafe fn _init_l_Std_Time_Formats_sqlDate() -> *mut crate::leanh::LeanObject {
    let mut v___x_2495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2495_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_leanDate___closed__5),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_leanDate___closed__5_once),
        _init_l_Std_Time_Formats_leanDate___closed__5,
    );
    return v___x_2495_;
}
pub unsafe fn _init_l_Std_Time_Formats_longDateFormat___closed__17() -> *mut crate::leanh::LeanObject
{
    let mut v___x_2538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2538_ = l_Std_Time_Formats_longDateFormat___closed__16;
    v___x_2539_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0_once),
        _init_l_Std_Time_Formats_iso8601___closed__0,
    );
    v___x_2540_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2540_, 0, v___x_2539_);
    crate::leanh::lean_ctor_set(v___x_2540_, 1, v___x_2538_);
    return v___x_2540_;
}
pub unsafe fn _init_l_Std_Time_Formats_longDateFormat() -> *mut crate::leanh::LeanObject {
    let mut v___x_2541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2541_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_longDateFormat___closed__17),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_longDateFormat___closed__17_once),
        _init_l_Std_Time_Formats_longDateFormat___closed__17,
    );
    return v___x_2541_;
}
pub unsafe fn _init_l_Std_Time_Formats_ascTime___closed__17() -> *mut crate::leanh::LeanObject {
    let mut v___x_2589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2589_ = l_Std_Time_Formats_ascTime___closed__16;
    v___x_2590_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0_once),
        _init_l_Std_Time_Formats_iso8601___closed__0,
    );
    v___x_2591_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2591_, 0, v___x_2590_);
    crate::leanh::lean_ctor_set(v___x_2591_, 1, v___x_2589_);
    return v___x_2591_;
}
pub unsafe fn _init_l_Std_Time_Formats_ascTime() -> *mut crate::leanh::LeanObject {
    let mut v___x_2592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2592_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_ascTime___closed__17),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_ascTime___closed__17_once),
        _init_l_Std_Time_Formats_ascTime___closed__17,
    );
    return v___x_2592_;
}
pub unsafe fn _init_l_Std_Time_Formats_rfc822___closed__16() -> *mut crate::leanh::LeanObject {
    let mut v___x_2639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2639_ = l_Std_Time_Formats_rfc822___closed__15;
    v___x_2640_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0_once),
        _init_l_Std_Time_Formats_iso8601___closed__0,
    );
    v___x_2641_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2641_, 0, v___x_2640_);
    crate::leanh::lean_ctor_set(v___x_2641_, 1, v___x_2639_);
    return v___x_2641_;
}
pub unsafe fn _init_l_Std_Time_Formats_rfc822() -> *mut crate::leanh::LeanObject {
    let mut v___x_2642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2642_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_rfc822___closed__16),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_rfc822___closed__16_once),
        _init_l_Std_Time_Formats_rfc822___closed__16,
    );
    return v___x_2642_;
}
pub unsafe fn _init_l_Std_Time_Formats_rfc850___closed__6() -> *mut crate::leanh::LeanObject {
    let mut v___x_2661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2661_ = l_Std_Time_Formats_rfc850___closed__5;
    v___x_2662_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0_once),
        _init_l_Std_Time_Formats_iso8601___closed__0,
    );
    v___x_2663_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2663_, 0, v___x_2662_);
    crate::leanh::lean_ctor_set(v___x_2663_, 1, v___x_2661_);
    return v___x_2663_;
}
pub unsafe fn _init_l_Std_Time_Formats_rfc850() -> *mut crate::leanh::LeanObject {
    let mut v___x_2664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2664_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_rfc850___closed__6),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_rfc850___closed__6_once),
        _init_l_Std_Time_Formats_rfc850___closed__6,
    );
    return v___x_2664_;
}
pub unsafe fn l_Std_Time_TimeZone_fromTimeZone___lam__0(
    mut v___x_2665_: u8,
    mut v_id_2666_: *mut crate::leanh::LeanObject,
    mut v_off_2667_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2668_: u8 = 0;
    let mut v___x_2669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2668_ = 1;
    crate::leanh::lean_inc(v_off_2667_);
    v___x_2669_ = l_Std_Time_TimeZone_Offset_toIsoString(v_off_2667_, v___x_2668_);
    v___x_2670_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_2670_, 0, v_off_2667_);
    crate::leanh::lean_ctor_set(v___x_2670_, 1, v_id_2666_);
    crate::leanh::lean_ctor_set(v___x_2670_, 2, v___x_2669_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2670_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v___x_2665_,
    );
    v___x_2671_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2671_, 0, v___x_2670_);
    return v___x_2671_;
}
pub unsafe fn l_Std_Time_TimeZone_fromTimeZone___lam__0___boxed(
    mut v___x_2672_: *mut crate::leanh::LeanObject,
    mut v_id_2673_: *mut crate::leanh::LeanObject,
    mut v_off_2674_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_30__boxed_2675_: u8 = 0;
    let mut v_res_2676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_30__boxed_2675_ = (crate::leanh::lean_unbox(v___x_2672_) as u8);
    v_res_2676_ =
        l_Std_Time_TimeZone_fromTimeZone___lam__0(v___x_30__boxed_2675_, v_id_2673_, v_off_2674_);
    return v_res_2676_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_fromTimeZone___closed__4() -> *mut crate::leanh::LeanObject
{
    let mut v___x_2688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_spec_2690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2688_ = l_Std_Time_TimeZone_fromTimeZone___closed__3;
    v___x_2689_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0_once),
        _init_l_Std_Time_Formats_iso8601___closed__0,
    );
    v_spec_2690_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v_spec_2690_, 0, v___x_2689_);
    crate::leanh::lean_ctor_set(v_spec_2690_, 1, v___x_2688_);
    return v_spec_2690_;
}
pub unsafe fn l_Std_Time_TimeZone_fromTimeZone(
    mut v_input_2691_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_spec_2693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2692_ = l_Std_Time_TimeZone_fromTimeZone___closed__0;
    v_spec_2693_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_TimeZone_fromTimeZone___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_TimeZone_fromTimeZone___closed__4_once),
        _init_l_Std_Time_TimeZone_fromTimeZone___closed__4,
    );
    v___x_2694_ =
        l_Std_Time_GenericFormat_parseBuilder___redArg(v_spec_2693_, v___f_2692_, v_input_2691_);
    return v___x_2694_;
}
pub unsafe fn l_Std_Time_TimeZone_Offset_fromOffset___lam__0(
    mut v_val_2695_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2696_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2696_, 0, v_val_2695_);
    return v___x_2696_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_Offset_fromOffset___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_spec_2707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2705_ = l_Std_Time_TimeZone_Offset_fromOffset___closed__3;
    v___x_2706_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0_once),
        _init_l_Std_Time_Formats_iso8601___closed__0,
    );
    v_spec_2707_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v_spec_2707_, 0, v___x_2706_);
    crate::leanh::lean_ctor_set(v_spec_2707_, 1, v___x_2705_);
    return v_spec_2707_;
}
pub unsafe fn l_Std_Time_TimeZone_Offset_fromOffset(
    mut v_input_2708_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_spec_2710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2709_ = l_Std_Time_TimeZone_Offset_fromOffset___closed__0;
    v_spec_2710_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_TimeZone_Offset_fromOffset___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_TimeZone_Offset_fromOffset___closed__4_once),
        _init_l_Std_Time_TimeZone_Offset_fromOffset___closed__4,
    );
    v___x_2711_ =
        l_Std_Time_GenericFormat_parseBuilder___redArg(v_spec_2710_, v___f_2709_, v_input_2708_);
    return v___x_2711_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_format___lam__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2712_ = crate::leanh::lean_unsigned_to_nat(4);
    v___x_2713_ = lean_nat_to_int(v___x_2712_);
    return v___x_2713_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_format___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2714_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2715_ = lean_nat_to_int(v___x_2714_);
    return v___x_2715_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_format___lam__0___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2716_ = crate::leanh::lean_unsigned_to_nat(400);
    v___x_2717_ = lean_nat_to_int(v___x_2716_);
    return v___x_2717_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_format___lam__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2718_ = crate::leanh::lean_unsigned_to_nat(100);
    v___x_2719_ = lean_nat_to_int(v___x_2718_);
    return v___x_2719_;
}
pub unsafe fn l_Std_Time_PlainDate_format___lam__0(
    mut v_date_2720_: *mut crate::leanh::LeanObject,
    mut v_locale_2721_: *mut crate::leanh::LeanObject,
    mut v_x_2722_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2724_: u8 = 0;
    let mut v___x_2725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_year_2729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2730_: u8 = 0;
    let mut v___x_2731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2735_: u8 = 0;
    let mut v_year_2736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2740_: u8 = 0;
    let mut v_unused_2741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2744_: u8 = 0;
    let mut v_year_2745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2749_: u8 = 0;
    let mut v_unused_2750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2753_: u8 = 0;
    let mut v_firstDayOfWeek_2754_: u8 = 0;
    let mut v___x_2755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2759_: u8 = 0;
    let mut v_unused_2760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_year_2761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: u8 = 0;
    let mut v___x_2769_: u8 = 0;
    let mut v___x_2770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: u8 = 0;
    let mut v___x_2774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2775_: u8 = 0;
    let mut v___x_2776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2780_: u8 = 0;
    let mut v_unused_2781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2784_: u8 = 0;
    let mut v_firstDayOfWeek_2785_: u8 = 0;
    let mut v___x_2786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2790_: u8 = 0;
    let mut v_unused_2791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2794_: u8 = 0;
    let mut v_firstDayOfWeek_2795_: u8 = 0;
    let mut v___x_2796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2800_: u8 = 0;
    let mut v_unused_2801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2804_: u8 = 0;
    let mut v_month_2805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2809_: u8 = 0;
    let mut v_unused_2810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2813_: u8 = 0;
    let mut v_day_2814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2818_: u8 = 0;
    let mut v_unused_2819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: u8 = 0;
    let mut v___x_2821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2825_: u8 = 0;
    let mut v___x_2826_: u8 = 0;
    let mut v___x_2827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2831_: u8 = 0;
    let mut v_unused_2832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2835_: u8 = 0;
    let mut v___x_2836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2840_: u8 = 0;
    let mut v_unused_2841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_2722_) {
                0 => {
                    crate::leanh::lean_dec_ref_known(v_x_2722_, 0);
                    v_year_2729_ = crate::leanh::lean_ctor_get(v_date_2720_, 0);
                    crate::leanh::lean_inc(v_year_2729_);
                    crate::leanh::lean_dec_ref(v_date_2720_);
                    v___x_2730_ = l_Std_Time_Year_Offset_era(v_year_2729_);
                    crate::leanh::lean_dec(v_year_2729_);
                    v___x_2731_ = crate::leanh::lean_box((v___x_2730_) as usize);
                    v___x_2732_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2732_, 0, v___x_2731_);
                    return v___x_2732_;
                }
                1 => {
                    v_isSharedCheck_2740_ = (!crate::leanh::lean_is_exclusive(v_x_2722_)) as u8;
                    if v_isSharedCheck_2740_ == 0 {
                        v_unused_2741_ = crate::leanh::lean_ctor_get(v_x_2722_, 0);
                        crate::leanh::lean_dec(v_unused_2741_);
                        v___x_2734_ = v_x_2722_;
                        v_isShared_2735_ = v_isSharedCheck_2740_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_x_2722_);
                        v___x_2734_ = crate::leanh::lean_box(0);
                        v_isShared_2735_ = v_isSharedCheck_2740_;
                        state = 2;
                        continue;
                    }
                }
                2 => {
                    v_isSharedCheck_2749_ = (!crate::leanh::lean_is_exclusive(v_x_2722_)) as u8;
                    if v_isSharedCheck_2749_ == 0 {
                        v_unused_2750_ = crate::leanh::lean_ctor_get(v_x_2722_, 0);
                        crate::leanh::lean_dec(v_unused_2750_);
                        v___x_2743_ = v_x_2722_;
                        v_isShared_2744_ = v_isSharedCheck_2749_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_x_2722_);
                        v___x_2743_ = crate::leanh::lean_box(0);
                        v_isShared_2744_ = v_isSharedCheck_2749_;
                        state = 4;
                        continue;
                    }
                }
                3 => {
                    v_isSharedCheck_2759_ = (!crate::leanh::lean_is_exclusive(v_x_2722_)) as u8;
                    if v_isSharedCheck_2759_ == 0 {
                        v_unused_2760_ = crate::leanh::lean_ctor_get(v_x_2722_, 0);
                        crate::leanh::lean_dec(v_unused_2760_);
                        v___x_2752_ = v_x_2722_;
                        v_isShared_2753_ = v_isSharedCheck_2759_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_x_2722_);
                        v___x_2752_ = crate::leanh::lean_box(0);
                        v_isShared_2753_ = v_isSharedCheck_2759_;
                        state = 6;
                        continue;
                    }
                }
                4 => {
                    crate::leanh::lean_dec_ref_known(v_x_2722_, 1);
                    v_year_2761_ = crate::leanh::lean_ctor_get(v_date_2720_, 0);
                    v___x_2762_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_format___lam__0___closed__0),
                        core::ptr::addr_of_mut!(
                            l_Std_Time_PlainDate_format___lam__0___closed__0_once
                        ),
                        _init_l_Std_Time_PlainDate_format___lam__0___closed__0,
                    );
                    v___x_2763_ = lean_int_mod(v_year_2761_, v___x_2762_);
                    v___x_2764_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_format___lam__0___closed__1),
                        core::ptr::addr_of_mut!(
                            l_Std_Time_PlainDate_format___lam__0___closed__1_once
                        ),
                        _init_l_Std_Time_PlainDate_format___lam__0___closed__1,
                    );
                    v___x_2769_ = lean_int_dec_eq(v___x_2763_, v___x_2764_);
                    crate::leanh::lean_dec(v___x_2763_);
                    if v___x_2769_ == 0 {
                        v___y_2724_ = v___x_2769_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2770_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Time_PlainDate_format___lam__0___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Time_PlainDate_format___lam__0___closed__3_once
                            ),
                            _init_l_Std_Time_PlainDate_format___lam__0___closed__3,
                        );
                        v___x_2771_ = lean_int_mod(v_year_2761_, v___x_2770_);
                        v___x_2772_ = lean_int_dec_eq(v___x_2771_, v___x_2764_);
                        crate::leanh::lean_dec(v___x_2771_);
                        if v___x_2772_ == 0 {
                            if v___x_2769_ == 0 {
                                state = 8;
                                continue;
                            } else {
                                v___y_2724_ = v___x_2769_;
                                state = 1;
                                continue;
                            }
                        } else {
                            state = 8;
                            continue;
                        }
                    }
                }
                7 => {
                    v_isSharedCheck_2780_ = (!crate::leanh::lean_is_exclusive(v_x_2722_)) as u8;
                    if v_isSharedCheck_2780_ == 0 {
                        v_unused_2781_ = crate::leanh::lean_ctor_get(v_x_2722_, 0);
                        crate::leanh::lean_dec(v_unused_2781_);
                        v___x_2774_ = v_x_2722_;
                        v_isShared_2775_ = v_isSharedCheck_2780_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_x_2722_);
                        v___x_2774_ = crate::leanh::lean_box(0);
                        v_isShared_2775_ = v_isSharedCheck_2780_;
                        state = 9;
                        continue;
                    }
                }
                8 => {
                    v_isSharedCheck_2790_ = (!crate::leanh::lean_is_exclusive(v_x_2722_)) as u8;
                    if v_isSharedCheck_2790_ == 0 {
                        v_unused_2791_ = crate::leanh::lean_ctor_get(v_x_2722_, 0);
                        crate::leanh::lean_dec(v_unused_2791_);
                        v___x_2783_ = v_x_2722_;
                        v_isShared_2784_ = v_isSharedCheck_2790_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_x_2722_);
                        v___x_2783_ = crate::leanh::lean_box(0);
                        v_isShared_2784_ = v_isSharedCheck_2790_;
                        state = 11;
                        continue;
                    }
                }
                9 => {
                    v_isSharedCheck_2800_ = (!crate::leanh::lean_is_exclusive(v_x_2722_)) as u8;
                    if v_isSharedCheck_2800_ == 0 {
                        v_unused_2801_ = crate::leanh::lean_ctor_get(v_x_2722_, 0);
                        crate::leanh::lean_dec(v_unused_2801_);
                        v___x_2793_ = v_x_2722_;
                        v_isShared_2794_ = v_isSharedCheck_2800_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_x_2722_);
                        v___x_2793_ = crate::leanh::lean_box(0);
                        v_isShared_2794_ = v_isSharedCheck_2800_;
                        state = 13;
                        continue;
                    }
                }
                5 => {
                    v_isSharedCheck_2809_ = (!crate::leanh::lean_is_exclusive(v_x_2722_)) as u8;
                    if v_isSharedCheck_2809_ == 0 {
                        v_unused_2810_ = crate::leanh::lean_ctor_get(v_x_2722_, 0);
                        crate::leanh::lean_dec(v_unused_2810_);
                        v___x_2803_ = v_x_2722_;
                        v_isShared_2804_ = v_isSharedCheck_2809_;
                        state = 15;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_x_2722_);
                        v___x_2803_ = crate::leanh::lean_box(0);
                        v_isShared_2804_ = v_isSharedCheck_2809_;
                        state = 15;
                        continue;
                    }
                }
                6 => {
                    v_isSharedCheck_2818_ = (!crate::leanh::lean_is_exclusive(v_x_2722_)) as u8;
                    if v_isSharedCheck_2818_ == 0 {
                        v_unused_2819_ = crate::leanh::lean_ctor_get(v_x_2722_, 0);
                        crate::leanh::lean_dec(v_unused_2819_);
                        v___x_2812_ = v_x_2722_;
                        v_isShared_2813_ = v_isSharedCheck_2818_;
                        state = 17;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_x_2722_);
                        v___x_2812_ = crate::leanh::lean_box(0);
                        v_isShared_2813_ = v_isSharedCheck_2818_;
                        state = 17;
                        continue;
                    }
                }
                10 => {
                    crate::leanh::lean_dec_ref_known(v_x_2722_, 0);
                    v___x_2820_ = l_Std_Time_PlainDate_weekday(v_date_2720_);
                    v___x_2821_ = crate::leanh::lean_box((v___x_2820_) as usize);
                    v___x_2822_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2822_, 0, v___x_2821_);
                    return v___x_2822_;
                }
                11 => {
                    v_isSharedCheck_2831_ = (!crate::leanh::lean_is_exclusive(v_x_2722_)) as u8;
                    if v_isSharedCheck_2831_ == 0 {
                        v_unused_2832_ = crate::leanh::lean_ctor_get(v_x_2722_, 0);
                        crate::leanh::lean_dec(v_unused_2832_);
                        v___x_2824_ = v_x_2722_;
                        v_isShared_2825_ = v_isSharedCheck_2831_;
                        state = 19;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_x_2722_);
                        v___x_2824_ = crate::leanh::lean_box(0);
                        v_isShared_2825_ = v_isSharedCheck_2831_;
                        state = 19;
                        continue;
                    }
                }
                12 => {
                    v_isSharedCheck_2840_ = (!crate::leanh::lean_is_exclusive(v_x_2722_)) as u8;
                    if v_isSharedCheck_2840_ == 0 {
                        v_unused_2841_ = crate::leanh::lean_ctor_get(v_x_2722_, 0);
                        crate::leanh::lean_dec(v_unused_2841_);
                        v___x_2834_ = v_x_2722_;
                        v_isShared_2835_ = v_isSharedCheck_2840_;
                        state = 21;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_x_2722_);
                        v___x_2834_ = crate::leanh::lean_box(0);
                        v_isShared_2835_ = v_isSharedCheck_2840_;
                        state = 21;
                        continue;
                    }
                }
                _ => {
                    crate::leanh::lean_dec(v_x_2722_);
                    crate::leanh::lean_dec_ref(v_date_2720_);
                    v___x_2842_ = crate::leanh::lean_box(0);
                    return v___x_2842_;
                }
            },
            1 => {
                v___x_2725_ = l_Std_Time_PlainDate_dayOfYear(v_date_2720_);
                crate::leanh::lean_dec_ref(v_date_2720_);
                v___x_2726_ = crate::leanh::lean_box((v___y_2724_) as usize);
                v___x_2727_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2727_, 0, v___x_2726_);
                crate::leanh::lean_ctor_set(v___x_2727_, 1, v___x_2725_);
                v___x_2728_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2728_, 0, v___x_2727_);
                return v___x_2728_;
            }
            2 => {
                v_year_2736_ = crate::leanh::lean_ctor_get(v_date_2720_, 0);
                crate::leanh::lean_inc(v_year_2736_);
                crate::leanh::lean_dec_ref(v_date_2720_);
                if v_isShared_2735_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2734_, 0, v_year_2736_);
                    v___x_2738_ = v___x_2734_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2739_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2739_, 0, v_year_2736_);
                    v___x_2738_ = v_reuseFailAlloc_2739_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2738_;
            }
            4 => {
                v_year_2745_ = crate::leanh::lean_ctor_get(v_date_2720_, 0);
                crate::leanh::lean_inc(v_year_2745_);
                crate::leanh::lean_dec_ref(v_date_2720_);
                if v_isShared_2744_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2743_, 1);
                    crate::leanh::lean_ctor_set(v___x_2743_, 0, v_year_2745_);
                    v___x_2747_ = v___x_2743_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2748_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2748_, 0, v_year_2745_);
                    v___x_2747_ = v_reuseFailAlloc_2748_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2747_;
            }
            6 => {
                v_firstDayOfWeek_2754_ = crate::leanh::lean_ctor_get_uint8(
                    v_locale_2721_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v___x_2755_ = l_Std_Time_PlainDate_weekYear(v_date_2720_, v_firstDayOfWeek_2754_);
                if v_isShared_2753_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2752_, 1);
                    crate::leanh::lean_ctor_set(v___x_2752_, 0, v___x_2755_);
                    v___x_2757_ = v___x_2752_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2758_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2758_, 0, v___x_2755_);
                    v___x_2757_ = v_reuseFailAlloc_2758_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2757_;
            }
            8 => {
                v___x_2766_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_format___lam__0___closed__2),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_format___lam__0___closed__2_once),
                    _init_l_Std_Time_PlainDate_format___lam__0___closed__2,
                );
                v___x_2767_ = lean_int_mod(v_year_2761_, v___x_2766_);
                v___x_2768_ = lean_int_dec_eq(v___x_2767_, v___x_2764_);
                crate::leanh::lean_dec(v___x_2767_);
                v___y_2724_ = v___x_2768_;
                state = 1;
                continue;
            }
            9 => {
                v___x_2776_ = l_Std_Time_PlainDate_quarter(v_date_2720_);
                crate::leanh::lean_dec_ref(v_date_2720_);
                if v_isShared_2775_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2774_, 1);
                    crate::leanh::lean_ctor_set(v___x_2774_, 0, v___x_2776_);
                    v___x_2778_ = v___x_2774_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2779_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2779_, 0, v___x_2776_);
                    v___x_2778_ = v_reuseFailAlloc_2779_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2778_;
            }
            11 => {
                v_firstDayOfWeek_2785_ = crate::leanh::lean_ctor_get_uint8(
                    v_locale_2721_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v___x_2786_ = l_Std_Time_PlainDate_weekOfYear(v_date_2720_, v_firstDayOfWeek_2785_);
                if v_isShared_2784_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2783_, 1);
                    crate::leanh::lean_ctor_set(v___x_2783_, 0, v___x_2786_);
                    v___x_2788_ = v___x_2783_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2789_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2789_, 0, v___x_2786_);
                    v___x_2788_ = v_reuseFailAlloc_2789_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2788_;
            }
            13 => {
                v_firstDayOfWeek_2795_ = crate::leanh::lean_ctor_get_uint8(
                    v_locale_2721_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v___x_2796_ =
                    l_Std_Time_PlainDate_alignedWeekOfMonth(v_date_2720_, v_firstDayOfWeek_2795_);
                if v_isShared_2794_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2793_, 1);
                    crate::leanh::lean_ctor_set(v___x_2793_, 0, v___x_2796_);
                    v___x_2798_ = v___x_2793_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2799_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2799_, 0, v___x_2796_);
                    v___x_2798_ = v_reuseFailAlloc_2799_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_2798_;
            }
            15 => {
                v_month_2805_ = crate::leanh::lean_ctor_get(v_date_2720_, 1);
                crate::leanh::lean_inc(v_month_2805_);
                crate::leanh::lean_dec_ref(v_date_2720_);
                if v_isShared_2804_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2803_, 1);
                    crate::leanh::lean_ctor_set(v___x_2803_, 0, v_month_2805_);
                    v___x_2807_ = v___x_2803_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2808_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2808_, 0, v_month_2805_);
                    v___x_2807_ = v_reuseFailAlloc_2808_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_2807_;
            }
            17 => {
                v_day_2814_ = crate::leanh::lean_ctor_get(v_date_2720_, 2);
                crate::leanh::lean_inc(v_day_2814_);
                crate::leanh::lean_dec_ref(v_date_2720_);
                if v_isShared_2813_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2812_, 1);
                    crate::leanh::lean_ctor_set(v___x_2812_, 0, v_day_2814_);
                    v___x_2816_ = v___x_2812_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2817_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2817_, 0, v_day_2814_);
                    v___x_2816_ = v_reuseFailAlloc_2817_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_2816_;
            }
            19 => {
                v___x_2826_ = l_Std_Time_PlainDate_weekday(v_date_2720_);
                v___x_2827_ = crate::leanh::lean_box((v___x_2826_) as usize);
                if v_isShared_2825_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2824_, 1);
                    crate::leanh::lean_ctor_set(v___x_2824_, 0, v___x_2827_);
                    v___x_2829_ = v___x_2824_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_2830_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2830_, 0, v___x_2827_);
                    v___x_2829_ = v_reuseFailAlloc_2830_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_2829_;
            }
            21 => {
                v___x_2836_ = l_Std_Time_PlainDate_weekOfMonth(v_date_2720_);
                crate::leanh::lean_dec_ref(v_date_2720_);
                if v_isShared_2835_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2834_, 1);
                    crate::leanh::lean_ctor_set(v___x_2834_, 0, v___x_2836_);
                    v___x_2838_ = v___x_2834_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_2839_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2839_, 0, v___x_2836_);
                    v___x_2838_ = v_reuseFailAlloc_2839_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_2838_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainDate_format___lam__0___boxed(
    mut v_date_2843_: *mut crate::leanh::LeanObject,
    mut v_locale_2844_: *mut crate::leanh::LeanObject,
    mut v_x_2845_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2846_ = l_Std_Time_PlainDate_format___lam__0(v_date_2843_, v_locale_2844_, v_x_2845_);
    crate::leanh::lean_dec_ref(v_locale_2844_);
    return v_res_2846_;
}
pub unsafe fn l_Std_Time_PlainDate_format(
    mut v_date_2849_: *mut crate::leanh::LeanObject,
    mut v_format_2850_: *mut crate::leanh::LeanObject,
    mut v_locale_2851_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_format_2853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2852_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0_once),
        _init_l_Std_Time_Formats_iso8601___closed__0,
    );
    v_format_2853_ = l_Std_Time_GenericFormat_spec___redArg(v_format_2850_, v___x_2852_);
    if crate::leanh::lean_obj_tag(v_format_2853_) == 0 {
        let mut v_a_2854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_locale_2851_);
        crate::leanh::lean_dec_ref(v_date_2849_);
        v_a_2854_ = crate::leanh::lean_ctor_get(v_format_2853_, 0);
        crate::leanh::lean_inc(v_a_2854_);
        crate::leanh::lean_dec_ref_known(v_format_2853_, 1);
        v___x_2855_ = l_Std_Time_PlainDate_format___closed__0;
        v___x_2856_ = lean_string_append(v___x_2855_, v_a_2854_);
        crate::leanh::lean_dec(v_a_2854_);
        return v___x_2856_;
    } else {
        let mut v_a_2857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_res_2859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_2857_ = crate::leanh::lean_ctor_get(v_format_2853_, 0);
        crate::leanh::lean_inc(v_a_2857_);
        crate::leanh::lean_dec_ref_known(v_format_2853_, 1);
        v___f_2858_ = crate::leanh::lean_alloc_closure(
            l_Std_Time_PlainDate_format___lam__0___boxed as *mut core::ffi::c_void,
            3,
            2,
        );
        crate::leanh::lean_closure_set(v___f_2858_, 0, v_date_2849_);
        crate::leanh::lean_closure_set(v___f_2858_, 1, v_locale_2851_);
        v_res_2859_ = l_Std_Time_GenericFormat_formatGeneric___redArg(v_a_2857_, v___f_2858_);
        if crate::leanh::lean_obj_tag(v_res_2859_) == 0 {
            let mut v___x_2860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2860_ = l_Std_Time_PlainDate_format___closed__1;
            return v___x_2860_;
        } else {
            let mut v_val_2861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_val_2861_ = crate::leanh::lean_ctor_get(v_res_2859_, 0);
            crate::leanh::lean_inc(v_val_2861_);
            crate::leanh::lean_dec_ref_known(v_res_2859_, 1);
            return v_val_2861_;
        }
    }
}
pub unsafe fn l_Std_Time_PlainDate_fromAmericanDateString___lam__0(
    mut v_m_2862_: *mut crate::leanh::LeanObject,
    mut v_d_2863_: *mut crate::leanh::LeanObject,
    mut v_y_2864_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2866_: u8 = 0;
    let mut v___x_2867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2868_: u8 = 0;
    let mut v___x_2869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2878_: u8 = 0;
    let mut v___x_2879_: u8 = 0;
    let mut v___x_2880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2882_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2872_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_format___lam__0___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_format___lam__0___closed__0_once),
                    _init_l_Std_Time_PlainDate_format___lam__0___closed__0,
                );
                v___x_2873_ = lean_int_mod(v_y_2864_, v___x_2872_);
                v___x_2874_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_format___lam__0___closed__1),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_format___lam__0___closed__1_once),
                    _init_l_Std_Time_PlainDate_format___lam__0___closed__1,
                );
                v___x_2879_ = lean_int_dec_eq(v___x_2873_, v___x_2874_);
                crate::leanh::lean_dec(v___x_2873_);
                if v___x_2879_ == 0 {
                    v___y_2866_ = v___x_2879_;
                    state = 1;
                    continue;
                } else {
                    v___x_2880_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_format___lam__0___closed__3),
                        core::ptr::addr_of_mut!(
                            l_Std_Time_PlainDate_format___lam__0___closed__3_once
                        ),
                        _init_l_Std_Time_PlainDate_format___lam__0___closed__3,
                    );
                    v___x_2881_ = lean_int_mod(v_y_2864_, v___x_2880_);
                    v___x_2882_ = lean_int_dec_eq(v___x_2881_, v___x_2874_);
                    crate::leanh::lean_dec(v___x_2881_);
                    if v___x_2882_ == 0 {
                        if v___x_2879_ == 0 {
                            state = 2;
                            continue;
                        } else {
                            v___y_2866_ = v___x_2879_;
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
                v___x_2867_ = l_Std_Time_Month_Ordinal_days(v___y_2866_, v_m_2862_);
                v___x_2868_ = lean_int_dec_le(v_d_2863_, v___x_2867_);
                crate::leanh::lean_dec(v___x_2867_);
                if v___x_2868_ == 0 {
                    crate::leanh::lean_dec(v_y_2864_);
                    crate::leanh::lean_dec(v_d_2863_);
                    crate::leanh::lean_dec(v_m_2862_);
                    v___x_2869_ = crate::leanh::lean_box(0);
                    return v___x_2869_;
                } else {
                    v___x_2870_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2870_, 0, v_y_2864_);
                    crate::leanh::lean_ctor_set(v___x_2870_, 1, v_m_2862_);
                    crate::leanh::lean_ctor_set(v___x_2870_, 2, v_d_2863_);
                    v___x_2871_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2871_, 0, v___x_2870_);
                    return v___x_2871_;
                }
            }
            2 => {
                v___x_2876_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_format___lam__0___closed__2),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_format___lam__0___closed__2_once),
                    _init_l_Std_Time_PlainDate_format___lam__0___closed__2,
                );
                v___x_2877_ = lean_int_mod(v_y_2864_, v___x_2876_);
                v___x_2878_ = lean_int_dec_eq(v___x_2877_, v___x_2874_);
                crate::leanh::lean_dec(v___x_2877_);
                v___y_2866_ = v___x_2878_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainDate_fromAmericanDateString(
    mut v_input_2884_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2885_ = l_Std_Time_PlainDate_fromAmericanDateString___closed__0;
    v___x_2886_ = l_Std_Time_Formats_americanDate;
    v___x_2887_ =
        l_Std_Time_GenericFormat_parseBuilder___redArg(v___x_2886_, v___f_2885_, v_input_2884_);
    return v___x_2887_;
}
pub unsafe fn l_Std_Time_PlainDate_toAmericanDateString(
    mut v_input_2888_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_year_2889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_month_2890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_day_2891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6__overap_2893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_year_2889_ = crate::leanh::lean_ctor_get(v_input_2888_, 0);
    crate::leanh::lean_inc(v_year_2889_);
    v_month_2890_ = crate::leanh::lean_ctor_get(v_input_2888_, 1);
    crate::leanh::lean_inc(v_month_2890_);
    v_day_2891_ = crate::leanh::lean_ctor_get(v_input_2888_, 2);
    crate::leanh::lean_inc(v_day_2891_);
    crate::leanh::lean_dec_ref(v_input_2888_);
    v___x_2892_ = l_Std_Time_Formats_americanDate;
    v___x_6__overap_2893_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_2892_);
    v___x_2894_ = crate::leanh::lean_apply_3(
        v___x_6__overap_2893_,
        v_month_2890_,
        v_day_2891_,
        v_year_2889_,
    );
    return v___x_2894_;
}
pub unsafe fn l_Std_Time_PlainDate_fromSQLDateString___lam__0(
    mut v___y_2895_: *mut crate::leanh::LeanObject,
    mut v___y_2896_: *mut crate::leanh::LeanObject,
    mut v___y_2897_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2899_: u8 = 0;
    let mut v___x_2900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: u8 = 0;
    let mut v___x_2902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2911_: u8 = 0;
    let mut v___x_2912_: u8 = 0;
    let mut v___x_2913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2915_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2905_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_format___lam__0___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_format___lam__0___closed__0_once),
                    _init_l_Std_Time_PlainDate_format___lam__0___closed__0,
                );
                v___x_2906_ = lean_int_mod(v___y_2895_, v___x_2905_);
                v___x_2907_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_format___lam__0___closed__1),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_format___lam__0___closed__1_once),
                    _init_l_Std_Time_PlainDate_format___lam__0___closed__1,
                );
                v___x_2912_ = lean_int_dec_eq(v___x_2906_, v___x_2907_);
                crate::leanh::lean_dec(v___x_2906_);
                if v___x_2912_ == 0 {
                    v___y_2899_ = v___x_2912_;
                    state = 1;
                    continue;
                } else {
                    v___x_2913_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_format___lam__0___closed__3),
                        core::ptr::addr_of_mut!(
                            l_Std_Time_PlainDate_format___lam__0___closed__3_once
                        ),
                        _init_l_Std_Time_PlainDate_format___lam__0___closed__3,
                    );
                    v___x_2914_ = lean_int_mod(v___y_2895_, v___x_2913_);
                    v___x_2915_ = lean_int_dec_eq(v___x_2914_, v___x_2907_);
                    crate::leanh::lean_dec(v___x_2914_);
                    if v___x_2915_ == 0 {
                        if v___x_2912_ == 0 {
                            state = 2;
                            continue;
                        } else {
                            v___y_2899_ = v___x_2912_;
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
                v___x_2900_ = l_Std_Time_Month_Ordinal_days(v___y_2899_, v___y_2896_);
                v___x_2901_ = lean_int_dec_le(v___y_2897_, v___x_2900_);
                crate::leanh::lean_dec(v___x_2900_);
                if v___x_2901_ == 0 {
                    crate::leanh::lean_dec(v___y_2897_);
                    crate::leanh::lean_dec(v___y_2896_);
                    crate::leanh::lean_dec(v___y_2895_);
                    v___x_2902_ = crate::leanh::lean_box(0);
                    return v___x_2902_;
                } else {
                    v___x_2903_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2903_, 0, v___y_2895_);
                    crate::leanh::lean_ctor_set(v___x_2903_, 1, v___y_2896_);
                    crate::leanh::lean_ctor_set(v___x_2903_, 2, v___y_2897_);
                    v___x_2904_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2904_, 0, v___x_2903_);
                    return v___x_2904_;
                }
            }
            2 => {
                v___x_2909_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_format___lam__0___closed__2),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_format___lam__0___closed__2_once),
                    _init_l_Std_Time_PlainDate_format___lam__0___closed__2,
                );
                v___x_2910_ = lean_int_mod(v___y_2895_, v___x_2909_);
                v___x_2911_ = lean_int_dec_eq(v___x_2910_, v___x_2907_);
                crate::leanh::lean_dec(v___x_2910_);
                v___y_2899_ = v___x_2911_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainDate_fromSQLDateString(
    mut v_input_2917_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2918_ = l_Std_Time_PlainDate_fromSQLDateString___closed__0;
    v___x_2919_ = l_Std_Time_Formats_sqlDate;
    v___x_2920_ =
        l_Std_Time_GenericFormat_parseBuilder___redArg(v___x_2919_, v___f_2918_, v_input_2917_);
    return v___x_2920_;
}
pub unsafe fn l_Std_Time_PlainDate_toSQLDateString(
    mut v_input_2921_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_year_2922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_month_2923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_day_2924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6__overap_2926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_year_2922_ = crate::leanh::lean_ctor_get(v_input_2921_, 0);
    crate::leanh::lean_inc(v_year_2922_);
    v_month_2923_ = crate::leanh::lean_ctor_get(v_input_2921_, 1);
    crate::leanh::lean_inc(v_month_2923_);
    v_day_2924_ = crate::leanh::lean_ctor_get(v_input_2921_, 2);
    crate::leanh::lean_inc(v_day_2924_);
    crate::leanh::lean_dec_ref(v_input_2921_);
    v___x_2925_ = l_Std_Time_Formats_sqlDate;
    v___x_6__overap_2926_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_2925_);
    v___x_2927_ = crate::leanh::lean_apply_3(
        v___x_6__overap_2926_,
        v_year_2922_,
        v_month_2923_,
        v_day_2924_,
    );
    return v___x_2927_;
}
pub unsafe fn l_Std_Time_PlainDate_fromLeanDateString(
    mut v_input_2928_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2929_ = l_Std_Time_PlainDate_fromSQLDateString___closed__0;
    v___x_2930_ = l_Std_Time_Formats_leanDate;
    v___x_2931_ =
        l_Std_Time_GenericFormat_parseBuilder___redArg(v___x_2930_, v___f_2929_, v_input_2928_);
    return v___x_2931_;
}
pub unsafe fn l_Std_Time_PlainDate_toLeanDateString(
    mut v_input_2932_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_year_2933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_month_2934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_day_2935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6__overap_2937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_year_2933_ = crate::leanh::lean_ctor_get(v_input_2932_, 0);
    crate::leanh::lean_inc(v_year_2933_);
    v_month_2934_ = crate::leanh::lean_ctor_get(v_input_2932_, 1);
    crate::leanh::lean_inc(v_month_2934_);
    v_day_2935_ = crate::leanh::lean_ctor_get(v_input_2932_, 2);
    crate::leanh::lean_inc(v_day_2935_);
    crate::leanh::lean_dec_ref(v_input_2932_);
    v___x_2936_ = l_Std_Time_Formats_leanDate;
    v___x_6__overap_2937_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_2936_);
    v___x_2938_ = crate::leanh::lean_apply_3(
        v___x_6__overap_2937_,
        v_year_2933_,
        v_month_2934_,
        v_day_2935_,
    );
    return v___x_2938_;
}
pub unsafe fn l_Std_Time_PlainDate_parse(
    mut v_input_2939_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_input_2939_);
    v___x_2940_ = l_Std_Time_PlainDate_fromAmericanDateString(v_input_2939_);
    if crate::leanh::lean_obj_tag(v___x_2940_) == 0 {
        let mut v___x_2941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref_known(v___x_2940_, 1);
        v___x_2941_ = l_Std_Time_PlainDate_fromSQLDateString(v_input_2939_);
        return v___x_2941_;
    } else {
        crate::leanh::lean_dec_ref(v_input_2939_);
        return v___x_2940_;
    }
}
pub unsafe fn l_Std_Time_PlainDate_instRepr___lam__0(
    mut v_data_2950_: *mut crate::leanh::LeanObject,
    mut v___y_2951_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2952_ = l_Std_Time_PlainDate_instRepr___lam__0___closed__1;
    v___x_2953_ = l_Std_Time_PlainDate_toLeanDateString(v_data_2950_);
    v___x_2954_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2954_, 0, v___x_2953_);
    v___x_2955_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2955_, 0, v___x_2952_);
    crate::leanh::lean_ctor_set(v___x_2955_, 1, v___x_2954_);
    v___x_2956_ = l_Std_Time_PlainDate_instRepr___lam__0___closed__3;
    v___x_2957_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2957_, 0, v___x_2955_);
    crate::leanh::lean_ctor_set(v___x_2957_, 1, v___x_2956_);
    v___x_2958_ = l_Repr_addAppParen(v___x_2957_, v___y_2951_);
    return v___x_2958_;
}
pub unsafe fn l_Std_Time_PlainDate_instRepr___lam__0___boxed(
    mut v_data_2959_: *mut crate::leanh::LeanObject,
    mut v___y_2960_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2961_ = l_Std_Time_PlainDate_instRepr___lam__0(v_data_2959_, v___y_2960_);
    crate::leanh::lean_dec(v___y_2960_);
    return v_res_2961_;
}
pub unsafe fn _init_l_Std_Time_PlainTime_format___lam__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2964_ = crate::leanh::lean_unsigned_to_nat(12);
    v___x_2965_ = lean_nat_to_int(v___x_2964_);
    return v___x_2965_;
}
pub unsafe fn l_Std_Time_PlainTime_format___lam__0(
    mut v_time_2966_: *mut crate::leanh::LeanObject,
    mut v_x_2967_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2970_: u8 = 0;
    let mut v_hour_2971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2975_: u8 = 0;
    let mut v_unused_2976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2979_: u8 = 0;
    let mut v_hour_2980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2985_: u8 = 0;
    let mut v_unused_2986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2989_: u8 = 0;
    let mut v_minute_2990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2994_: u8 = 0;
    let mut v_unused_2995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2998_: u8 = 0;
    let mut v_nanosecond_2999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3003_: u8 = 0;
    let mut v_unused_3004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3007_: u8 = 0;
    let mut v_second_3008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3012_: u8 = 0;
    let mut v_unused_3013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hour_3014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: u8 = 0;
    let mut v___x_3016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3020_: u8 = 0;
    let mut v_hour_3021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3026_: u8 = 0;
    let mut v_unused_3027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3030_: u8 = 0;
    let mut v_hour_3031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3037_: u8 = 0;
    let mut v_unused_3038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3041_: u8 = 0;
    let mut v_nanosecond_3042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3046_: u8 = 0;
    let mut v_unused_3047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3050_: u8 = 0;
    let mut v___x_3051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3055_: u8 = 0;
    let mut v_unused_3056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3059_: u8 = 0;
    let mut v___x_3060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3064_: u8 = 0;
    let mut v_unused_3065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_2967_) {
                17 => {
                    v_isSharedCheck_2975_ = (!crate::leanh::lean_is_exclusive(v_x_2967_)) as u8;
                    if v_isSharedCheck_2975_ == 0 {
                        v_unused_2976_ = crate::leanh::lean_ctor_get(v_x_2967_, 0);
                        crate::leanh::lean_dec(v_unused_2976_);
                        v___x_2969_ = v_x_2967_;
                        v_isShared_2970_ = v_isSharedCheck_2975_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_x_2967_);
                        v___x_2969_ = crate::leanh::lean_box(0);
                        v_isShared_2970_ = v_isSharedCheck_2975_;
                        state = 1;
                        continue;
                    }
                }
                16 => {
                    v_isSharedCheck_2985_ = (!crate::leanh::lean_is_exclusive(v_x_2967_)) as u8;
                    if v_isSharedCheck_2985_ == 0 {
                        v_unused_2986_ = crate::leanh::lean_ctor_get(v_x_2967_, 0);
                        crate::leanh::lean_dec(v_unused_2986_);
                        v___x_2978_ = v_x_2967_;
                        v_isShared_2979_ = v_isSharedCheck_2985_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_x_2967_);
                        v___x_2978_ = crate::leanh::lean_box(0);
                        v_isShared_2979_ = v_isSharedCheck_2985_;
                        state = 3;
                        continue;
                    }
                }
                18 => {
                    v_isSharedCheck_2994_ = (!crate::leanh::lean_is_exclusive(v_x_2967_)) as u8;
                    if v_isSharedCheck_2994_ == 0 {
                        v_unused_2995_ = crate::leanh::lean_ctor_get(v_x_2967_, 0);
                        crate::leanh::lean_dec(v_unused_2995_);
                        v___x_2988_ = v_x_2967_;
                        v_isShared_2989_ = v_isSharedCheck_2994_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_x_2967_);
                        v___x_2988_ = crate::leanh::lean_box(0);
                        v_isShared_2989_ = v_isSharedCheck_2994_;
                        state = 5;
                        continue;
                    }
                }
                22 => {
                    v_isSharedCheck_3003_ = (!crate::leanh::lean_is_exclusive(v_x_2967_)) as u8;
                    if v_isSharedCheck_3003_ == 0 {
                        v_unused_3004_ = crate::leanh::lean_ctor_get(v_x_2967_, 0);
                        crate::leanh::lean_dec(v_unused_3004_);
                        v___x_2997_ = v_x_2967_;
                        v_isShared_2998_ = v_isSharedCheck_3003_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_x_2967_);
                        v___x_2997_ = crate::leanh::lean_box(0);
                        v_isShared_2998_ = v_isSharedCheck_3003_;
                        state = 7;
                        continue;
                    }
                }
                19 => {
                    v_isSharedCheck_3012_ = (!crate::leanh::lean_is_exclusive(v_x_2967_)) as u8;
                    if v_isSharedCheck_3012_ == 0 {
                        v_unused_3013_ = crate::leanh::lean_ctor_get(v_x_2967_, 0);
                        crate::leanh::lean_dec(v_unused_3013_);
                        v___x_3006_ = v_x_2967_;
                        v_isShared_3007_ = v_isSharedCheck_3012_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_x_2967_);
                        v___x_3006_ = crate::leanh::lean_box(0);
                        v_isShared_3007_ = v_isSharedCheck_3012_;
                        state = 9;
                        continue;
                    }
                }
                13 => {
                    crate::leanh::lean_dec_ref_known(v_x_2967_, 0);
                    v_hour_3014_ = crate::leanh::lean_ctor_get(v_time_2966_, 0);
                    v___x_3015_ = l_Std_Time_HourMarker_ofOrdinal(v_hour_3014_);
                    v___x_3016_ = crate::leanh::lean_box((v___x_3015_) as usize);
                    v___x_3017_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3017_, 0, v___x_3016_);
                    return v___x_3017_;
                }
                14 => {
                    v_isSharedCheck_3026_ = (!crate::leanh::lean_is_exclusive(v_x_2967_)) as u8;
                    if v_isSharedCheck_3026_ == 0 {
                        v_unused_3027_ = crate::leanh::lean_ctor_get(v_x_2967_, 0);
                        crate::leanh::lean_dec(v_unused_3027_);
                        v___x_3019_ = v_x_2967_;
                        v_isShared_3020_ = v_isSharedCheck_3026_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_x_2967_);
                        v___x_3019_ = crate::leanh::lean_box(0);
                        v_isShared_3020_ = v_isSharedCheck_3026_;
                        state = 11;
                        continue;
                    }
                }
                15 => {
                    v_isSharedCheck_3037_ = (!crate::leanh::lean_is_exclusive(v_x_2967_)) as u8;
                    if v_isSharedCheck_3037_ == 0 {
                        v_unused_3038_ = crate::leanh::lean_ctor_get(v_x_2967_, 0);
                        crate::leanh::lean_dec(v_unused_3038_);
                        v___x_3029_ = v_x_2967_;
                        v_isShared_3030_ = v_isSharedCheck_3037_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_x_2967_);
                        v___x_3029_ = crate::leanh::lean_box(0);
                        v_isShared_3030_ = v_isSharedCheck_3037_;
                        state = 13;
                        continue;
                    }
                }
                20 => {
                    v_isSharedCheck_3046_ = (!crate::leanh::lean_is_exclusive(v_x_2967_)) as u8;
                    if v_isSharedCheck_3046_ == 0 {
                        v_unused_3047_ = crate::leanh::lean_ctor_get(v_x_2967_, 0);
                        crate::leanh::lean_dec(v_unused_3047_);
                        v___x_3040_ = v_x_2967_;
                        v_isShared_3041_ = v_isSharedCheck_3046_;
                        state = 15;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_x_2967_);
                        v___x_3040_ = crate::leanh::lean_box(0);
                        v_isShared_3041_ = v_isSharedCheck_3046_;
                        state = 15;
                        continue;
                    }
                }
                21 => {
                    v_isSharedCheck_3055_ = (!crate::leanh::lean_is_exclusive(v_x_2967_)) as u8;
                    if v_isSharedCheck_3055_ == 0 {
                        v_unused_3056_ = crate::leanh::lean_ctor_get(v_x_2967_, 0);
                        crate::leanh::lean_dec(v_unused_3056_);
                        v___x_3049_ = v_x_2967_;
                        v_isShared_3050_ = v_isSharedCheck_3055_;
                        state = 17;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_x_2967_);
                        v___x_3049_ = crate::leanh::lean_box(0);
                        v_isShared_3050_ = v_isSharedCheck_3055_;
                        state = 17;
                        continue;
                    }
                }
                23 => {
                    v_isSharedCheck_3064_ = (!crate::leanh::lean_is_exclusive(v_x_2967_)) as u8;
                    if v_isSharedCheck_3064_ == 0 {
                        v_unused_3065_ = crate::leanh::lean_ctor_get(v_x_2967_, 0);
                        crate::leanh::lean_dec(v_unused_3065_);
                        v___x_3058_ = v_x_2967_;
                        v_isShared_3059_ = v_isSharedCheck_3064_;
                        state = 19;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_x_2967_);
                        v___x_3058_ = crate::leanh::lean_box(0);
                        v_isShared_3059_ = v_isSharedCheck_3064_;
                        state = 19;
                        continue;
                    }
                }
                _ => {
                    crate::leanh::lean_dec(v_x_2967_);
                    v___x_3066_ = crate::leanh::lean_box(0);
                    return v___x_3066_;
                }
            },
            1 => {
                v_hour_2971_ = crate::leanh::lean_ctor_get(v_time_2966_, 0);
                crate::leanh::lean_inc(v_hour_2971_);
                if v_isShared_2970_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2969_, 1);
                    crate::leanh::lean_ctor_set(v___x_2969_, 0, v_hour_2971_);
                    v___x_2973_ = v___x_2969_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2974_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2974_, 0, v_hour_2971_);
                    v___x_2973_ = v_reuseFailAlloc_2974_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2973_;
            }
            3 => {
                v_hour_2980_ = crate::leanh::lean_ctor_get(v_time_2966_, 0);
                v___x_2981_ = l_Std_Time_Hour_Ordinal_shiftTo1BasedHour(v_hour_2980_);
                if v_isShared_2979_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2978_, 1);
                    crate::leanh::lean_ctor_set(v___x_2978_, 0, v___x_2981_);
                    v___x_2983_ = v___x_2978_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2984_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2984_, 0, v___x_2981_);
                    v___x_2983_ = v_reuseFailAlloc_2984_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2983_;
            }
            5 => {
                v_minute_2990_ = crate::leanh::lean_ctor_get(v_time_2966_, 1);
                crate::leanh::lean_inc(v_minute_2990_);
                if v_isShared_2989_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2988_, 1);
                    crate::leanh::lean_ctor_set(v___x_2988_, 0, v_minute_2990_);
                    v___x_2992_ = v___x_2988_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2993_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2993_, 0, v_minute_2990_);
                    v___x_2992_ = v_reuseFailAlloc_2993_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2992_;
            }
            7 => {
                v_nanosecond_2999_ = crate::leanh::lean_ctor_get(v_time_2966_, 3);
                crate::leanh::lean_inc(v_nanosecond_2999_);
                if v_isShared_2998_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2997_, 1);
                    crate::leanh::lean_ctor_set(v___x_2997_, 0, v_nanosecond_2999_);
                    v___x_3001_ = v___x_2997_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3002_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3002_, 0, v_nanosecond_2999_);
                    v___x_3001_ = v_reuseFailAlloc_3002_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3001_;
            }
            9 => {
                v_second_3008_ = crate::leanh::lean_ctor_get(v_time_2966_, 2);
                crate::leanh::lean_inc(v_second_3008_);
                if v_isShared_3007_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3006_, 1);
                    crate::leanh::lean_ctor_set(v___x_3006_, 0, v_second_3008_);
                    v___x_3010_ = v___x_3006_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3011_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3011_, 0, v_second_3008_);
                    v___x_3010_ = v_reuseFailAlloc_3011_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3010_;
            }
            11 => {
                v_hour_3021_ = crate::leanh::lean_ctor_get(v_time_2966_, 0);
                v___x_3022_ = l_Std_Time_Hour_Ordinal_toRelative(v_hour_3021_);
                if v_isShared_3020_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3019_, 1);
                    crate::leanh::lean_ctor_set(v___x_3019_, 0, v___x_3022_);
                    v___x_3024_ = v___x_3019_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3025_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3025_, 0, v___x_3022_);
                    v___x_3024_ = v_reuseFailAlloc_3025_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3024_;
            }
            13 => {
                v_hour_3031_ = crate::leanh::lean_ctor_get(v_time_2966_, 0);
                v___x_3032_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainTime_format___lam__0___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainTime_format___lam__0___closed__0_once),
                    _init_l_Std_Time_PlainTime_format___lam__0___closed__0,
                );
                v___x_3033_ = lean_int_emod(v_hour_3031_, v___x_3032_);
                if v_isShared_3030_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3029_, 1);
                    crate::leanh::lean_ctor_set(v___x_3029_, 0, v___x_3033_);
                    v___x_3035_ = v___x_3029_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3036_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3036_, 0, v___x_3033_);
                    v___x_3035_ = v_reuseFailAlloc_3036_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_3035_;
            }
            15 => {
                v_nanosecond_3042_ = crate::leanh::lean_ctor_get(v_time_2966_, 3);
                crate::leanh::lean_inc(v_nanosecond_3042_);
                if v_isShared_3041_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3040_, 1);
                    crate::leanh::lean_ctor_set(v___x_3040_, 0, v_nanosecond_3042_);
                    v___x_3044_ = v___x_3040_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3045_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3045_, 0, v_nanosecond_3042_);
                    v___x_3044_ = v_reuseFailAlloc_3045_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_3044_;
            }
            17 => {
                v___x_3051_ = l_Std_Time_PlainTime_toMilliseconds(v_time_2966_);
                if v_isShared_3050_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3049_, 1);
                    crate::leanh::lean_ctor_set(v___x_3049_, 0, v___x_3051_);
                    v___x_3053_ = v___x_3049_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3054_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3054_, 0, v___x_3051_);
                    v___x_3053_ = v_reuseFailAlloc_3054_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_3053_;
            }
            19 => {
                v___x_3060_ = l_Std_Time_PlainTime_toNanoseconds(v_time_2966_);
                if v_isShared_3059_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3058_, 1);
                    crate::leanh::lean_ctor_set(v___x_3058_, 0, v___x_3060_);
                    v___x_3062_ = v___x_3058_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3063_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3063_, 0, v___x_3060_);
                    v___x_3062_ = v_reuseFailAlloc_3063_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_3062_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainTime_format___lam__0___boxed(
    mut v_time_3067_: *mut crate::leanh::LeanObject,
    mut v_x_3068_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3069_ = l_Std_Time_PlainTime_format___lam__0(v_time_3067_, v_x_3068_);
    crate::leanh::lean_dec_ref(v_time_3067_);
    return v_res_3069_;
}
pub unsafe fn l_Std_Time_PlainTime_format(
    mut v_time_3070_: *mut crate::leanh::LeanObject,
    mut v_format_3071_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_format_3073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3072_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0_once),
        _init_l_Std_Time_Formats_iso8601___closed__0,
    );
    v_format_3073_ = l_Std_Time_GenericFormat_spec___redArg(v_format_3071_, v___x_3072_);
    if crate::leanh::lean_obj_tag(v_format_3073_) == 0 {
        let mut v_a_3074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_time_3070_);
        v_a_3074_ = crate::leanh::lean_ctor_get(v_format_3073_, 0);
        crate::leanh::lean_inc(v_a_3074_);
        crate::leanh::lean_dec_ref_known(v_format_3073_, 1);
        v___x_3075_ = l_Std_Time_PlainDate_format___closed__0;
        v___x_3076_ = lean_string_append(v___x_3075_, v_a_3074_);
        crate::leanh::lean_dec(v_a_3074_);
        return v___x_3076_;
    } else {
        let mut v_a_3077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_res_3079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_3077_ = crate::leanh::lean_ctor_get(v_format_3073_, 0);
        crate::leanh::lean_inc(v_a_3077_);
        crate::leanh::lean_dec_ref_known(v_format_3073_, 1);
        v___f_3078_ = crate::leanh::lean_alloc_closure(
            l_Std_Time_PlainTime_format___lam__0___boxed as *mut core::ffi::c_void,
            2,
            1,
        );
        crate::leanh::lean_closure_set(v___f_3078_, 0, v_time_3070_);
        v_res_3079_ = l_Std_Time_GenericFormat_formatGeneric___redArg(v_a_3077_, v___f_3078_);
        if crate::leanh::lean_obj_tag(v_res_3079_) == 0 {
            let mut v___x_3080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3080_ = l_Std_Time_PlainDate_format___closed__1;
            return v___x_3080_;
        } else {
            let mut v_val_3081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_val_3081_ = crate::leanh::lean_ctor_get(v_res_3079_, 0);
            crate::leanh::lean_inc(v_val_3081_);
            crate::leanh::lean_dec_ref_known(v_res_3079_, 1);
            return v_val_3081_;
        }
    }
}
pub unsafe fn _init_l_Std_Time_PlainTime_fromTime24Hour___lam__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3082_ = crate::leanh::lean_unsigned_to_nat(1000000000);
    v___x_3083_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3084_ = lean_nat_mod(v___x_3083_, v___x_3082_);
    return v___x_3084_;
}
pub unsafe fn _init_l_Std_Time_PlainTime_fromTime24Hour___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3085_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_fromTime24Hour___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_fromTime24Hour___lam__0___closed__0_once),
        _init_l_Std_Time_PlainTime_fromTime24Hour___lam__0___closed__0,
    );
    v___x_3086_ = lean_nat_to_int(v___x_3085_);
    return v___x_3086_;
}
pub unsafe fn l_Std_Time_PlainTime_fromTime24Hour___lam__0(
    mut v_h_3087_: *mut crate::leanh::LeanObject,
    mut v_m_3088_: *mut crate::leanh::LeanObject,
    mut v_s_3089_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3090_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_fromTime24Hour___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_fromTime24Hour___lam__0___closed__1_once),
        _init_l_Std_Time_PlainTime_fromTime24Hour___lam__0___closed__1,
    );
    v___x_3091_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3091_, 0, v_h_3087_);
    crate::leanh::lean_ctor_set(v___x_3091_, 1, v_m_3088_);
    crate::leanh::lean_ctor_set(v___x_3091_, 2, v_s_3089_);
    crate::leanh::lean_ctor_set(v___x_3091_, 3, v___x_3090_);
    v___x_3092_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3092_, 0, v___x_3091_);
    return v___x_3092_;
}
pub unsafe fn l_Std_Time_PlainTime_fromTime24Hour(
    mut v_input_3094_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3095_ = l_Std_Time_PlainTime_fromTime24Hour___closed__0;
    v___x_3096_ = l_Std_Time_Formats_time24Hour;
    v___x_3097_ =
        l_Std_Time_GenericFormat_parseBuilder___redArg(v___x_3096_, v___f_3095_, v_input_3094_);
    return v___x_3097_;
}
pub unsafe fn l_Std_Time_PlainTime_toTime24Hour(
    mut v_input_3098_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_hour_3099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_minute_3100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6__overap_3103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_hour_3099_ = crate::leanh::lean_ctor_get(v_input_3098_, 0);
    crate::leanh::lean_inc(v_hour_3099_);
    v_minute_3100_ = crate::leanh::lean_ctor_get(v_input_3098_, 1);
    crate::leanh::lean_inc(v_minute_3100_);
    v_second_3101_ = crate::leanh::lean_ctor_get(v_input_3098_, 2);
    crate::leanh::lean_inc(v_second_3101_);
    crate::leanh::lean_dec_ref(v_input_3098_);
    v___x_3102_ = l_Std_Time_Formats_time24Hour;
    v___x_6__overap_3103_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_3102_);
    v___x_3104_ = crate::leanh::lean_apply_3(
        v___x_6__overap_3103_,
        v_hour_3099_,
        v_minute_3100_,
        v_second_3101_,
    );
    return v___x_3104_;
}
pub unsafe fn l_Std_Time_PlainTime_fromLeanTime24Hour___lam__0(
    mut v_h_3105_: *mut crate::leanh::LeanObject,
    mut v_m_3106_: *mut crate::leanh::LeanObject,
    mut v_s_3107_: *mut crate::leanh::LeanObject,
    mut v_n_3108_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3109_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3109_, 0, v_h_3105_);
    crate::leanh::lean_ctor_set(v___x_3109_, 1, v_m_3106_);
    crate::leanh::lean_ctor_set(v___x_3109_, 2, v_s_3107_);
    crate::leanh::lean_ctor_set(v___x_3109_, 3, v_n_3108_);
    v___x_3110_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3110_, 0, v___x_3109_);
    return v___x_3110_;
}
pub unsafe fn l_Std_Time_PlainTime_fromLeanTime24Hour(
    mut v_input_3112_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3113_ = l_Std_Time_PlainTime_fromLeanTime24Hour___closed__0;
    v___x_3114_ = l_Std_Time_Formats_leanTime24Hour;
    crate::leanh::lean_inc_ref(v_input_3112_);
    v___x_3115_ =
        l_Std_Time_GenericFormat_parseBuilder___redArg(v___x_3114_, v___f_3113_, v_input_3112_);
    if crate::leanh::lean_obj_tag(v___x_3115_) == 0 {
        let mut v___f_3116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref_known(v___x_3115_, 1);
        v___f_3116_ = l_Std_Time_PlainTime_fromTime24Hour___closed__0;
        v___x_3117_ = l_Std_Time_Formats_leanTime24HourNoNanos;
        v___x_3118_ =
            l_Std_Time_GenericFormat_parseBuilder___redArg(v___x_3117_, v___f_3116_, v_input_3112_);
        return v___x_3118_;
    } else {
        crate::leanh::lean_dec_ref(v_input_3112_);
        return v___x_3115_;
    }
}
pub unsafe fn l_Std_Time_PlainTime_toLeanTime24Hour(
    mut v_input_3119_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_hour_3120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_minute_3121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_3123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7__overap_3125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_hour_3120_ = crate::leanh::lean_ctor_get(v_input_3119_, 0);
    crate::leanh::lean_inc(v_hour_3120_);
    v_minute_3121_ = crate::leanh::lean_ctor_get(v_input_3119_, 1);
    crate::leanh::lean_inc(v_minute_3121_);
    v_second_3122_ = crate::leanh::lean_ctor_get(v_input_3119_, 2);
    crate::leanh::lean_inc(v_second_3122_);
    v_nanosecond_3123_ = crate::leanh::lean_ctor_get(v_input_3119_, 3);
    crate::leanh::lean_inc(v_nanosecond_3123_);
    crate::leanh::lean_dec_ref(v_input_3119_);
    v___x_3124_ = l_Std_Time_Formats_leanTime24Hour;
    v___x_7__overap_3125_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_3124_);
    v___x_3126_ = crate::leanh::lean_apply_4(
        v___x_7__overap_3125_,
        v_hour_3120_,
        v_minute_3121_,
        v_second_3122_,
        v_nanosecond_3123_,
    );
    return v___x_3126_;
}
pub unsafe fn _init_l_Std_Time_PlainTime_fromTime12Hour___lam__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3127_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_3128_ = lean_nat_to_int(v___x_3127_);
    return v___x_3128_;
}
pub unsafe fn l_Std_Time_PlainTime_fromTime12Hour___lam__0(
    mut v_h_3129_: *mut crate::leanh::LeanObject,
    mut v_m_3130_: *mut crate::leanh::LeanObject,
    mut v_s_3131_: *mut crate::leanh::LeanObject,
    mut v_a_3132_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: u8 = 0;
    v___x_3133_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_fromTime12Hour___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_fromTime12Hour___lam__0___closed__0_once),
        _init_l_Std_Time_PlainTime_fromTime12Hour___lam__0___closed__0,
    );
    v___x_3134_ = lean_int_dec_le(v___x_3133_, v_h_3129_);
    if v___x_3134_ == 0 {
        let mut v___x_3135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_s_3131_);
        crate::leanh::lean_dec(v_m_3130_);
        v___x_3135_ = crate::leanh::lean_box(0);
        return v___x_3135_;
    } else {
        let mut v___x_3136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3137_: u8 = 0;
        v___x_3136_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_Time_PlainTime_format___lam__0___closed__0),
            core::ptr::addr_of_mut!(l_Std_Time_PlainTime_format___lam__0___closed__0_once),
            _init_l_Std_Time_PlainTime_format___lam__0___closed__0,
        );
        v___x_3137_ = lean_int_dec_le(v_h_3129_, v___x_3136_);
        if v___x_3137_ == 0 {
            let mut v___x_3138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_s_3131_);
            crate::leanh::lean_dec(v_m_3130_);
            v___x_3138_ = crate::leanh::lean_box(0);
            return v___x_3138_;
        } else {
            let mut v___x_3139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3139_ = l_Std_Time_HourMarker_toAbsolute(v_a_3132_, v_h_3129_);
            v___x_3140_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Std_Time_PlainTime_fromTime24Hour___lam__0___closed__1),
                core::ptr::addr_of_mut!(
                    l_Std_Time_PlainTime_fromTime24Hour___lam__0___closed__1_once
                ),
                _init_l_Std_Time_PlainTime_fromTime24Hour___lam__0___closed__1,
            );
            v___x_3141_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_3141_, 0, v___x_3139_);
            crate::leanh::lean_ctor_set(v___x_3141_, 1, v_m_3130_);
            crate::leanh::lean_ctor_set(v___x_3141_, 2, v_s_3131_);
            crate::leanh::lean_ctor_set(v___x_3141_, 3, v___x_3140_);
            v___x_3142_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_3142_, 0, v___x_3141_);
            return v___x_3142_;
        }
    }
}
pub unsafe fn l_Std_Time_PlainTime_fromTime12Hour___lam__0___boxed(
    mut v_h_3143_: *mut crate::leanh::LeanObject,
    mut v_m_3144_: *mut crate::leanh::LeanObject,
    mut v_s_3145_: *mut crate::leanh::LeanObject,
    mut v_a_3146_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_3147_: u8 = 0;
    let mut v_res_3148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_3147_ = (crate::leanh::lean_unbox(v_a_3146_) as u8);
    v_res_3148_ = l_Std_Time_PlainTime_fromTime12Hour___lam__0(
        v_h_3143_,
        v_m_3144_,
        v_s_3145_,
        v_a_boxed_3147_,
    );
    crate::leanh::lean_dec(v_h_3143_);
    return v_res_3148_;
}
pub unsafe fn l_Std_Time_PlainTime_fromTime12Hour(
    mut v_input_3150_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_builder_3151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_builder_3151_ = l_Std_Time_PlainTime_fromTime12Hour___closed__0;
    v___x_3152_ = l_Std_Time_Formats_time12Hour;
    v___x_3153_ =
        l_Std_Time_GenericFormat_parseBuilder___redArg(v___x_3152_, v_builder_3151_, v_input_3150_);
    return v___x_3153_;
}
pub unsafe fn l_Std_Time_PlainTime_toTime12Hour(
    mut v_input_3154_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_hour_3155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_minute_3156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3163_: u8 = 0;
    v_hour_3155_ = crate::leanh::lean_ctor_get(v_input_3154_, 0);
    crate::leanh::lean_inc(v_hour_3155_);
    v_minute_3156_ = crate::leanh::lean_ctor_get(v_input_3154_, 1);
    crate::leanh::lean_inc(v_minute_3156_);
    v_second_3157_ = crate::leanh::lean_ctor_get(v_input_3154_, 2);
    crate::leanh::lean_inc(v_second_3157_);
    crate::leanh::lean_dec_ref(v_input_3154_);
    v___x_3158_ = l_Std_Time_Formats_time12Hour;
    v___x_3159_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_format___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_format___lam__0___closed__0_once),
        _init_l_Std_Time_PlainTime_format___lam__0___closed__0,
    );
    v___x_3160_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_fromTime12Hour___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_fromTime12Hour___lam__0___closed__0_once),
        _init_l_Std_Time_PlainTime_fromTime12Hour___lam__0___closed__0,
    );
    v___x_3161_ = lean_int_emod(v_hour_3155_, v___x_3159_);
    v___x_3162_ = lean_int_add(v___x_3161_, v___x_3160_);
    crate::leanh::lean_dec(v___x_3161_);
    v___x_3163_ = lean_int_dec_le(v___x_3159_, v_hour_3155_);
    crate::leanh::lean_dec(v_hour_3155_);
    if v___x_3163_ == 0 {
        let mut v___x_3164_: u8 = 0;
        let mut v___x_56__overap_3165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3164_ = 0;
        v___x_56__overap_3165_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_3158_);
        v___x_3166_ = crate::leanh::lean_box((v___x_3164_) as usize);
        v___x_3167_ = crate::leanh::lean_apply_4(
            v___x_56__overap_3165_,
            v___x_3162_,
            v_minute_3156_,
            v_second_3157_,
            v___x_3166_,
        );
        return v___x_3167_;
    } else {
        let mut v___x_3168_: u8 = 0;
        let mut v___x_57__overap_3169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3168_ = 1;
        v___x_57__overap_3169_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_3158_);
        v___x_3170_ = crate::leanh::lean_box((v___x_3168_) as usize);
        v___x_3171_ = crate::leanh::lean_apply_4(
            v___x_57__overap_3169_,
            v___x_3162_,
            v_minute_3156_,
            v_second_3157_,
            v___x_3170_,
        );
        return v___x_3171_;
    }
}
pub unsafe fn l_Std_Time_PlainTime_parse(
    mut v_input_3172_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_input_3172_);
    v___x_3173_ = l_Std_Time_PlainTime_fromTime12Hour(v_input_3172_);
    if crate::leanh::lean_obj_tag(v___x_3173_) == 0 {
        let mut v___x_3174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref_known(v___x_3173_, 1);
        v___x_3174_ = l_Std_Time_PlainTime_fromTime24Hour(v_input_3172_);
        return v___x_3174_;
    } else {
        crate::leanh::lean_dec_ref(v_input_3172_);
        return v___x_3173_;
    }
}
pub unsafe fn l_Std_Time_PlainTime_instRepr___lam__0(
    mut v_data_3180_: *mut crate::leanh::LeanObject,
    mut v___y_3181_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3182_ = l_Std_Time_PlainTime_instRepr___lam__0___closed__1;
    v___x_3183_ = l_Std_Time_PlainTime_toLeanTime24Hour(v_data_3180_);
    v___x_3184_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3184_, 0, v___x_3183_);
    v___x_3185_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3185_, 0, v___x_3182_);
    crate::leanh::lean_ctor_set(v___x_3185_, 1, v___x_3184_);
    v___x_3186_ = l_Std_Time_PlainDate_instRepr___lam__0___closed__3;
    v___x_3187_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3187_, 0, v___x_3185_);
    crate::leanh::lean_ctor_set(v___x_3187_, 1, v___x_3186_);
    v___x_3188_ = l_Repr_addAppParen(v___x_3187_, v___y_3181_);
    return v___x_3188_;
}
pub unsafe fn l_Std_Time_PlainTime_instRepr___lam__0___boxed(
    mut v_data_3189_: *mut crate::leanh::LeanObject,
    mut v___y_3190_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3191_ = l_Std_Time_PlainTime_instRepr___lam__0(v_data_3189_, v___y_3190_);
    crate::leanh::lean_dec(v___y_3190_);
    return v_res_3191_;
}
pub unsafe fn _init_l_Std_Time_ZonedDateTime_format___lam__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3194_ = crate::leanh::lean_unsigned_to_nat(1000000000);
    v___x_3195_ = lean_nat_to_int(v___x_3194_);
    return v___x_3195_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_format___lam__0(
    mut v_timezone_3196_: *mut crate::leanh::LeanObject,
    mut v_timestamp_3197_: *mut crate::leanh::LeanObject,
    mut v_x_3198_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_offset_3199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_3201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_offset_3199_ = crate::leanh::lean_ctor_get(v_timezone_3196_, 0);
    v_second_3200_ = crate::leanh::lean_ctor_get(v_timestamp_3197_, 0);
    v_nano_3201_ = crate::leanh::lean_ctor_get(v_timestamp_3197_, 1);
    v___x_3202_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_format___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_format___lam__0___closed__1_once),
        _init_l_Std_Time_PlainDate_format___lam__0___closed__1,
    );
    v___x_3203_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_format___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_format___lam__0___closed__0_once),
        _init_l_Std_Time_ZonedDateTime_format___lam__0___closed__0,
    );
    v___x_3204_ = lean_int_mul(v_second_3200_, v___x_3203_);
    v___x_3205_ = lean_int_add(v___x_3204_, v_nano_3201_);
    crate::leanh::lean_dec(v___x_3204_);
    v___x_3206_ = lean_int_mul(v_offset_3199_, v___x_3203_);
    v___x_3207_ = lean_int_add(v___x_3206_, v___x_3202_);
    crate::leanh::lean_dec(v___x_3206_);
    v___x_3208_ = lean_int_add(v___x_3205_, v___x_3207_);
    crate::leanh::lean_dec(v___x_3207_);
    crate::leanh::lean_dec(v___x_3205_);
    v___x_3209_ = l_Std_Time_Duration_ofNanoseconds(v___x_3208_);
    crate::leanh::lean_dec(v___x_3208_);
    v___x_3210_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_3209_);
    return v___x_3210_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_format___lam__0___boxed(
    mut v_timezone_3211_: *mut crate::leanh::LeanObject,
    mut v_timestamp_3212_: *mut crate::leanh::LeanObject,
    mut v_x_3213_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3214_ =
        l_Std_Time_ZonedDateTime_format___lam__0(v_timezone_3211_, v_timestamp_3212_, v_x_3213_);
    crate::leanh::lean_dec_ref(v_timestamp_3212_);
    crate::leanh::lean_dec_ref(v_timezone_3211_);
    return v_res_3214_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_format(
    mut v_data_3215_: *mut crate::leanh::LeanObject,
    mut v_format_3216_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_format_3218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3217_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0_once),
        _init_l_Std_Time_Formats_iso8601___closed__0,
    );
    v_format_3218_ = l_Std_Time_GenericFormat_spec___redArg(v_format_3216_, v___x_3217_);
    if crate::leanh::lean_obj_tag(v_format_3218_) == 0 {
        let mut v_a_3219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_data_3215_);
        v_a_3219_ = crate::leanh::lean_ctor_get(v_format_3218_, 0);
        crate::leanh::lean_inc(v_a_3219_);
        crate::leanh::lean_dec_ref_known(v_format_3218_, 1);
        v___x_3220_ = l_Std_Time_PlainDate_format___closed__0;
        v___x_3221_ = lean_string_append(v___x_3220_, v_a_3219_);
        crate::leanh::lean_dec(v_a_3219_);
        return v___x_3221_;
    } else {
        let mut v_a_3222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_timestamp_3223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_timezone_3224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_3222_ = crate::leanh::lean_ctor_get(v_format_3218_, 0);
        crate::leanh::lean_inc(v_a_3222_);
        crate::leanh::lean_dec_ref_known(v_format_3218_, 1);
        v_timestamp_3223_ = crate::leanh::lean_ctor_get(v_data_3215_, 1);
        crate::leanh::lean_inc_ref_n(v_timestamp_3223_, 2);
        v_timezone_3224_ = crate::leanh::lean_ctor_get(v_data_3215_, 3);
        crate::leanh::lean_inc_ref_n(v_timezone_3224_, 2);
        crate::leanh::lean_dec_ref(v_data_3215_);
        v___x_3225_ = crate::leanh::lean_box(1);
        v___f_3226_ = crate::leanh::lean_alloc_closure(
            l_Std_Time_ZonedDateTime_format___lam__0___boxed as *mut core::ffi::c_void,
            3,
            2,
        );
        crate::leanh::lean_closure_set(v___f_3226_, 0, v_timezone_3224_);
        crate::leanh::lean_closure_set(v___f_3226_, 1, v_timestamp_3223_);
        v___x_3227_ = lean_mk_thunk(v___f_3226_);
        v___x_3228_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3228_, 0, v_timestamp_3223_);
        crate::leanh::lean_ctor_set(v___x_3228_, 1, v___x_3227_);
        v___x_3229_ =
            l_Std_Time_GenericFormat_format(v___x_3225_, v_timezone_3224_, v_a_3222_, v___x_3228_);
        crate::leanh::lean_dec_ref(v_timezone_3224_);
        return v___x_3229_;
    }
}
pub unsafe fn l_Std_Time_ZonedDateTime_fromISO8601String(
    mut v_input_3230_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3231_ = crate::leanh::lean_box(1);
    v___x_3232_ = l_Std_Time_Formats_iso8601;
    v___x_3233_ = l_Std_Time_GenericFormat_parse(v___x_3231_, v___x_3232_, v_input_3230_);
    return v___x_3233_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_toISO8601String(
    mut v_date_3234_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_timestamp_3235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_timezone_3236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_timestamp_3235_ = crate::leanh::lean_ctor_get(v_date_3234_, 1);
    crate::leanh::lean_inc_ref_n(v_timestamp_3235_, 2);
    v_timezone_3236_ = crate::leanh::lean_ctor_get(v_date_3234_, 3);
    crate::leanh::lean_inc_ref_n(v_timezone_3236_, 2);
    crate::leanh::lean_dec_ref(v_date_3234_);
    v___x_3237_ = crate::leanh::lean_box(1);
    v___f_3238_ = crate::leanh::lean_alloc_closure(
        l_Std_Time_ZonedDateTime_format___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3238_, 0, v_timezone_3236_);
    crate::leanh::lean_closure_set(v___f_3238_, 1, v_timestamp_3235_);
    v___x_3239_ = l_Std_Time_Formats_iso8601;
    v___x_3240_ = lean_mk_thunk(v___f_3238_);
    v___x_3241_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3241_, 0, v_timestamp_3235_);
    crate::leanh::lean_ctor_set(v___x_3241_, 1, v___x_3240_);
    v___x_3242_ =
        l_Std_Time_GenericFormat_format(v___x_3237_, v_timezone_3236_, v___x_3239_, v___x_3241_);
    crate::leanh::lean_dec_ref(v_timezone_3236_);
    return v___x_3242_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_fromRFC822String(
    mut v_input_3243_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3244_ = crate::leanh::lean_box(1);
    v___x_3245_ = l_Std_Time_Formats_rfc822;
    v___x_3246_ = l_Std_Time_GenericFormat_parse(v___x_3244_, v___x_3245_, v_input_3243_);
    return v___x_3246_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_toRFC822String(
    mut v_date_3247_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_timestamp_3248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_timezone_3249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_timestamp_3248_ = crate::leanh::lean_ctor_get(v_date_3247_, 1);
    crate::leanh::lean_inc_ref_n(v_timestamp_3248_, 2);
    v_timezone_3249_ = crate::leanh::lean_ctor_get(v_date_3247_, 3);
    crate::leanh::lean_inc_ref_n(v_timezone_3249_, 2);
    crate::leanh::lean_dec_ref(v_date_3247_);
    v___x_3250_ = crate::leanh::lean_box(1);
    v___f_3251_ = crate::leanh::lean_alloc_closure(
        l_Std_Time_ZonedDateTime_format___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3251_, 0, v_timezone_3249_);
    crate::leanh::lean_closure_set(v___f_3251_, 1, v_timestamp_3248_);
    v___x_3252_ = l_Std_Time_Formats_rfc822;
    v___x_3253_ = lean_mk_thunk(v___f_3251_);
    v___x_3254_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3254_, 0, v_timestamp_3248_);
    crate::leanh::lean_ctor_set(v___x_3254_, 1, v___x_3253_);
    v___x_3255_ =
        l_Std_Time_GenericFormat_format(v___x_3250_, v_timezone_3249_, v___x_3252_, v___x_3254_);
    crate::leanh::lean_dec_ref(v_timezone_3249_);
    return v___x_3255_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_fromRFC850String(
    mut v_input_3256_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3257_ = crate::leanh::lean_box(1);
    v___x_3258_ = l_Std_Time_Formats_rfc850;
    v___x_3259_ = l_Std_Time_GenericFormat_parse(v___x_3257_, v___x_3258_, v_input_3256_);
    return v___x_3259_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_toRFC850String(
    mut v_date_3260_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_timestamp_3261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_timezone_3262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_timestamp_3261_ = crate::leanh::lean_ctor_get(v_date_3260_, 1);
    crate::leanh::lean_inc_ref_n(v_timestamp_3261_, 2);
    v_timezone_3262_ = crate::leanh::lean_ctor_get(v_date_3260_, 3);
    crate::leanh::lean_inc_ref_n(v_timezone_3262_, 2);
    crate::leanh::lean_dec_ref(v_date_3260_);
    v___x_3263_ = crate::leanh::lean_box(1);
    v___f_3264_ = crate::leanh::lean_alloc_closure(
        l_Std_Time_ZonedDateTime_format___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3264_, 0, v_timezone_3262_);
    crate::leanh::lean_closure_set(v___f_3264_, 1, v_timestamp_3261_);
    v___x_3265_ = l_Std_Time_Formats_rfc850;
    v___x_3266_ = lean_mk_thunk(v___f_3264_);
    v___x_3267_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3267_, 0, v_timestamp_3261_);
    crate::leanh::lean_ctor_set(v___x_3267_, 1, v___x_3266_);
    v___x_3268_ =
        l_Std_Time_GenericFormat_format(v___x_3263_, v_timezone_3262_, v___x_3265_, v___x_3267_);
    crate::leanh::lean_dec_ref(v_timezone_3262_);
    return v___x_3268_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_fromDateTimeWithZoneString(
    mut v_input_3269_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3270_ = crate::leanh::lean_box(1);
    v___x_3271_ = l_Std_Time_Formats_dateTimeWithZone;
    v___x_3272_ = l_Std_Time_GenericFormat_parse(v___x_3270_, v___x_3271_, v_input_3269_);
    return v___x_3272_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_toDateTimeWithZoneString(
    mut v_pdt_3273_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_timestamp_3274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_timezone_3275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_timestamp_3274_ = crate::leanh::lean_ctor_get(v_pdt_3273_, 1);
    crate::leanh::lean_inc_ref_n(v_timestamp_3274_, 2);
    v_timezone_3275_ = crate::leanh::lean_ctor_get(v_pdt_3273_, 3);
    crate::leanh::lean_inc_ref_n(v_timezone_3275_, 2);
    crate::leanh::lean_dec_ref(v_pdt_3273_);
    v___x_3276_ = crate::leanh::lean_box(1);
    v___f_3277_ = crate::leanh::lean_alloc_closure(
        l_Std_Time_ZonedDateTime_format___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_3277_, 0, v_timezone_3275_);
    crate::leanh::lean_closure_set(v___f_3277_, 1, v_timestamp_3274_);
    v___x_3278_ = l_Std_Time_Formats_dateTimeWithZone;
    v___x_3279_ = lean_mk_thunk(v___f_3277_);
    v___x_3280_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3280_, 0, v_timestamp_3274_);
    crate::leanh::lean_ctor_set(v___x_3280_, 1, v___x_3279_);
    v___x_3281_ =
        l_Std_Time_GenericFormat_format(v___x_3276_, v_timezone_3275_, v___x_3278_, v___x_3280_);
    crate::leanh::lean_dec_ref(v_timezone_3275_);
    return v___x_3281_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_fromLeanDateTimeWithZoneString(
    mut v_input_3282_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3283_ = crate::leanh::lean_box(1);
    v___x_3284_ = l_Std_Time_Formats_leanDateTimeWithZone;
    crate::leanh::lean_inc_ref(v_input_3282_);
    v___x_3285_ = l_Std_Time_GenericFormat_parse(v___x_3283_, v___x_3284_, v_input_3282_);
    if crate::leanh::lean_obj_tag(v___x_3285_) == 0 {
        let mut v___x_3286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref_known(v___x_3285_, 1);
        v___x_3286_ = l_Std_Time_Formats_leanDateTimeWithZoneNoNanos;
        v___x_3287_ = l_Std_Time_GenericFormat_parse(v___x_3283_, v___x_3286_, v_input_3282_);
        return v___x_3287_;
    } else {
        crate::leanh::lean_dec_ref(v_input_3282_);
        return v___x_3285_;
    }
}
pub unsafe fn l_Std_Time_ZonedDateTime_fromLeanDateTimeWithIdentifierString(
    mut v_input_3288_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3289_ = crate::leanh::lean_box(1);
    v___x_3290_ = l_Std_Time_Formats_leanDateTimeWithIdentifier;
    crate::leanh::lean_inc_ref(v_input_3288_);
    v___x_3291_ = l_Std_Time_GenericFormat_parse(v___x_3289_, v___x_3290_, v_input_3288_);
    if crate::leanh::lean_obj_tag(v___x_3291_) == 0 {
        let mut v___x_3292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref_known(v___x_3291_, 1);
        v___x_3292_ = l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos;
        v___x_3293_ = l_Std_Time_GenericFormat_parse(v___x_3289_, v___x_3292_, v_input_3288_);
        return v___x_3293_;
    } else {
        crate::leanh::lean_dec_ref(v_input_3288_);
        return v___x_3291_;
    }
}
pub unsafe fn l_Std_Time_ZonedDateTime_toLeanDateTimeWithZoneString(
    mut v_zdt_3294_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_3295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_timezone_3296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_3298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_3299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_year_3300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_month_3301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_day_3302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hour_3303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_minute_3304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_3306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_3307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_14__overap_3309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_date_3295_ = crate::leanh::lean_ctor_get(v_zdt_3294_, 0);
    crate::leanh::lean_inc_ref(v_date_3295_);
    v_timezone_3296_ = crate::leanh::lean_ctor_get(v_zdt_3294_, 3);
    crate::leanh::lean_inc_ref(v_timezone_3296_);
    crate::leanh::lean_dec_ref(v_zdt_3294_);
    v___x_3297_ = lean_thunk_get_own(v_date_3295_);
    crate::leanh::lean_dec_ref(v_date_3295_);
    v_date_3298_ = crate::leanh::lean_ctor_get(v___x_3297_, 0);
    crate::leanh::lean_inc_ref(v_date_3298_);
    v_time_3299_ = crate::leanh::lean_ctor_get(v___x_3297_, 1);
    crate::leanh::lean_inc_ref(v_time_3299_);
    crate::leanh::lean_dec(v___x_3297_);
    v_year_3300_ = crate::leanh::lean_ctor_get(v_date_3298_, 0);
    crate::leanh::lean_inc(v_year_3300_);
    v_month_3301_ = crate::leanh::lean_ctor_get(v_date_3298_, 1);
    crate::leanh::lean_inc(v_month_3301_);
    v_day_3302_ = crate::leanh::lean_ctor_get(v_date_3298_, 2);
    crate::leanh::lean_inc(v_day_3302_);
    crate::leanh::lean_dec_ref(v_date_3298_);
    v_hour_3303_ = crate::leanh::lean_ctor_get(v_time_3299_, 0);
    crate::leanh::lean_inc(v_hour_3303_);
    v_minute_3304_ = crate::leanh::lean_ctor_get(v_time_3299_, 1);
    crate::leanh::lean_inc(v_minute_3304_);
    v_second_3305_ = crate::leanh::lean_ctor_get(v_time_3299_, 2);
    crate::leanh::lean_inc(v_second_3305_);
    v_nanosecond_3306_ = crate::leanh::lean_ctor_get(v_time_3299_, 3);
    crate::leanh::lean_inc(v_nanosecond_3306_);
    crate::leanh::lean_dec_ref(v_time_3299_);
    v_offset_3307_ = crate::leanh::lean_ctor_get(v_timezone_3296_, 0);
    crate::leanh::lean_inc(v_offset_3307_);
    crate::leanh::lean_dec_ref(v_timezone_3296_);
    v___x_3308_ = l_Std_Time_Formats_leanDateTimeWithZone;
    v___x_14__overap_3309_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_3308_);
    v___x_3310_ = crate::leanh::lean_apply_8(
        v___x_14__overap_3309_,
        v_year_3300_,
        v_month_3301_,
        v_day_3302_,
        v_hour_3303_,
        v_minute_3304_,
        v_second_3305_,
        v_nanosecond_3306_,
        v_offset_3307_,
    );
    return v___x_3310_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_toLeanDateTimeWithIdentifierString(
    mut v_zdt_3311_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_3312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_timezone_3313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_3315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_3316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_year_3317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_month_3318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_day_3319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hour_3320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_minute_3321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_3323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_3324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_15__overap_3326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_date_3312_ = crate::leanh::lean_ctor_get(v_zdt_3311_, 0);
    crate::leanh::lean_inc_ref(v_date_3312_);
    v_timezone_3313_ = crate::leanh::lean_ctor_get(v_zdt_3311_, 3);
    crate::leanh::lean_inc_ref(v_timezone_3313_);
    crate::leanh::lean_dec_ref(v_zdt_3311_);
    v___x_3314_ = lean_thunk_get_own(v_date_3312_);
    crate::leanh::lean_dec_ref(v_date_3312_);
    v_date_3315_ = crate::leanh::lean_ctor_get(v___x_3314_, 0);
    crate::leanh::lean_inc_ref(v_date_3315_);
    v_time_3316_ = crate::leanh::lean_ctor_get(v___x_3314_, 1);
    crate::leanh::lean_inc_ref(v_time_3316_);
    crate::leanh::lean_dec(v___x_3314_);
    v_year_3317_ = crate::leanh::lean_ctor_get(v_date_3315_, 0);
    crate::leanh::lean_inc(v_year_3317_);
    v_month_3318_ = crate::leanh::lean_ctor_get(v_date_3315_, 1);
    crate::leanh::lean_inc(v_month_3318_);
    v_day_3319_ = crate::leanh::lean_ctor_get(v_date_3315_, 2);
    crate::leanh::lean_inc(v_day_3319_);
    crate::leanh::lean_dec_ref(v_date_3315_);
    v_hour_3320_ = crate::leanh::lean_ctor_get(v_time_3316_, 0);
    crate::leanh::lean_inc(v_hour_3320_);
    v_minute_3321_ = crate::leanh::lean_ctor_get(v_time_3316_, 1);
    crate::leanh::lean_inc(v_minute_3321_);
    v_second_3322_ = crate::leanh::lean_ctor_get(v_time_3316_, 2);
    crate::leanh::lean_inc(v_second_3322_);
    v_nanosecond_3323_ = crate::leanh::lean_ctor_get(v_time_3316_, 3);
    crate::leanh::lean_inc(v_nanosecond_3323_);
    crate::leanh::lean_dec_ref(v_time_3316_);
    v_name_3324_ = crate::leanh::lean_ctor_get(v_timezone_3313_, 1);
    crate::leanh::lean_inc_ref(v_name_3324_);
    crate::leanh::lean_dec_ref(v_timezone_3313_);
    v___x_3325_ = l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos;
    v___x_15__overap_3326_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_3325_);
    v___x_3327_ = crate::leanh::lean_apply_8(
        v___x_15__overap_3326_,
        v_year_3317_,
        v_month_3318_,
        v_day_3319_,
        v_hour_3320_,
        v_minute_3321_,
        v_second_3322_,
        v_nanosecond_3323_,
        v_name_3324_,
    );
    return v___x_3327_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_parse(
    mut v_input_3328_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_input_3328_);
    v___x_3329_ = l_Std_Time_ZonedDateTime_fromISO8601String(v_input_3328_);
    if crate::leanh::lean_obj_tag(v___x_3329_) == 0 {
        let mut v___x_3330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref_known(v___x_3329_, 1);
        crate::leanh::lean_inc_ref(v_input_3328_);
        v___x_3330_ = l_Std_Time_ZonedDateTime_fromRFC822String(v_input_3328_);
        if crate::leanh::lean_obj_tag(v___x_3330_) == 0 {
            let mut v___x_3331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref_known(v___x_3330_, 1);
            crate::leanh::lean_inc_ref(v_input_3328_);
            v___x_3331_ = l_Std_Time_ZonedDateTime_fromRFC850String(v_input_3328_);
            if crate::leanh::lean_obj_tag(v___x_3331_) == 0 {
                let mut v___x_3332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref_known(v___x_3331_, 1);
                crate::leanh::lean_inc_ref(v_input_3328_);
                v___x_3332_ = l_Std_Time_ZonedDateTime_fromDateTimeWithZoneString(v_input_3328_);
                if crate::leanh::lean_obj_tag(v___x_3332_) == 0 {
                    let mut v___x_3333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec_ref_known(v___x_3332_, 1);
                    v___x_3333_ = l_Std_Time_ZonedDateTime_fromLeanDateTimeWithIdentifierString(
                        v_input_3328_,
                    );
                    return v___x_3333_;
                } else {
                    crate::leanh::lean_dec_ref(v_input_3328_);
                    return v___x_3332_;
                }
            } else {
                crate::leanh::lean_dec_ref(v_input_3328_);
                return v___x_3331_;
            }
        } else {
            crate::leanh::lean_dec_ref(v_input_3328_);
            return v___x_3330_;
        }
    } else {
        crate::leanh::lean_dec_ref(v_input_3328_);
        return v___x_3329_;
    }
}
pub unsafe fn l_Std_Time_ZonedDateTime_instRepr___lam__0(
    mut v_data_3339_: *mut crate::leanh::LeanObject,
    mut v___y_3340_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3341_ = l_Std_Time_ZonedDateTime_instRepr___lam__0___closed__1;
    v___x_3342_ = l_Std_Time_ZonedDateTime_toLeanDateTimeWithZoneString(v_data_3339_);
    v___x_3343_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3343_, 0, v___x_3342_);
    v___x_3344_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3344_, 0, v___x_3341_);
    crate::leanh::lean_ctor_set(v___x_3344_, 1, v___x_3343_);
    v___x_3345_ = l_Std_Time_PlainDate_instRepr___lam__0___closed__3;
    v___x_3346_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3346_, 0, v___x_3344_);
    crate::leanh::lean_ctor_set(v___x_3346_, 1, v___x_3345_);
    v___x_3347_ = l_Repr_addAppParen(v___x_3346_, v___y_3340_);
    return v___x_3347_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_instRepr___lam__0___boxed(
    mut v_data_3348_: *mut crate::leanh::LeanObject,
    mut v___y_3349_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3350_ = l_Std_Time_ZonedDateTime_instRepr___lam__0(v_data_3348_, v___y_3349_);
    crate::leanh::lean_dec(v___y_3349_);
    return v_res_3350_;
}
pub unsafe fn l_Std_Time_PlainDateTime_format___lam__0(
    mut v_date_3353_: *mut crate::leanh::LeanObject,
    mut v_locale_3354_: *mut crate::leanh::LeanObject,
    mut v_x_3355_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_3356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_year_3357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: u8 = 0;
    let mut v___x_3359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3363_: u8 = 0;
    let mut v_date_3364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_year_3365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3369_: u8 = 0;
    let mut v_unused_3370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3373_: u8 = 0;
    let mut v_date_3374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_year_3375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3379_: u8 = 0;
    let mut v_unused_3380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3383_: u8 = 0;
    let mut v_firstDayOfWeek_3384_: u8 = 0;
    let mut v_date_3385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3390_: u8 = 0;
    let mut v_unused_3391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3394_: u8 = 0;
    let mut v_date_3395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3398_: u8 = 0;
    let mut v_year_3399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_month_3400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_day_3401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3403_: u8 = 0;
    let mut v___y_3404_: u8 = 0;
    let mut v___x_3406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3416_: u8 = 0;
    let mut v___y_3417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3420_: u8 = 0;
    let mut v___y_3422_: u8 = 0;
    let mut v___x_3423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3426_: u8 = 0;
    let mut v___x_3427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3429_: u8 = 0;
    let mut v___x_3430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: u8 = 0;
    let mut v___x_3437_: u8 = 0;
    let mut v___x_3438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3440_: u8 = 0;
    let mut v_isSharedCheck_3441_: u8 = 0;
    let mut v_unused_3442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3443_: u8 = 0;
    let mut v_unused_3444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3447_: u8 = 0;
    let mut v_date_3448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3453_: u8 = 0;
    let mut v_unused_3454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3457_: u8 = 0;
    let mut v_firstDayOfWeek_3458_: u8 = 0;
    let mut v_date_3459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3464_: u8 = 0;
    let mut v_unused_3465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3468_: u8 = 0;
    let mut v_firstDayOfWeek_3469_: u8 = 0;
    let mut v_date_3470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3475_: u8 = 0;
    let mut v_unused_3476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3479_: u8 = 0;
    let mut v_date_3480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_month_3481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3485_: u8 = 0;
    let mut v_unused_3486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3489_: u8 = 0;
    let mut v_date_3490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_day_3491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3495_: u8 = 0;
    let mut v_unused_3496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_3497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3498_: u8 = 0;
    let mut v___x_3499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3503_: u8 = 0;
    let mut v_date_3504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3505_: u8 = 0;
    let mut v___x_3506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3510_: u8 = 0;
    let mut v_unused_3511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3514_: u8 = 0;
    let mut v___x_3515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3519_: u8 = 0;
    let mut v_unused_3520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3523_: u8 = 0;
    let mut v_time_3524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hour_3525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3529_: u8 = 0;
    let mut v_unused_3530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3533_: u8 = 0;
    let mut v_time_3534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hour_3535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3540_: u8 = 0;
    let mut v_unused_3541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3544_: u8 = 0;
    let mut v_time_3545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_minute_3546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3550_: u8 = 0;
    let mut v_unused_3551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3554_: u8 = 0;
    let mut v_time_3555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_3556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3560_: u8 = 0;
    let mut v_unused_3561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3564_: u8 = 0;
    let mut v_time_3565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3570_: u8 = 0;
    let mut v_unused_3571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_3572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hour_3573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: u8 = 0;
    let mut v___x_3575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3579_: u8 = 0;
    let mut v_time_3580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hour_3581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3586_: u8 = 0;
    let mut v_unused_3587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3590_: u8 = 0;
    let mut v_time_3591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hour_3592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3598_: u8 = 0;
    let mut v_unused_3599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3602_: u8 = 0;
    let mut v_time_3603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_3604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3608_: u8 = 0;
    let mut v_unused_3609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3612_: u8 = 0;
    let mut v_time_3613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3618_: u8 = 0;
    let mut v_unused_3619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3622_: u8 = 0;
    let mut v_time_3623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3628_: u8 = 0;
    let mut v_unused_3629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_3355_) {
                0 => {
                    crate::leanh::lean_dec_ref_known(v_x_3355_, 0);
                    v_date_3356_ = crate::leanh::lean_ctor_get(v_date_3353_, 0);
                    crate::leanh::lean_inc_ref(v_date_3356_);
                    crate::leanh::lean_dec_ref(v_date_3353_);
                    v_year_3357_ = crate::leanh::lean_ctor_get(v_date_3356_, 0);
                    crate::leanh::lean_inc(v_year_3357_);
                    crate::leanh::lean_dec_ref(v_date_3356_);
                    v___x_3358_ = l_Std_Time_Year_Offset_era(v_year_3357_);
                    crate::leanh::lean_dec(v_year_3357_);
                    v___x_3359_ = crate::leanh::lean_box((v___x_3358_) as usize);
                    v___x_3360_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3360_, 0, v___x_3359_);
                    return v___x_3360_;
                }
                1 => {
                    v_isSharedCheck_3369_ = (!crate::leanh::lean_is_exclusive(v_x_3355_)) as u8;
                    if v_isSharedCheck_3369_ == 0 {
                        v_unused_3370_ = crate::leanh::lean_ctor_get(v_x_3355_, 0);
                        crate::leanh::lean_dec(v_unused_3370_);
                        v___x_3362_ = v_x_3355_;
                        v_isShared_3363_ = v_isSharedCheck_3369_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_x_3355_);
                        v___x_3362_ = crate::leanh::lean_box(0);
                        v_isShared_3363_ = v_isSharedCheck_3369_;
                        state = 1;
                        continue;
                    }
                }
                2 => {
                    v_isSharedCheck_3379_ = (!crate::leanh::lean_is_exclusive(v_x_3355_)) as u8;
                    if v_isSharedCheck_3379_ == 0 {
                        v_unused_3380_ = crate::leanh::lean_ctor_get(v_x_3355_, 0);
                        crate::leanh::lean_dec(v_unused_3380_);
                        v___x_3372_ = v_x_3355_;
                        v_isShared_3373_ = v_isSharedCheck_3379_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_x_3355_);
                        v___x_3372_ = crate::leanh::lean_box(0);
                        v_isShared_3373_ = v_isSharedCheck_3379_;
                        state = 3;
                        continue;
                    }
                }
                3 => {
                    v_isSharedCheck_3390_ = (!crate::leanh::lean_is_exclusive(v_x_3355_)) as u8;
                    if v_isSharedCheck_3390_ == 0 {
                        v_unused_3391_ = crate::leanh::lean_ctor_get(v_x_3355_, 0);
                        crate::leanh::lean_dec(v_unused_3391_);
                        v___x_3382_ = v_x_3355_;
                        v_isShared_3383_ = v_isSharedCheck_3390_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_x_3355_);
                        v___x_3382_ = crate::leanh::lean_box(0);
                        v_isShared_3383_ = v_isSharedCheck_3390_;
                        state = 5;
                        continue;
                    }
                }
                4 => {
                    v_isSharedCheck_3443_ = (!crate::leanh::lean_is_exclusive(v_x_3355_)) as u8;
                    if v_isSharedCheck_3443_ == 0 {
                        v_unused_3444_ = crate::leanh::lean_ctor_get(v_x_3355_, 0);
                        crate::leanh::lean_dec(v_unused_3444_);
                        v___x_3393_ = v_x_3355_;
                        v_isShared_3394_ = v_isSharedCheck_3443_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_x_3355_);
                        v___x_3393_ = crate::leanh::lean_box(0);
                        v_isShared_3394_ = v_isSharedCheck_3443_;
                        state = 7;
                        continue;
                    }
                }
                7 => {
                    v_isSharedCheck_3453_ = (!crate::leanh::lean_is_exclusive(v_x_3355_)) as u8;
                    if v_isSharedCheck_3453_ == 0 {
                        v_unused_3454_ = crate::leanh::lean_ctor_get(v_x_3355_, 0);
                        crate::leanh::lean_dec(v_unused_3454_);
                        v___x_3446_ = v_x_3355_;
                        v_isShared_3447_ = v_isSharedCheck_3453_;
                        state = 15;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_x_3355_);
                        v___x_3446_ = crate::leanh::lean_box(0);
                        v_isShared_3447_ = v_isSharedCheck_3453_;
                        state = 15;
                        continue;
                    }
                }
                8 => {
                    v_isSharedCheck_3464_ = (!crate::leanh::lean_is_exclusive(v_x_3355_)) as u8;
                    if v_isSharedCheck_3464_ == 0 {
                        v_unused_3465_ = crate::leanh::lean_ctor_get(v_x_3355_, 0);
                        crate::leanh::lean_dec(v_unused_3465_);
                        v___x_3456_ = v_x_3355_;
                        v_isShared_3457_ = v_isSharedCheck_3464_;
                        state = 17;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_x_3355_);
                        v___x_3456_ = crate::leanh::lean_box(0);
                        v_isShared_3457_ = v_isSharedCheck_3464_;
                        state = 17;
                        continue;
                    }
                }
                9 => {
                    v_isSharedCheck_3475_ = (!crate::leanh::lean_is_exclusive(v_x_3355_)) as u8;
                    if v_isSharedCheck_3475_ == 0 {
                        v_unused_3476_ = crate::leanh::lean_ctor_get(v_x_3355_, 0);
                        crate::leanh::lean_dec(v_unused_3476_);
                        v___x_3467_ = v_x_3355_;
                        v_isShared_3468_ = v_isSharedCheck_3475_;
                        state = 19;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_x_3355_);
                        v___x_3467_ = crate::leanh::lean_box(0);
                        v_isShared_3468_ = v_isSharedCheck_3475_;
                        state = 19;
                        continue;
                    }
                }
                5 => {
                    v_isSharedCheck_3485_ = (!crate::leanh::lean_is_exclusive(v_x_3355_)) as u8;
                    if v_isSharedCheck_3485_ == 0 {
                        v_unused_3486_ = crate::leanh::lean_ctor_get(v_x_3355_, 0);
                        crate::leanh::lean_dec(v_unused_3486_);
                        v___x_3478_ = v_x_3355_;
                        v_isShared_3479_ = v_isSharedCheck_3485_;
                        state = 21;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_x_3355_);
                        v___x_3478_ = crate::leanh::lean_box(0);
                        v_isShared_3479_ = v_isSharedCheck_3485_;
                        state = 21;
                        continue;
                    }
                }
                6 => {
                    v_isSharedCheck_3495_ = (!crate::leanh::lean_is_exclusive(v_x_3355_)) as u8;
                    if v_isSharedCheck_3495_ == 0 {
                        v_unused_3496_ = crate::leanh::lean_ctor_get(v_x_3355_, 0);
                        crate::leanh::lean_dec(v_unused_3496_);
                        v___x_3488_ = v_x_3355_;
                        v_isShared_3489_ = v_isSharedCheck_3495_;
                        state = 23;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_x_3355_);
                        v___x_3488_ = crate::leanh::lean_box(0);
                        v_isShared_3489_ = v_isSharedCheck_3495_;
                        state = 23;
                        continue;
                    }
                }
                10 => {
                    crate::leanh::lean_dec_ref_known(v_x_3355_, 0);
                    v_date_3497_ = crate::leanh::lean_ctor_get(v_date_3353_, 0);
                    crate::leanh::lean_inc_ref(v_date_3497_);
                    crate::leanh::lean_dec_ref(v_date_3353_);
                    v___x_3498_ = l_Std_Time_PlainDate_weekday(v_date_3497_);
                    v___x_3499_ = crate::leanh::lean_box((v___x_3498_) as usize);
                    v___x_3500_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3500_, 0, v___x_3499_);
                    return v___x_3500_;
                }
                11 => {
                    v_isSharedCheck_3510_ = (!crate::leanh::lean_is_exclusive(v_x_3355_)) as u8;
                    if v_isSharedCheck_3510_ == 0 {
                        v_unused_3511_ = crate::leanh::lean_ctor_get(v_x_3355_, 0);
                        crate::leanh::lean_dec(v_unused_3511_);
                        v___x_3502_ = v_x_3355_;
                        v_isShared_3503_ = v_isSharedCheck_3510_;
                        state = 25;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_x_3355_);
                        v___x_3502_ = crate::leanh::lean_box(0);
                        v_isShared_3503_ = v_isSharedCheck_3510_;
                        state = 25;
                        continue;
                    }
                }
                12 => {
                    v_isSharedCheck_3519_ = (!crate::leanh::lean_is_exclusive(v_x_3355_)) as u8;
                    if v_isSharedCheck_3519_ == 0 {
                        v_unused_3520_ = crate::leanh::lean_ctor_get(v_x_3355_, 0);
                        crate::leanh::lean_dec(v_unused_3520_);
                        v___x_3513_ = v_x_3355_;
                        v_isShared_3514_ = v_isSharedCheck_3519_;
                        state = 27;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_x_3355_);
                        v___x_3513_ = crate::leanh::lean_box(0);
                        v_isShared_3514_ = v_isSharedCheck_3519_;
                        state = 27;
                        continue;
                    }
                }
                17 => {
                    v_isSharedCheck_3529_ = (!crate::leanh::lean_is_exclusive(v_x_3355_)) as u8;
                    if v_isSharedCheck_3529_ == 0 {
                        v_unused_3530_ = crate::leanh::lean_ctor_get(v_x_3355_, 0);
                        crate::leanh::lean_dec(v_unused_3530_);
                        v___x_3522_ = v_x_3355_;
                        v_isShared_3523_ = v_isSharedCheck_3529_;
                        state = 29;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_x_3355_);
                        v___x_3522_ = crate::leanh::lean_box(0);
                        v_isShared_3523_ = v_isSharedCheck_3529_;
                        state = 29;
                        continue;
                    }
                }
                16 => {
                    v_isSharedCheck_3540_ = (!crate::leanh::lean_is_exclusive(v_x_3355_)) as u8;
                    if v_isSharedCheck_3540_ == 0 {
                        v_unused_3541_ = crate::leanh::lean_ctor_get(v_x_3355_, 0);
                        crate::leanh::lean_dec(v_unused_3541_);
                        v___x_3532_ = v_x_3355_;
                        v_isShared_3533_ = v_isSharedCheck_3540_;
                        state = 31;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_x_3355_);
                        v___x_3532_ = crate::leanh::lean_box(0);
                        v_isShared_3533_ = v_isSharedCheck_3540_;
                        state = 31;
                        continue;
                    }
                }
                18 => {
                    v_isSharedCheck_3550_ = (!crate::leanh::lean_is_exclusive(v_x_3355_)) as u8;
                    if v_isSharedCheck_3550_ == 0 {
                        v_unused_3551_ = crate::leanh::lean_ctor_get(v_x_3355_, 0);
                        crate::leanh::lean_dec(v_unused_3551_);
                        v___x_3543_ = v_x_3355_;
                        v_isShared_3544_ = v_isSharedCheck_3550_;
                        state = 33;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_x_3355_);
                        v___x_3543_ = crate::leanh::lean_box(0);
                        v_isShared_3544_ = v_isSharedCheck_3550_;
                        state = 33;
                        continue;
                    }
                }
                22 => {
                    v_isSharedCheck_3560_ = (!crate::leanh::lean_is_exclusive(v_x_3355_)) as u8;
                    if v_isSharedCheck_3560_ == 0 {
                        v_unused_3561_ = crate::leanh::lean_ctor_get(v_x_3355_, 0);
                        crate::leanh::lean_dec(v_unused_3561_);
                        v___x_3553_ = v_x_3355_;
                        v_isShared_3554_ = v_isSharedCheck_3560_;
                        state = 35;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_x_3355_);
                        v___x_3553_ = crate::leanh::lean_box(0);
                        v_isShared_3554_ = v_isSharedCheck_3560_;
                        state = 35;
                        continue;
                    }
                }
                19 => {
                    v_isSharedCheck_3570_ = (!crate::leanh::lean_is_exclusive(v_x_3355_)) as u8;
                    if v_isSharedCheck_3570_ == 0 {
                        v_unused_3571_ = crate::leanh::lean_ctor_get(v_x_3355_, 0);
                        crate::leanh::lean_dec(v_unused_3571_);
                        v___x_3563_ = v_x_3355_;
                        v_isShared_3564_ = v_isSharedCheck_3570_;
                        state = 37;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_x_3355_);
                        v___x_3563_ = crate::leanh::lean_box(0);
                        v_isShared_3564_ = v_isSharedCheck_3570_;
                        state = 37;
                        continue;
                    }
                }
                13 => {
                    crate::leanh::lean_dec_ref_known(v_x_3355_, 0);
                    v_time_3572_ = crate::leanh::lean_ctor_get(v_date_3353_, 1);
                    crate::leanh::lean_inc_ref(v_time_3572_);
                    crate::leanh::lean_dec_ref(v_date_3353_);
                    v_hour_3573_ = crate::leanh::lean_ctor_get(v_time_3572_, 0);
                    crate::leanh::lean_inc(v_hour_3573_);
                    crate::leanh::lean_dec_ref(v_time_3572_);
                    v___x_3574_ = l_Std_Time_HourMarker_ofOrdinal(v_hour_3573_);
                    crate::leanh::lean_dec(v_hour_3573_);
                    v___x_3575_ = crate::leanh::lean_box((v___x_3574_) as usize);
                    v___x_3576_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3576_, 0, v___x_3575_);
                    return v___x_3576_;
                }
                14 => {
                    v_isSharedCheck_3586_ = (!crate::leanh::lean_is_exclusive(v_x_3355_)) as u8;
                    if v_isSharedCheck_3586_ == 0 {
                        v_unused_3587_ = crate::leanh::lean_ctor_get(v_x_3355_, 0);
                        crate::leanh::lean_dec(v_unused_3587_);
                        v___x_3578_ = v_x_3355_;
                        v_isShared_3579_ = v_isSharedCheck_3586_;
                        state = 39;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_x_3355_);
                        v___x_3578_ = crate::leanh::lean_box(0);
                        v_isShared_3579_ = v_isSharedCheck_3586_;
                        state = 39;
                        continue;
                    }
                }
                15 => {
                    v_isSharedCheck_3598_ = (!crate::leanh::lean_is_exclusive(v_x_3355_)) as u8;
                    if v_isSharedCheck_3598_ == 0 {
                        v_unused_3599_ = crate::leanh::lean_ctor_get(v_x_3355_, 0);
                        crate::leanh::lean_dec(v_unused_3599_);
                        v___x_3589_ = v_x_3355_;
                        v_isShared_3590_ = v_isSharedCheck_3598_;
                        state = 41;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_x_3355_);
                        v___x_3589_ = crate::leanh::lean_box(0);
                        v_isShared_3590_ = v_isSharedCheck_3598_;
                        state = 41;
                        continue;
                    }
                }
                20 => {
                    v_isSharedCheck_3608_ = (!crate::leanh::lean_is_exclusive(v_x_3355_)) as u8;
                    if v_isSharedCheck_3608_ == 0 {
                        v_unused_3609_ = crate::leanh::lean_ctor_get(v_x_3355_, 0);
                        crate::leanh::lean_dec(v_unused_3609_);
                        v___x_3601_ = v_x_3355_;
                        v_isShared_3602_ = v_isSharedCheck_3608_;
                        state = 43;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_x_3355_);
                        v___x_3601_ = crate::leanh::lean_box(0);
                        v_isShared_3602_ = v_isSharedCheck_3608_;
                        state = 43;
                        continue;
                    }
                }
                21 => {
                    v_isSharedCheck_3618_ = (!crate::leanh::lean_is_exclusive(v_x_3355_)) as u8;
                    if v_isSharedCheck_3618_ == 0 {
                        v_unused_3619_ = crate::leanh::lean_ctor_get(v_x_3355_, 0);
                        crate::leanh::lean_dec(v_unused_3619_);
                        v___x_3611_ = v_x_3355_;
                        v_isShared_3612_ = v_isSharedCheck_3618_;
                        state = 45;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_x_3355_);
                        v___x_3611_ = crate::leanh::lean_box(0);
                        v_isShared_3612_ = v_isSharedCheck_3618_;
                        state = 45;
                        continue;
                    }
                }
                23 => {
                    v_isSharedCheck_3628_ = (!crate::leanh::lean_is_exclusive(v_x_3355_)) as u8;
                    if v_isSharedCheck_3628_ == 0 {
                        v_unused_3629_ = crate::leanh::lean_ctor_get(v_x_3355_, 0);
                        crate::leanh::lean_dec(v_unused_3629_);
                        v___x_3621_ = v_x_3355_;
                        v_isShared_3622_ = v_isSharedCheck_3628_;
                        state = 47;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_x_3355_);
                        v___x_3621_ = crate::leanh::lean_box(0);
                        v_isShared_3622_ = v_isSharedCheck_3628_;
                        state = 47;
                        continue;
                    }
                }
                _ => {
                    crate::leanh::lean_dec(v_x_3355_);
                    crate::leanh::lean_dec_ref(v_date_3353_);
                    v___x_3630_ = crate::leanh::lean_box(0);
                    return v___x_3630_;
                }
            },
            1 => {
                v_date_3364_ = crate::leanh::lean_ctor_get(v_date_3353_, 0);
                crate::leanh::lean_inc_ref(v_date_3364_);
                crate::leanh::lean_dec_ref(v_date_3353_);
                v_year_3365_ = crate::leanh::lean_ctor_get(v_date_3364_, 0);
                crate::leanh::lean_inc(v_year_3365_);
                crate::leanh::lean_dec_ref(v_date_3364_);
                if v_isShared_3363_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3362_, 0, v_year_3365_);
                    v___x_3367_ = v___x_3362_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3368_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3368_, 0, v_year_3365_);
                    v___x_3367_ = v_reuseFailAlloc_3368_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3367_;
            }
            3 => {
                v_date_3374_ = crate::leanh::lean_ctor_get(v_date_3353_, 0);
                crate::leanh::lean_inc_ref(v_date_3374_);
                crate::leanh::lean_dec_ref(v_date_3353_);
                v_year_3375_ = crate::leanh::lean_ctor_get(v_date_3374_, 0);
                crate::leanh::lean_inc(v_year_3375_);
                crate::leanh::lean_dec_ref(v_date_3374_);
                if v_isShared_3373_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3372_, 1);
                    crate::leanh::lean_ctor_set(v___x_3372_, 0, v_year_3375_);
                    v___x_3377_ = v___x_3372_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3378_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3378_, 0, v_year_3375_);
                    v___x_3377_ = v_reuseFailAlloc_3378_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3377_;
            }
            5 => {
                v_firstDayOfWeek_3384_ = crate::leanh::lean_ctor_get_uint8(
                    v_locale_3354_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_date_3385_ = crate::leanh::lean_ctor_get(v_date_3353_, 0);
                crate::leanh::lean_inc_ref(v_date_3385_);
                crate::leanh::lean_dec_ref(v_date_3353_);
                v___x_3386_ = l_Std_Time_PlainDate_weekYear(v_date_3385_, v_firstDayOfWeek_3384_);
                if v_isShared_3383_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3382_, 1);
                    crate::leanh::lean_ctor_set(v___x_3382_, 0, v___x_3386_);
                    v___x_3388_ = v___x_3382_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3389_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3389_, 0, v___x_3386_);
                    v___x_3388_ = v_reuseFailAlloc_3389_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3388_;
            }
            7 => {
                v_date_3395_ = crate::leanh::lean_ctor_get(v_date_3353_, 0);
                v_isSharedCheck_3441_ = (!crate::leanh::lean_is_exclusive(v_date_3353_)) as u8;
                if v_isSharedCheck_3441_ == 0 {
                    v_unused_3442_ = crate::leanh::lean_ctor_get(v_date_3353_, 1);
                    crate::leanh::lean_dec(v_unused_3442_);
                    v___x_3397_ = v_date_3353_;
                    v_isShared_3398_ = v_isSharedCheck_3441_;
                    state = 8;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_date_3395_);
                    crate::leanh::lean_dec(v_date_3353_);
                    v___x_3397_ = crate::leanh::lean_box(0);
                    v_isShared_3398_ = v_isSharedCheck_3441_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v_year_3399_ = crate::leanh::lean_ctor_get(v_date_3395_, 0);
                crate::leanh::lean_inc(v_year_3399_);
                v_month_3400_ = crate::leanh::lean_ctor_get(v_date_3395_, 1);
                crate::leanh::lean_inc(v_month_3400_);
                v_day_3401_ = crate::leanh::lean_ctor_get(v_date_3395_, 2);
                crate::leanh::lean_inc(v_day_3401_);
                crate::leanh::lean_dec_ref(v_date_3395_);
                v___x_3430_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_format___lam__0___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_format___lam__0___closed__0_once),
                    _init_l_Std_Time_PlainDate_format___lam__0___closed__0,
                );
                v___x_3431_ = lean_int_mod(v_year_3399_, v___x_3430_);
                v___x_3432_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_format___lam__0___closed__1),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_format___lam__0___closed__1_once),
                    _init_l_Std_Time_PlainDate_format___lam__0___closed__1,
                );
                v___x_3437_ = lean_int_dec_eq(v___x_3431_, v___x_3432_);
                crate::leanh::lean_dec(v___x_3431_);
                if v___x_3437_ == 0 {
                    v___y_3422_ = v___x_3437_;
                    state = 13;
                    continue;
                } else {
                    v___x_3438_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_format___lam__0___closed__3),
                        core::ptr::addr_of_mut!(
                            l_Std_Time_PlainDate_format___lam__0___closed__3_once
                        ),
                        _init_l_Std_Time_PlainDate_format___lam__0___closed__3,
                    );
                    v___x_3439_ = lean_int_mod(v_year_3399_, v___x_3438_);
                    v___x_3440_ = lean_int_dec_eq(v___x_3439_, v___x_3432_);
                    crate::leanh::lean_dec(v___x_3439_);
                    if v___x_3440_ == 0 {
                        if v___x_3437_ == 0 {
                            state = 14;
                            continue;
                        } else {
                            v___y_3422_ = v___x_3437_;
                            state = 13;
                            continue;
                        }
                    } else {
                        state = 14;
                        continue;
                    }
                }
            }
            9 => {
                if v_isShared_3398_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3397_, 1, v_day_3401_);
                    crate::leanh::lean_ctor_set(v___x_3397_, 0, v_month_3400_);
                    v___x_3406_ = v___x_3397_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3413_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3413_, 0, v_month_3400_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3413_, 1, v_day_3401_);
                    v___x_3406_ = v_reuseFailAlloc_3413_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_3407_ = l_Std_Time_ValidDate_dayOfYear(v___y_3404_, v___x_3406_);
                crate::leanh::lean_dec_ref(v___x_3406_);
                v___x_3408_ = crate::leanh::lean_box((v___y_3403_) as usize);
                v___x_3409_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3409_, 0, v___x_3408_);
                crate::leanh::lean_ctor_set(v___x_3409_, 1, v___x_3407_);
                if v_isShared_3394_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3393_, 1);
                    crate::leanh::lean_ctor_set(v___x_3393_, 0, v___x_3409_);
                    v___x_3411_ = v___x_3393_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3412_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3412_, 0, v___x_3409_);
                    v___x_3411_ = v_reuseFailAlloc_3412_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3411_;
            }
            12 => {
                v___x_3418_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_format___lam__0___closed__2),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_format___lam__0___closed__2_once),
                    _init_l_Std_Time_PlainDate_format___lam__0___closed__2,
                );
                v___x_3419_ = lean_int_mod(v___y_3417_, v___x_3418_);
                crate::leanh::lean_dec(v___y_3417_);
                v___x_3420_ = lean_int_dec_eq(v___x_3419_, v___y_3415_);
                crate::leanh::lean_dec(v___x_3419_);
                v___y_3403_ = v___y_3416_;
                v___y_3404_ = v___x_3420_;
                state = 9;
                continue;
            }
            13 => {
                v___x_3423_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_format___lam__0___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_format___lam__0___closed__0_once),
                    _init_l_Std_Time_PlainDate_format___lam__0___closed__0,
                );
                v___x_3424_ = lean_int_mod(v_year_3399_, v___x_3423_);
                v___x_3425_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_format___lam__0___closed__1),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_format___lam__0___closed__1_once),
                    _init_l_Std_Time_PlainDate_format___lam__0___closed__1,
                );
                v___x_3426_ = lean_int_dec_eq(v___x_3424_, v___x_3425_);
                crate::leanh::lean_dec(v___x_3424_);
                if v___x_3426_ == 0 {
                    crate::leanh::lean_dec(v_year_3399_);
                    v___y_3403_ = v___y_3422_;
                    v___y_3404_ = v___x_3426_;
                    state = 9;
                    continue;
                } else {
                    v___x_3427_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_format___lam__0___closed__3),
                        core::ptr::addr_of_mut!(
                            l_Std_Time_PlainDate_format___lam__0___closed__3_once
                        ),
                        _init_l_Std_Time_PlainDate_format___lam__0___closed__3,
                    );
                    v___x_3428_ = lean_int_mod(v_year_3399_, v___x_3427_);
                    v___x_3429_ = lean_int_dec_eq(v___x_3428_, v___x_3425_);
                    crate::leanh::lean_dec(v___x_3428_);
                    if v___x_3429_ == 0 {
                        if v___x_3426_ == 0 {
                            v___y_3415_ = v___x_3425_;
                            v___y_3416_ = v___y_3422_;
                            v___y_3417_ = v_year_3399_;
                            state = 12;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_year_3399_);
                            v___y_3403_ = v___y_3422_;
                            v___y_3404_ = v___x_3426_;
                            state = 9;
                            continue;
                        }
                    } else {
                        v___y_3415_ = v___x_3425_;
                        v___y_3416_ = v___y_3422_;
                        v___y_3417_ = v_year_3399_;
                        state = 12;
                        continue;
                    }
                }
            }
            14 => {
                v___x_3434_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_format___lam__0___closed__2),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_format___lam__0___closed__2_once),
                    _init_l_Std_Time_PlainDate_format___lam__0___closed__2,
                );
                v___x_3435_ = lean_int_mod(v_year_3399_, v___x_3434_);
                v___x_3436_ = lean_int_dec_eq(v___x_3435_, v___x_3432_);
                crate::leanh::lean_dec(v___x_3435_);
                v___y_3422_ = v___x_3436_;
                state = 13;
                continue;
            }
            15 => {
                v_date_3448_ = crate::leanh::lean_ctor_get(v_date_3353_, 0);
                crate::leanh::lean_inc_ref(v_date_3448_);
                crate::leanh::lean_dec_ref(v_date_3353_);
                v___x_3449_ = l_Std_Time_PlainDate_quarter(v_date_3448_);
                crate::leanh::lean_dec_ref(v_date_3448_);
                if v_isShared_3447_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3446_, 1);
                    crate::leanh::lean_ctor_set(v___x_3446_, 0, v___x_3449_);
                    v___x_3451_ = v___x_3446_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3452_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3452_, 0, v___x_3449_);
                    v___x_3451_ = v_reuseFailAlloc_3452_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_3451_;
            }
            17 => {
                v_firstDayOfWeek_3458_ = crate::leanh::lean_ctor_get_uint8(
                    v_locale_3354_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_date_3459_ = crate::leanh::lean_ctor_get(v_date_3353_, 0);
                crate::leanh::lean_inc_ref(v_date_3459_);
                crate::leanh::lean_dec_ref(v_date_3353_);
                v___x_3460_ = l_Std_Time_PlainDate_weekOfYear(v_date_3459_, v_firstDayOfWeek_3458_);
                if v_isShared_3457_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3456_, 1);
                    crate::leanh::lean_ctor_set(v___x_3456_, 0, v___x_3460_);
                    v___x_3462_ = v___x_3456_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3463_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3463_, 0, v___x_3460_);
                    v___x_3462_ = v_reuseFailAlloc_3463_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_3462_;
            }
            19 => {
                v_firstDayOfWeek_3469_ = crate::leanh::lean_ctor_get_uint8(
                    v_locale_3354_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_date_3470_ = crate::leanh::lean_ctor_get(v_date_3353_, 0);
                crate::leanh::lean_inc_ref(v_date_3470_);
                crate::leanh::lean_dec_ref(v_date_3353_);
                v___x_3471_ =
                    l_Std_Time_PlainDate_alignedWeekOfMonth(v_date_3470_, v_firstDayOfWeek_3469_);
                if v_isShared_3468_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3467_, 1);
                    crate::leanh::lean_ctor_set(v___x_3467_, 0, v___x_3471_);
                    v___x_3473_ = v___x_3467_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3474_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3474_, 0, v___x_3471_);
                    v___x_3473_ = v_reuseFailAlloc_3474_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_3473_;
            }
            21 => {
                v_date_3480_ = crate::leanh::lean_ctor_get(v_date_3353_, 0);
                crate::leanh::lean_inc_ref(v_date_3480_);
                crate::leanh::lean_dec_ref(v_date_3353_);
                v_month_3481_ = crate::leanh::lean_ctor_get(v_date_3480_, 1);
                crate::leanh::lean_inc(v_month_3481_);
                crate::leanh::lean_dec_ref(v_date_3480_);
                if v_isShared_3479_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3478_, 1);
                    crate::leanh::lean_ctor_set(v___x_3478_, 0, v_month_3481_);
                    v___x_3483_ = v___x_3478_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_3484_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3484_, 0, v_month_3481_);
                    v___x_3483_ = v_reuseFailAlloc_3484_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_3483_;
            }
            23 => {
                v_date_3490_ = crate::leanh::lean_ctor_get(v_date_3353_, 0);
                crate::leanh::lean_inc_ref(v_date_3490_);
                crate::leanh::lean_dec_ref(v_date_3353_);
                v_day_3491_ = crate::leanh::lean_ctor_get(v_date_3490_, 2);
                crate::leanh::lean_inc(v_day_3491_);
                crate::leanh::lean_dec_ref(v_date_3490_);
                if v_isShared_3489_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3488_, 1);
                    crate::leanh::lean_ctor_set(v___x_3488_, 0, v_day_3491_);
                    v___x_3493_ = v___x_3488_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_3494_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3494_, 0, v_day_3491_);
                    v___x_3493_ = v_reuseFailAlloc_3494_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_3493_;
            }
            25 => {
                v_date_3504_ = crate::leanh::lean_ctor_get(v_date_3353_, 0);
                crate::leanh::lean_inc_ref(v_date_3504_);
                crate::leanh::lean_dec_ref(v_date_3353_);
                v___x_3505_ = l_Std_Time_PlainDate_weekday(v_date_3504_);
                v___x_3506_ = crate::leanh::lean_box((v___x_3505_) as usize);
                if v_isShared_3503_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3502_, 1);
                    crate::leanh::lean_ctor_set(v___x_3502_, 0, v___x_3506_);
                    v___x_3508_ = v___x_3502_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_3509_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3509_, 0, v___x_3506_);
                    v___x_3508_ = v_reuseFailAlloc_3509_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_3508_;
            }
            27 => {
                v___x_3515_ = l_Std_Time_PlainDateTime_weekOfMonth(v_date_3353_);
                crate::leanh::lean_dec_ref(v_date_3353_);
                if v_isShared_3514_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3513_, 1);
                    crate::leanh::lean_ctor_set(v___x_3513_, 0, v___x_3515_);
                    v___x_3517_ = v___x_3513_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_3518_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3518_, 0, v___x_3515_);
                    v___x_3517_ = v_reuseFailAlloc_3518_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_3517_;
            }
            29 => {
                v_time_3524_ = crate::leanh::lean_ctor_get(v_date_3353_, 1);
                crate::leanh::lean_inc_ref(v_time_3524_);
                crate::leanh::lean_dec_ref(v_date_3353_);
                v_hour_3525_ = crate::leanh::lean_ctor_get(v_time_3524_, 0);
                crate::leanh::lean_inc(v_hour_3525_);
                crate::leanh::lean_dec_ref(v_time_3524_);
                if v_isShared_3523_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3522_, 1);
                    crate::leanh::lean_ctor_set(v___x_3522_, 0, v_hour_3525_);
                    v___x_3527_ = v___x_3522_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_3528_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3528_, 0, v_hour_3525_);
                    v___x_3527_ = v_reuseFailAlloc_3528_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_3527_;
            }
            31 => {
                v_time_3534_ = crate::leanh::lean_ctor_get(v_date_3353_, 1);
                crate::leanh::lean_inc_ref(v_time_3534_);
                crate::leanh::lean_dec_ref(v_date_3353_);
                v_hour_3535_ = crate::leanh::lean_ctor_get(v_time_3534_, 0);
                crate::leanh::lean_inc(v_hour_3535_);
                crate::leanh::lean_dec_ref(v_time_3534_);
                v___x_3536_ = l_Std_Time_Hour_Ordinal_shiftTo1BasedHour(v_hour_3535_);
                crate::leanh::lean_dec(v_hour_3535_);
                if v_isShared_3533_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3532_, 1);
                    crate::leanh::lean_ctor_set(v___x_3532_, 0, v___x_3536_);
                    v___x_3538_ = v___x_3532_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_3539_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3539_, 0, v___x_3536_);
                    v___x_3538_ = v_reuseFailAlloc_3539_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_3538_;
            }
            33 => {
                v_time_3545_ = crate::leanh::lean_ctor_get(v_date_3353_, 1);
                crate::leanh::lean_inc_ref(v_time_3545_);
                crate::leanh::lean_dec_ref(v_date_3353_);
                v_minute_3546_ = crate::leanh::lean_ctor_get(v_time_3545_, 1);
                crate::leanh::lean_inc(v_minute_3546_);
                crate::leanh::lean_dec_ref(v_time_3545_);
                if v_isShared_3544_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3543_, 1);
                    crate::leanh::lean_ctor_set(v___x_3543_, 0, v_minute_3546_);
                    v___x_3548_ = v___x_3543_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_3549_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3549_, 0, v_minute_3546_);
                    v___x_3548_ = v_reuseFailAlloc_3549_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                return v___x_3548_;
            }
            35 => {
                v_time_3555_ = crate::leanh::lean_ctor_get(v_date_3353_, 1);
                crate::leanh::lean_inc_ref(v_time_3555_);
                crate::leanh::lean_dec_ref(v_date_3353_);
                v_nanosecond_3556_ = crate::leanh::lean_ctor_get(v_time_3555_, 3);
                crate::leanh::lean_inc(v_nanosecond_3556_);
                crate::leanh::lean_dec_ref(v_time_3555_);
                if v_isShared_3554_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3553_, 1);
                    crate::leanh::lean_ctor_set(v___x_3553_, 0, v_nanosecond_3556_);
                    v___x_3558_ = v___x_3553_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_3559_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3559_, 0, v_nanosecond_3556_);
                    v___x_3558_ = v_reuseFailAlloc_3559_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                return v___x_3558_;
            }
            37 => {
                v_time_3565_ = crate::leanh::lean_ctor_get(v_date_3353_, 1);
                crate::leanh::lean_inc_ref(v_time_3565_);
                crate::leanh::lean_dec_ref(v_date_3353_);
                v_second_3566_ = crate::leanh::lean_ctor_get(v_time_3565_, 2);
                crate::leanh::lean_inc(v_second_3566_);
                crate::leanh::lean_dec_ref(v_time_3565_);
                if v_isShared_3564_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3563_, 1);
                    crate::leanh::lean_ctor_set(v___x_3563_, 0, v_second_3566_);
                    v___x_3568_ = v___x_3563_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_3569_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3569_, 0, v_second_3566_);
                    v___x_3568_ = v_reuseFailAlloc_3569_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_3568_;
            }
            39 => {
                v_time_3580_ = crate::leanh::lean_ctor_get(v_date_3353_, 1);
                crate::leanh::lean_inc_ref(v_time_3580_);
                crate::leanh::lean_dec_ref(v_date_3353_);
                v_hour_3581_ = crate::leanh::lean_ctor_get(v_time_3580_, 0);
                crate::leanh::lean_inc(v_hour_3581_);
                crate::leanh::lean_dec_ref(v_time_3580_);
                v___x_3582_ = l_Std_Time_Hour_Ordinal_toRelative(v_hour_3581_);
                crate::leanh::lean_dec(v_hour_3581_);
                if v_isShared_3579_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3578_, 1);
                    crate::leanh::lean_ctor_set(v___x_3578_, 0, v___x_3582_);
                    v___x_3584_ = v___x_3578_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_3585_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3585_, 0, v___x_3582_);
                    v___x_3584_ = v_reuseFailAlloc_3585_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                return v___x_3584_;
            }
            41 => {
                v_time_3591_ = crate::leanh::lean_ctor_get(v_date_3353_, 1);
                crate::leanh::lean_inc_ref(v_time_3591_);
                crate::leanh::lean_dec_ref(v_date_3353_);
                v_hour_3592_ = crate::leanh::lean_ctor_get(v_time_3591_, 0);
                crate::leanh::lean_inc(v_hour_3592_);
                crate::leanh::lean_dec_ref(v_time_3591_);
                v___x_3593_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainTime_format___lam__0___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainTime_format___lam__0___closed__0_once),
                    _init_l_Std_Time_PlainTime_format___lam__0___closed__0,
                );
                v___x_3594_ = lean_int_emod(v_hour_3592_, v___x_3593_);
                crate::leanh::lean_dec(v_hour_3592_);
                if v_isShared_3590_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3589_, 1);
                    crate::leanh::lean_ctor_set(v___x_3589_, 0, v___x_3594_);
                    v___x_3596_ = v___x_3589_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_3597_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3597_, 0, v___x_3594_);
                    v___x_3596_ = v_reuseFailAlloc_3597_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                return v___x_3596_;
            }
            43 => {
                v_time_3603_ = crate::leanh::lean_ctor_get(v_date_3353_, 1);
                crate::leanh::lean_inc_ref(v_time_3603_);
                crate::leanh::lean_dec_ref(v_date_3353_);
                v_nanosecond_3604_ = crate::leanh::lean_ctor_get(v_time_3603_, 3);
                crate::leanh::lean_inc(v_nanosecond_3604_);
                crate::leanh::lean_dec_ref(v_time_3603_);
                if v_isShared_3602_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3601_, 1);
                    crate::leanh::lean_ctor_set(v___x_3601_, 0, v_nanosecond_3604_);
                    v___x_3606_ = v___x_3601_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_3607_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3607_, 0, v_nanosecond_3604_);
                    v___x_3606_ = v_reuseFailAlloc_3607_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                return v___x_3606_;
            }
            45 => {
                v_time_3613_ = crate::leanh::lean_ctor_get(v_date_3353_, 1);
                crate::leanh::lean_inc_ref(v_time_3613_);
                crate::leanh::lean_dec_ref(v_date_3353_);
                v___x_3614_ = l_Std_Time_PlainTime_toMilliseconds(v_time_3613_);
                crate::leanh::lean_dec_ref(v_time_3613_);
                if v_isShared_3612_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3611_, 1);
                    crate::leanh::lean_ctor_set(v___x_3611_, 0, v___x_3614_);
                    v___x_3616_ = v___x_3611_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_3617_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3617_, 0, v___x_3614_);
                    v___x_3616_ = v_reuseFailAlloc_3617_;
                    state = 46;
                    continue;
                }
            }
            46 => {
                return v___x_3616_;
            }
            47 => {
                v_time_3623_ = crate::leanh::lean_ctor_get(v_date_3353_, 1);
                crate::leanh::lean_inc_ref(v_time_3623_);
                crate::leanh::lean_dec_ref(v_date_3353_);
                v___x_3624_ = l_Std_Time_PlainTime_toNanoseconds(v_time_3623_);
                crate::leanh::lean_dec_ref(v_time_3623_);
                if v_isShared_3622_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3621_, 1);
                    crate::leanh::lean_ctor_set(v___x_3621_, 0, v___x_3624_);
                    v___x_3626_ = v___x_3621_;
                    state = 48;
                    continue;
                } else {
                    v_reuseFailAlloc_3627_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3627_, 0, v___x_3624_);
                    v___x_3626_ = v_reuseFailAlloc_3627_;
                    state = 48;
                    continue;
                }
            }
            48 => {
                return v___x_3626_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainDateTime_format___lam__0___boxed(
    mut v_date_3631_: *mut crate::leanh::LeanObject,
    mut v_locale_3632_: *mut crate::leanh::LeanObject,
    mut v_x_3633_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3634_ = l_Std_Time_PlainDateTime_format___lam__0(v_date_3631_, v_locale_3632_, v_x_3633_);
    crate::leanh::lean_dec_ref(v_locale_3632_);
    return v_res_3634_;
}
pub unsafe fn l_Std_Time_PlainDateTime_format(
    mut v_date_3635_: *mut crate::leanh::LeanObject,
    mut v_format_3636_: *mut crate::leanh::LeanObject,
    mut v_locale_3637_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_format_3639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3638_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0_once),
        _init_l_Std_Time_Formats_iso8601___closed__0,
    );
    v_format_3639_ = l_Std_Time_GenericFormat_spec___redArg(v_format_3636_, v___x_3638_);
    if crate::leanh::lean_obj_tag(v_format_3639_) == 0 {
        let mut v_a_3640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_locale_3637_);
        crate::leanh::lean_dec_ref(v_date_3635_);
        v_a_3640_ = crate::leanh::lean_ctor_get(v_format_3639_, 0);
        crate::leanh::lean_inc(v_a_3640_);
        crate::leanh::lean_dec_ref_known(v_format_3639_, 1);
        v___x_3641_ = l_Std_Time_PlainDate_format___closed__0;
        v___x_3642_ = lean_string_append(v___x_3641_, v_a_3640_);
        crate::leanh::lean_dec(v_a_3640_);
        return v___x_3642_;
    } else {
        let mut v_a_3643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_res_3645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_3643_ = crate::leanh::lean_ctor_get(v_format_3639_, 0);
        crate::leanh::lean_inc(v_a_3643_);
        crate::leanh::lean_dec_ref_known(v_format_3639_, 1);
        v___f_3644_ = crate::leanh::lean_alloc_closure(
            l_Std_Time_PlainDateTime_format___lam__0___boxed as *mut core::ffi::c_void,
            3,
            2,
        );
        crate::leanh::lean_closure_set(v___f_3644_, 0, v_date_3635_);
        crate::leanh::lean_closure_set(v___f_3644_, 1, v_locale_3637_);
        v_res_3645_ = l_Std_Time_GenericFormat_formatGeneric___redArg(v_a_3643_, v___f_3644_);
        if crate::leanh::lean_obj_tag(v_res_3645_) == 0 {
            let mut v___x_3646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3646_ = l_Std_Time_PlainDate_format___closed__1;
            return v___x_3646_;
        } else {
            let mut v_val_3647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_val_3647_ = crate::leanh::lean_ctor_get(v_res_3645_, 0);
            crate::leanh::lean_inc(v_val_3647_);
            crate::leanh::lean_dec_ref_known(v_res_3645_, 1);
            return v_val_3647_;
        }
    }
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_fromAscTimeString___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3648_ = l_Std_Time_TimeZone_GMT;
    v___x_3649_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3649_, 0, v___x_3648_);
    return v___x_3649_;
}
pub unsafe fn l_Std_Time_PlainDateTime_fromAscTimeString(
    mut v_input_3650_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3657_: u8 = 0;
    let mut v___x_3659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3661_: u8 = 0;
    let mut v_a_3662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3665_: u8 = 0;
    let mut v_date_3666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3671_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3651_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_fromAscTimeString___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDateTime_fromAscTimeString___closed__0_once
                    ),
                    _init_l_Std_Time_PlainDateTime_fromAscTimeString___closed__0,
                );
                v___x_3652_ = l_Std_Time_Formats_ascTime;
                v___x_3653_ =
                    l_Std_Time_GenericFormat_parse(v___x_3651_, v___x_3652_, v_input_3650_);
                if crate::leanh::lean_obj_tag(v___x_3653_) == 0 {
                    v_a_3654_ = crate::leanh::lean_ctor_get(v___x_3653_, 0);
                    v_isSharedCheck_3661_ = (!crate::leanh::lean_is_exclusive(v___x_3653_)) as u8;
                    if v_isSharedCheck_3661_ == 0 {
                        v___x_3656_ = v___x_3653_;
                        v_isShared_3657_ = v_isSharedCheck_3661_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3654_);
                        crate::leanh::lean_dec(v___x_3653_);
                        v___x_3656_ = crate::leanh::lean_box(0);
                        v_isShared_3657_ = v_isSharedCheck_3661_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3662_ = crate::leanh::lean_ctor_get(v___x_3653_, 0);
                    v_isSharedCheck_3671_ = (!crate::leanh::lean_is_exclusive(v___x_3653_)) as u8;
                    if v_isSharedCheck_3671_ == 0 {
                        v___x_3664_ = v___x_3653_;
                        v_isShared_3665_ = v_isSharedCheck_3671_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3662_);
                        crate::leanh::lean_dec(v___x_3653_);
                        v___x_3664_ = crate::leanh::lean_box(0);
                        v_isShared_3665_ = v_isSharedCheck_3671_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3657_ == 0 {
                    v___x_3659_ = v___x_3656_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3660_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3660_, 0, v_a_3654_);
                    v___x_3659_ = v_reuseFailAlloc_3660_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3659_;
            }
            3 => {
                v_date_3666_ = crate::leanh::lean_ctor_get(v_a_3662_, 1);
                crate::leanh::lean_inc_ref(v_date_3666_);
                crate::leanh::lean_dec(v_a_3662_);
                v___x_3667_ = lean_thunk_get_own(v_date_3666_);
                crate::leanh::lean_dec_ref(v_date_3666_);
                if v_isShared_3665_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3664_, 0, v___x_3667_);
                    v___x_3669_ = v___x_3664_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3670_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3670_, 0, v___x_3667_);
                    v___x_3669_ = v_reuseFailAlloc_3670_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3669_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainDateTime_toAscTimeString___lam__0(
    mut v_pdt_3672_: *mut crate::leanh::LeanObject,
    mut v_x_3673_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_pdt_3672_);
    return v_pdt_3672_;
}
pub unsafe fn l_Std_Time_PlainDateTime_toAscTimeString___lam__0___boxed(
    mut v_pdt_3674_: *mut crate::leanh::LeanObject,
    mut v_x_3675_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3676_ = l_Std_Time_PlainDateTime_toAscTimeString___lam__0(v_pdt_3674_, v_x_3675_);
    crate::leanh::lean_dec_ref(v_pdt_3674_);
    return v_res_3676_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_toAscTimeString___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3677_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_format___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_format___lam__0___closed__1_once),
        _init_l_Std_Time_PlainDate_format___lam__0___closed__1,
    );
    v___x_3678_ = lean_int_neg(v___x_3677_);
    return v___x_3678_;
}
pub unsafe fn l_Std_Time_PlainDateTime_toAscTimeString(
    mut v_pdt_3679_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_3681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_3684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3687_: u8 = 0;
    let mut v___f_3688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tm_3699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3705_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3680_ = l_Std_Time_TimeZone_UTC;
                v_offset_3681_ = crate::leanh::lean_ctor_get(v___x_3680_, 0);
                crate::leanh::lean_inc_ref(v_pdt_3679_);
                v___x_3682_ = l_Std_Time_PlainDateTime_toWallTime(v_pdt_3679_);
                v_second_3683_ = crate::leanh::lean_ctor_get(v___x_3682_, 0);
                v_nano_3684_ = crate::leanh::lean_ctor_get(v___x_3682_, 1);
                v_isSharedCheck_3705_ = (!crate::leanh::lean_is_exclusive(v___x_3682_)) as u8;
                if v_isSharedCheck_3705_ == 0 {
                    v___x_3686_ = v___x_3682_;
                    v_isShared_3687_ = v_isSharedCheck_3705_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nano_3684_);
                    crate::leanh::lean_inc(v_second_3683_);
                    crate::leanh::lean_dec(v___x_3682_);
                    v___x_3686_ = crate::leanh::lean_box(0);
                    v_isShared_3687_ = v_isSharedCheck_3705_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_3688_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_PlainDateTime_toAscTimeString___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3688_, 0, v_pdt_3679_);
                v___x_3689_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_fromAscTimeString___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDateTime_fromAscTimeString___closed__0_once
                    ),
                    _init_l_Std_Time_PlainDateTime_fromAscTimeString___closed__0,
                );
                v___x_3690_ = l_Std_Time_Formats_ascTime;
                v___x_3691_ = lean_int_neg(v_offset_3681_);
                v___x_3692_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_toAscTimeString___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDateTime_toAscTimeString___closed__0_once
                    ),
                    _init_l_Std_Time_PlainDateTime_toAscTimeString___closed__0,
                );
                v___x_3693_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_format___lam__0___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_format___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_format___lam__0___closed__0,
                );
                v___x_3694_ = lean_int_mul(v_second_3683_, v___x_3693_);
                crate::leanh::lean_dec(v_second_3683_);
                v___x_3695_ = lean_int_add(v___x_3694_, v_nano_3684_);
                crate::leanh::lean_dec(v_nano_3684_);
                crate::leanh::lean_dec(v___x_3694_);
                v___x_3696_ = lean_int_mul(v___x_3691_, v___x_3693_);
                crate::leanh::lean_dec(v___x_3691_);
                v___x_3697_ = lean_int_add(v___x_3696_, v___x_3692_);
                crate::leanh::lean_dec(v___x_3696_);
                v___x_3698_ = lean_int_add(v___x_3695_, v___x_3697_);
                crate::leanh::lean_dec(v___x_3697_);
                crate::leanh::lean_dec(v___x_3695_);
                v_tm_3699_ = l_Std_Time_Duration_ofNanoseconds(v___x_3698_);
                crate::leanh::lean_dec(v___x_3698_);
                v___x_3700_ = lean_mk_thunk(v___f_3688_);
                if v_isShared_3687_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3686_, 1, v___x_3700_);
                    crate::leanh::lean_ctor_set(v___x_3686_, 0, v_tm_3699_);
                    v___x_3702_ = v___x_3686_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3704_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3704_, 0, v_tm_3699_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3704_, 1, v___x_3700_);
                    v___x_3702_ = v_reuseFailAlloc_3704_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3703_ = l_Std_Time_GenericFormat_format(
                    v___x_3689_,
                    v___x_3680_,
                    v___x_3690_,
                    v___x_3702_,
                );
                return v___x_3703_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainDateTime_fromLongDateFormatString(
    mut v_input_3706_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3713_: u8 = 0;
    let mut v___x_3715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3717_: u8 = 0;
    let mut v_a_3718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3721_: u8 = 0;
    let mut v_date_3722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3727_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3707_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_fromAscTimeString___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDateTime_fromAscTimeString___closed__0_once
                    ),
                    _init_l_Std_Time_PlainDateTime_fromAscTimeString___closed__0,
                );
                v___x_3708_ = l_Std_Time_Formats_longDateFormat;
                v___x_3709_ =
                    l_Std_Time_GenericFormat_parse(v___x_3707_, v___x_3708_, v_input_3706_);
                if crate::leanh::lean_obj_tag(v___x_3709_) == 0 {
                    v_a_3710_ = crate::leanh::lean_ctor_get(v___x_3709_, 0);
                    v_isSharedCheck_3717_ = (!crate::leanh::lean_is_exclusive(v___x_3709_)) as u8;
                    if v_isSharedCheck_3717_ == 0 {
                        v___x_3712_ = v___x_3709_;
                        v_isShared_3713_ = v_isSharedCheck_3717_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3710_);
                        crate::leanh::lean_dec(v___x_3709_);
                        v___x_3712_ = crate::leanh::lean_box(0);
                        v_isShared_3713_ = v_isSharedCheck_3717_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3718_ = crate::leanh::lean_ctor_get(v___x_3709_, 0);
                    v_isSharedCheck_3727_ = (!crate::leanh::lean_is_exclusive(v___x_3709_)) as u8;
                    if v_isSharedCheck_3727_ == 0 {
                        v___x_3720_ = v___x_3709_;
                        v_isShared_3721_ = v_isSharedCheck_3727_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3718_);
                        crate::leanh::lean_dec(v___x_3709_);
                        v___x_3720_ = crate::leanh::lean_box(0);
                        v_isShared_3721_ = v_isSharedCheck_3727_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3713_ == 0 {
                    v___x_3715_ = v___x_3712_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3716_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3716_, 0, v_a_3710_);
                    v___x_3715_ = v_reuseFailAlloc_3716_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3715_;
            }
            3 => {
                v_date_3722_ = crate::leanh::lean_ctor_get(v_a_3718_, 1);
                crate::leanh::lean_inc_ref(v_date_3722_);
                crate::leanh::lean_dec(v_a_3718_);
                v___x_3723_ = lean_thunk_get_own(v_date_3722_);
                crate::leanh::lean_dec_ref(v_date_3722_);
                if v_isShared_3721_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3720_, 0, v___x_3723_);
                    v___x_3725_ = v___x_3720_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3726_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3726_, 0, v___x_3723_);
                    v___x_3725_ = v_reuseFailAlloc_3726_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3725_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainDateTime_toLongDateFormatString(
    mut v_pdt_3728_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_3730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_3733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3736_: u8 = 0;
    let mut v___f_3737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tm_3748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3754_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3729_ = l_Std_Time_TimeZone_UTC;
                v_offset_3730_ = crate::leanh::lean_ctor_get(v___x_3729_, 0);
                crate::leanh::lean_inc_ref(v_pdt_3728_);
                v___x_3731_ = l_Std_Time_PlainDateTime_toWallTime(v_pdt_3728_);
                v_second_3732_ = crate::leanh::lean_ctor_get(v___x_3731_, 0);
                v_nano_3733_ = crate::leanh::lean_ctor_get(v___x_3731_, 1);
                v_isSharedCheck_3754_ = (!crate::leanh::lean_is_exclusive(v___x_3731_)) as u8;
                if v_isSharedCheck_3754_ == 0 {
                    v___x_3735_ = v___x_3731_;
                    v_isShared_3736_ = v_isSharedCheck_3754_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nano_3733_);
                    crate::leanh::lean_inc(v_second_3732_);
                    crate::leanh::lean_dec(v___x_3731_);
                    v___x_3735_ = crate::leanh::lean_box(0);
                    v_isShared_3736_ = v_isSharedCheck_3754_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_3737_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_PlainDateTime_toAscTimeString___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3737_, 0, v_pdt_3728_);
                v___x_3738_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_fromAscTimeString___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDateTime_fromAscTimeString___closed__0_once
                    ),
                    _init_l_Std_Time_PlainDateTime_fromAscTimeString___closed__0,
                );
                v___x_3739_ = l_Std_Time_Formats_longDateFormat;
                v___x_3740_ = lean_int_neg(v_offset_3730_);
                v___x_3741_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_toAscTimeString___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDateTime_toAscTimeString___closed__0_once
                    ),
                    _init_l_Std_Time_PlainDateTime_toAscTimeString___closed__0,
                );
                v___x_3742_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_format___lam__0___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_format___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_format___lam__0___closed__0,
                );
                v___x_3743_ = lean_int_mul(v_second_3732_, v___x_3742_);
                crate::leanh::lean_dec(v_second_3732_);
                v___x_3744_ = lean_int_add(v___x_3743_, v_nano_3733_);
                crate::leanh::lean_dec(v_nano_3733_);
                crate::leanh::lean_dec(v___x_3743_);
                v___x_3745_ = lean_int_mul(v___x_3740_, v___x_3742_);
                crate::leanh::lean_dec(v___x_3740_);
                v___x_3746_ = lean_int_add(v___x_3745_, v___x_3741_);
                crate::leanh::lean_dec(v___x_3745_);
                v___x_3747_ = lean_int_add(v___x_3744_, v___x_3746_);
                crate::leanh::lean_dec(v___x_3746_);
                crate::leanh::lean_dec(v___x_3744_);
                v_tm_3748_ = l_Std_Time_Duration_ofNanoseconds(v___x_3747_);
                crate::leanh::lean_dec(v___x_3747_);
                v___x_3749_ = lean_mk_thunk(v___f_3737_);
                if v_isShared_3736_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3735_, 1, v___x_3749_);
                    crate::leanh::lean_ctor_set(v___x_3735_, 0, v_tm_3748_);
                    v___x_3751_ = v___x_3735_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3753_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3753_, 0, v_tm_3748_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3753_, 1, v___x_3749_);
                    v___x_3751_ = v_reuseFailAlloc_3753_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3752_ = l_Std_Time_GenericFormat_format(
                    v___x_3738_,
                    v___x_3729_,
                    v___x_3739_,
                    v___x_3751_,
                );
                return v___x_3752_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainDateTime_fromDateTimeString(
    mut v_input_3755_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3762_: u8 = 0;
    let mut v___x_3764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3766_: u8 = 0;
    let mut v_a_3767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3770_: u8 = 0;
    let mut v_date_3771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3776_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3756_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_fromAscTimeString___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDateTime_fromAscTimeString___closed__0_once
                    ),
                    _init_l_Std_Time_PlainDateTime_fromAscTimeString___closed__0,
                );
                v___x_3757_ = l_Std_Time_Formats_dateTime24Hour;
                v___x_3758_ =
                    l_Std_Time_GenericFormat_parse(v___x_3756_, v___x_3757_, v_input_3755_);
                if crate::leanh::lean_obj_tag(v___x_3758_) == 0 {
                    v_a_3759_ = crate::leanh::lean_ctor_get(v___x_3758_, 0);
                    v_isSharedCheck_3766_ = (!crate::leanh::lean_is_exclusive(v___x_3758_)) as u8;
                    if v_isSharedCheck_3766_ == 0 {
                        v___x_3761_ = v___x_3758_;
                        v_isShared_3762_ = v_isSharedCheck_3766_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3759_);
                        crate::leanh::lean_dec(v___x_3758_);
                        v___x_3761_ = crate::leanh::lean_box(0);
                        v_isShared_3762_ = v_isSharedCheck_3766_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3767_ = crate::leanh::lean_ctor_get(v___x_3758_, 0);
                    v_isSharedCheck_3776_ = (!crate::leanh::lean_is_exclusive(v___x_3758_)) as u8;
                    if v_isSharedCheck_3776_ == 0 {
                        v___x_3769_ = v___x_3758_;
                        v_isShared_3770_ = v_isSharedCheck_3776_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3767_);
                        crate::leanh::lean_dec(v___x_3758_);
                        v___x_3769_ = crate::leanh::lean_box(0);
                        v_isShared_3770_ = v_isSharedCheck_3776_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3762_ == 0 {
                    v___x_3764_ = v___x_3761_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3765_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3765_, 0, v_a_3759_);
                    v___x_3764_ = v_reuseFailAlloc_3765_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3764_;
            }
            3 => {
                v_date_3771_ = crate::leanh::lean_ctor_get(v_a_3767_, 1);
                crate::leanh::lean_inc_ref(v_date_3771_);
                crate::leanh::lean_dec(v_a_3767_);
                v___x_3772_ = lean_thunk_get_own(v_date_3771_);
                crate::leanh::lean_dec_ref(v_date_3771_);
                if v_isShared_3770_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3769_, 0, v___x_3772_);
                    v___x_3774_ = v___x_3769_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3775_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3775_, 0, v___x_3772_);
                    v___x_3774_ = v_reuseFailAlloc_3775_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3774_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainDateTime_toDateTimeString(
    mut v_pdt_3777_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_3778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_3779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_year_3780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_month_3781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_day_3782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hour_3783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_minute_3784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_3786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_12__overap_3788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_date_3778_ = crate::leanh::lean_ctor_get(v_pdt_3777_, 0);
    crate::leanh::lean_inc_ref(v_date_3778_);
    v_time_3779_ = crate::leanh::lean_ctor_get(v_pdt_3777_, 1);
    crate::leanh::lean_inc_ref(v_time_3779_);
    crate::leanh::lean_dec_ref(v_pdt_3777_);
    v_year_3780_ = crate::leanh::lean_ctor_get(v_date_3778_, 0);
    crate::leanh::lean_inc(v_year_3780_);
    v_month_3781_ = crate::leanh::lean_ctor_get(v_date_3778_, 1);
    crate::leanh::lean_inc(v_month_3781_);
    v_day_3782_ = crate::leanh::lean_ctor_get(v_date_3778_, 2);
    crate::leanh::lean_inc(v_day_3782_);
    crate::leanh::lean_dec_ref(v_date_3778_);
    v_hour_3783_ = crate::leanh::lean_ctor_get(v_time_3779_, 0);
    crate::leanh::lean_inc(v_hour_3783_);
    v_minute_3784_ = crate::leanh::lean_ctor_get(v_time_3779_, 1);
    crate::leanh::lean_inc(v_minute_3784_);
    v_second_3785_ = crate::leanh::lean_ctor_get(v_time_3779_, 2);
    crate::leanh::lean_inc(v_second_3785_);
    v_nanosecond_3786_ = crate::leanh::lean_ctor_get(v_time_3779_, 3);
    crate::leanh::lean_inc(v_nanosecond_3786_);
    crate::leanh::lean_dec_ref(v_time_3779_);
    v___x_3787_ = l_Std_Time_Formats_dateTime24Hour;
    v___x_12__overap_3788_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_3787_);
    v___x_3789_ = crate::leanh::lean_apply_7(
        v___x_12__overap_3788_,
        v_year_3780_,
        v_month_3781_,
        v_day_3782_,
        v_hour_3783_,
        v_minute_3784_,
        v_second_3785_,
        v_nanosecond_3786_,
    );
    return v___x_3789_;
}
pub unsafe fn l_Std_Time_PlainDateTime_fromLeanDateTimeString(
    mut v_input_3790_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3796_: u8 = 0;
    let mut v___x_3798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3800_: u8 = 0;
    let mut v_a_3801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3804_: u8 = 0;
    let mut v_date_3805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3810_: u8 = 0;
    let mut v___x_3811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3811_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_fromAscTimeString___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDateTime_fromAscTimeString___closed__0_once
                    ),
                    _init_l_Std_Time_PlainDateTime_fromAscTimeString___closed__0,
                );
                v___x_3812_ = l_Std_Time_Formats_leanDateTime24Hour;
                crate::leanh::lean_inc_ref(v_input_3790_);
                v___x_3813_ =
                    l_Std_Time_GenericFormat_parse(v___x_3811_, v___x_3812_, v_input_3790_);
                if crate::leanh::lean_obj_tag(v___x_3813_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_3813_, 1);
                    v___x_3814_ = l_Std_Time_Formats_leanDateTime24HourNoNanos;
                    v___x_3815_ =
                        l_Std_Time_GenericFormat_parse(v___x_3811_, v___x_3814_, v_input_3790_);
                    v___y_3792_ = v___x_3815_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_input_3790_);
                    v___y_3792_ = v___x_3813_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v___y_3792_) == 0 {
                    v_a_3793_ = crate::leanh::lean_ctor_get(v___y_3792_, 0);
                    v_isSharedCheck_3800_ = (!crate::leanh::lean_is_exclusive(v___y_3792_)) as u8;
                    if v_isSharedCheck_3800_ == 0 {
                        v___x_3795_ = v___y_3792_;
                        v_isShared_3796_ = v_isSharedCheck_3800_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3793_);
                        crate::leanh::lean_dec(v___y_3792_);
                        v___x_3795_ = crate::leanh::lean_box(0);
                        v_isShared_3796_ = v_isSharedCheck_3800_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_3801_ = crate::leanh::lean_ctor_get(v___y_3792_, 0);
                    v_isSharedCheck_3810_ = (!crate::leanh::lean_is_exclusive(v___y_3792_)) as u8;
                    if v_isSharedCheck_3810_ == 0 {
                        v___x_3803_ = v___y_3792_;
                        v_isShared_3804_ = v_isSharedCheck_3810_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3801_);
                        crate::leanh::lean_dec(v___y_3792_);
                        v___x_3803_ = crate::leanh::lean_box(0);
                        v_isShared_3804_ = v_isSharedCheck_3810_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3796_ == 0 {
                    v___x_3798_ = v___x_3795_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3799_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3799_, 0, v_a_3793_);
                    v___x_3798_ = v_reuseFailAlloc_3799_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3798_;
            }
            4 => {
                v_date_3805_ = crate::leanh::lean_ctor_get(v_a_3801_, 1);
                crate::leanh::lean_inc_ref(v_date_3805_);
                crate::leanh::lean_dec(v_a_3801_);
                v___x_3806_ = lean_thunk_get_own(v_date_3805_);
                crate::leanh::lean_dec_ref(v_date_3805_);
                if v_isShared_3804_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3803_, 0, v___x_3806_);
                    v___x_3808_ = v___x_3803_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3809_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3809_, 0, v___x_3806_);
                    v___x_3808_ = v_reuseFailAlloc_3809_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3808_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainDateTime_toLeanDateTimeString(
    mut v_pdt_3816_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_3817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_3818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_year_3819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_month_3820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_day_3821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hour_3822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_minute_3823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_3825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_12__overap_3827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_date_3817_ = crate::leanh::lean_ctor_get(v_pdt_3816_, 0);
    crate::leanh::lean_inc_ref(v_date_3817_);
    v_time_3818_ = crate::leanh::lean_ctor_get(v_pdt_3816_, 1);
    crate::leanh::lean_inc_ref(v_time_3818_);
    crate::leanh::lean_dec_ref(v_pdt_3816_);
    v_year_3819_ = crate::leanh::lean_ctor_get(v_date_3817_, 0);
    crate::leanh::lean_inc(v_year_3819_);
    v_month_3820_ = crate::leanh::lean_ctor_get(v_date_3817_, 1);
    crate::leanh::lean_inc(v_month_3820_);
    v_day_3821_ = crate::leanh::lean_ctor_get(v_date_3817_, 2);
    crate::leanh::lean_inc(v_day_3821_);
    crate::leanh::lean_dec_ref(v_date_3817_);
    v_hour_3822_ = crate::leanh::lean_ctor_get(v_time_3818_, 0);
    crate::leanh::lean_inc(v_hour_3822_);
    v_minute_3823_ = crate::leanh::lean_ctor_get(v_time_3818_, 1);
    crate::leanh::lean_inc(v_minute_3823_);
    v_second_3824_ = crate::leanh::lean_ctor_get(v_time_3818_, 2);
    crate::leanh::lean_inc(v_second_3824_);
    v_nanosecond_3825_ = crate::leanh::lean_ctor_get(v_time_3818_, 3);
    crate::leanh::lean_inc(v_nanosecond_3825_);
    crate::leanh::lean_dec_ref(v_time_3818_);
    v___x_3826_ = l_Std_Time_Formats_leanDateTime24Hour;
    v___x_12__overap_3827_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_3826_);
    v___x_3828_ = crate::leanh::lean_apply_7(
        v___x_12__overap_3827_,
        v_year_3819_,
        v_month_3820_,
        v_day_3821_,
        v_hour_3822_,
        v_minute_3823_,
        v_second_3824_,
        v_nanosecond_3825_,
    );
    return v___x_3828_;
}
pub unsafe fn l_Std_Time_PlainDateTime_parse(
    mut v_date_3829_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_date_3829_);
    v___x_3830_ = l_Std_Time_PlainDateTime_fromAscTimeString(v_date_3829_);
    if crate::leanh::lean_obj_tag(v___x_3830_) == 0 {
        let mut v___x_3831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref_known(v___x_3830_, 1);
        crate::leanh::lean_inc_ref(v_date_3829_);
        v___x_3831_ = l_Std_Time_PlainDateTime_fromLongDateFormatString(v_date_3829_);
        if crate::leanh::lean_obj_tag(v___x_3831_) == 0 {
            let mut v___x_3832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref_known(v___x_3831_, 1);
            crate::leanh::lean_inc_ref(v_date_3829_);
            v___x_3832_ = l_Std_Time_PlainDateTime_fromDateTimeString(v_date_3829_);
            if crate::leanh::lean_obj_tag(v___x_3832_) == 0 {
                let mut v___x_3833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref_known(v___x_3832_, 1);
                v___x_3833_ = l_Std_Time_PlainDateTime_fromLeanDateTimeString(v_date_3829_);
                return v___x_3833_;
            } else {
                crate::leanh::lean_dec_ref(v_date_3829_);
                return v___x_3832_;
            }
        } else {
            crate::leanh::lean_dec_ref(v_date_3829_);
            return v___x_3831_;
        }
    } else {
        crate::leanh::lean_dec_ref(v_date_3829_);
        return v___x_3830_;
    }
}
pub unsafe fn l_Std_Time_PlainDateTime_instRepr___lam__0(
    mut v_data_3839_: *mut crate::leanh::LeanObject,
    mut v___y_3840_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3841_ = l_Std_Time_PlainDateTime_instRepr___lam__0___closed__1;
    v___x_3842_ = l_Std_Time_PlainDateTime_toLeanDateTimeString(v_data_3839_);
    v___x_3843_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3843_, 0, v___x_3842_);
    v___x_3844_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3844_, 0, v___x_3841_);
    crate::leanh::lean_ctor_set(v___x_3844_, 1, v___x_3843_);
    v___x_3845_ = l_Std_Time_PlainDate_instRepr___lam__0___closed__3;
    v___x_3846_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3846_, 0, v___x_3844_);
    crate::leanh::lean_ctor_set(v___x_3846_, 1, v___x_3845_);
    v___x_3847_ = l_Repr_addAppParen(v___x_3846_, v___y_3840_);
    return v___x_3847_;
}
pub unsafe fn l_Std_Time_PlainDateTime_instRepr___lam__0___boxed(
    mut v_data_3848_: *mut crate::leanh::LeanObject,
    mut v___y_3849_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3850_ = l_Std_Time_PlainDateTime_instRepr___lam__0(v_data_3848_, v___y_3849_);
    crate::leanh::lean_dec(v___y_3849_);
    return v_res_3850_;
}
pub unsafe fn l_Std_Time_DateTime_format(
    mut v_tz_3853_: *mut crate::leanh::LeanObject,
    mut v_data_3854_: *mut crate::leanh::LeanObject,
    mut v_format_3855_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_format_3857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3856_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0_once),
        _init_l_Std_Time_Formats_iso8601___closed__0,
    );
    v_format_3857_ = l_Std_Time_GenericFormat_spec___redArg(v_format_3855_, v___x_3856_);
    if crate::leanh::lean_obj_tag(v_format_3857_) == 0 {
        let mut v_a_3858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_data_3854_);
        v_a_3858_ = crate::leanh::lean_ctor_get(v_format_3857_, 0);
        crate::leanh::lean_inc(v_a_3858_);
        crate::leanh::lean_dec_ref_known(v_format_3857_, 1);
        v___x_3859_ = l_Std_Time_PlainDate_format___closed__0;
        v___x_3860_ = lean_string_append(v___x_3859_, v_a_3858_);
        crate::leanh::lean_dec(v_a_3858_);
        return v___x_3860_;
    } else {
        let mut v_a_3861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_3861_ = crate::leanh::lean_ctor_get(v_format_3857_, 0);
        crate::leanh::lean_inc(v_a_3861_);
        crate::leanh::lean_dec_ref_known(v_format_3857_, 1);
        v___x_3862_ = crate::leanh::lean_box(1);
        v___x_3863_ =
            l_Std_Time_GenericFormat_format(v___x_3862_, v_tz_3853_, v_a_3861_, v_data_3854_);
        return v___x_3863_;
    }
}
pub unsafe fn l_Std_Time_DateTime_format___boxed(
    mut v_tz_3864_: *mut crate::leanh::LeanObject,
    mut v_data_3865_: *mut crate::leanh::LeanObject,
    mut v_format_3866_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3867_ = l_Std_Time_DateTime_format(v_tz_3864_, v_data_3865_, v_format_3866_);
    crate::leanh::lean_dec_ref(v_tz_3864_);
    return v_res_3867_;
}
pub unsafe fn l_Std_Time_DateTime_fromAscTimeString(
    mut v_input_3868_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3869_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_fromAscTimeString___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_fromAscTimeString___closed__0_once),
        _init_l_Std_Time_PlainDateTime_fromAscTimeString___closed__0,
    );
    v___x_3870_ = l_Std_Time_Formats_ascTime;
    v___x_3871_ = l_Std_Time_GenericFormat_parse(v___x_3869_, v___x_3870_, v_input_3868_);
    return v___x_3871_;
}
pub unsafe fn l_Std_Time_DateTime_toAscTimeString(
    mut v_datetime_3872_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3873_ = l_Std_Time_TimeZone_GMT;
    v___x_3874_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_fromAscTimeString___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_fromAscTimeString___closed__0_once),
        _init_l_Std_Time_PlainDateTime_fromAscTimeString___closed__0,
    );
    v___x_3875_ = l_Std_Time_Formats_ascTime;
    v___x_3876_ =
        l_Std_Time_GenericFormat_format(v___x_3874_, v___x_3873_, v___x_3875_, v_datetime_3872_);
    return v___x_3876_;
}
pub unsafe fn l_Std_Time_DateTime_fromLongDateFormatString(
    mut v_input_3877_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3878_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_fromAscTimeString___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_fromAscTimeString___closed__0_once),
        _init_l_Std_Time_PlainDateTime_fromAscTimeString___closed__0,
    );
    v___x_3879_ = l_Std_Time_Formats_longDateFormat;
    v___x_3880_ = l_Std_Time_GenericFormat_parse(v___x_3878_, v___x_3879_, v_input_3877_);
    return v___x_3880_;
}
pub unsafe fn l_Std_Time_DateTime_toLongDateFormatString(
    mut v_datetime_3881_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3882_ = l_Std_Time_TimeZone_GMT;
    v___x_3883_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_fromAscTimeString___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_fromAscTimeString___closed__0_once),
        _init_l_Std_Time_PlainDateTime_fromAscTimeString___closed__0,
    );
    v___x_3884_ = l_Std_Time_Formats_longDateFormat;
    v___x_3885_ =
        l_Std_Time_GenericFormat_format(v___x_3883_, v___x_3882_, v___x_3884_, v_datetime_3881_);
    return v___x_3885_;
}
pub unsafe fn l_Std_Time_DateTime_toISO8601String(
    mut v_tz_3886_: *mut crate::leanh::LeanObject,
    mut v_date_3887_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3888_ = crate::leanh::lean_box(1);
    v___x_3889_ = l_Std_Time_Formats_iso8601;
    v___x_3890_ =
        l_Std_Time_GenericFormat_format(v___x_3888_, v_tz_3886_, v___x_3889_, v_date_3887_);
    return v___x_3890_;
}
pub unsafe fn l_Std_Time_DateTime_toISO8601String___boxed(
    mut v_tz_3891_: *mut crate::leanh::LeanObject,
    mut v_date_3892_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3893_ = l_Std_Time_DateTime_toISO8601String(v_tz_3891_, v_date_3892_);
    crate::leanh::lean_dec_ref(v_tz_3891_);
    return v_res_3893_;
}
pub unsafe fn l_Std_Time_DateTime_toRFC822String(
    mut v_tz_3894_: *mut crate::leanh::LeanObject,
    mut v_date_3895_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3896_ = crate::leanh::lean_box(1);
    v___x_3897_ = l_Std_Time_Formats_rfc822;
    v___x_3898_ =
        l_Std_Time_GenericFormat_format(v___x_3896_, v_tz_3894_, v___x_3897_, v_date_3895_);
    return v___x_3898_;
}
pub unsafe fn l_Std_Time_DateTime_toRFC822String___boxed(
    mut v_tz_3899_: *mut crate::leanh::LeanObject,
    mut v_date_3900_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3901_ = l_Std_Time_DateTime_toRFC822String(v_tz_3899_, v_date_3900_);
    crate::leanh::lean_dec_ref(v_tz_3899_);
    return v_res_3901_;
}
pub unsafe fn l_Std_Time_DateTime_toRFC850String(
    mut v_tz_3902_: *mut crate::leanh::LeanObject,
    mut v_date_3903_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3904_ = crate::leanh::lean_box(1);
    v___x_3905_ = l_Std_Time_Formats_rfc850;
    v___x_3906_ =
        l_Std_Time_GenericFormat_format(v___x_3904_, v_tz_3902_, v___x_3905_, v_date_3903_);
    return v___x_3906_;
}
pub unsafe fn l_Std_Time_DateTime_toRFC850String___boxed(
    mut v_tz_3907_: *mut crate::leanh::LeanObject,
    mut v_date_3908_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3909_ = l_Std_Time_DateTime_toRFC850String(v_tz_3907_, v_date_3908_);
    crate::leanh::lean_dec_ref(v_tz_3907_);
    return v_res_3909_;
}
pub unsafe fn l_Std_Time_DateTime_toDateTimeWithZoneString(
    mut v_tz_3910_: *mut crate::leanh::LeanObject,
    mut v_pdt_3911_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3912_ = crate::leanh::lean_box(1);
    v___x_3913_ = l_Std_Time_Formats_dateTimeWithZone;
    v___x_3914_ =
        l_Std_Time_GenericFormat_format(v___x_3912_, v_tz_3910_, v___x_3913_, v_pdt_3911_);
    return v___x_3914_;
}
pub unsafe fn l_Std_Time_DateTime_toDateTimeWithZoneString___boxed(
    mut v_tz_3915_: *mut crate::leanh::LeanObject,
    mut v_pdt_3916_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3917_ = l_Std_Time_DateTime_toDateTimeWithZoneString(v_tz_3915_, v_pdt_3916_);
    crate::leanh::lean_dec_ref(v_tz_3915_);
    return v_res_3917_;
}
pub unsafe fn l_Std_Time_DateTime_toLeanDateTimeWithZoneString(
    mut v_tz_3918_: *mut crate::leanh::LeanObject,
    mut v_pdt_3919_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3920_ = crate::leanh::lean_box(1);
    v___x_3921_ = l_Std_Time_Formats_leanDateTimeWithZone;
    v___x_3922_ =
        l_Std_Time_GenericFormat_format(v___x_3920_, v_tz_3918_, v___x_3921_, v_pdt_3919_);
    return v___x_3922_;
}
pub unsafe fn l_Std_Time_DateTime_toLeanDateTimeWithZoneString___boxed(
    mut v_tz_3923_: *mut crate::leanh::LeanObject,
    mut v_pdt_3924_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3925_ = l_Std_Time_DateTime_toLeanDateTimeWithZoneString(v_tz_3923_, v_pdt_3924_);
    crate::leanh::lean_dec_ref(v_tz_3923_);
    return v_res_3925_;
}
pub unsafe fn l_Std_Time_DateTime_parse(
    mut v_date_3926_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_date_3926_);
    v___x_3927_ = l_Std_Time_DateTime_fromAscTimeString(v_date_3926_);
    if crate::leanh::lean_obj_tag(v___x_3927_) == 0 {
        let mut v___x_3928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref_known(v___x_3927_, 1);
        v___x_3928_ = l_Std_Time_DateTime_fromLongDateFormatString(v_date_3926_);
        return v___x_3928_;
    } else {
        crate::leanh::lean_dec_ref(v_date_3926_);
        return v___x_3927_;
    }
}
pub unsafe fn l_Std_Time_DateTime_instRepr___lam__0(
    mut v_tz_3929_: *mut crate::leanh::LeanObject,
    mut v_data_3930_: *mut crate::leanh::LeanObject,
    mut v___y_3931_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3932_ = l_Std_Time_DateTime_toLeanDateTimeWithZoneString(v_tz_3929_, v_data_3930_);
    v___x_3933_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3933_, 0, v___x_3932_);
    v___x_3934_ = l_Repr_addAppParen(v___x_3933_, v___y_3931_);
    return v___x_3934_;
}
pub unsafe fn l_Std_Time_DateTime_instRepr___lam__0___boxed(
    mut v_tz_3935_: *mut crate::leanh::LeanObject,
    mut v_data_3936_: *mut crate::leanh::LeanObject,
    mut v___y_3937_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3938_ = l_Std_Time_DateTime_instRepr___lam__0(v_tz_3935_, v_data_3936_, v___y_3937_);
    crate::leanh::lean_dec(v___y_3937_);
    crate::leanh::lean_dec_ref(v_tz_3935_);
    return v_res_3938_;
}
pub unsafe fn l_Std_Time_DateTime_instRepr(
    mut v_tz_3939_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3940_ = crate::leanh::lean_alloc_closure(
        l_Std_Time_DateTime_instRepr___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3940_, 0, v_tz_3939_);
    return v___f_3940_;
}
pub unsafe fn l_Std_Time_DateTime_instToString(
    mut v_tz_3941_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3942_ = crate::leanh::lean_alloc_closure(
        l_Std_Time_DateTime_toLeanDateTimeWithZoneString___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___x_3942_, 0, v_tz_3941_);
    return v___x_3942_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Time_Format(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Time_Notation_Spec(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Format_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Format_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Std_Time_Formats_iso8601 = _init_l_Std_Time_Formats_iso8601();
    crate::leanh::lean_mark_persistent(l_Std_Time_Formats_iso8601);
    l_Std_Time_Formats_americanDate = _init_l_Std_Time_Formats_americanDate();
    crate::leanh::lean_mark_persistent(l_Std_Time_Formats_americanDate);
    l_Std_Time_Formats_europeanDate = _init_l_Std_Time_Formats_europeanDate();
    crate::leanh::lean_mark_persistent(l_Std_Time_Formats_europeanDate);
    l_Std_Time_Formats_time12Hour = _init_l_Std_Time_Formats_time12Hour();
    crate::leanh::lean_mark_persistent(l_Std_Time_Formats_time12Hour);
    l_Std_Time_Formats_time24Hour = _init_l_Std_Time_Formats_time24Hour();
    crate::leanh::lean_mark_persistent(l_Std_Time_Formats_time24Hour);
    l_Std_Time_Formats_dateTime24Hour = _init_l_Std_Time_Formats_dateTime24Hour();
    crate::leanh::lean_mark_persistent(l_Std_Time_Formats_dateTime24Hour);
    l_Std_Time_Formats_dateTimeWithZone = _init_l_Std_Time_Formats_dateTimeWithZone();
    crate::leanh::lean_mark_persistent(l_Std_Time_Formats_dateTimeWithZone);
    l_Std_Time_Formats_leanTime24Hour = _init_l_Std_Time_Formats_leanTime24Hour();
    crate::leanh::lean_mark_persistent(l_Std_Time_Formats_leanTime24Hour);
    l_Std_Time_Formats_leanTime24HourNoNanos = _init_l_Std_Time_Formats_leanTime24HourNoNanos();
    crate::leanh::lean_mark_persistent(l_Std_Time_Formats_leanTime24HourNoNanos);
    l_Std_Time_Formats_leanDateTime24Hour = _init_l_Std_Time_Formats_leanDateTime24Hour();
    crate::leanh::lean_mark_persistent(l_Std_Time_Formats_leanDateTime24Hour);
    l_Std_Time_Formats_leanDateTime24HourNoNanos =
        _init_l_Std_Time_Formats_leanDateTime24HourNoNanos();
    crate::leanh::lean_mark_persistent(l_Std_Time_Formats_leanDateTime24HourNoNanos);
    l_Std_Time_Formats_leanDateTimeWithZone = _init_l_Std_Time_Formats_leanDateTimeWithZone();
    crate::leanh::lean_mark_persistent(l_Std_Time_Formats_leanDateTimeWithZone);
    l_Std_Time_Formats_leanDateTimeWithZoneNoNanos =
        _init_l_Std_Time_Formats_leanDateTimeWithZoneNoNanos();
    crate::leanh::lean_mark_persistent(l_Std_Time_Formats_leanDateTimeWithZoneNoNanos);
    l_Std_Time_Formats_leanDateTimeWithIdentifier =
        _init_l_Std_Time_Formats_leanDateTimeWithIdentifier();
    crate::leanh::lean_mark_persistent(l_Std_Time_Formats_leanDateTimeWithIdentifier);
    l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos =
        _init_l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos();
    crate::leanh::lean_mark_persistent(l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos);
    l_Std_Time_Formats_leanDate = _init_l_Std_Time_Formats_leanDate();
    crate::leanh::lean_mark_persistent(l_Std_Time_Formats_leanDate);
    l_Std_Time_Formats_sqlDate = _init_l_Std_Time_Formats_sqlDate();
    crate::leanh::lean_mark_persistent(l_Std_Time_Formats_sqlDate);
    l_Std_Time_Formats_longDateFormat = _init_l_Std_Time_Formats_longDateFormat();
    crate::leanh::lean_mark_persistent(l_Std_Time_Formats_longDateFormat);
    l_Std_Time_Formats_ascTime = _init_l_Std_Time_Formats_ascTime();
    crate::leanh::lean_mark_persistent(l_Std_Time_Formats_ascTime);
    l_Std_Time_Formats_rfc822 = _init_l_Std_Time_Formats_rfc822();
    crate::leanh::lean_mark_persistent(l_Std_Time_Formats_rfc822);
    l_Std_Time_Formats_rfc850 = _init_l_Std_Time_Formats_rfc850();
    crate::leanh::lean_mark_persistent(l_Std_Time_Formats_rfc850);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Time_Format(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Time_Format(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Time_Notation_Spec(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Time_Format_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Time_Format_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Format(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Time_Format(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Time_Format(builtin);
}
